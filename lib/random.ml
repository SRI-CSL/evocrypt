open Domainslib

open EcPrimeField
open FieldPolynomial
open Shamir
open EcList

module PrimeField = struct

  let dt' : unit -> Z.t = fun _ -> Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !EcPrimeField.q
  let dt () =
    let coef = ref Z.zero in
    let quit = ref false in
    while not !quit do
      coef := dt' () ;
      if not (Z.equal !coef Z.zero) then quit := true
    done ;
    !coef

end 

module Polynomial = struct

  let rec dpolynomial' (i : Z.t) (d : Z.t) (p : monomial list) : monomial list =
    if Z.gt i d then p
    else
      let coef = PrimeField.dt () in
      if coef = Z.zero then dpolynomial' i d p
      else dpolynomial' (Z.add i Z.one) d (Cons ({ coef = coef ; expo = i}, p))
      
  let dpolynomial : Z.t -> monomial list =
    fun n -> dpolynomial' Z.zero n Nil

end

module Shamir (PC : PartyConfiguration) = struct

  let rec shamir_random_generator' i n =
    if Z.equal i n then Nil
    else
      let r = Polynomial.dpolynomial PC.t in
      Cons (r, shamir_random_generator' (Z.add i Z.one) n)

  let shamir_random_generator n = shamir_random_generator' Z.zero n

end

module BGW (PC : PartyConfiguration) = struct

  open ArithmeticCircuit 
  open ArithmeticGates
  open BGWAddition
  open BGWMultiplication
  open BGWSMultiplication
  open BGWRefresh
  open BGWProtocol

  open ArithmeticProtocol

  module BGWData = ArithmeticProtocolData (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC))

  let rec bgw_party_random_generator (g : ArithmeticGates.gates_t) =
    match g with
    | PInput _ -> Nil
    | SInput _ -> Nil
    | Constant _ -> Nil
    | Addition (gid, wl, wr) -> 
       concat (concat (bgw_party_random_generator wl) (Cons ((gid, BGWData.AdditionRand ()), Nil))) (bgw_party_random_generator wr)
    | Multiplication (gid, wl, wr) -> 
       concat (concat (bgw_party_random_generator wl) (Cons ((gid, BGWData.MultiplicationRand (Polynomial.dpolynomial PC.t)), Nil))) (bgw_party_random_generator wr)
    | SMultiplication (gid, wl, wr) -> 
       concat (concat (bgw_party_random_generator wl) (Cons ((gid, BGWData.SMultiplicationRand ()), Nil))) (bgw_party_random_generator wr)

  let bgw_random_generator (g : ArithmeticGates.gates_t) = map (fun pid -> (pid, (bgw_party_random_generator g, Polynomial.dpolynomial PC.t))) PC.pid_set

end

module MITHBGW (PC : PartyConfiguration) = struct

  open ArithmeticCircuit 
  open ArithmeticGates

  module ShamirR = Shamir(PC)
  module BGWR = BGW(PC)

  let generate_prover_randomness (g : ArithmeticGates.gates_t) n =
    let r_ss = ShamirR.shamir_random_generator n in
    let r_mpc = BGWR.bgw_random_generator g in
    let r_cs = map (fun pid -> (pid, ())) PC.pid_set in
    (r_ss, r_mpc, r_cs)

  let dt' : unit -> Z.t = fun _ -> Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) (Z.add PC.n Z.one)
  let dt () =
    let coef = ref Z.zero in
    let quit = ref false in
    while not !quit do
      coef := dt' () ;
      if not (Z.equal !coef Z.zero) then quit := true
    done ;
    !coef

  let generate_verifier_randomness () = 
    let r1 = ref Z.zero in
    let r2 = ref Z.zero in
    let quit_loop = ref false in
  
    while not !quit_loop do
      let r1' = dt () in
      let r2' = dt () in
      if r1' <> r2' && r1' <> Z.zero && r2' <> Z.zero then
        begin r1 := r1' ; r2 := r2' ; quit_loop := true ; end
    done ;
    (!r1, !r2) ;;

end

module LPZK = struct

  open LPZK

  let dt' () = Z.rem (Z.of_bits (Cryptokit.Random.string (Cryptokit.Random.pseudo_rng "0000000000000000") 128)) !LPZK.q
  let dt () =
    let coef = ref Z.zero in
    let quit = ref false in
    while not !quit do
      coef := dt' () ;
      if not (Z.equal !coef Z.zero) then quit := true
    done ;
    !coef

  let generate_lpzk_prover_randomness (ngates : int) : LPZK.prover_rand_t =
    let total_rand = ngates + 2 + 1 in
    let rp = Array.make total_rand LPZK.def_ui in
    let generate_random_ui () = { a = dt () ; b = dt () ; a' = dt () ; b' = dt () } in

    for i = 0 to total_rand - 1 do
      Array.set rp i (generate_random_ui ())
    done;
    rp

  let generate_lpzk_verifier_randomness (ngates : int) : LPZK.verifier_rand_t =
    let total_rand = ngates + 2 + 1 in
    let y = Array.make total_rand def_yi in
    let alpha = Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !LPZK.q in

    for i = 0 to total_rand - 1 do
      let a = dt () in
      let b = dt () in
      let a' = dt () in
      let b' = dt () in
      Array.set y i { v = Z.erem (Z.add (Z.mul a alpha) b) !LPZK.q ; v' = Z.erem (Z.add (Z.mul a' alpha) b') !LPZK.q }
    done;
    { alpha = alpha ; y = y }

  let parallel_generate_lpzk_prover_randomness pool (ngates : int) : LPZK.prover_rand_t =
    let total_rand = ngates + 2 + 1 in
    let rp = Array.make total_rand LPZK.def_ui in
    let generate_random_ui () = { a = dt () ; b = dt () ; a' = dt () ; b' = dt () } in

    Task.parallel_for pool ~start:0 ~finish:(total_rand - 1) ~body:(fun i ->
      Array.set rp i (generate_random_ui ())
    );
    rp

  let parallel_generate_lpzk_verifier_randomness pool (ngates : int) : LPZK.verifier_rand_t =
    let total_rand = ngates + 2 + 1 in
    let y = Array.make total_rand def_yi in
    let alpha = Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !LPZK.q in

    Task.parallel_for pool ~start:0 ~finish:(total_rand - 1) ~body:(fun i ->
      let a = dt () in
      let b = dt () in
      let a' = dt () in
      let b' = dt () in
      Array.set y i { v = Z.erem (Z.add (Z.mul a alpha) b) !LPZK.q ; v' = Z.erem (Z.add (Z.mul a' alpha) b') !LPZK.q }
    );
    { alpha = alpha ; y = y }

end