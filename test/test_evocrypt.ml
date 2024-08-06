open Format

open Evocrypt
open EcLib
open EcList
open EcOption

open Zarith.FieldPolynomial

let error_occurred = ref false

let test test_name answer correct_answer =
  flush stdout;
  flush stderr;
  if answer <> correct_answer then begin
    eprintf "*** Bad result (%s)@." test_name;
    flush stderr;
    error_occurred := true
  end else begin
    printf " %s...@." test_name
  end

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (EcOption.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

let p = Cons({ coef = Z.of_string "5" ; expo = Z.of_string "2"}, Cons({ coef = Z.of_string "7"; expo = Z.of_string "1"}, Cons({ coef = Z.of_string "3"; expo = Z.of_string "0"}, Nil)))

(* =========================================================================== *)
(** Arithmetic circuit tests *)

open Circuit.ArithmeticCircuit 
open ArithmeticGates

let default_gates = Multiplication (Z.of_string "8", 
                                    Addition (Z.of_string "7",
                                      Addition (Z.of_string "6", PInput (Z.of_string "0"), SInput (Z.of_string "2")),
                                      Multiplication (Z.of_string "5", 
                                        Constant (Z.of_string "4", Z.of_string "2"),
                                        SInput (Z.of_string "3"))),
                                    PInput (Z.of_string "1"))
let default_topology = (Z.of_string "2", Z.of_string "2", Z.of_string "1", Z.of_string "5")
let default_circuit = (default_topology, default_gates)

let _ = 
  let xp = Cons(Z.of_string "1", Cons(Z.of_string "2", Nil)) in
  let xs = Cons(Z.of_string "3", Cons(Z.of_string "4", Nil)) in
  let answer = ArithmeticCircuit.eval_circuit default_circuit xp (pad_witness (Z.of_string "2") xs) in
  test "Circuit evaluation test" answer (Z.of_string "16")
(* =========================================================================== *)

(* =========================================================================== *)
(** Commitment test *)
open Evocrypt.Commitment.SHA3Commitment

let _ = 
  let msg = "The quick brown fox jumps over the lazy dog" in
  let answer = SHA3Commitment.verify msg (SHA3Commitment.commit () msg) in
  test "SHA3 commitment test (TRUE)" answer true ;
  let answer = SHA3Commitment.verify msg (SHA3Commitment.commit () "") in
  test "SHA3 commitment test (FALSE)" answer false
(* =========================================================================== *)

(* =========================================================================== *)
(** Secret sharing test *)
open Evocrypt.SecretSharing.Shamir

let p1 = Z.of_string "1"
let p2 = Z.of_string "2"
let p3 = Z.of_string "3"
let p4 = Z.of_string "4"
let p5 = Z.of_string "5"

let pid_mpc_set : Z.t list = Cons (p1, Cons (p2, Cons (p3, Cons (p4, Cons (p5, Nil)))))

module PC5 = struct
  let n = Z.of_string "5"
  let t = Z.of_string "2"
  type pid_t = Z.t
  let pid_set : pid_t list = pid_mpc_set
end 

module Shamir5 = Shamir (PC5)

let _ = 
  EcPrimeField.q := Z.of_string "11" ;
  let p = Cons({ coef = Z.of_string "5" ; expo = Z.of_string "1"}, Cons({ coef = Z.of_string "7"; expo = Z.zero}, Nil)) in
  let s = Z.of_string "4" in
  let answer = Shamir5.share p s in
  test "Shamir test share" answer (Cons((p1, Z.of_string "9"), Cons((p2, Z.of_string "3"), Cons((p3, Z.of_string "8"), Cons((p4, Z.of_string "2"), Cons((p5, Z.of_string "7"), Nil)))))) ;
  let answer = Shamir5.reconstruct answer in
  test "Shamir test reconstruct (all shares)" answer s ;
  let answer = Shamir5.reconstruct (Cons((p1, Z.of_string "9"), Cons((p2, Z.of_string "3"), Cons((p3, Z.of_string "8"), Nil)))) in
  test "Shamir test reconstruct (subset of shares)" answer s
(* =========================================================================== *)

(* =========================================================================== *)
(** BGW test *)
open Evocrypt.SecretSharing.ASecretSharing

open Evocrypt.MPC.BGW.BGWAddition
open Evocrypt.MPC.BGW.BGWMultiplication
open Evocrypt.MPC.BGW.BGWSMultiplication
open Evocrypt.MPC.BGW.BGWRefresh
open Evocrypt.MPC.BGW.BGWProtocol

module BGW5Add = BGWAdditionGate (PC5)
module BGW5Mul5 = BGWMultiplicationGate (PC5)
module BGW5SMul = BGWSMultiplicationGate (PC5)
module BGW5Refresh = BGWRefreshGate (PC5)

open Evocrypt.MPC.ArithmeticProtocol

module BGW5Data = ArithmeticProtocolData (ShamirData (PC5)) (BGWAdditionData (PC5)) (BGWMultiplicationData (PC5)) (BGWSMultiplicationData (PC5))

module BGW5 = BGWProtocol(PC5)
module ListShamir5 = ListSecretSharing((ShamirData (PC5)))

let _ = 
  EcPrimeField.q := Z.of_string "17" ;
  let xs = Cons(Z.of_string "3", Cons(Z.of_string "4", Nil)) in
  let xp = Cons(Z.of_string "1", Cons(Z.of_string "2", Nil)) in

  let p = Cons({ coef = Z.of_string "5" ; expo = Z.of_string "1"}, Cons({ coef = Z.of_string "7"; expo = Z.zero}, Nil)) in
  let r_ss = Cons(p, Cons(p, Nil)) in
  let ss = ListShamir5.share r_ss xs in

  let x_mpc = map (fun pid -> (pid, (xp, pad_witness (Z.of_string "2") (oget (assoc ss pid))))) PC5.pid_set in
  let module BGWR = Evocrypt.Random.BGW(PC5) in
  let r_mpc = BGWR.bgw_random_generator default_gates in

  let answer = Shamir5.reconstruct (snd (BGW5.protocol default_circuit r_mpc x_mpc)) in
  test "BGW test" answer (Z.of_string "7") 
(* =========================================================================== *)

(* =========================================================================== *)
(** BGW-MITH test *)
open ZK.ShamirBGWSha3MitH

module ShamirBGW5Sha3MitH = ShamirBGWSha3MitHData (PC5)

let _ = 
  EcPrimeField.q := Z.of_string "17" ;
  let witness = Cons(Z.of_string "3", Cons(Z.of_string "4", Nil)) in
  let instance = Cons(Z.of_string "1", Cons(Z.of_string "0", Nil)) in
  let witness = pad_witness (Z.of_string "2") witness in

  let module MITHBGWR = Evocrypt.Random.MITHBGW(PC5) in
  let prover_rand = MITHBGWR.generate_prover_randomness default_gates (Z.of_string "4") in
  let verifier_rand = MITHBGWR.generate_verifier_randomness () in

  let module RELC = struct let relc = default_circuit end in
  let module ShamirBGW5Sha3MitH = ShamirBGW5Sha3MitH (RELC) in

  let (ps, cs) = ShamirBGW5Sha3MitH.commitment prover_rand (witness, instance) in
  let (vs, chl) = ShamirBGW5Sha3MitH.challenge verifier_rand instance cs in
  let resp = ShamirBGW5Sha3MitH.response ps chl in
  let answer = ShamirBGW5Sha3MitH.check vs resp in
  test "BGW-MITH test" answer true

(* =========================================================================== *)

(* =========================================================================== *)
(** LPZK test *)
open ZK
open ZK.LPZK

let default_gates : LPZK.gates_t = Multiplication (Z.of_string "8", 
                                    Addition (Z.of_string "7",
                                      Addition (Z.of_string "6", PInput (Z.of_string "0"), SInput (Z.of_string "2")),
                                      Multiplication (Z.of_string "5", 
                                        Constant (Z.of_string "4", Z.of_string "2"),
                                        SInput (Z.of_string "3"))),
                                    PInput (Z.of_string "1"))
let default_topology = { npinputs = Z.of_string "2" ; nsinputs = Z.of_string "2" ; noutputs = Z.of_string "1" ; ngates = Z.of_string "5" }
let default_circuit = (default_topology, default_gates)

let pad_witness l ws = 
  let pad = Array.make l Z.zero in
  Array.append pad ws

let _ = 
  LPZK.q := Z.of_string "17" ;
  let witness = Array.make 2 (Z.of_string "3") in
  witness.(1) <- Z.of_string "4" ;
  let witness = pad_witness 2 witness in

  let instance = Array.make 2 (Z.of_string "1") in
  instance.(1) <- Z.of_string "0" ;

  let statement = (default_circuit, instance) in

  let prover_rand = Evocrypt.Random.LPZK.generate_lpzk_prover_randomness 7 in
  let verifier_rand = Evocrypt.Random.LPZK.generate_lpzk_verifier_randomness 7 in

  let c = LPZK.commit prover_rand (witness, statement) in
  let answer = LPZK.prove verifier_rand statement c in
  test "LPZK test" answer true
  
(* =========================================================================== *)

(** End of tests *)
let _ =
  print_newline();
  if !error_occurred then begin
    printf "********* TEST FAILED ***********\n";
    exit 2 
  end else begin
    printf "All tests successful.\n";
    exit 0
  end