require import Int IntDiv Ring.
import IntID. 

from Zarith require import AGroup MGroup.

op p : int.
op q : int.

axiom prime_p : prime p.
axiom prime_q : prime q.

axiom n_val : n = p * q.

op phi : int = Int.( * ) (Int.(-) p 1) (Int.(-) q 1).

axiom exp1 (x : mgroup) : x ^ phi = g1. 

axiom gcd_phi : gcd phi n = 1.
axiom gcd_mgroup (x : mgroup) : gcd (mtoint x) n^2 = 1.
axiom gcd_gamma : gcd (1 + n) n^2 = 1.

type mn2_group_t.

op g : mn2_group_t. (* the generator *)
op ( * ) : mn2_group_t -> mn2_group_t -> mn2_group_t.   (* multiplication of group elements *)
op inv : mn2_group_t -> mn2_group_t.             (* inverse of the multiplication *)
op ( / ) : mn2_group_t -> mn2_group_t -> mn2_group_t.   (* division *)
op ( ^ ) : mn2_group_t -> int -> mn2_group_t.       (* exponentiation *)
op log  : mn2_group_t -> int.                (* discrete logarithm *)
op g1 = g ^ 0.

axiom gpow_log (a:mn2_group_t): g ^ (log a) = a.
axiom log_gpow x : log (g ^ x) = x.

axiom nosmt log_bij x y: x = y <=> log x = log y.
lemma nosmt pow_bij (x y: int): x = y <=> g ^ x = g ^ y by smt.

axiom inv_def (a:mn2_group_t): inv a = g ^ (- (log a)).
axiom div_def (a b:mn2_group_t): g ^ (log a - log b) = a / b.

axiom mul_pow g (x y: int): g ^ x * g ^ y = g ^ (x + y).

axiom pow_pow g (x y: int): g ^ x ^ y = g ^ (x * y).

axiom has_mul_inv_phi (x : int) : gcd (phi * x) n = 1.

axiom mtoint_mofint_mul_invm (x y : int) : mtoint (mofint (x * y) * inv (mofint x)) = y.

lemma nosmt log_pow (g1:mn2_group_t) x: log (g1 ^ x) = (log g1) * x by smt.

lemma nosmt log_mul (g1 g2:mn2_group_t): log (g1 * g2) = log g1 + log g2.
proof.
  have : exists x, g1 = g ^ x by exists (log g1); rewrite gpow_log.
  have : exists y, g2 = g ^ y by exists (log g2); rewrite gpow_log.
  progress.
  by smt.
qed.

lemma nosmt pow_mul (g1 g2:mn2_group_t) x: (g1 ^ x) * (g2 ^ x) = (g1 * g2) ^ x.
proof.
  rewrite -{1}(gpow_log g1) -{1}(gpow_log g2) !pow_pow mul_pow.
  by rewrite -mulzDl -pow_pow -mul_pow !gpow_log.
qed.

lemma nosmt pow_opp (x:mn2_group_t) (p: int): x ^ (-p) = inv (x ^ p).
proof.
  rewrite inv_def.
  have -> : -p =  - p * 1 by smt().
  have -> : - (log (x ^ p)) = (- 1) * (log (x ^ p)) by smt().
  by rewrite !(mulzC (- 1)) -!pow_pow gpow_log pow_pow /#.
qed.

lemma nosmt mulC (x y: mn2_group_t): x * y = y * x.
proof.
  by rewrite -(gpow_log x) -(gpow_log y) mul_pow;smt.
qed.

lemma nosmt mulA (x y z: mn2_group_t): x * (y * z) = (x * y) * z.
proof.
  by rewrite -(gpow_log x) -(gpow_log y) -(gpow_log z) !mul_pow;smt.
qed.

lemma nosmt mul1 x: g1 * x = x.
proof.
  by rewrite /g1 -(gpow_log x) mul_pow;smt.
qed.

lemma nosmt divK (a:mn2_group_t): a / a = g1.
proof strict.
  by rewrite -div_def.
qed.

axiom log_g : log g = 1.

lemma nosmt g_neq0 : g1 <> g.
proof.
  rewrite /g1 -{2}(gpow_log g) log_g -pow_bij;smt.
qed.

lemma mulN (x:mn2_group_t): x * (inv x) = g1.
proof.
  rewrite inv_def -{1}(gpow_log x) mul_pow;smt.
qed.

lemma inj_gpow_log (a:mn2_group_t): a = g ^ (log a) by smt.

lemma pow1 (a : mn2_group_t) : a ^ 1 = a.
proof. by rewrite inj_gpow_log pow_pow. qed.

lemma pow0 (a : mn2_group_t) : a ^ 0 = g1.
proof.
  have : exists e, a = g ^ e. 
exists (log a). 
smt.
progress.
rewrite pow_pow.
have ->: e * 0 = 0 by smt().
by rewrite /g1.
qed.

(* To/from int *)
op mn2toint : mn2_group_t -> int.
op mn2ofint : int -> mn2_group_t.

axiom mn2ofint1: mn2ofint 1 = g1.
axiom mn2toint1: mn2toint g1 = 1.
axiom mn2ofintN (x:int): mn2ofint (x ^ -1) = inv (mn2ofint x).

axiom mn2toint_bounded (x:mn2_group_t): 0 <= mn2toint x < n.
axiom mn2oftoint (x:mn2_group_t): mn2ofint (mn2toint x) = x.
axiom mn2toofint_mod (x : int) : mn2toint (mn2ofint x) = x %% n^2.
lemma mn2toofint (x:int): 0 <= x < n^2 => mn2toint (mn2ofint x) = x.
proof. by progress; rewrite mn2toofint_mod; smt(@IntDiv). qed.

axiom mn2ofint_mul_mod (x y : int) : mn2ofint (x * y) = mn2ofint x * mn2ofint y.
axiom mn2ofint_pow_mod (x : mn2_group_t) (e : int) : mn2toint (x ^ e) = (mn2toint x ^ e) %% n^2.

(* Order n^2  *)
(*axiom exp_modn2 (x : agroup) : mn2ofint ((1 + n) ^ atoint x) = mn2ofint (1 + atoint x * n).*)
axiom exp_modn2 (x : int) : 0 <= x <= n => mn2ofint (1 + n) ^ x = mn2ofint (1 + x * n).
lemma exp_modn2_order_one : mn2ofint (1 + n) ^ n = mn2ofint 1.
proof.
rewrite exp_modn2.
smt(n_pos).
have ->: mn2ofint (1 + n * n) = mn2ofint 1 <=> 
         mn2toint (mn2ofint (1 + n * n)) = mn2toint (mn2ofint 1).
smt.
have ->: 1 + n * n = 1 + n^2 by smt(@Ring.IntID).
rewrite !mn2toofint_mod.
(*have ->: gcd (1 + n ^ 2) (n ^ 2) = gcd (n ^ 2) (1 + n ^ 2).*)
smt(@IntDiv).
(*rewrite gcdDr.
smt().
smt().
rewrite modzDr.
done.*)
qed.

axiom exp_modn2_order (x : int) : mn2ofint (1 + n) ^ x = mn2ofint (1 + n) ^ (x %% n).
axiom n2mul_nmul (m1 m2 : mgroup) :
  (mn2ofint (mtoint m1) * mn2ofint (mtoint m2)) ^ n = mn2ofint (mtoint (m1 * m2)) ^ n.
(* exponentiation in N^2 with order N *)

op agroup_mn2_group_iso (a : agroup) (b : mgroup) : mn2_group_t =
  mn2ofint (Int.(+) 1 n) ^ (atoint a) * (mn2ofint (mtoint b) ^ n).

op l (x : int) : int = (Int.(+) x 1) %/ n.

axiom exp2_modn (x : int) : 0 <= x < n => mofint (l (mn2toint (mn2ofint (1 + n) ^ x))) = mofint x.

lemma agroup_mn2_group_iso_mul (a1 a2 : agroup) (b1 b2 : mgroup) :
  agroup_mn2_group_iso a1 b1 * agroup_mn2_group_iso a2 b2 =
  agroup_mn2_group_iso (a1 + a2) (b1 * b2).
proof.
rewrite /agroup_mn2_group_iso //=.
pose a := mn2ofint (1 + n) ^ atoint a1.
pose b := mn2ofint (mtoint b1) ^ n.
pose c := mn2ofint (1 + n) ^ atoint a2.
pose d := mn2ofint (mtoint b2) ^ n.
have ->: a * b * (c * d) = (a * c) * (b * d).
rewrite !mulA.
congr.
rewrite -mulA.
rewrite (mulC b c).
rewrite mulA.
done.
congr.
rewrite /a /c.
rewrite mul_pow.

have ->: atoint (a1 + a2) = atoint (aofint (atoint a1 + atoint a2)).
smt.
rewrite atoofint_mod.
rewrite exp_modn2_order .
done.

rewrite /b /d.
rewrite pow_mul.

rewrite n2mul_nmul.
done.
qed.

lemma agroup_mn2_group_iso_pow (a : agroup) (b : mgroup) (x : int) : 
  (agroup_mn2_group_iso a b) ^ x = 
  agroup_mn2_group_iso (aofint (x * (atoint a))) (b ^ x).
proof.
admitted.

lemma agroup_mn2_group_iso_inv (a : agroup) (b : mgroup) :
  mofint (mn2toint (mn2ofint (1 + n) ^ atoint a * mn2ofint (mtoint b) ^ n * mn2ofint (1 - atoint a * n))) ^ invm n phi = b.
proof.
admitted.

theory MN2GDistr.

  require Distr.

  require import Real.

  op dmn2group: mn2_group_t distr.

  axiom dmn2group_fu: Distr.is_full dmn2group.

  axiom dmn2group1E: forall (s:mn2_group_t), Distr.mu1 dmn2group s = (1%r/n%r)%Real.

  axiom dmn2group_ll: Distr.is_lossless dmn2group.

  lemma dmn2group_funi: Distr.is_funiform dmn2group.
  proof. by move=> ??;rewrite !dmn2group1E. qed.

end MN2GDistr.
