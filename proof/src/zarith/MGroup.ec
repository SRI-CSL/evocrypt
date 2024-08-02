require import Int.

op order : int.

type mgroup.

op g : mgroup. (* the generator *)
op ( * ) : mgroup -> mgroup -> mgroup.   (* multiplication of group elements *)
op inv : mgroup -> mgroup.             (* inverse of the multiplication *)
op ( / ) : mgroup -> mgroup -> mgroup.   (* division *)
op ( ^ ) : mgroup -> int -> mgroup.       (* exponentiation *)
op log  : mgroup -> int.                (* discrete logarithm *)
op g1 = g ^ 0.

axiom gpow_log (a:mgroup): g ^ (log a) = a.
axiom log_gpow x : log (g ^ x) = x.

axiom nosmt log_bij x y: x = y <=> log x = log y.
lemma nosmt pow_bij (x y: int): x = y <=> g ^ x = g ^ y by smt.

axiom inv_def (a:mgroup): inv a = g ^ (- (log a)).
axiom div_def (a b:mgroup): g ^ (log a - log b) = a / b.

axiom mul_pow g (x y: int): g ^ x * g ^ y = g ^ (x + y).

axiom pow_pow g (x y: int): g ^ x ^ y = g ^ (x * y).

lemma nosmt log_pow (g1:mgroup) x: log (g1 ^ x) = (log g1) * x by smt.

lemma nosmt log_mul (g1 g2:mgroup): log (g1 * g2) = log g1 + log g2.
proof.
  have : exists x, g1 = g ^ x by exists (log g1); rewrite gpow_log.
  have : exists y, g2 = g ^ y by exists (log g2); rewrite gpow_log.
  progress.
  by smt.
qed.

lemma nosmt pow_mul (g1 g2:mgroup) x: (g1 ^ x) * (g2 ^ x) = (g1 * g2) ^ x.
proof.
  rewrite -{1}(gpow_log g1) -{1}(gpow_log g2) !pow_pow mul_pow.
  by rewrite -mulzDl -pow_pow -mul_pow !gpow_log.
qed.

lemma nosmt pow_opp (x:mgroup) (p: int): x ^ (-p) = inv (x ^ p).
proof.
  rewrite inv_def.
  have -> : -p =  - p * 1 by smt().
  have -> : - (log (x ^ p)) = (- 1) * (log (x ^ p)) by smt().
  by rewrite !(mulzC (- 1)) -!pow_pow gpow_log pow_pow /#.
qed.

lemma nosmt mulC (x y: mgroup): x * y = y * x.
proof.
  by rewrite -(gpow_log x) -(gpow_log y) mul_pow;smt.
qed.

lemma nosmt mulA (x y z: mgroup): x * (y * z) = (x * y) * z.
proof.
  by rewrite -(gpow_log x) -(gpow_log y) -(gpow_log z) !mul_pow;smt.
qed.

lemma nosmt mul1 x: g1 * x = x.
proof.
  by rewrite /g1 -(gpow_log x) mul_pow;smt.
qed.

lemma nosmt divK (a:mgroup): a / a = g1.
proof strict.
  by rewrite -div_def.
qed.

axiom log_g : log g = 1.

lemma nosmt g_neq0 : g1 <> g.
proof.
  rewrite /g1 -{2}(gpow_log g) log_g -pow_bij;smt.
qed.

lemma mulN (x:mgroup): x * (inv x) = g1.
proof.
  rewrite inv_def -{1}(gpow_log x) mul_pow;smt.
qed.

lemma inj_gpow_log (a:mgroup): a = g ^ (log a) by smt.

lemma pow1 (a : mgroup) : a ^ 1 = a.
have ->: a = g ^ (log a) by rewrite gpow_log.
rewrite pow_pow.
smt.
qed.

(* To/from int *)
require import Int IntDiv Ring.
import IntID.

op mtoint : mgroup -> int.
op mofint : int -> mgroup.

axiom mofint1: mofint 1 = g1.
axiom mtoint1: mtoint g1 = 1.
axiom mofintN (x:int): mofint (x ^ -1) = inv (mofint x).

from Zarith require import AGroup.

axiom mtoint_bounded (x:mgroup): 0 <= mtoint x < n.
axiom moftoint (x:mgroup): mofint (mtoint x) = x.
axiom mtoofint_mod (x : int) : mtoint (mofint x) = x %% n.
lemma mtoofint (x:int): 0 <= x < n => mtoint (mofint x) = x.
proof. by progress; rewrite mtoofint_mod; smt(@IntDiv). qed.

(* agroup <-> mgroup *)
axiom agroup_mgroup_gcd (x : int) : gcd x n = 1 => atoint (aofint x) = mtoint (mofint x).

axiom mofint_mul_mod (x y : int) : mofint (x * y) = mofint x * mofint y.

theory MGDistr.

  require Distr.

  require import Real.

  op dmgroup: mgroup distr.

  axiom dmgroup_fu: Distr.is_full dmgroup.

  axiom dmgroup1E: forall (s:mgroup), Distr.mu1 dmgroup s = (1%r/order%r)%Real.

  axiom dmgroup_ll: Distr.is_lossless dmgroup.

  lemma dmgroup_funi: Distr.is_funiform dmgroup.
  proof. by move=> ??;rewrite !dmgroup1E. qed.

end MGDistr.
