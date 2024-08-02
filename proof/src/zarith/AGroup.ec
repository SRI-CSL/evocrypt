require import Int IntDiv.

op n : int. (* order, {0, ..., n-1} *)
            (* operations done over [mod n] *)

axiom n_pos : 2 < n.

type agroup.

op ( + ) : agroup -> agroup -> agroup.

axiom addC (x y : agroup) : x + y = y + x.
axiom addA (x y z : agroup) : x + (y + z) = (x + y) + z.

(* Neutral element *)
op zero : agroup.
axiom addg0 (x : agroup) : x + zero = x.
lemma add0g (x : agroup) : zero + x = x.
proof. by rewrite addC addg0. qed.

(* Additive inverse *)
op [-] : agroup -> agroup.
axiom addgN (x : agroup) : x + -x = zero.
op ( - ) : agroup -> agroup -> agroup.
axiom sub_def (x y : agroup) : x - y = x + -y.

(* To/from int *)
op atoint : agroup -> int.
op aofint : int -> agroup.

axiom aofint0: aofint 0 = zero.
axiom aofintS (x:int): Int.(<=) 0 x => aofint (Int.(+) x 1) = aofint x + aofint 1.
axiom aofintN (x:int): aofint (Int.([-]) x) = - (aofint x).

axiom atoint_bounded (x:agroup): 0 <= atoint x < n.
axiom aoftoint (x:agroup): aofint (atoint x) = x.
axiom atoofint_mod (x : int) : atoint (aofint x) = x %% n.
lemma atoofint (x:int): 0 <= x < n => atoint (aofint x) = x.
proof. by progress; rewrite atoofint_mod; smt(@IntDiv). qed.

axiom aofint_add (x y : int) : aofint x + aofint y = aofint (x + y).

theory AGDistr.

  require Distr.

  require import Real.

  op dagroup: agroup distr.

  axiom dagroup_fu: Distr.is_full dagroup.

  axiom dagroup1E: forall (s:agroup), Distr.mu1 dagroup s = (1%r/n%r)%Real.

  axiom dagroup_ll: Distr.is_lossless dagroup.

  lemma dagroup_funi: Distr.is_funiform dagroup.
  proof. by move=> ??;rewrite !dagroup1E. qed.

end AGDistr.

from Zarith require import PrimeField.

op group_to_field (x : agroup) : t = ofint (atoint x).
op field_to_group (x : t) : agroup = aofint (toint x).
