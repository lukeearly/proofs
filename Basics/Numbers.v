Require Import
  Unbundled.Operators
  Unbundled.Semiring
  Unbundled.Field
  Unbundled.VectorSpace.
From Coq Require Import
  Classes.RelationClasses
  Classes.Morphisms
  Arith.PeanoNat
  QArith.

Instance sring_nat : Semiring nat eq Nat.add O Nat.mul (S O).
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  apply eq_equivalence.
  unfold Proper, "==>".
  intros. rewrite H, H0. reflexivity.
  unfold Associative.
  intros. induction x. reflexivity.
  simpl. rewrite IHx. reflexivity.
  constructor.
  unfold LeftIdentity. reflexivity.
  unfold RightIdentity.
  induction x. reflexivity.
  simpl. rewrite IHx. reflexivity.
  unfold Commutative.
  intros. induction x. induction y.
  reflexivity.
  simpl. rewrite <- IHy. reflexivity.
  simpl. rewrite IHx. apply plus_n_Sm.
  constructor.
  constructor.
  constructor.
  apply eq_equivalence.
  unfold Proper, "==>".
  intros. rewrite H, H0. reflexivity.
  unfold Associative. apply Nat.mul_assoc.
  constructor.
  unfold LeftIdentity. apply Nat.mul_1_l.
  unfold RightIdentity. apply Nat.mul_1_r.
  constructor.
  unfold LeftDistributive. apply Nat.mul_add_distr_l.
  unfold RightDistributive. intros. apply Nat.mul_add_distr_r.
  reflexivity.
Qed.

Instance field_rat : Field Q Qeq Qplus 0%Q Qopp Qmult 1%Q Qinv.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  apply Q_Setoid.
  apply Qplus_comp.
  unfold Associative. apply Qplus_assoc.
  constructor.
  unfold LeftIdentity. apply Qplus_0_l.
  unfold RightIdentity. apply Qplus_0_r.
  constructor.
  unfold LeftInverse. intro. remember (-x)%Q as q. rewrite <- Qopp_involutive with (q := x). rewrite Heqq. apply Qplus_opp_r.
  unfold RightInverse. apply Qplus_opp_r.
  unfold Commutative. intros. apply Qplus_comm.
  constructor.
  constructor.
  constructor.
  apply Q_Setoid.
  apply Qmult_comp.
  unfold Associative. apply Qmult_assoc.
  constructor.
  unfold LeftIdentity. apply Qmult_1_l.
  unfold RightIdentity. apply Qmult_1_r.
  constructor.
  unfold LeftDistributive. apply Qmult_plus_distr_r.
  unfold RightDistributive. intros. apply Qmult_plus_distr_l.
  reflexivity.
  unfold Commutative. apply Qmult_comm.
  intros. apply Qmult_inv_r. intro. symmetry in H0. contradiction.
Qed.

Instance vs_fn {F} `{Hf: Field F} : VectorSpace F F s_equiv f_add zero f_opp s_equiv f_add zero f_opp f_mult one f_recip f_mult.
Proof.
  split; try apply Hf.
  - intros.
    destruct Hf, f_cring, cr_ring, r_mult_monoid, m_semigroup.
    unfold Associative in *.
    destruct sg_setoid.
    symmetry.
    apply sg_op_assoc.
  - intros.
    destruct Hf, f_cring, cr_ring, r_distr.
    destruct r_mult_monoid, m_semigroup, sg_setoid.
    unfold RightDistributive in *.
    apply distributive_right.
Qed.
