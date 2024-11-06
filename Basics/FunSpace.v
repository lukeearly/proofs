From Math Require Import
  Unbundled.Unbundled
  Unbundled.Operators.
From Coq Require Import
  Classes.Morphisms.

Section Definitions.

Definition pointwise2 {X Y Z} A (op : X -> Y -> Z) : (A -> X) -> (A -> Y) -> (A -> Z) :=
  fun f g a => op (f a) (g a).

Context {X Y : Type}.

Instance associative_pointwise (op : bin_op Y) `{Associative Y op} : @Associative (X -> Y) (pointwise_relation X (===)%group) (pointwise2 X op).
Proof.
  red in H. red. unfold pointwise2, s_equiv, pointwise_relation.
  intros.
  apply H.
Qed.

Instance commutative_pointwise (op : bin_op Y) `{Commutative Y op} : @Commutative (X -> Y) (pointwise_relation X (===)%group) (pointwise2 X op).
Proof.
  red in H. red. unfold pointwise2, s_equiv, pointwise_relation.
  intros.
  apply H.
Qed.

Instance identity_pointwise (op : bin_op Y) `{Identity Y op} : @Identity (X -> Y) (pointwise_relation X (===)%group) (pointwise2 X op) (fun _ => e).
Proof.
  destruct H. constructor; red; unfold pointwise2, s_equiv, pointwise_relation.
  intros. apply identity_left.
  intros. apply identity_right.
Qed.

Instance setoid_fs `{Setoid Y} : Setoid (X -> Y) (pointwise_relation _ (===)%group).
Proof.
  destruct H.
  constructor.
  typeclasses eauto.
Qed.

Instance semigroup_fs `{Semigroup Y} : Semigroup (X -> Y) (pointwise_relation _ (===)%group) (pointwise2 _ (&)%group).
Proof.
  destruct H.
  constructor.
  apply setoid_fs.
  unfold Proper, respectful, pointwise_relation, pointwise2.
  intros. apply sg_op_proper. apply H. apply H0.
  typeclasses eauto.
Qed.

Instance monoid_fs `{Monoid Y} : Monoid (X -> Y) (pointwise_relation _ (===)%group) (pointwise2 _ (&)%group) (fun _ => ident).
Proof.
  destruct H.
  constructor.
  apply semigroup_fs.
  unfold Proper, respectful, pointwise_relation, pointwise2.
  apply identity_pointwise.
  apply m_identity.
Qed.

End Definitions.
