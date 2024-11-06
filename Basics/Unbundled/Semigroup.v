From Math Require Import
  Unbundled.Notations
  Unbundled.Setoid
  Unbundled.Operators.
From Coq Require Import
  Classes.Morphisms.

Local Open Scope group_scope.

Class Semigroup (A : Type) (eq : SetoidEquiv A) (op : GroupOp A) :=
 { sg_setoid : Setoid A eq
 ; sg_op_proper : Proper (eq ==> eq ==> eq) op
 ; sg_op_assoc : Associative op }.

Theorem four_trans (A : Type) `{Setoid A} : forall w x y z,
  w === x ->
  x === y ->
  y === z ->
  w === z.
Proof.
  intros.
  transitivity y.
  transitivity x.
  all: assumption.
Qed.

Theorem one_assoc (A : Type) `{Semigroup A} : forall w x y,
  w & (x & y) === (w & x) & y.
Proof.
  intros. destruct H, sg_setoid0.
  apply associativity.
Qed.

Theorem two_assoc (A : Type) `{Semigroup A} : forall w x y z,
  ((w & x) & y) & z === w & (x & (y & z)).
Proof.
  intros. destruct H, sg_setoid0.
  rewrite associativity. rewrite associativity. reflexivity.
Qed.
