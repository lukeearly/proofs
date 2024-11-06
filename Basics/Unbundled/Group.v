Require Export Notations.

From Math Require Import
  Unbundled.Setoid
  Unbundled.Semigroup
  Unbundled.Monoid
  Unbundled.Operators.

Class GroupInv (A : Type) :=
  g_inv : un_op A.
Class Group (A : Type) (eq : SetoidEquiv A) (op : GroupOp A) (identity: MonoidId A) (inv : GroupInv A) :=
  { g_monoid : Monoid A eq op identity
  ; g_inverse : Inverse op identity inv }.

Notation "~ x" := (g_inv x).
