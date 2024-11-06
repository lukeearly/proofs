From Math Require Import
  Unbundled.Notations
  Unbundled.Setoid
  Unbundled.Semigroup
  Unbundled.Operators.

Class MonoidId (A : Type) :=
  ident : A.
Class Monoid (A : Type) (eq : SetoidEquiv A) (op : GroupOp A) (identity: MonoidId A) :=
  { m_semigroup : Semigroup A eq op
  ; m_identity : Identity op identity }.
