From Math Require Import
  Unbundled.Notations
  Unbundled.Setoid
  Unbundled.Semigroup
  Unbundled.Monoid
  Unbundled.Operators.

Class CMonoid (A : Type) (eq : SetoidEquiv A) (op : GroupOp A) (identity: MonoidId A) :=
  { cm_monoid : Monoid A eq op identity
  ; cm_comm : Commutative op }.
