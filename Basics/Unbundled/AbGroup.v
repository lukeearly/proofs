From Math Require Import
  Unbundled.Notations
  Unbundled.Setoid
  Unbundled.Semigroup
  Unbundled.Monoid
  Unbundled.Group
  Unbundled.Operators.

Class AbGroup (A : Type) (eq : SetoidEquiv A) (op : GroupOp A) (identity: MonoidId A) (inv : GroupInv A) :=
  { ag_group : Group A eq op identity inv 
  ; ag_op_comm : Commutative op }.
