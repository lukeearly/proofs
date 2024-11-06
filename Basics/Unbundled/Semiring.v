Require Export Notations.

From Math Require Import
  Unbundled.Setoid
  Unbundled.Semigroup
  Unbundled.Monoid
  Unbundled.CMonoid
  Unbundled.Group
  Unbundled.Operators.

Local Open Scope field_scope.

Class Semiring (A : Type) (eq : SetoidEquiv A)
  (add : FieldAdd A) (zero: FieldZero A)
  (mult : FieldMult A) (one : FieldOne A) :=
  { sr_add_cmonoid : CMonoid A eq add zero
  ; sr_mult_monoid : Monoid A eq mult one
  ; sr_distr : Distributive mult add
  ; sr_absorb : forall x, 0 * x === 0 }.
