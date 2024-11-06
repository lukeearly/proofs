From Math Require Import
  Unbundled.Setoid
  Unbundled.Monoid
  Unbundled.AbGroup
  Unbundled.Semiring
  Unbundled.Operators.

Class Ring (A : Type) (eq : SetoidEquiv A)
  (add : FieldAdd A) (zero: FieldZero A) (opp : FieldOpp A)
  (mult : FieldMult A) (one: FieldOne A) :=
  { r_add_abgroup : AbGroup A eq add zero opp
  ; r_mult_monoid : Monoid A eq mult one
  ; r_distr : Distributive mult add
  ; r_absorb : forall x, eq (mult zero x) zero }.