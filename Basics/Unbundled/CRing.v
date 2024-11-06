From Math Require Import
  Unbundled.Setoid
  Unbundled.Semiring
  Unbundled.Ring
  Unbundled.Operators.

Class CRing (A : Type) (eq : SetoidEquiv A)
  (add : FieldAdd A) (zero: FieldZero A) (opp : FieldOpp A)
  (mult : FieldMult A) (one: FieldOne A) :=
  { cr_ring : Ring A eq add zero opp mult one
  ; cr_mult_comm : Commutative mult }.
