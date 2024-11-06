Require Export Notations.

From Math Require Import
  Unbundled.Setoid
  Unbundled.Semiring
  Unbundled.CRing
  Unbundled.Operators.

Class Field (A : Type) (eq : SetoidEquiv A)
  (add : FieldAdd A) (zero: FieldZero A) (opp : FieldOpp A)
  (mult : FieldMult A) (one: FieldOne A) (recip : FieldRecip A) :=
  { f_cring : CRing A eq add zero opp mult one
  ; f_recip_id : forall x, not (eq zero x) -> eq (mult x (recip x)) one }.
