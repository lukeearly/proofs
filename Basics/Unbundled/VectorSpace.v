Require Export Notations.

From Math Require Import
  Unbundled.Setoid
  Unbundled.AbGroup
  Unbundled.Semiring
  Unbundled.Field
  Unbundled.Operators.

Local Open Scope vector_scope.

Class VectorSpace (V : Type) (F : Type)
  (veq : SetoidEquiv V)
  (vadd : VecAdd V) (vzero : VecZero V) (vopp : VecOpp V)
  (feq : SetoidEquiv F)
  (fadd : FieldAdd F) (fzero: FieldZero F) (fopp : FieldOpp F)
  (fmult : FieldMult F) (fone: FieldOne F) (frecip : FieldRecip F)
  (sm : ScalarMult V F) :=
  { vs_abgroup : AbGroup V veq vadd vzero vopp
  ; vs_field : Field F feq fadd fzero fopp fmult fone frecip
  ; vs_sm_one_l : forall v : V, 1 * v === v
  ; vs_fm_sm_assoc : forall (a b : F) (v : V), (a * b) * v === a * (b * v)
  ; vs_sm_over_fa : forall (a b : F) (v : V), (a + b) * v === a * v + b * v
  ; vs_sm_over_va : forall (a : F) (u v : V), a * (u + v) === a * u + a * v }.
