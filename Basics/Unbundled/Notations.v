Reserved Infix "==="
  (at level 90, no associativity).
Reserved Infix "=!="
  (at level 90, no associativity).

Reserved Infix "&"
  (at level 50, left associativity).

Declare Scope group_scope.
Declare Scope field_scope.
Declare Scope vector_scope.

Delimit Scope group_scope with group.
Delimit Scope field_scope with field.
Delimit Scope vector_scope with vec.

Class SetoidEquiv (A : Type) :=
  s_equiv : A -> A -> Prop.

Notation "(===)" := s_equiv : group_scope.
Notation "(===)" := s_equiv : field_scope.
Notation "(===)" := s_equiv : vector_scope.
Notation "x === y" := (s_equiv x%group y%group) : group_scope.
Notation "x === y" := (s_equiv x%field y%field) : field_scope.
Notation "x === y" := (s_equiv x%vec y%vec) : vector_scope.
Notation "x =!= y" := (not (s_equiv x%group y%group)) : group_scope.
Notation "x =!= y" := (not (s_equiv x%field y%field)) : field_scope.
Notation "x =!= y" := (not (s_equiv x%vec y%vec)) : vector_scope.

Class GroupOp (A : Type) :=
  g_op : A -> A -> A.

Notation "(&)" := g_op : group_scope.
Notation "x & y" := (g_op x y) : group_scope.

Class FieldAdd (A : Type) :=
  f_add : A -> A -> A.
Class FieldMult (A : Type) :=
  f_mult : A -> A -> A.

Class FieldZero (A : Type) :=
  f_zero : A.
Class FieldOne (A : Type) :=
  f_one : A.

Class FieldOpp (A : Type) :=
  f_opp : A -> A.
Class FieldRecip (A : Type) :=
  f_recip : A -> A.

Notation "0" := f_zero : field_scope.
Notation "1" := f_one : field_scope.

Notation "(+)" := f_add : field_scope.
Notation "(*)" := f_mult : field_scope.
Notation "x + y" := (f_add x%field y%field) : field_scope.
Notation "x * y" := (f_mult x%field y%field) : field_scope.

Notation "- x" := (f_opp x%field) : field_scope.

Notation "(-)" := (fun x y => f_add x (f_opp y)) : field_scope.
Notation "(/)" := (fun x y => f_mult x (f_recip y)) : field_scope.
Notation "x - y" := (f_add x%field (f_opp y%field)) : field_scope.
Notation "x / y" := (f_mult x%field (f_recip y%field)) : field_scope.

Class VecAdd (V : Type) :=
  v_add : V -> V -> V.
Class VecZero (V : Type) :=
  v_zero : V.
Class VecOpp (V : Type) :=
  v_opp : V -> V.

Class ScalarMult (V F : Type) :=
  v_smult : F -> V -> V.

Notation "(+)" := v_add : vector_scope.
Notation "x + y" := (v_add x%vec y%vec) : vector_scope.

Notation "(-)" := (fun x y => v_add x (v_opp y)) : vector_scope.
Notation "- x" := (v_opp x%vec) : vector_scope.
Notation "x - y" := (v_add x%vec (v_opp y%vec)) : vector_scope.

Notation "0" := v_zero : vector_scope.

Notation "(*)" := v_smult : vector_scope.
Notation "x * v" := (v_smult x%field v%vec) : vector_scope.
