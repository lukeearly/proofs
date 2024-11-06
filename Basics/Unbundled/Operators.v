From Math Require Import
  Unbundled.Notations
  Unbundled.Setoid.
From Coq Require Import
  Relations.Relations.

Definition bin_op (A : Type) := A -> A -> A.
Definition un_op (A : Type) := A -> A.
Section Operator.
  Generalizable Variables A.
  Context `{Setoid A}.
  Local Open Scope group_scope.

  Class Commutative (op : bin_op A) :=
    commutativity : forall (x y : A), op x y === op y x.
  Class Associative (op : bin_op A) :=
    associativity : forall (x y z : A), op x (op y z) === op (op x y) z.
  Class LeftDistributive (op1 op2 : bin_op A) :=
    left_distributivity : forall (x y z : A), op1 x (op2 y z) === op2 (op1 x y) (op1 x z).
  Class RightDistributive (op1 op2 : bin_op A) :=
    right_distributivity : forall (x y z : A), op1 (op2 y z) x === op2 (op1 y x) (op1 z x).
  Class Distributive (op1 op2 : bin_op A) :=
    { distributive_left : LeftDistributive op1 op2
    ; distributive_right : RightDistributive op1 op2 }.

  Class LeftIdentity (op : bin_op A) (e : A) :=
    left_identity : forall (x : A), op e x === x.
  Class RightIdentity (op : bin_op A) (e : A) :=
    right_identity : forall (x : A), op x e === x.
  Class Identity (op : bin_op A) (e : A) :=
    { identity_left : LeftIdentity op e
    ; identity_right : RightIdentity op e }.

  Class LeftInverse (op : bin_op A) (e : A) (inv : un_op A) :=
    left_inverse : forall x, op (inv x) x === e.
  Class RightInverse (op : bin_op A) (e : A) (inv : un_op A) :=
    right_inverse : forall x, op x (inv x) === e.
  Class Inverse (op : bin_op A) (e : A) (inv : un_op A) :=
    { inverse_left : LeftInverse op e inv
    ; inverse_right : RightInverse op e inv }.
End Operator.
