(* From Coq Require Import QArith.QArith. *)
From Coq Require Import ZArith.ZArith.
From Coq Require Import Reals.Reals.
From Coq Require Import Lia.

Definition operator (A : Type) := A -> A -> A.

Class Commutative {A : Type} (op : operator A) := 
  commutativity : forall (x y : A), op x y = op y x.
Class Associative {A : Type} (op : operator A) := 
  associativity : forall (x y z : A), op (op x y) z = op x (op y z).
Class LeftDistributive {A : Type} (op1 op2 : operator A) := 
  distributivity_l : forall (x y z : A), op1 x (op2 y z) = op2 (op1 x y) (op1 x z).
Class RightDistributive {A : Type} (op1 op2 : operator A) := 
  distributivity_r : forall (x y z : A), op1 (op2 y z) x = op2 (op1 y x) (op1 z x).
Class Distributive {A : Type} (op1 op2 : operator A) :=
  { Distributive_Left :: LeftDistributive op1 op2 ;
    Distributive_Right :: RightDistributive op1 op2 }.

Class Group (A : Type) (op : operator A) :=
  { Group_Associative :: Associative op ;
    e : A ;
    inv : A -> A ;

Class AbelianGroup (A : Type) (op : operator A) :=
  { AbelianGroup_Group :: Group A op ;
    AbelianGroup_Commutative : Commutative op }.


Theorem distributive_lr_implies_distributive : forall (A : Type) (op1 op2 : operator A),
  LeftDistributive A op1 op2 -> RightDistributive A op1 op2 -> Distributive A op1 op2.
Proof.
  intros.
  split; assumption.
Qed.

Theorem tri_commute : forall (A : Type) (op : operator A) (x y z : A),
  Commutative A op ->
  Associative A op ->
  op (op x y) z = op (op z y) x.
Proof.
  intros.
  rewrite associativity, commutativity.
  assert (op y z = op z y) as S. apply commutativity.
  rewrite S. reflexivity. Qed.

Theorem tri_commute' : forall (A : Type) (op : operator A) (x y z : A),
  AbelianGroup A op ->
  op (op x y) z = op (op z y) x.
Proof.
  intros. destruct X.
  rewrite associativity. rewrite commutativity.
  assert (op y z = op z y) as S. apply commutativity.
  rewrite S. reflexivity. Qed.

Class Ring (A : Type) (add mult: operator A) :=
  { Ring_AdditiveAbelianGroup :: AbelianGroup A add ;
    Ring_MultAssoc :: Associative A mult ;
    Ring_Distrib :: Distributive A mult add }.



#[refine] Instance Z_add_grp : AbelianGroup Z Z.add := {}.
Proof.
  econstructor. 
   - unfold Associative. lia.
   - intro. exists (-x)%Z. assert (-x + x = 0). lia.
   - unfold Commutative. lia.
Defined.

#[refine] Instance Q_add_grp : Group Q Qplus :=
  { identity := 0 }.
Proof.
  Admitted.

#[refine] Instance R_add_grp : Group R Rplus :=
  { identity := 0 }.
Proof.
  all: try lia.
  Admitted.