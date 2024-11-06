From Coq Require Import
  Setoids.Setoid
  Classes.Morphisms
  Classes.RelationClasses.
Require Import Notations.

Class Setoid (A : Type) (eq: SetoidEquiv A) : Prop :=
  { setoid_er : Equivalence eq }.
Global Existing Instance setoid_er.
Global Instance setoid_trans `{Setoid} : Transitive s_equiv.
Proof. destruct H, setoid_er0. assumption. Qed.
Global Instance setoid_sym `{Setoid} : Symmetric s_equiv.
Proof. destruct H, setoid_er0. assumption. Qed.
Global Instance setoid_refl `{Setoid} : Reflexive s_equiv.
Proof. destruct H, setoid_er0. assumption. Qed.

(* Program Instance setoid_eqr {A : Type} {_ : Setoid A eq} : Equivalence eq := *)
  (* setoid_er. *)

(* Program Instance EquivalenceRelation_Equivalence eq : Equivalence eq. *)

(* Add Parametric Relation `{Setoid A} : A (equiv)
  [transitivity proved by er_trans]. *)

(* Class Proper {A : Type} (rel: relation A) (x : A) :=
  prf_proper : rel x x.
Definition respectful {A B : Type} (r : relation A) (r' : relation B)
  : relation (A -> B) :=
  fun f g => forall x y, r x y -> r' (f x) (g y).
Infix "==>" := respectful (right associativity, at level 55). *)

