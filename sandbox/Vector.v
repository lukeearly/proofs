From Math Require Import
  Unbundled.Unbundled.
From Coq Require Import
  Relations
  Classes.RelationClasses.

Inductive tuple (A : Type) : nat -> Type :=
  | nil : tuple A O
  | cons (h : A) : forall n, tuple A n -> tuple A (S n).

Notation "A ^ n" := (tuple A n) : type_scope.

Notation "[ a ',' .. ',' b ]" := (cons _ a _ .. (cons _ b _ (nil _)) ..)
  (at level 50).

Definition t_cons {A n} (x : A) (y : A^n) := cons A x n y.

Fixpoint t_fill A n x : A ^ n :=
  match n with
  | O => nil A
  | S n' => cons A x n' (t_fill A n' x)
  end.

Definition t_head {A n} (v : A ^ (S n)) : A :=
  match v with
  | cons _ h _ _ => h
  end.

Definition t_tail {A n} (v : A ^ (S n)) : A ^ n :=
  match v with
  | cons _ _ _ t => t
  end.

Fixpoint t_map {A B n} (f : A -> B) (v : A ^ n) : B ^ n :=
  match v with
  | nil _ => nil B
  | cons _ h n' t => cons B (f h) n' (t_map f t)
  end.

Fixpoint t_bin {A B n} (op : A -> A -> B) (v1 : A ^ n) : A ^ n -> B ^ n :=
  match v1 with
  | nil _ => fun _ => nil B
  | cons _ h n' t => fun v2 => cons B (op h (t_head v2)) n' (t_bin op t (t_tail v2))
  end.

Fixpoint t_fold {A B n} (init : B) (op : B -> A -> B) (v : A ^ n) : B :=
  match v with
  | nil _ => init
  | cons _ h _ t => op (t_fold init op t) h
  end.

Definition t_all {n} (v : Prop ^ n) : Prop :=
  t_fold True and v.

Fixpoint t_rel {A n} (r : relation A) (v1 : A ^ n) : A ^ n -> Prop :=
  match v1 with
  | nil _ => fun _ => True
  | cons _ h n' t => fun v2 => (r h (t_head v2)) /\ (t_rel r t (t_tail v2))
  end.
(* Definition t_rel {A n} (r : relation A) (v1 v2 : A ^ n) : Prop :=
  t_all (t_bin r v1 v2). *)

Require Coq.Vectors.Fin.

Definition t_ith {A n} (i : Fin.t n) (v : A ^ n) : A.
  induction i.
  - inversion v. apply h.
  - inversion v. apply IHi. apply X.
Defined.

Lemma t_all_forall {n} (v : Prop ^ n) :
  t_all v <-> forall i : Fin.t n, t_ith i v.
Proof.
  split.
  - intros.
    inversion v.
    + inversion i.
    + inversion i.


Compute (t_ith (Fin.FS) (t_cons 1 (t_cons 2 (t_cons 3 (nil _))))).

Instance tuple_setoid F n `{Setoid F}
  : Setoid (F ^ n) (t_rel s_equiv).
Proof.
  constructor.
  constructor.
  unfold Reflexive.
  induction x. unfold t_rel. easy.
  simpl. split. apply setoid_er. apply IHx.
  unfold Symmetric. intros.
  admit.
  unfold Transitive. intros.
  admit.
Admitted.

Inductive blade V `{VectorSpace V} : nat -> Type :=
  | blade_nil : blade V O
  | blade_cons (v : V) : forall n,
    blade V n ->
    blade V (S n).

Fixpoint wedge {V n m} `{VectorSpace V} (x : blade V n) (y : blade V m) : blade V (n + m) :=
  match x with
  | blade_nil _ => y
  | blade_cons _ _ h t => y
  end.

(* Fixpoint pow_type A n : Type :=
  match n with
  | O => unit
  | S n' => prod A (pow_type A n')
  end.

Notation "A ^ n" := (pow_type A n)
  : type_scope.

Definition tuple_head A p : A ^ (S p) -> A := fst.
Definition tuple_tail A p : A ^ (S p) -> A ^ p := snd.

Fixpoint fill_vec A n x : A ^ n :=
  match n return A ^ n with
  | O => tt
  | S n' => (x, fill_vec A n' x)
  end.

Fixpoint tup_map A {n} (f : un_op A) (v : A ^ n) :=
  match v in (A ^ n) return A ^ n with
  | tt => tt
  | (h, t) => (f h, tup_map A f t)
  end.

Fixpoint tup_map' A n (f : un_op A) (v : A ^ n) :=
  match n return A ^ n with
  | O => tt
  | S n' => (f (tuple_head A n' v), tup_map A n' f (tuple_tail A n' v))
  end. *)
