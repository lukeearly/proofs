Require Import Coq.Classes.RelationClasses.

Context (A : nat -> Prop).

Fixpoint Union (n : nat) (seq : nat -> Prop) : Prop :=
  match n with
  | O => False
  | S n' => seq n' \/ Union n' seq
  end.
Fixpoint Inter (n : nat) (seq : nat -> Prop) : Prop :=
  match n with
  | O => True
  | S n' => seq n' /\ Inter n' seq
  end.

Definition B (n : nat) : Prop :=
  A n /\ Inter n (fun i => ~ A i).

Lemma dml : forall n s, ~ Union n s <-> Inter n (fun i => ~ s i).
Proof.
  intros.
  induction n.
  - simpl. split; auto.
  - simpl.
    split; intros.
    + split. auto. apply IHn. auto.
    + intro. destruct H. apply IHn in H1. destruct H0; contradiction.
Qed.

Theorem union_equiv :
  forall n, Union n A <-> Union n B.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. split.
    + unfold B. intros.
      destruct H as [H|H].
    etransitivity. etransitivity.
