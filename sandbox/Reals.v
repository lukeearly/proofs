Require Import Coq.QArith.QArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.PeanoNat.

Locate "<".

Definition is_cauchy_sequence (f : nat -> Q) : Prop :=
  forall epsilon : Q, (0 < epsilon)%Q ->
                 exists N : nat, forall n1 n2 : nat, (N < n1 < n2)%nat ->
                                         -epsilon < (f n1) - (f n2) < epsilon.

Record extended_dedekind_cut (f : Q -> Prop) : Prop :=
  { closed_left : forall q1 q2 : Q, q1 < q2 -> f q2 -> f q1
  ; open_right : forall q1 : Q, f q1 -> exists q2 : Q, q1 < q2 /\ f q2 }.

Record dedekind_cut (f : Q -> Prop) : Prop :=
  { edc : extended_dedekind_cut f
  ; nonempty : exists q : Q, f q
  ; nonfull : exists q : Q, ~ f q}.

Inductive cauchy_real : Type :=
  | lim (f : nat -> Q) (_ : is_cauchy_sequence f).

Inductive dc_real : Type :=
  | cut (f : Q -> Prop) (_ : dedekind_cut f).

Definition q2cr (q : Q) : cauchy_real.
Proof.
  eapply lim with (fun _ => q).
  unfold is_cauchy_sequence.
  intros.
  exists O.
  intros.
  split.
  unfold Qminus.
  rewrite Qplus_opp_r.
Admitted.

Lemma Q112 : 1 + 1 = 2.
Proof. auto with qarith. Qed.

Lemma Q_bisect (q1 q2 : Q) : q1 < q2 -> q1 < (q1 + q2) / 2 < q2.
Proof.
  intro H. split.
  apply Qlt_shift_div_l. eauto with qarith.
  rewrite <- Q112. rewrite Qmult_plus_distr_r.
  repeat rewrite Qmult_1_r.
  apply <- Qplus_lt_r. assumption.
  apply Qlt_shift_div_r. eauto with qarith.
  rewrite <- Q112. rewrite Qmult_plus_distr_r.
  repeat rewrite Qmult_1_r.
  apply <- Qplus_lt_l. assumption.
Qed.

Definition q2dr (q : Q) : dc_real.
Proof.
  eapply cut with (fun x => x < q).
  repeat split.
  - intros. eapply Qlt_trans. apply H. apply H0.
  - intros. exists ((q1 + q) / 2). apply Q_bisect, H.
  - exists (q + -1).
    apply Qplus_lt_l with 1.
    rewrite <- Qplus_assoc.
    rewrite <- (Qopp_involutive 1) at 1.
    rewrite Qplus_opp_r.
    apply <- Qplus_lt_r. auto with qarith.
  - exists q.
    apply Qlt_irrefl.
Qed.

Definition cr2dr (cr : cauchy_real) : dc_real.
Proof.
  destruct cr.
  eapply cut with (fun x => exists N : nat, forall n : nat, (N < n)%nat -> x < f n).
  repeat split.
  - intros.
    destruct H0 as [N H0].
    exists N. intros.
    eapply Qlt_trans. apply H. apply H0. apply H1.
  - intros.
    destruct H as [N H].
    exists ((q1 + f (N + 1)%nat) / 2).
    split. apply Q_bisect. apply H.
    rewrite PeanoNat.Nat.add_comm. simpl. unfold lt. reflexivity.
    unfold is_cauchy_sequence in i.
    evar (e : Q). specialize i with e.
    destruct i as [N1].
    shelve.
    Abort.

Definition approach (f : Q -> bool) (sx : Q * Q) : Q * Q :=
  let (step, x) := sx in
  if f x then
    if f (x + step) then
      (step, x + step)
    else
      (step / 2, x)
  else
    if f (x - step) then
      (step, x - step)
    else
      (step / 2, x).
Fixpoint repeat {A} (n : nat) (f : A -> A) (a : A) :=
  match n with
  | O => a
  | S n' => repeat n' f (f a)
  end.

Definition dr2cr (dr : dc_real) : cauchy_real.
Proof.
  destruct dr.
  eapply lim with (fun n => fst (repeat n (approach f) (1, 0))).
