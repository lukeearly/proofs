Require Import AlgPred.

Fixpoint pow_type A n : Type :=
  match n with
  | O => unit
  | S n' => prod A (pow_type A n')
  end.

Notation "A ^ n" := (pow_type A n)
  : type_scope.

Section TupleSpace.

Variable F : Type.
Context `{Field F}.

Local Open Scope F_scope.

Fixpoint fn_plus (n : nat) (a b : F^n) : F^n :=
  match n with
  | O => tt
  | S n' => pair (fst a + fst b) (fn_plus n' (snd a) (snd b))
  end.

Variable n : nat.
Let V := F^n.

End TupleSpace.