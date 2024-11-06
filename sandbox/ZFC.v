From Coq Require Import Strings.String.

Delimit Scope fol_scope with fol.
Local Open Scope fol_scope.

Definition Var := string.

Inductive Term : Set :=
  | SEq : Var -> Var -> Term
  | SIn : Var -> Var -> Term
  | Univ : Var -> Term -> Term
  | T : Term
  | Neg : Term -> Term
  | Conj : Term -> Term -> Term.

Notation "x == y" := (SEq x y)
  (at level 70, no associativity) : fol_scope.
Notation "x 'in' y" := (SIn x y)
  (at level 70, no associativity) : fol_scope.
Notation "'Forall' x , P" := (Univ x P)
  (at level 200, right associativity) : fol_scope.
Notation "'Top'" := T : fol_scope.
Notation "~ P" := (Neg P) : fol_scope.
Notation "P /\ Q" := (Conj P Q) : fol_scope.

Notation "x != y" := (~ SEq x y)
  (at level 70, no associativity) : fol_scope.
Notation "x !in y" := (~ SIn x y)
  (at level 70, no associativity) : fol_scope.
Notation "'Exists' x , P" := (~ Forall x, ~ P)
  (at level 200, right associativity) : fol_scope.
Notation "'Bot'" := (~ T) : fol_scope.
Notation "P \/ Q" := (~(~P /\ ~Q)) : fol_scope.
Notation "P -> Q" := (~P \/ Q) : fol_scope.
Notation "P <-> Q" := (P -> Q /\ Q -> P) : fol_scope.

Definition subst_v (v x : Var) (t : Var) :=
  if String.eqb v t then x else t.
Definition subst (v x : Var) : Term -> Term :=
  fix subst' t :=
    match t with
    | SEq t1 t2 => SEq (subst_v v x t1) (subst_v v x t2)
    | SIn t1 t2 => SIn (subst_v v x t1) (subst_v v x t2)
    | Univ v' t' => if String.eqb v v' then Univ v' t'
                   else Univ v' (subst' t')
    | T => T
    | Neg t' => Neg (subst' t')
    | Conj t1 t2 => Conj (subst' t1) (subst' t2)
    end.

Inductive occurs : Var -> Term -> Prop :=
  | Occ_SEq_l (l r : Var) : occurs l (l == r)
  | Occ_SEq_r (l r : Var) : occurs r (l == r)
  | Occ_SIn_l (l r : Var) : occurs l (l in r)
  | Occ_SIn_r (l r : Var) : occurs r (l in r)
  | Occ_Univ_Sym (x y : Var) (t : Term) :
      x = y -> occurs x (Forall y, t)
  | Occ_Univ (x y : Var) (t : Term) :
      occurs x t -> occurs x (Forall y, t)
  | Occ_Neg (x : Var) (t : Term) :
      occurs x t -> occurs x (~ t)
  | Occ_Conj_l (x : Var) (t1 t2 : Term) :
      occurs x t1 -> occurs x (t1 /\ t2)
  | Occ_Conj_r (x : Var) (t1 t2 : Term) :
      occurs x t2 -> occurs x (t1 /\ t2).

Reserved Notation "P |- Q"
  (at level 200).

(* https://www.cs.utexas.edu/~mooney/cs343/slide-handouts/inference.4.pdf *)
Inductive deriveable : Term -> Term -> Prop :=
  | D_UnivElim (v g : Var) (t : Term) :
    Forall v, t |- subst v g t
  | D_ExistElim (v k : Var) (t : Term) :
    ~ occurs k t ->
    Exists v, t |- subst v k t
  | D_ExistIntro (v g : Var) (t : Term) :
    ~ occurs v t ->
    t |- Exists v, (subst g v t)
where "P |- Q" := (deriveable P Q).

Section ZF.

End ZF.