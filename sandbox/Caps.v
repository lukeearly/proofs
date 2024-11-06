Inductive bvec : nat -> Set :=
  | BNIL : bvec 0
  | B0 : forall n, bvec n -> bvec (S n)
  | B1 : forall n, bvec n -> bvec (S n).

Definition regno := bvec 5.
Definition word := bvec 32.

Inductive instruction : Set :=
  | MOV   (dest src : regno)
  | ADD   (dest src : regno)
  | SUB   (dest src : regno)
  | MUL   (dest src : regno)
  | DIV   (dest src : regno)
  | LOAD  (dest src : regno)
  | STORE (dest src : regno).

Definition regfile := regno -> word.
Definition memory := word -> word.
Record state : Type := mkState
  { st_regfile : regfile
  ; st_memory : memory
  ; st_pc : word }.

Reserved Notation
  "st '=[' i ']=>' st'"
  (at level 50).
Inductive exec : instruction -> state -> state :=
  | E_Mov : forall d s st,
    st =[ MOV d s ]=> mkState (d |-> s; st_regfile st) (st_memory) (st_pc + 1)
  where "st '=[' i ']=>' st'" := exec i st st'.