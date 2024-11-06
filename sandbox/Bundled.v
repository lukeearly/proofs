From Coq Require Import
  Setoids.Setoid
  Classes.Morphisms
  Classes.RelationClasses.
From Math Require Import
  Operators.

Section structs.

Class Setoid :=
  { setoid_crr : Set
  ; setoid_rel : relation setoid_crr
  ; setoid_rel_refl : Reflexive setoid_rel
  ; setoid_rel_sym : Symmetric setoid_rel
  ; setoid_rel_trans : Transitive setoid_rel }.

Class Semigroup :=
  { semigroup_crr : Set
  ; semigroup_rel : relation semigroup_crr
  ; semigroup_op : bin_op semigroup_crr
  ; semigroup_rel_refl : Reflexive semigroup_rel
  ; semigroup_rel_sym : Symmetric semigroup_rel
  ; semigroup_rel_trans : Transitive semigroup_rel
  ; semigroup_assoc : Associative semigroup_rel semigroup_op }.

Class Monoid :=
  { monoid_crr : Set
  ; monoid_rel : relation monoid_crr
  ; monoid_op : bin_op monoid_crr
  ; monoid_unit : monoid_crr
  ; monoid_rel_refl : Reflexive monoid_rel
  ; monoid_rel_sym : Symmetric monoid_rel
  ; monoid_rel_trans : Transitive monoid_rel
  ; monoid_assoc : Associative monoid_rel monoid_op
  ; monoid_id : Identity monoid_rel monoid_op monoid_unit }.

Class Group :=
  { group_crr : Set
  ; group_rel : relation group_crr
  ; group_op : bin_op group_crr
  ; group_inv : un_op group_crr
  ; group_unit : group_crr
  ; group_rel_refl : Reflexive group_rel
  ; group_rel_sym : Symmetric group_rel
  ; group_rel_trans : Transitive group_rel
  ; group_assoc : Associative group_rel group_op
  ; group_id : Identity group_rel group_op group_unit
  ; group_cancel : Inverse group_rel group_op group_unit group_inv }.

End structs.

Theorem grp4trans {G : Group} : forall (w x y z : group_crr),
  group_rel w x ->
  group_rel x y ->
  group_rel y z ->
  group_rel w z.
Proof.
  intros. destruct G.
  transitivity y.
  transitivity x.
  all: assumption.
Qed.