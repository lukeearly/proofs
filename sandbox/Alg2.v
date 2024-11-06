Structure setoid : Type :=
  { setoid_crr_set :> Set ;
    setoid_eq : relation setoid_crr_set ;
    setoid_prf_equiv : equivalence setoid_crr_set eq }.

Structure semigroup : Type :=
  { semigroup_crr_setoid :> setoid ;
    semigroup_op : bin_op semigroup_crr_setoid ;
    semigroup_prf_assoc : associative semigroup_crr_setoid semigroup_op }.

Structure monoid : Type :=
  { monoid_crr_semigroup :> semigroup ;
    monoid_id : monoid_crr_semigroup ;
    monoid_prf_id : identity_element monoid_crr_semigroup (semigroup_op monoid_crr_semigroup) monoid_id }.

Structure group : Type :=
  { group_crr_monoid :> monoid ;
    group_inv : un_op group_crr_monoid ;
    group_prf_inv : inverse_op group_crr_monoid (semigroup_op group_crr_monoid) (monoid_id group_crr_monoid) group_inv }.

Structure abgroup : Type :=
  { abgroup_crr_grp :> group ;
    abgroup_prf_comm : commutative abgroup_crr_grp (semigroup_op abgroup_crr_grp)}.

Structure ring : Type :=
  { ring_add_abgroup : abgroup ;
    (* ring_mult_monoid := ; *)
    ring_mult : bin_op ring_add_abgroup ;
    ring_prf_distrib : distributive ring_add_abgroup ring_mult (semigroup_op ring_add_abgroup) }.

Structure field : Type.