Section Category.

Variable C0 : Set.
Variable C1 : C0 -> C0 -> Set.
Variable id : forall x : C0, C1 x x.
Variable comp : forall {x y z : C0}, C1 x y -> C1 y z -> C1 x z.
Variable idl : forall {x y : C0} (f : C1 x y),
  comp f (id y) = f.
Variable idr : forall {x y : C0} (f : C1 x y),
  comp (id x) f = f.
Variable comp_assoc :
  forall {w x y z : C0} (f : C1 w x) (g : C1 x y) (h : C1 y z),
  comp f (comp g h) = comp (comp f g) h.


Definition is_equivalence {x y} (f : C1 x y) :=
Definition is_iso {x y} (f : C1 x y) :=
  forall z, is_equivalence (fun g : C1 y z => comp f g).

End Category.