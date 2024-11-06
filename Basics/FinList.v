Section VectorDef.
Context {A : Type} {n : nat}.

Definition t := { l : list A & length l = n }.

End VectorDef.

Notation "A ^ n" := (t A n) : type_scope.
