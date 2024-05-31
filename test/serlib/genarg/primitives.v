Require Export CarryType.

Primitive int := #int63_type.
Primitive lsl := #int63_lsl.

Set Universe Polymorphism.

Primitive array := #array_type.

Primitive make : forall A, int -> A -> array A := #array_make.
Arguments make {_} _ _.
