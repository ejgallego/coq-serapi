Module Type AType.
Parameter A : Type.
End AType.

Module Functor (AT : AType).
Definition A := AT.A.
End Functor.
