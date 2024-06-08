import Mathlib.Algebra.Ring.Defs

/--
Just a little class to encapsulate the operations needed for a ring without
axioms. This is just here so that we can have something to name for the
blueprint (i.e. we can have a definition in the blueprint that refers to an
instance of this class).
-/
class RingOps (A:Type) extends Zero A, One A, Add A, Neg A, Mul A

