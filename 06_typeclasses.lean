import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Module.Defs
/-

Lean uses type classes pervasively

-/


-- Notation typeclasses
#check Add
#check Mul
#check Zero


-- Algebraic typeclasses
#check Monoid
#check AddMonoid
#check Group
#check Ring
#check NonUnitalNonAssocCommSemiring


-- Type classes with type class parameters
#check Module


-- Type classes for properties ("mixins")
#check IsLeftCancelMul
