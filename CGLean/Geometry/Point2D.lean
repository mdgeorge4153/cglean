import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.Ring.Defs
-- `Lex` is a type synonym and inherits no instances of its own; this supplies
-- the algebraic structure that gives `Point` its `+`.
import Mathlib.Algebra.Order.Group.Synonym

variable (k : Type)
variable [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]

-- Points are pairs of numbers. We use lexicographic ordering for <, so that
-- we first sort by x coordinate and then y coordinate. You can think of this
-- as sorting from left to right, except we need a way to handle the special
-- case where p₁ and p₂ have the same x coordinate. The trick is that we
-- imagine applying a tiny shear transformation, so that the pair (x,y) really
-- represents the point (x+εy, y). Then if y₁ < y₂, the point represented by
-- (x,y₁) is actually a little to the left of the point represented by (x,y₂).
-- This is exactly what we get by using the lexicographic ordering
abbrev Point := k ×ₗ k

abbrev Segment := Point k × Point k

abbrev Point.x (p : Point k) := p.fst
abbrev Point.y (p : Point k) := p.snd

-- TODO: notation typeclass for this:
def Point.dot (p q : Point k) : k := p.x * q.x + p.y * q.y
infixl:72 " ⬝ " => Point.dot _
