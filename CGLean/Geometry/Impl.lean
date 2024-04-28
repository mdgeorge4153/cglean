import Mathlib.Data.Rat.Field
import Mathlib.Algebra.Ring.Prod

variable (k : Type)
variable [LinearOrderedRing k]

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

def p : Point Rat := (1,2)
def q : Point Rat := (3,4)

def f (p₁ p₂ : Point k) : Point k := p₁ + p₂

#eval p < q
#eval 3*p
#eval p - q
#eval p / 3

def dotProduct (p q : Point k) : k := p.x * q.x + p.y * q.y

infixl:72 " ⬝ " => dotProduct _

#eval p ⬝ q
#eval compare p q

def h (p₁ p₂ : Point k) : k := p₁ ⬝ p₂

