import Std.Data.Rat.Basic

class Floatable (α : Type) where
  toFloat : α → Float

instance: Floatable Nat where
  toFloat := Nat.toFloat

instance: Floatable Int where
  toFloat := fun
    | Int.ofNat n => Floatable.toFloat n
    | Int.negSucc n => -1 -Floatable.toFloat n

instance: Floatable Rat where
  toFloat r := Floatable.toFloat r.num / Floatable.toFloat r.den

