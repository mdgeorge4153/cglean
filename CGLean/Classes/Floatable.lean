module



public class Floatable (α : Type) where
  toFloat : α → Float

public instance: Floatable Float where
  toFloat := id

public instance: Floatable Nat where
  toFloat := Nat.toFloat

public instance: Floatable Int where
  toFloat := fun
    | Int.ofNat n => Floatable.toFloat n
    | Int.negSucc n => -1 -Floatable.toFloat n

public instance: Floatable Rat where
  toFloat r := Floatable.toFloat r.num / Floatable.toFloat r.den


