/-!
If you have jam, then you have jam or bread.
Finish implementing this function to prove it
formally.
-/

def quiz2 { jam bread : Type} : jam → jam ⊕ bread
| jam => Sum.inl jam

/-!
Provide a term of type Unit × Nat.
-/

def unit_or_empty : Unit × Nat := ((), 3)
