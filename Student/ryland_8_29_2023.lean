/-
  Class Notes: 8/29/2023
-/

def func_1 (f : Nat -> Nat) (a : Nat) : Nat := (f a)
#eval func_1 Nat.succ 3

def same_func_1 (f : Bool) (a : Bool) : Bool
| f, a => true
#eval same_func_1 Nat.succ 3

def func_2 : (a : Bool) -> (b : Bool) -> Bool
| a, b => and a b
#eval func_2 true true

def func_3 : Bool -> Bool -> Bool
| one, false => and one false
| one, true => and one true

def func_4 : Nat -> Nat -> Nat
| one, two => one + two

#eval func_4 2 4

def same_number : Nat -> Nat
| f => f

def polymorphic_id(T : Type) : T → T
| t, v => v

