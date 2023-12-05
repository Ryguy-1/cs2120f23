-- easy
example : ∀ (n : Nat), Nat.add n 0 = n := by
simp [Nat.add]

-- challenge
example : ∀ (n : Nat), Nat.add 0 n = n := by
simp [Nat.add]
_   -- NOPE


def left_zero (n : Nat) := Nat.add 0 n = n

-- Want a proof ∀ n, left_zero n
def goal := ∀ n, left_zero n

-- see if answer by induction

#reduce left_zero 0

-- base machine
def add_base : left_zero 0 := rfl

-- step machine
def add_step (n' : Nat) (pf : left_zero n') : left_zero (Nat.add n' 1) := by
simp [Nat.add]
simp [left_zero]

def factorial_step_function (n' ans_n' : Nat) := (n' + 1) * ans_n'
#eval factorial_step_function 5 120
