import Mathlib.Data.Set.Basic

/-!
# Final Exam: Part 2

Here you can show that you've got what we covered in class,
up to and including set theory. The focus is on set theory,
as it encompassess the underlying logic as well. A hint: You
will want to review the existential quantifier and proofs of
existentially quantified propositions.

## Problem #1:

Use set comprehension notation in Lean to define *odds*
as the set of odd numbers, by way of a membership predicate
for this set.

[[ Ryland: Done ]]
-/

-- Here
def odds : Set Nat := { n : Nat | n % 2 = 1}

/-!
## Problem #2:

Use set comprehension and other set notations in Lean to
define the set, *perfect_squares*, of natural numbers, n,
such that each n is the square of some natural number, m.
For example, 36 is a perfect square because it is the square
of another number, namely m = 6.

[[ Ryland: Done ]]
-/

-- Here
def perfect_squares : Set Nat := { n : Nat | ∃ (m : Nat), m^2 = n}
#check perfect_squares

/-!
## Problem #3:

Use set comprehension notation to define the set, odd_perfects,
to be the intersection of the odds and the perfect squares.

[[ Ryland: Done ]]
-/

-- Here
def odd_perfects : Set Nat := {n : Nat | n ∈ odds ∩ perfect_squares}
-- Can also be done like this
def odd_perfects' : Set Nat := odds ∩ perfect_squares

/-!
## Problem #4:

Formally state and prove the proposition that 9 ∈ odd_perfects.
Hint: A proof within a proof.
-/

-- Here
def nine_in_odd_perfects : 9 ∈ odd_perfects := ⟨ rfl, Exists.intro 3 rfl ⟩
