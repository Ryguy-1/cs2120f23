/-!
# Exam 1
## Ryland Birchmeier
## Computing ID: zbp6dw

DO NOT CHEAT.
-/

/-! 
## #1 Easy Functions [15 points]

Define a function, *pythag*, that takes three natural 
numbers, call them *a, b,* and *c*, and that returns
*true* if *a^2 + b^2 = c^2* and that returns *false*
otherwise.

[[Ryland: DONE]]
-/

-- Define your function here
def pythag : (a : Nat) -> (b : Nat) -> (c : Nat) -> Bool
| a, b, c => a^2 + b^2 == c^2

-- The following test cases should then pass
#eval pythag 3 4 5  -- expect true
#eval pythag 6 7 8  -- expect false

/-! 
## #2 Recursive Functions

Define a function, sum_cubes, that takes any natural
number, *n*, as an argument, and that retrns the sum
of the cubes of the natural numbers from *1* up to *n*
inclusive.

[[Ryland: DONE]]
-/

-- Define your function here
def sum_cubes : (n : Nat) -> Nat
| 0 => 0
| (n' + 1) => (n' + 1)^3 + sum_cubes (n')

-- test case: sum_cubes 4 = 1 + 8 + 27 + 64 = 100
#eval sum_cubes 4   -- expect 100


/-!
## #3 Product and Sum Types

Define two functions, called *prod_ors_to_or_prods*, 
and *or_prods_to_prod_ors* that shows that a product 
of sums be converted into a sum of products in a way
that the result can then be converted back into the
original product of sums. 

As a concrete example, you might want to show that if 
you have an apple or an orange and you have a cup or
a bowl, then you have an apple and a cup or an apple
and a bowl or an orange and a cup or an orange and a
bowl. 

Hints: 1. Be sure you understand the reasoning before
you try to define your functions. 2. Use four cases. 3. 
Use type-guided, top-down programming, assisted by the
Lean prover to work out a solution for each case.  

[[Ryland: DONE]]
-/

def prod_ors_to_or_prods {α β γ δ: Type} :
  (α ⊕ β) × (γ ⊕ δ) → α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ 
| (Sum.inl a, Sum.inl g) => Sum.inl (a, g)
| (Sum.inl a, Sum.inr d) => Sum.inr (Sum.inl (a, d))
| (Sum.inr b, Sum.inl g) => Sum.inr (Sum.inr (Sum.inl (b, g)))
| (Sum.inr b, Sum.inr d) => Sum.inr (Sum.inr (Sum.inr (b, d)))

-- Write the second function here from scratch
def or_prods_to_prod_ors {α β γ δ: Type} :
  α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ → (α ⊕ β) × (γ ⊕ δ)
| Sum.inl (a, g) => (Sum.inl a, Sum.inl g)
| Sum.inr (Sum.inl (a, d)) => (Sum.inl a, Sum.inr d)
| Sum.inr (Sum.inr (Sum.inl (b, g))) => (Sum.inr b, Sum.inl g)
| Sum.inr (Sum.inr (Sum.inr (b, d))) => (Sum.inr b, Sum.inr d)

/-!
## #4 Propositional Logic Syntax and Semantics

Extend your Homework #7 solution to implement the
propositional logic *iff/equivalence* (↔) operator.
Note that Lean does not natively define the *iff*
Boolean operator. 

[[Ryland: DONE -> THIS IS IN THE LECTURE_13 FILE!!]]
-/

/-!
Using our syntax for propositional logic, and the
variable names *A, O, C,* and *B*, respectively for
the propositions *I have an apple, I have an orange,
I have a cup,* and *I have a bowl* write a proposition
that having an orange or an apple and a bowl or a cup
is equivalent to having an apple and a bowl or an
apple and a cup or an orange and a bowl or an orange
and a cup.

Note: There's no need here to use our implementation
of propositional logic. Just write the expression 
here using the notation we've defined.

[[Ryland: DONE]]
-/

/-
  Ryland Answer:
  - Note that I grouped the first half's OR statements together due to
  the way that the question was phrased. It implies that Orange and Apple
  should be evaluated first along with Bowl and Cup and then AND those two
  together. The parenthesis on the second half of the statement are also
  redundant because AND takes precedence anyways in propositional logic
  order of operations!

  ((O ∨ A) ∧ (B ∨ C) ⇔ ((A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C)))
-/


/-!
## #5 Propositional Logic Validity
At the end of your updated Homework #7 file, use our
validity checking function to check your expression
for validity, in the expectation that the checker will
determine that the expression is in fact valid. 

[[Ryland: DONE -> THIS IS IN THE LECTURE_13 FILE!!]]
-/
-- Final Answer (can be seen working in Lecture 13 file v)
-- #eval valid ((O ∨ A) ∧ (B ∨ C) ⇔ ((A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C))) -- true
