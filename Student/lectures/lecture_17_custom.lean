/-!
# Curry-Howard Correspondance
-/

/-!
## Empty ==> False
-/

#check Empty
-- inductive Empty : Type

inductive Chaos : Type

def from_empty (e : Empty) : Chaos := nomatch e

-- Bool -> values are true/false
-- False -> type prop -> values are proofs!!

-- False is to Prop like Empty is to Type (both uninhabited)
-- can prove anything with false
#check False -- type = prop
-- inductive False : Prop

-- P is a proposition
-- p is a proof of false here
def from_false  {P : Prop} (p : False) : P := False.elim p
def from_false' {P : Prop} (p : False) : P := nomatch p -- Ryland: realized you can also do this it seems.

def from_false_true_is_false (p : False) : True = False := False.elim p

-- no introduction rule

/-!
## Unit ==> True
-/

-- Unit is like True in Prop
#check Unit
#check True
#check True.intro -- proof of true


-- no elimination rule! -> not useful at all really

def proof_of_true : True := True.intro

def false_implies_true : False → True := (λ f => False.elim f)
def false_implies_true' : False → True := False.elim

/-!
## Prod ==> And
-/

#check Prod
/-!
structure Prod (α : Type u) (β : Type v) where
  /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
  snd : β
-/

#check And
/-!
structure And (a b : Prop) : Prop where
  /-- `And.intro : a → b → a ∧ b` is the constructor for the And operation. -/
  intro ::
  /-- Extract the left conjunct from a conjunction. `h : a ∧ b` then
  `h.left`, also notated as `h.1`, is a proof of `a`. -/
  left : a
  /-- Extract the right conjunct from a conjunction. `h : a ∧ b` then
  `h.right`, also notated as `h.2`, is a proof of `b`. -/
  right : b

-/


-- has 2 proofs
inductive Birds_Chirping : Prop
| yes
| spooky

inductive Sky_Blue : Prop
| yep

#check And Birds_Chirping Sky_Blue

theorem both_and : And Birds_Chirping Sky_Blue := And.intro Birds_Chirping.spooky Sky_Blue.yep


/-!
## Proof Irrelevance
-/

-- here you really care about which type you use, but in propositional
-- logic, it shouldn't matter which proof you use (and it doesn't! (see above))
namespace cs2120f23
inductive Bool : Type
| true
| false

theorem proof_equal : Birds_Chirping.spooky = Birds_Chirping.yes := by trivial

-- In Prop, all proofs are equivalent
-- Choice of values in Prop can't influence computations

/-!
## Sum ==> Or
-/

#check Sum

/-!
inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
  | inr (val : β) : Sum α β
-/

#check Or
/-!
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b
-/

theorem one_or_other : Or Birds_Chirping Sky_Blue := Or.inl Birds_Chirping.yes
theorem one_or_other' : Or Birds_Chirping Sky_Blue := Or.inr Sky_Blue.yep

-- example is like theorem, but don't have to give name
example : Or Birds_Chirping (0=1) := Or.inl Birds_Chirping.spooky
example : (0=1) ∨ (1==2) := _  -- there is no proof you can make here

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ d =>
  match d with
  | Or.inl a => Or.inr a
  | Or.inr b => Or.inl b

/-!
## Not (no)
-/

def no (α : Type) := α → Empty

#check Not -- "defined to be p → False"!! Same as alpha to Empty!

example : no Chaos := (λ (c : Chaos) => nomatch c)


inductive Raining : Prop

example : ¬Raining := (λ (a : Raining) => nomatch a)
