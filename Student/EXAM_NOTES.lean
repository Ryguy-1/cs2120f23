#eval !true           -- prefix notation for not
#eval true && true    -- infix notation for and
#eval true || true    -- infix notation for or
#eval 0 + 0          -- infix notation for Nat.add
#eval "Hello" ++ ", Logic!" -- infix notation for String.append

-- implies function
def imp : Bool -> Bool -> Bool
| true, false => false
| _, _ => true

def isEven : Nat → Bool
| n => if (n%2 = 0) then true else false

def compose {α β γ : Type} :
  (β → γ) → 
  (α → β) → 
  (α → γ)       
| g, f => (fun a => g (f a)) 

def double (n : Nat) := 2 * n 
def square (n : Nat) := n ^ 2
def exclaim (s : String) := s ++ "!"
def is_even (n : Nat) := n % 2 == 0

#eval compose (λ a => a%2==0) String.length "helloooo"
#eval ((λ a => a%2==0) ∘ String.length) "testd"

def double_after_square := (double ∘ square)

inductive Result : Type
| wins
| loses
| ties

open Result

-- Polymorphic Type -> Type Builder of Sorts
inductive Box (α : Type) : Type
| put (a : α)

#check Box.put -- α -> Box α

-- Eliminator
def get {α : Type} : Box α → α -- get the thing back out of the box
| (Box.put o) => o

inductive Prod3 (α β γ: Type) : Type
| trio (a : α) (b : β) (c : γ)

def third {α β γ : Type} : Prod3 α β γ → γ
| (Prod3.trio _ _ γ) => γ

-- The name of the single Prod constructor is mk
def pair0 := Prod.mk true 10

-- It's better to use standard "outfix" notation
def pair1 := ("Hello",5)

--"×" (product) is Right Associative
-- → is right associative (ℕ -> ℕ -> ℕ, which is equivalent to ℕ -> (ℕ -> ℕ))
-- function application is left associative (f g h, which is equivalent to (f g) h)
--  this is why you have to manually override if want to, say, apply twice!


def sum_elim {α β γ : Type} : 
  (α ⊕ β) → 
  (α → γ) → 
  (β → γ) 
  → γ
| (Sum.inl a), a2y, _ => a2y a
| (Sum.inr b), _, b2y => b2y b


def demorgan1'  {α β : Type} : ((α → Empty) ⊕ (β → Empty)) → (α × β → Empty)  
| Sum.inl a2e => (fun (ab : α × β) => a2e ab.fst)
| Sum.inr b2e => (fun (ab : α × β) => b2e ab.snd)

def demorgan2' {α β : Type} : (α ⊕ β → Empty) → ((α → Empty) × (β → Empty))
| sumab => (fun (a : α) => sumab (Sum.inl a : α ⊕ β), fun (b : β) => sumab (Sum.inr b : α ⊕ β))

def demorgan3' {α β : Type} : ((α → Empty) × (β → Empty)) → ((α ⊕ β) → Empty)  
| (a2e, b2e) => fun (aSb : α ⊕ β) => 
  match (aSb : α ⊕ β) with 
  | Sum.inl (a : α) => a2e a
  | Sum.inr (b : β) => b2e b

#check ()

def silly : Unit → Nat
| () => 5
#eval silly () --5
-- Ryland Note: Unit like void type in other languages

def empty2nat : Empty → Nat 
| e => nomatch e

-- Learn this new syntax please (match expression)
def negate' : Bool → Bool :=  -- type
  fun x : Bool =>             -- assume given Bool x
    match x with              -- case analysis on x
    | true => false           -- result in case true
    | false => true           -- result in case false

#check (λ x : Bool =>                
    match x with
    | true => false
    | false => true)

def empty2empty : Empty → Empty := λ e => e

-- Defining the function noe2s (inhabited)
def noe2s : String ⊕ Empty → Nat
| Sum.inl s => String.length s  -- If the input is a string, return its length
| Sum.inr e => nomatch e -- This case will never be reached

-- Prove this type uninhabited: {α : Type} → α × (α → Empty)
  -- Must be because α -> Empty is uninhabited, so the entire product
  --  type must also be uninhabited

inductive Doll : Type
| solid -- Ryland: very last doll inside
| shell (d : Doll) -- Ryland: a doll is otherwise a shell

open Doll

def d0' := solid
def d1' := shell solid
def d2' := shell (shell solid)
def d3' := shell (shell (shell solid))

def depth : Doll → Nat 
| solid => 0                      -- *base case*
| shell d' => 1 + depth d'        -- recursive case

#eval depth d0'
#eval depth d1'
#eval depth d2'
#eval depth d3'

def len {α : Type} : List α → Nat
| [] => 0
| _::t => 1 + len t

#eval len [3,2,1,0]

def apply_n {α : Type} : (α → α) → α → Nat → α  
| _, a, 0 => a
| f, a, (n' + 1) => f (apply_n f a n')

def concat {α : Type} : List α -> List α -> List α
| [], m => m
| h1::t1, l2 => h1::concat t1 l2

def list_rev {α : Type} : List α -> List α
| [] => []
| h::t => concat (list_rev t) [h]

def prod_ors_to_or_prods {α β γ δ: Type} :
  (α ⊕ β) × (γ ⊕ δ) → α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ 
| (Sum.inl a, Sum.inl g) => Sum.inl (a, g)
| (Sum.inl a, Sum.inr d) => Sum.inr (Sum.inl (a, d))
| (Sum.inr b, Sum.inl g) => Sum.inr (Sum.inr (Sum.inl (b, g)))
| (Sum.inr b, Sum.inr d) => Sum.inr (Sum.inr (Sum.inr (b, d)))

/-
Atomic Propositions
- It's raining
- The ground is wet
- x * y = 1

Not Atomic
- If it's raining then the ground is wet
- a implies b (using propositional letters)
- x * y = 1 or x * y ≠ 1 (x and y are not propositional letters in this context, but refer to numbers)

- If *a* is an atomic formula then *{a}* is an expression
- If *b* and *c* are expressions, then so are the following:
  - ¬b        -- not b
  - b ∧ c     -- b and c
  - b ∨ c     -- b or c
  - b ⇒ c     -- b implies c; if b then c
  - b ↔ c     -- b if and only if c; b and c are equivalent -- Ryland: Must Have Same Value

Now assume that a and b are any expressions
- ¬a            -- it's not raining
- a ⇒ b         -- if it's raining then the ground is wet
- a ∨ b         -- it's raining or the ground is wet
- (a ∧ b) ∨ ¬a  -- (raining and wet) or (not raining) 

-- INTERPRETATION NOTE: with n variables => 2^n interpretations

-- Each row is an interpretation
| a      | b      |  {a} ∨ {b}  |
|--------|--------|-------------|
| true   | true   |     true    |
| true   | false  |     true    |
| false  | true   |     true    |
| false  | false  |     false   |


-/

-- FINAL FORM OF LOGIC (including iff)
structure var : Type :=  (n: Nat)
inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
| iff                                   -- Ryland: ADDED THIS HOMEWORK 7
inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)
notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true
def biimplies : Bool -> Bool -> Bool    -- Ryland: ADDED THIS HOMEWORK 7
| true, true => true
| false, false => true
| _, _ => false
def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => biimplies            -- Ryland: ADDED THIS HOMEWORK 7
def Interp := var → Bool  
def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)

-- If Need to Evaluate, use Bottom of Lecture 13 (with all other solver code)
-- #eval valid ((O ∨ A) ∧ (B ∨ C) ⇔ ((A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C))) -- true


-------------------------
def factorial : Nat -> Nat
| 0 => 1
| (n' + 1) => (n' + 1) * factorial n'
#eval factorial 3

def list_len {α : Type} : List α -> Nat
| [] => 0
| _::t => 1 + list_len t
#eval list_len [1, 2, 3]

def sum_cubes : List Nat -> Nat
| [] => 0
| h::t => h^3 + sum_cubes t
#eval sum_cubes [1, 2]

def sum_power : List Nat -> Nat -> Nat
| [], _ => 0
| h::t, pow => h^pow + sum_power t pow
#eval sum_power [1, 2] 3

def any_true : List Bool -> Bool
| [] => false
| h::t => or h (any_true t)
#eval any_true [false, false, false]
#eval any_true [false, true, false]

def every_true : List Bool -> Bool
| [] => true
| h::t => and h (any_true t)
#eval every_true [false, false, false]
#eval every_true [false, true, false]
#eval every_true [true, true, true]

def is_even' : Nat -> Bool
| 0 => true
| 1 => false
| (n' + 2) => is_even' n'
#eval is_even' 7

def is_odd' : Nat -> Bool
| n => not (is_even' n)
#eval is_odd' 7
