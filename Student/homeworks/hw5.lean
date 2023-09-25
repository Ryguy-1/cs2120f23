/-!
# Homework 5: Inhabitedness and Induction
## Ryland Birchmeier
## Computing ID: zbp6dw

The PURPOSE of this homework is to greatly strengthen 
your understanding of reasoning with sum and product
types along with properties of being inhabited or not. 

READ THIS: The collaboration rule for this homework is 
that you may *not* collaborate. You can ask friends and 
colleagues to help you understand the class material, 
but you may not discuss any of these homework problems
with anyone other than one of the instructors or TAs.

Finally, what you're seeing here is the FIRST set of
questions on this homework, giving you an opportunity
to deepen your understanding of the Empty type and its
uses. 

[[[- Ryland: Done]]]
-/

/-!

## PART 1: Inhabitedness and Logical Negation

Of particular importance in these questions is the
idea that *having* a function value (implementation) 
of type *α → Empty* proves that α is uninhabited, in
that if there were a value (a : α) then you'd be able
to derive a value of type Empty, and that simply can't
be done, so there must be no such (a : α). That's the
great idea that we reached at the end of lecture_09.

More concretely every time you see function type that
looks like (α → Empty) in what follows, you can read 
it as saying *there is no value of type α*. Second, if 
youwant to *return* a result of type (α → Empty), to
showing that there can be no α value, then you need 
to return a *function*; and you will often want to do
so by writing the return value as a lambda expression. 

[[[- Ryland: Done]]]
-/

/-!
### #1 Not Jam or Not Cheese Implies Not Jam and Cheese

Suppose you don't have cheese OR you don't have jam. 
Then it must be that you don't have (cheese AND jam).
Before you go on, think about why this has to be true.
Here's a proof of it in the form of a function. The 
function takes jam and cheese implicitly as types.
It takes a value that either indicates there is no
jam, or a value that indicates that there's no cheese,
and you are to construct a value that shows that there
can be no jam and cheese. It works by breaking the first
argument into two cases: either a proof that there is
no jam (there are no values of this type), or a proof
that there is no cheese, and shows *in either case*
that there can be no jam AND cheese. 

[[[- Ryland: Done]]]
-/

/-!
## New Addition: no (α : Type) := α → Empty

We can make the logical intent of our
types and computations clearer by introducing a
shorthand, *no α* for the type *α → Empty*. Then
in each place where a type like *α → Empty appears
in this homework, replace it with *no α*. Use the
right local names in each instance, of course. 

[[[- Ryland: Done]]]
-/

def no (α : Type) := α → Empty

/-!
We've now replaced each α → Empty with no α. We
suggest that you go ahead and use *no* wherever
doing so makes the logical meaning clearer. 

[[[- Ryland: Done]]]
-/

def not_either_not_both { jam cheese } :
  ((no jam) ⊕ (no cheese)) → 
  (no (jam × cheese)) 
| Sum.inl nojam => (fun (jamcheese : jam × cheese) => nojam jamcheese.fst)
| Sum.inr nocheese => (fun (jamcheese : jam × cheese) => nocheese jamcheese.snd)

-- [EXTRA // Ryland]: (other way that I find clearer):
def not_either_not_both' { jam cheese } :
  ((jam → Empty) ⊕ (cheese → Empty)) → 
  (jam × cheese → Empty)
| Sum.inl jam2empty => (λ (a : jam × cheese) => jam2empty a.fst)
| Sum.inr cheese2empty => (λ (a : jam × cheese) => cheese2empty a.snd)

/-!
### #2: Not One or Not the Other Implies Not Both
Now prove this principle *in general* by defining a 
function, demorgan1, of the following type. It's will
be the same function, just with the names α and β for
the types, rather than the more suggestive but specific
names, *jam* and *cheese*. 

{α β : Type} → (α → Empty ⊕ β → Empty) → (α × β → Empty).

[[[- Ryland: Done]]]
-/

def demorgan1  {α β : Type} : ((α → Empty) ⊕ (β → Empty)) → (α × β → Empty)  
| (Sum.inl noa) => (λ ab => noa ab.fst)
| (Sum.inr nob) => (λ ab => nob ab.snd)

-- [EXTRA // Ryland] another way of writing with clear typing:
def demorgan1'  {α β : Type} : ((α → Empty) ⊕ (β → Empty)) → (α × β → Empty)  
| Sum.inl a2e => (fun (ab : α × β) => a2e ab.fst)
| Sum.inr b2e => (fun (ab : α × β) => b2e ab.snd)

/-!
### #3: Not Either Implies Not One And Not The Other
Now suppose that you don't have either jam and cheese. 
Then you don't have jam and you don't have cheese. More
generally, if you don't have an α OR a β, then you can
conclude that you don't have an α  Here's a function type that asserts
this fact in a general way. Show it's true in general
by implementing it. An implementation will show that
given *any* types, α and β,  

[[[- Ryland: Done]]]
-/

def demorgan2 {α β : Type} : (α ⊕ β → Empty) → ((α → Empty) × (β → Empty))
| noaorb => (fun a => noaorb (Sum.inl a), fun b => noaorb (Sum.inr b))

-- [EXTRA // Ryland] another way of writing with clear typing:
def demorgan2' {α β : Type} : (α ⊕ β → Empty) → ((α → Empty) × (β → Empty))
| sumab => (fun (a : α) => sumab (Sum.inl a : α ⊕ β), fun (b : β) => sumab (Sum.inr b : α ⊕ β))

/-!
### #4: Not One And Not The Other Implies Not One Or The Other 
Suppose you know that there is no α AND there is no β. Then 
you can deduce that there can be no (α ⊕ β) object. Again
we give you the function type that expresses this idea,
and you must show it's true by implementing the function. 
Hint: You might want to use an explicit match expression
in writing your solution.

[[[- Ryland: Done]]]
-/

def demorgan3 {α β : Type} : ((α → Empty) × (β → Empty)) → ((α ⊕ β) → Empty)  
| (a2e, b2e) => 
  fun aorb => match aorb with
  | Sum.inl a => a2e a
  | Sum.inr b => b2e b

-- [EXTRA // Ryland] another way of writing with clear typing:
def demorgan3' {α β : Type} : ((α → Empty) × (β → Empty)) → ((α ⊕ β) → Empty)  
| (a2e, b2e) => fun (aSb : α ⊕ β) => 
  match (aSb : α ⊕ β) with 
  | Sum.inl (a : α) => a2e a
  | Sum.inr (b : β) => b2e b

/-!
## PART 2

The following problems aim to strengthen your 
understanding of inductive type definitions and
recusrive functions.

[[[- Ryland: Done]]]
-/

-- Here are some named Nat values, for testing
def n0 := Nat.zero
def n1 := Nat.succ n0
def n2 := Nat.succ n1
def n3 := Nat.succ n2
def n4 := Nat.succ n3
def n5 := Nat.succ n4

/-!
### #1. Pattern Matching Enables Destructuring

#1: Defne a function, pred: Nat → Nat, that takes an any
Nat, n, and, if n is zero, returns zero, otherwise analyze
n as (Nat.succ n') and return n'. Yes this question should
be easy. Be sure you understand destructuring and pattern
matching.  

[[[- Ryland: Done]]]
-/

-- Here
def pred: Nat -> Nat
| 0 => 0
| (Nat.succ n') => n'


-- Test cases
#reduce pred 3    -- expect 2
#reduce pred 0    -- expect 0

/-!
### #2. Big Doll from Smaller One n Times

Write a function, *mk_doll : Nat → Doll*, that takes
any natural number argument, *n*, and that returns a doll 
n shells deep. The verify using #reduce that (mk_doll 3)
returns the same doll as *d3*. 

[[[- Ryland: Done, but I added Doll Defintion for Checking!]]]
-/

-- Answer here

-- (Note -> Ryland: I ADDED DOLL DEFINITION TO CHECK)
inductive Doll : Type
| solid
| shell (d : Doll)

open Doll

def mk_doll : Nat → Doll
| 0 => solid
| (Nat.succ n') => shell (mk_doll n')


-- test cases
#check mk_doll 3
#reduce mk_doll 0
#reduce mk_doll 1
#reduce mk_doll 2
#reduce mk_doll 3

/-!
### #3. A Boolean Nat Equality Predicate

Write a function, *nat_eq : Nat → Nat → Bool*, that
takes any two natural numbers and that returns Boolean 
*true* if they're equal, and false otherwise. Finish
off the definition by filling the remaining hole (_). 

[[[- Ryland: DONE]]]
-/

def nat_eq : Nat → Nat → Bool
| 0, 0 => true
| 0, _ + 1 => false
| _ + 1, 0 => false
| (n' + 1), (m' + 1) => nat_eq n' m'

-- a few tests
#eval nat_eq 0 0 -- true
#eval nat_eq 0 1
#eval nat_eq 1 0
#eval nat_eq 1 1 -- true
#eval nat_eq 2 0
#eval nat_eq 2 1
#eval nat_eq 2 2 -- true

/-!
### #4. Natural Number Less Than Or Equal

Write a function, *nat_le : Nat → Nat → Bool*, that
takes any two natural numbers and that returns Boolean 
*true* if the first value is less than or equal to the 
second, and false otherwise. Hint: what are the relevant 
cases? Match to destructure them then return the right
result *in each case*.

[[[- Ryland: DONE]]]
-/

-- Here
def nat_le : Nat → Nat → Bool
| 0, 0 => true -- first equal (true)
| 0, _ + 1 => true -- first less than (true)
| _ + 1, 0 => false -- false otherwise
| (n' + 1), (m' + 1) => nat_le n' m'

-- Ryland Check:
#eval nat_le 0 0 -- true
#eval nat_le 0 1 -- true
#eval nat_le 1 0
#eval nat_le 1 1 -- true
#eval nat_le 2 0
#eval nat_le 2 1
#eval nat_le 2 2 -- true

/-!
###  #5. Nat Number Addition 

Complete this function definition to implement
a natural number addition function. 

[[[- Ryland: Done]]]
 -/

def add : Nat → Nat → Nat
| m, 0 => m
| m, (Nat.succ n') => add (m+1) n'   -- hint: recursion


-- Some test cases
#reduce add 0 0   -- expect 0
#reduce add 5 0   -- expect 5
#reduce add 0 5   -- expect 5
#reduce add 5 4   -- expect 9
#reduce add 4 5   -- expect 9
#reduce add 5 5   -- expect 10


/-!
###  #6. Natural Number Multiplication 

Complete this function definition to implement
a natural number multiplication function. You
can't use Lean's Nat multiplication function.
Your implementation should use productively
the add function you just definied. Wite a few
test cases to show that it appears to be working. 

[[[- Ryland: Done]]]
 -/

def mul : Nat → Nat → Nat
| _, 0 => 0
| m, (Nat.succ n') => add (m) (mul m n')

-- Ex: 5 5 5 5 (m = 5, n = 4)

-- Ryland: Some test cases
#reduce mul 0 0   -- expect 0
#reduce mul 5 0   -- expect 0
#reduce mul 0 5   -- expect 0
#reduce mul 5 4   -- expect 20
#reduce mul 4 5   -- expect 20
#reduce mul 5 5   -- expect 25

/-!
### Sum Binary Nat Function Over Range 0 to n 
Define a function, sum_f, that takes a function,
f : Nat → Nat and a natural number n, and that
returns the sum of all of the values of (f k)
for k ranging from 0 to n. 

Compute expected results by hand for a few
test cases and write the tests using #reduce. 
For example, you might use the squaring function
as an argument, with a nat, n, to obtain the 
sum of the squares of all the numbers from 0
to and including n. 

[[[- Ryland: Done]]]
-/

def sum_f : (Nat → Nat) → Nat → Nat 
| f, 0 => f 0
| f, n' + 1 => add (f (n' + 1)) (sum_f f n')

-- Ryland Checks:
def square : Nat -> Nat
| n => n * n
def add_1 : Nat -> Nat
| n => n + 1

-- Ryland Check:
#eval square 4
#eval sum_f square 2 -- 5
#eval sum_f square 3 -- 14

#eval sum_f add_1 2 -- 6
#eval sum_f add_1 5 -- 21
