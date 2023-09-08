/-!
# Homework #3
## Ryland Birchmeier - Computing ID: zbp6dw

Near final DRAFT. 

The purpose of this homework is to strengthen your
understanding of function composition and of enumerated
and product data types. 
-/

/-!
## Problem #1

Define a function of the following polymorphic type:
{α β γ : Type} → (β → γ) → (α → β) → (α → γ). Call it
*funkom*. After the implicit type arguments it should
take two function arguments and return a function as
a result. 
-/

-- Answer below
def funkom : {α β γ : Type} → (β → γ) → (α → β) → (α → γ)
| _, _, _, g, f => (λ a => g (f a))

-- Ryland Check
#eval funkom (fun a => a%2==0) String.length "sdaf" --true
#eval funkom (fun a => a%2==0) String.length "sdafd" --false

/-! 
## Problem #2

Define a function of the following polymorphic type:
{α β : Type} → (a : α) → (b : β) → α × β. Call it mkop.
-/

-- Answer below
def mkop : {α β : Type} → (a : α) → (b : β) → α × β
| _, _, a, b => (a, b)

-- Ryland Check
def prod_ex_0 := mkop "hello" 3
#check prod_ex_0 -- String × Nat
#eval prod_ex_0 -- ("hello", 3)

/-! 
## Problem #3

Define a function of the following polymorphic type:
{α β : Type} → α × β → α. Call it op_left.
-/

-- Answer below
def op_left : {α β : Type} → α × β → α
| _, _, p => p.fst

-- Ryland Check
#eval op_left prod_ex_0 --hello

/-! 
## Problem #4

Define a function of the following polymorphic type:
{α β : Type} → α × β → β. Call it op_right.
-/

-- Answer below
def op_right : {α β : Type} → α × β → β
| _, _, p => p.snd

-- Ryland Check
#eval op_right prod_ex_0 --3

/-! #5
## Problem #5

Define a data type called *Day*, the values of which
are the names of the seven days of the week: *sunday,
monday, etc. -Done

Some days are work days and some days are play
days. Define a data type, *kind*, with two values,
*work* and *play*. -Done

Now define a function, *day2kind*, that takes a *day*
as an argument and returns the *kind* of day it is as
a result. Specify *day2kind* so that weekdays (monday
through friday) are *work* days and weekend days are
*play* days. -Done

Next, define a data type, *reward*, with two values,
*money* and *health*. -Done

Now define a function, *kind2reward*, from *kind* to 
*reward* where *reward work* is *money* and *reward play* 
is *health*. -Done

Finally, use your *funkom* function to produce a new
function that takes a day and returns the corresponding
reward. Call it *day2reward*. -Done

Include test cases using #reduce to show that the reward
from each weekday is *money* and the reward from a weekend
day is *health*. -Done
-/
namespace DayKind

inductive Day : Type
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

inductive kind : Type
| work
| play

open Day
open kind

def day2kind : Day -> kind
| saturday => play
| sunday => play
| _ => work

inductive reward : Type
| money
| health

open reward

def kind2reward : kind -> reward
| work => money
| play => health

def day2reward : Day -> reward
| d => funkom kind2reward day2kind d

#reduce day2reward saturday
#reduce day2reward sunday
#reduce day2reward monday
#reduce day2reward tuesday
#reduce day2reward wednesday
#reduce day2reward thursday
#reduce day2reward friday

end DayKind

/-!
Problem #6

Consider the outputs of the following #check commands. 
-/

#check Nat × Nat × Nat
#check Nat × (Nat × Nat)
#check (Nat × Nat) × Nat

/-!
Is × left associative or right associative?

Answer here: right associative

Define a function, *triple*, of the following type:
{ α β γ : Type } → α → β → γ → (α × β × γ)  
-/

-- Here:
def triple : { α β γ : Type } → α → β → γ → (α × β × γ)
| _, _, _, a, b, c => (a, b, c)

def finish_triple := triple "one" 2 "three"
#eval finish_triple
#check finish_triple

/-!
Define three functions, call them *first*, *second*, 
and *third*, each of which takes any such triple as
an argument and that returns, respectively, it first,
second, and third elements.
-/

-- Here: 
def first { α β γ : Type } : (α × β × γ) -> α
| (α, _, _) => α
def second { α β γ : Type } : (α × β × γ) -> β
| (_, β, _) => β
def third { α β γ : Type } : (α × β × γ) -> γ
| (_, _, γ) => γ

/-!
Write three test cases using #eval to show that when 
you apply each of these "elimination" functions to a
triple (that you can make up) it returns the correct
element of that triple.  
-/

-- Here:
def testObject := triple 1 "test2" "threeeee"
#eval first testObject
#eval second testObject
#eval third testObject

/-!
Use #check to check the type of a term (that you can
make up) of type (Nat × String) × Bool. 
-/

#check ((3, "hello"), true)
