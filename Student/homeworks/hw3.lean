/-!
# Homework #3
## Ryland Birchmeier
## Computing ID: zbp6dw

Near final DRAFT. 

## Overview and Rules

The purpose of this homework is to strengthen your
understanding of function composition and of enumerated
and product data types. 

The collaboration rule for this homework is that
you may *not* collaborate. You can ask friends and
colleagues to help you understand material in the
class notes, but you may not discuss any aspect
of this homework itself with anyone other than one
of the instructors or TAs. Why? Because *you* need
to learn this material to pass the exam to come.
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
#check funkom -- as expected
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
#check mkop
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

/-! 
## Problem #5

Define a data type called *Day*, the values of which
are the names of the seven days of the week: *sunday,
monday,* etc. 

Some days are work days and some days are play
days. Define a data type, *kind*, with two values,
*work* and *play*.       -DONE

Now define a function, *day2kind*, that takes a *day*
as an argument and returns the *kind* of day it is as
a result. Specify *day2kind* so that weekdays (monday
through friday) are *work* days and weekend days are
*play* days.       -DONE

Next, define a data type, *reward*, with two values,
*money* and *health*.       -DONE

Now define a function, *kind2reward*, from *kind* to 
*reward* where *reward work* is *money* and *reward play* 
is *health*.       -DONE

Finally, use your *funkom* function to produce a new
function that takes a day and returns the corresponding
reward. Call it *day2reward*.       -DONE

Include test cases using #reduce to show that the reward
from each weekday is *money* and the reward from a weekend
day is *health*.       -DONE
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

#reduce day2reward saturday   -- health
#reduce day2reward sunday     -- health
#reduce day2reward monday     -- money
#reduce day2reward tuesday    -- money
#reduce day2reward wednesday  -- money
#reduce day2reward thursday   -- money
#reduce day2reward friday     -- money

end DayKind

/-!
## Problem #6

### A. 
Consider the outputs of the following #check commands. 
-/

#check Nat × Nat × Nat
#check Nat × (Nat × Nat)
#check (Nat × Nat) × Nat

/-!
Is × left associative or right associative? Briefly explain
how you reached your answer.

Answer here: "×" is Right Associative. You can tell because
  "#check Nat × Nat × Nat" produces the same output as 
  "#check Nat × (Nat × Nat)" which means that they are treated
  the same in Lean. On the other hand, "#check (Nat × Nat) × Nat"
  produces a different output. From all of this, we know we should
  evalulate the parts of expressions with "×" from right
  to left, therefore - Right Associative.

### B.
Define a function, *triple*, of the following type:
{ α β γ : Type } → α → β → γ → (α × β × γ)  
-/

-- Here:
def triple : { α β γ : Type } → α → β → γ → (α × β × γ)
| _, _, _, a, b, c => (a, b, c)

-- Ryland Check
def finish_triple := triple "one" 2 "three"
#eval finish_triple   -- ("one", 2, "three")
#check finish_triple  -- String × Nat × String

/-!
### C.
Define three functions, call them *first*, *second*, 
and *third*, each of which takes any such triple as
an argument and that returns, respectively, its first,
second, or third elements.
-/

-- Here:
def first { α β γ : Type } : (α × β × γ) -> α
| (α, _, _) => α
def second { α β γ : Type } : (α × β × γ) -> β
| (_, β, _) => β
def third { α β γ : Type } : (α × β × γ) -> γ
| (_, _, γ) => γ

/-!
### D.
Write three test cases using #eval to show that when 
you apply each of these "elimination" functions to a
triple (that you can make up) it returns the correct
element of that triple.  
-/

-- Here:
def testObject := triple 1 "test2" "threeeee"
#eval testObject -- (1, "test2", "threeeee")
#eval first testObject -- 1
#eval second testObject -- test2
#eval third testObject -- threeeee

/-!
### E.
Use #check to check the type of a term. that you make 
up, of type (Nat × String) × Bool. The challenge here
is to write a term of that type. 
-/

#check ((3, "hello"), true) -- (Nat × String) × Bool
-- OR, you can do it this way for fun...
#check Prod.mk (Prod.mk 3 "hello") true -- (Nat × String) × Bool
