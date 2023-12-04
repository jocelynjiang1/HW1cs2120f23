/-!
# Homework #3

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
def funkom {α β γ : Type}: (β → γ) →  (α → β) → (α → γ)
|g, f => (fun a => g (f a))

/-! 
## Problem #2

Define a function of the following polymorphic type:
{α β : Type} → (a : α) → (b : β) → α × β. Call it mkop.
-/

-- Answer below
def mkop {α β: Type} : (a : α) → (b : β) → α × β
| g, f => Prod.mk g f -- could also do outfix notation, or replace Prod.mk g f with (a,b), which is shorthand for same thing.


/-! 
## Problem #3

Define a function of the following polymorphic type:
{α β : Type} → α × β → α. Call it op_left.
-/

-- Answer below
def op_left {α β : Type}: (α × β) → α
| Prod.mk g f => g
-- should be α, β, p => Prod.fst(p), where p matches to alpha cross beta and reps the pair. You take first elementout of the product
-- p is of type Prod alpha beta, an ordered pair.


/-! 
## Problem #4

Define a function of the following polymorphic type:
{α β : Type} → α × β → β. Call it op_right.
-/

-- Answer below
def op_right {α β : Type}: (α × β) → β 
| Prod.mk g f => f

-- alternative pattern matching again: α, β, p => match p with | (a, b) => b
/-! 
## Problem #5

Define a data type called *Day*, the values of which
are the names of the seven days of the week: *sunday,
monday,* etc. 

Some days are work days and some days are play
days. Define a data type, *kind*, with two values,
*work* and *play*.

Now define a function, *day2kind*, that takes a *day*
as an argument and returns the *kind* of day it is as
a result. Specify *day2kind* so that weekdays (monday
through friday) are *work* days and weekend days are
*play* days.

Next, define a data type, *reward*, with two values,
*money* and *health*.

Now define a function, *kind2reward*, from *kind* to 
*reward* where *reward work* is *money* and *reward play* 
is *health*.

Finally, use your *funkom* function to produce a new
function that takes a day and returns the corresponding
reward. Call it *day2reward*.

Include test cases using #reduce to show that the reward
from each weekday is *money* and the reward from a weekend
day is *health*.
-/
inductive Day: Type
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

inductive kind: Type
| work
| play

open Day

open kind

def day2kind: Day → kind
| sunday => play
| monday => work
| tuesday => work
| wednesday => work
| thursday => work
| friday => work
| saturday => play
-- after defining weekends, could have represented all work days with _ => work, where _ reps all values other than Saturday or Sunday

inductive reward: Type
| money
| health

open reward

def kind2reward: kind → reward
| work => money
| play => health

def day2reward:= funkom kind2reward day2kind -- remember you'd read this in the same order as g(f(x))

#reduce day2reward monday
#reduce day2reward tuesday
#reduce day2reward wednesday
#reduce day2reward thursday
#reduce day2reward friday
#reduce day2reward saturday
#reduce day2reward sunday

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

Answer here: The x is right associative; the first and second cases have the same Type Nat x Nat x Nat, even when the second case includes ().
However, the third case is also of Type Type, but it is not equivalent to Nat x Nat x Nat (and its parentheses are associated with the left).

### B.
Define a function, *triple*, of the following type:
{ α β γ : Type } → α → β → γ → (α × β × γ)  
-/

-- Here:
def triple { α β γ : Type }: α → β → γ → (α × β × γ)
|g,f,a => (Prod.mk g (Prod.mk f a)) --  part after the => could also be written as (g, (f, a))
/-!
### C.
Define three functions, call them *first*, *second*, 
and *third*, each of which takes any such triple as
an argument and that returns, respectively, its first,
second, or third elements.
-/

-- Here:
def first {α β γ: Type}: (α × β × γ) → α
| (Prod.mk a (Prod.mk _ _))  => a -- or match t to the product, and do t => Prod.fst(Prod.snd), where you take out middle by taking out first element of second element of outside pair

def second {α β γ: Type}: (α × β × γ) → β 
| (Prod.mk _ (Prod.mk b _))  => b

def third {α β γ: Type}: (α × β × γ) → γ 
| (Prod.mk _ (Prod.mk _ c))  => c
/-!
### D.
Write three test cases using #eval to show that when 
you apply each of these "elimination" functions to a
triple (that you can make up) it returns the correct
element of that triple.  
-/

-- Here:
#eval first ("Hi", 5, true) -- returns first element
#eval second ("Second one", "missing my dog", 200001) -- returns second, "missing my dog"
#eval third (true, 56713, false) -- returns false
/-!
### E.
Use #check to check the type of a term. that you make 
up, of type (Nat × String) × Bool. The challenge here
is to write a term of that type. 
-/
--Not the same as Nat x String x Bool because right associative, and here () are on left.

def tripleExample := ((19, "Does this work?"), true)
#check tripleExample -- Type does show to be Nat x String x Bool




