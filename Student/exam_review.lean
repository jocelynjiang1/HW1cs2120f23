--Factorial example
def fact: Nat → Nat
| 0 => 1 --Imagine his floor-building machine in a 10 story building: can't build 10th floor till you've built  9th, can't build 9th until 8th built, ...and only able to build after 0th laid.
| (n+1) => (n+1)*(fact n)

#eval fact 5 -- 5! is 5 * factorial of 4, or 5* (4*3*2*1*1)
#eval fact 3
-- Key to recursion: assume you have answer to next step down. You can access that answer by calling the function itself
-- n is really n - 1 here, (n+1) is n. Only written as n+1 because of Lean


def list_len {α : Type}: List α → Nat
| [] => 0 --always have a base case for recursion
| h::t => 1 + list_len t -- remember to assume you have answer to next step down, assume you can have a value list_len t already.

#eval list_len ["Hi", "here's", "an", "example"] --returns 4!

-- A sum of cubes function:
def sum_of_cubes: List Nat → Nat
| [] => 0 --here, our base case is 0, but if we'd done product,
| h::t => h^3 + (sum_of_cubes t)

#eval sum_of_cubes [1,2,3] -- returns 1^3 + 2^3 + 3^3 = 36!

-- Our made-up function
def add_fact: Nat → Nat
| 0 => 0
| n+1 => (n+1) + add_fact n

-- Function checking if list has any trues, returning true if there's a true
-- if you get a problem related to particular values of list elements, think case analysis
def check_trues_or: List Bool → Bool
| [] => false -- there can't be any trues if the list is empty!
| h::t => or h (check_trues_or t)
-- for base case: think about case analysis. If b is or'd with a: if b is true and a is true, then result is true. If b is false and a is false, then result is false. In either case, outpout is the same as b (something like that?)
#eval check_trues_or [false, true, false]

def check_trues_and: List Bool → Bool
| [] => true --Understand how to determine this base case!
| h::t => and h (check_trues_and t)
 -- for base case: think about case analysis. If

#eval check_trues_and [true, true,true,true,true,false]

def is_even: Nat → Bool
| 0 => true
| 1 => false
| n + 2 => is_even n

#eval is_even 10

/- Imagine if 2 were passed in as the Nat. That means 2 = (n+2), 
which would return is_even 0 (true). That's correct! But if it were 
n+1 => is_even n, would return is_even 1, which would say is_even 2 is false, 
which is incorrect. Can figure this out be testing or think 
if you do n+1 => is_even n, you'd be checking the evenness of the number
1 smaller than what you gave, so with usual n+1, will always be exact opposite
return value that it should be. Do n+2 to account for every other number
always being even to "skip" over the opposing evenness value of n+1
while still satisfying Lean.-/

-- destructure incoming arguments to make it clear you've got a structure to do structural recursion
-- My attempt: | n+1 => (n%2=0)



-- variable expression captures a variable, and variable has an index (var.mk 0, for ex). Underlying vars have indices 0-...
-- variable is a type (one constructor, "just a box with a Natural number in it") whereas variable expression encapsulates a variable ("like a box with a variable in it")


 -- Syntax: how can you construct the proposition in well-formed logic?
 -- what constitutes an expression in prop logic?
 /-To make a larger proposition, can combine two smaller props with an operand
 For prop logic, use the ⇒ rather than =>, the function def one. Just use it that way-/

 -- Semantics:


-- How do you show a type is uninhabited? If there exists a function α → empty. Because if α is true, then it would be True → False, which can't be, meaning α must be false/empty as well.
-- So show α is uninhabited by showing there can be a func α → empty
def reduce_or: List Bool → Bool
| [] => false -- 
| h::t => or h (reduce_or t)

def is_sat: Expr → Bool := λ e: Expr => reduce_or (truth_table_outputs e) -- just not working because need to copy and paste funcs from lecture_13
-- our lambda expression is a function that takes an expression

-- remember that ¬(X ∧ Y) ⇔ (¬X ∨ ¬Y). Biimplication because these two are equivalent and remember it's DeMorgan's *laws*
-- "inhabited types as a proxy for true, uninhabited types as a proxy for false"

/- # To study 
  - Go through all the notes quickly
  - Make up your own functions and create test cases for them
  - Look at homework keys
  - Extend logic we have for implies, iff to xor, for example (practice this)
  - satisfiability/read-ahead doc
-/
