/-!
Note: These notes are not yet complete. They
current extend the material presented at the
end of lecture 3, August 29, 2023. This section
will be extended as we go forward.

# Polymorphic functions

Consider the following three functions. 
Each one simply returns the single value 
given as its single argument. We call these 
function *identity functions*, for arguments
of types Nat, String, and Bool respectively.
-/

def id_nat : Nat → Nat
| n => n

def id_string : String → String
| n => n

def id_bool : Bool → Bool
| n => n
/-These^ are identity functions--take vals and return them back-/
/-
## Functions varying in argument types

Each one returns the value of its single 
argument. We call such function *identity
functions*. We thus have identity functions
for arguments of types Nat, String, and Bool,
respectively. Here are example applications.
-/

#eval id_nat 7
#eval id_string "Hello"
#eval id_bool true
/-
Beyond having different names, these
functions *vary* only in the types of
their argument and return values. 

We wouldn't want to have to write one
such function for each of hundreds of
types. We can avoid such repetition by
"factoring out" the varying part of the
definition into a parameter (argument). 
-/

/-!
## Factor out variability into a type parameter

If we bind a name, such as *T* or *α* ,to
a first *type* argument, then we can define
the type of the rest of this function to be
T → T, or α → α. In Lean it's conventional 
to use greek letter names for type values, 
so we will do that from now on.

Let's see how to write a single *polymorphic*
identity function that covers in one definition
an infinitude of identity functions, varying in
the types of their argument and return values. 
Then we'll analyze the definition to understand 
it in detail.
-/

def id_poly : (α : Type) → α → α /-If alpha is Nat (a Type) or Bool or String etc., then the rest of func is also that type. Polymorphic because can take args of diff types.-/
| α, v => v /-in cases where it will match on any arg value, don't need to give it a name--can just replace alpha in this line with an underscore.-/
/-First arg is a type, second arg (second alpha) is a value/argument of that type. "|" is the evaluation rule.-/
/-if alpha = Nat and v = 5, alpha gets bound to Type Nat, v to 5. All that's returned is 5. If it's type Nat but input is not a Nat, then get an error.-/
/-We give a name to the first arg (alpha) so that we can use it later on in the func-/
/-The alpha is already present throughout the func definition, so the rest of the id_poly def line already has alpha matched. Can even take out the alpha after the bar.-/
/-The alpha in the id_poly def line is limited in scope to the def line. The alpha in next line's scope is limited to the pattern matching rule.-/
/-!
Here are the elements of this definition:

- def is the keyword for giving a definition
- id_poly is the name of the function being defined
- (α : Type) binds the name α to the first argument to id_poly: a type value
- the : separates the named arguments from ones as yet not named
- the | is the one and only pattern matching rule for this function
- v matches the second argument *of type α* for whatever value α has
- => separates a pattern on the left from the return value on the righ
- v, bound to the second argument, is the return value of this function 

Now we can see that our single definition provides an identity
function for any type of value.
-/

#eval (id_poly String) "Hello!"
  /- ^ remember that func application is left-associative. Above, the part in () is a function that takes in a String and returns a String (String -> String)-/
#eval (id_poly Nat) 7
/- ^ is a Nat -> Nat. Each of the above parenthesized terms reduces to a func specialized to the type that is given to id_poly.-/
#eval id_poly Bool true /-parametrically polymorphic b/c gets its polymorphism from its parameter/s-/
#eval id_poly Bool 5 /-error message, identifies in Messages that 5 is actually of type Nat and doesn't have way to convert the # to Bool.-/
-- problem here is that in func def, first arg says it will be the Type that α is. Every α afterwards is a value of the Type. Here, 7 is not a value of Bool, so doesn't match up/make sense to Lean.
#eval id_poly Bool false
#eval id_poly Nat 5
#eval id_poly Type Bool /-error because Type is not a Type; it's (a) Type1 while our func was defined w/ input being Type-/
#eval id_poly "Hello" /-Lean knows the type is String, but you have to add String in front of the string b/c we said in the func def that we'd give the type as one of the inputs-/

def id_nat' := id_poly Nat /-SPECIALIZATION: by applying id_poly to Nat, we specialize back so that we have an identity func just for Nat.-/
/-So we had specialized, but then generalized to poly_id func, then specialized again to specific Types.-/
/-!
## Parametric Polymorphism

What we're seeing here is called parametric polymorphism! We have 
one function definition that can take arguments of many different 
types. Here the *type* of it's second argument is given by the type
*value* (such as Bool or Nat or String) of its first argument. 

Lean easily detects type errors in such expressions. For example,
if we pass Bool as the first argument but 7 as the second, Lean 
will report an error. Let's try. 
-/

#check id_poly Bool 7   -- Lean says it can't convert 7 into a Bool

/-!
# Implicit Arguments

You might have noticed that in principle Lean can always infer
the *type value* of the first argument to the id_poly function
from the *data value* passed as the second argument. For example,
if the second argument is "Hello!", the first argument just *has
to be* String. If the second argument is 7, the first has to be 
Nat. If the second is true, the first has to be Bool.

In these cases, you can ask Lean to silently fill in argument
values when it knows what they must be, so that you don't have 
to write them explicitly. To tell Lean you want it to infer the
value of the first *type* argument to id_poly, you specify it as 
an argument when defining the function not using (α : Type) but 
using curly braces instead: {α : Type}. Let's define the function 
again (with the name id_poly') to see this idea in action.
-/

def id_poly'' {α : Type} : α → α   -- α is now an implicit argument!!! 
| v => v
/-APOSTROPHE: seems that it's like a prime in math--just signals an adaptation from the original. Takes og and makes some changes-/
/-IMPLICIT ARGS: means you no longer have to specify the Type before the value of the Type, and in fact you are not allowed to explicitly state the Type. There'll be an error.-/
/-EXCEPTION to above about not explicitly stating: place @ before the func name. "Turns off" the implicit arg--allows Lean to use an explicit arg to help understand. Used when Lean cannot infer what type the term is-/
/-!
Now we can write applications of id_poly' without giving the
first (*type*) argument explicitly. It's there, but we don't
have to write it. Instead, Lean infers what it's value must
be from context: specifically from the type of the value we
pass as the second argument. The resulting code is beautifully
simple and evidently polymorphic. It also eliminates possible
type mismatches between the first and second arguments, as the
type in question is inferred automatically from the value to 
be returned. 
-/

#eval id_poly'' 7
#eval id_poly'' "Hello!"
#eval id_poly'' true

def apply2_nat : (Nat → Nat) → Nat → Nat
| f, a => f (f a)

def double : Nat → Nat
| n => 2*n

#eval apply2_nat double 4     -- expect 16 (2 * (2 * 4))
#eval apply2_nat double 10    -- expect 40 (2 * (2 * 10))

def square : Nat → Nat
| x => x*x

#eval apply2_nat square 5 /-Should give you 625 because look at what's after | in apply2_nat definition: applies f to (f a), or applies square to square of 5.-/

def exclaim : String → String 
| s => s ++ "!"    -- with s bound to first argument value

#check (exclaim "Hello")
#eval exclaim "Hello"
#eval exclaim (exclaim "Hello")

/-What if we want to use apply2 for not just Nat-> Nat funcs? Can make a polymorphic version, factoring out the type so that it can work for diff types-/

/-CODING TYPE INFERENCE ONWARD IN TEACHER DOC IS WHAT HW IS -/