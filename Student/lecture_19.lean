/-!
# Quantifiers

Quantifiers are part of the syntax of predicate logic. They allow one
to assert that every object (∀) of some type has some property, or that
there exists (∃) (there is) at least one object of a given type with a
specified property. The syntax of such propositions is as follows:

- ∀ (x : T), P x -- every x of type T has type P
-- ^ takes something of type T that returns a proposition that may or may not be true
-- ^ is only true iff each and every x indeed has propoerty P.
-- for any value of type T, there is a proof of P x. I.e. every object of type T makes P x true.
-- How do you show this? A function to show ∀. input is value of type T, returns proof of P x ***

- ∃ (x : T), P x -- P is a predicate that takes x of type T. "There exists an x of type t that makes proposition *P x* true"

-- a zero-argument predicate: a proposition
-- a zero-argument function in other langs is a constant (?)

## Universal Quantification

The first proposition can be read as asserting that every value *x* of
type *T* satisfies predicate *P*. Another way to say this is that for
every *x* there is a proof of the proposition, *P x*. Another way to
say that is that there's a function that when given any *x* returns a
proof of *P x*. Indeed, that's how we prove such a proposition: show
that if given any *x* you can produce and return a proof of *P x*.
-/


-- "∀ is like a generalized and"
  -- universal quantification is a potentially infinitely ... something

-- *** CONTINUED:
example : ∀ (n: ℕ), True := fun n => True.intro -- function that takes any natural number and returns True
-- this proves every/any natural number has the property True
-- ∀ (n: ℕ), True means given any Nat, will return True
-- Curry Howard Correspondence coming in:
#check ∀ (n: Nat), True -- to prove a for all (∀), just write funciton that takes values of the type and return True

/- proof of a forall proposition is really just proof that for any arbitrarily selected element of the quantified type,
there's proof of the predicate applied to that object.

To use a forall, just do function application: apply the function to a type that the function can accept.

Universal generalization: everything of some type has some property. If you give this generalization
(aka forall function) a type, then you are doing universal specialization: specializing/applying to
a value of the type based on universal generalization-/

-- ∃ is given by \ exist
example : ∃ (n: Nat), True := ⟨3,  True.intro⟩-- there exists an n that satsifies the predicate, which is that it's a nat
-- in the pair on right side of :=, we have a pair: 3 and a proof of True, which could be about the value 3.
-- a dependent pair: type of the second value depends on the first value. In this case, True.intro happens to be True no matter what (that's what True.intro is), but that's what a dependent pair would be

example : ∃ (n: Nat), n%2 = 0 := ⟨ 4, rfl⟩ -- rfl is reflexive that proves (?) equality
-- n%2 = 0 is a predicate, n is argument
-- 4 is a "witness", and example that you know will make proposition true, and rfl is proof that it's true
-- Curry Howard gives us bridge from computational thinking to logical thinking






def zornz'' (n : Nat) : n = 0 ∨ n ≠ 0 :=
match n with
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

def zornz' : (n : Nat) →  n = 0 ∨ n ≠ 0
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

def zornz : ∀ (n : Nat),  n = 0 ∨ n ≠ 0
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

def ex_mis : ∀ (P : Prop), P ∨ ¬P
| _ => _    -- no can do


/-!
### ∃ (there exists)
-/

def sl5 : ∃ (s : String), s.length = 5 := ⟨"Hello", rfl ⟩
