#check Empty
-- inductive Empty: Type
def from_empty (e: Empty) : Nat := 7 --takes a val of type empty, which doesn't exist, and returns a Nat

inductive Chaos: Type
def from_empty_2 (e: Empty) : Chaos := nomatch e--we do computing in Type, we do logic in prop
#check False -- type is Prop (note capital F)
-- no values, or no proofs.
-- values of a Prop can be thought of as proofs. No proofs for False. That's why False's def is just inductive False: Prop.
-- an empty type in Prop. Can we create a proof of False? no.
def from_false {P: Prop} (p: False) : P := False.elim p--Assumes a proposition of False is given. p is a value of the type False, aka p is a proof object of type False.
-- we return a value of type P (a proof of P). If we're given a proof of False, can we turn it into any proposition? P?
-- False.elim gives Prop analog of nomatch in Type

def from_false_true_is_false (p: False) : True = False := False.elim p
--we have a proof of False somehow. how do we get a proof of anything?
-- "from false anything follows"
-- we've now proved something untrue (True = False), but we've done it by making some assumption or something like that
-- you can prove something false if you're given/assume something false(?)

/-logical proposition True is analog of Unit
Unit ==> True
-/
#check Unit -- has one value, intro.
-- Proof of True: True.intro
-- what can you do with a proof of True?

#check True
-- inductive True: Prop where
--  | intro : True

-- what the type of proof of True?
def proof_of_true : True := True.intro --this is the one proof of True

def false_implies_true : False → True := λ f => False.elim f
--if I have a proof of False, I can turn it into a proof of True. That's correct/true because anything follows from True.
-- lambda func takes a little f of type False and returns a

 -- Remember Prod corresponds to And

#check Prod -- a polymorphic type
#check And -- reprersented as a data type is polymorph, takes two propositions. Takes two args like prod but takes two Props, not two Types. Then returns a Prop, not a Type
-- create a value of type And using And's constructors
-- structure means we're introducing a type def
-- And followed by two other types yields a proposition, where those two types themselves need to be propositions. Build a bigger proposiiton from two small ones (think that way)
--structure has default mk constructor. But can also make yoru own.
--Constructor for And: And.intro.

inductive Birds_chirping: Prop
| yep
| boo
--Birds_chirping.yep is a proof. Birds_chirping is a Prop with two proofs
inductive Sky_blue: Prop
| yep
#check (And Birds_chirping Sky_blue)

-- Let's prove with theorem:
theorem both_and : And Birds_chirping Sky_blue := And.intro Birds_chirping.boo Sky_blue.yep --we'll need a proof of Birds_chirping and one of Sky_blue
--We have two proofs of Birds_chirping lying around, so great! Should be able to choose yep or boo (doesn't matter that we chose boo over yep because either could be used since both prove the same theorem)
-- to prove an And, we need a proof of both pieces
-- Right now, all we care about is whether a Prop can be proven by a proof. We don't care which proof is more efficient, easier to get, etc. So either constructor (boo/yep) would work

/- Proof Irrelevance --why we use a separate type universe-/

namespace cs2120f23
inductive Bool : Type
| true
| false --true does not equal false here. We do care about

theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial --just trust the by trivial. Uses some procedure to generate a proof, knows our prop birds...boo = prop...yep is true.yep
-- "We don't want proof values to influence computed vlaues in Type."
-- In Prop, all proofs are equivalent
-- Choice of values in Prop can't influence computations

/-Sum ==> Or-/ -- A proof of just one will be enough

#check Sum -- polymorph in the types it can take
#check Or --polymorphic in the propositions

theorem one_or_other: Or Birds_chirping Sky_blue := Or.inl Birds_chirping.yep -- or you could do Or.inr Sky_blue.yep

example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep--example is like theorem expect don't need to give a name
-- this works because (0=1) is always false, and we have a proof of Birds_chirping (that one's true)

theorem one_or_other_2: Or Birds_chirping Sky_blue := Or.inr Sky_blue.yep
example: (0=1) ∨ (1=2) := _

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ d =>
  match d with
  | Or.inl p => Or.inr p--little p is a proof of P
  | Or.inr q => Or.inl q

--turning a proof of antecedent into proof of
--existence of func implementation here is a proof of the principle

--How could we represent Not?
/- Not (no) ...we defined Not this way before-/
def no {α : Type} := α → Empty
#check Not
-- Not P is defined to be P → False (P implies False)

open Chaos

example : no Chaos := λ (c: Chaos) => nomatch c --this is within Type (we prove no chaos this way)

inductive Raining: Prop
example: ¬ Raining := λ (r: Raining) => nomatch r --not raining means Raining implies false (r → false). so we write a function that assumes it's given a proposition saying that it is raining and returns false to show it's a contradiction
-- nomatch r works because Raining is 
