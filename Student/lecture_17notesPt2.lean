/-!
# Curry-Howard Correspondence
-/

/-!
## Empty ↦ False
-/

/-!
### Empty

You've already met and understood the Empty data type.
-/

#check Empty
/-!
inductive Empty : Type
-/

/-!
As an example, here's another uninhabited type (in Type)
-/
inductive Chaos : Type

/-!
From an assumption that one has a value of type Empty,
anything can follow. We can even promise to return a
value of our new uninhabited type.
-/
def from_empty (e : Empty) : Chaos := nomatch e

/-!
### False

The *logical* analog of the Empty *data* type is the proposition,
False. It is an uninhabited type, but now in Prop. Such a type is
understood as representing a proposition. That there is no proof
of False---no value of this type---means that as a proposition it
is logically false.
-/

#check False
/-!
inductive False : Prop
-/

def from_false {P : Prop} (p : False) : P := False.elim p

def from_false_true_is_false (p : False) : True = False := False.elim p

-- no introduction rule, as there are no proofs of False


/-!
## Unit ↦ True

### Unit
-/

#check Unit
-- inductive PUnit : Sort u where
--  | unit : PUnit

/-!
### True
-/

#check True
/-!
inductive True : Prop where
| intro : True
-/

#check True.intro

-- no elimination rule

def proof_of_true : True := True.intro

/-!
Example
-/
def false_implies_true : False → Chaos :=
   λ f => False.elim f


/-!
## Prod ↦ And

### Prod
-/

#check Prod

/-
structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β
-/

/-!
### And
-/

#check And
/-
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-/

-- Propositions as types, proofs as values
inductive Birds_chirping : Prop
| yep
| boo

-- Propositions as types, proofs as values
inductive Sky_blue : Prop
| yep


#check (And Birds_chirping Sky_blue)
#check (Birds_chirping ∧ Sky_blue)

theorem a_proof : Birds_chirping ∧ Sky_blue :=
  -- And.intro Birds_chirping.yep Sky_blue.yep
  ⟨ Birds_chirping.yep, Sky_blue.yep ⟩  --  notation

/-!
Proof Irrelevance

For the purpose of demonstrating that a given proposition
is true (or, more accurately, valid), any proof will do. All
proofs are equivalent in this dimension. In Prop, all proof
values are considered to be equal. Moreover, choices among
otherwise equivalent proofs aren't allowed to affect rsults
of computations.
-/

namespace cs2120f23

/-!
With values of data types, we care a lot about particular
values. There's a huge difference between *tre* and *false*
as values of the Boolean type,

Indeed, one of the fundamental rules of inductive *data*
type definitions (in Type or above) is that *constructors
are disjoint*. This means that different constructors always
create values that are different: unequal.
-/
inductive Bool : Type
| true
| false


/-!
But because Birds_chirping is in Prop (it's a proposition, right)
all of its values, all values accepted as proofs of the propisition,
are actually considered to be equal. You would understand the details
of the formal proof until we talk about equality, but you can trust
that Lean is accepting that there is a proof that boo and yep really
are *equal*.

-/
theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial




/-!
## Sum ↦ Or

### Sum Data Type
-/

#check Sum

/-
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
-/

/-!
### Or Connective
-/

#check Or
/-
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

-- Two different proofs of the same proposition,
theorem one_or_other  : Or Birds_chirping Sky_blue := Or.inl Birds_chirping.yep
theorem one_or_other' : Or Birds_chirping Sky_blue := Or.inr Sky_blue.yep

/-!
In some cases you'll need to select the disjuct for which you have a proof.
-/
example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep  -- inr is no go
example : (0=1) ∨ (1=2):= _  -- there's no proof of either disjunct


/-!
Example: We state and prove the proposition (in one direction)
that *Or* is commutative. In English, the proposition says that
if we assume that P and Q are arbitrary propositions, then if the
proposition P ∨ Q is true (has a proof, d) then it me be that we
can derive a proof of Q ∨ P. Q ∨ P must also
be true (have a proof). The proof of that is by case analysis
-/
theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ (d : P ∨ Q) =>
  match d with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q


/-!
## Not (no)
-/

/-!
When representing logical operations using computational
types (in Type), we represented negation of a proposition,
α, as a function from α (a Type) to the type, *Empty*. If
there is a value (implementation) of such a function type,
then the type must be uninhabited, which we took as meaning
that there's no proof of it, so it must be false, and the
negation in turn must be true.
-/
def no (α : Type) : Type := α → Empty

/-!
Example. Recall that Chaos is an uninhabited type (in Type)
-/
example : no Chaos := λ c => nomatch c

/-!
We'll now see that the approach is analogous in Prop, the
type Universe for logical reasoning in Lean. If P is any
proposition, then Not P (concrete notation, ¬P) is also a
proposition. It is true when P (the type of proofs of P) is
uninhabited.
-/
#check Not
/-!
def Not (a : Prop) : Prop := a → False
-/

example : no Chaos := λ (c : Chaos) => nomatch c

inductive Raining : Prop

example : ¬Raining := λ (r : Raining) => nomatch r

example: ¬False :=
λ f => False.elim f

example (P: Prop) : ¬(P ∧ ¬P) := -- (P ∧ ¬P) → False. How to prove this? A func
λ pandnotp => (pandnotp.right) (pandnotp.left)
--Lean tells us pandnotp.left is a P, meaning it's a proof of P
-- a proof of not P is a function that is a proof of P → False, and since there's no way to get false, P must be false.
-- We have a proof of P → False, and we have a P. pandnotp.right represents the not P (P → False). If we give a P → False a P (pandnotp.left), then we can get it to return False.

--a proof of P ∧ ¬ P is a pair of proofs

--OR
example (P: Prop) : ¬(P ∧ ¬P) := λ (⟨ p, np ⟩) => np p-- (P ∧ ¬P) → False. How to prove this? A func

example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := --transitivity
fun pq qr => fun p => qr (pq p) --we have a function that takes two args: fun pq qr. Then, what's returned is a function taking a p and returning a P → R.
--we've proven ehre that implication is transitive

example (α β γ : Type) : (α → β ) →  (β → γ ) → (α → γ) :=
λ ab bc => fun a => bc (ab a) --we need to get a b from an a to be able to use β → γ
--These last two are examples of Curry Howard
--basically funciton proposition

example (P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
| Or.inl p => ⟨Or.inl p, Or.inl p⟩
| Or.inr ⟨ q, r ⟩ => ⟨Or.inr q, Or.inr r⟩

example (A B : Prop) : ¬(A ∧ B) → ¬A ∨ ¬B
| nab => Or.inl (⟨na,⟩)
| nab => _

example (A B : Prop) : ¬A ∨ ¬B →  ¬(A ∧ B)
| Or.inl nota => λ ⟨ a, b ⟩ => nota a --you just need the part nota a takes up to be False to show that A and B (rep'd as ⟨a, b⟩) returns False. This is the same as not (A and B).
| Or.inr notb => λ ⟨ a, b ⟩ => notb b

example : X ∨ ¬X := _
--^Law of the Excluded Middle: just the axiom that every proposition is either true or not true. But there are some propositions for which we don't know is true.
--We don't know if there is a SAT solver with computaiton time faster than exponential time. We don't have proof that there isn't something better though (or something)
--the "p = np" problem: is polynomial time the turning complete something? Can you prove...
--but LEM isn't always true in Lean because we can't always get the pieces we need to prove (?)

axiom em: ∀ (P : Prop), P ∨ ¬P --excluded middle. The *axiom* keyword tells Lean to just assume what we give it in the def to be true.


example : X ∨ ¬X := em X --when em applied to X, gives us the proposition X ∨ ¬ X. The X ∨ ¬ X comes before the :=, meaning the usual "what follows the := is how you reach my statement"
