def from_ab_pair_a {α β : Type} : α x β → α --Type is the type of
| (a, _) => a -- This would be the proof.
#check @Prod
def x := (1,2) -- a Prod Nat Nat
#eval x.1 --extract first element
#eval x.2
def  from_ab_proof_a_proof {α β : Prop} : α ∧ β → α --we can now use logical symbols because Prop shifts us to logical world
-- a and b are types that encode propositions. a and b are arbitrary propositions. But propositions are types
-- And.intro needs two args: first being type a, second of type b. More specifically, a is a proposition. We need a value of the a type.
--What you can derive/deduce from a proof si that a proposition is valid/true independent of interpretation (true no matter the interp).
--And.intro is a proof constructor that takes a value/proof of a and a proof of b and constructs a proof of a AND b.
--And.intro constructs larger proof from smaller proofs.

--Prop as a type. "Type of Prop is type. But Prop is its own type universe, so it has its own inhabitants, which are all propositions reprsented as types (e.g., rep'd as Bool/Nat/String...)"
--remember structure is the same as using inductive data type with just one constructor
--Prod is a polymorphic type: notice how its args are two types
--Prod has one constructor, mk. Takes two args, fst and snd

--For And, constructor is .intro. Takes two args, left and right
--Diff b/w Prod and And? Prod lives in Type, and And in Prop

--constructors make values of a given type


--Axioms and Theorems
-- Axiom: proposition that's assumed to be accepted. E.g., And.intro is an axiom. Assuming/given an a and b...
--From axioms, we can derive theorems. Constructors are basically axioms that explain how to build proofs of the given type.
def from_ab_true_a_true {α β : Prop} : α ∧ β → α
| ⟨a, _  ⟩ => a --usual () used for Prod.mk won't work here. do backslash <, backslash > instead

#check Sum

#check Or --Or is defined with inductive, not structure, because has two constructors, Sum.inl and Sum.inr

--Sum vs Or. Sum takes two types and gives back sum of those types. Or takes two propositions and gives back a proposition

def sum_elim {α β γ : Type} : (α ⊕ β) → (α → γ ) → (β → γ) → γ --think that when creating the sum, would have done γ → α or γ → β to achieve α or β (α ⊕ β)
| (Sum.inl a), f, g => f a
| (Sum.inr b), f, g => g b
-- The Lean definitions of Sum and Or using inductive tells constructors and their args, and those constructors are axioms.
#check Or.elim -- if I have a proof a or b, and I am given a way to do proof a to c or a proof of b to c, and I have a proof of a and proof of b, then I can get a c

--theorem keyword is like *def*.
-- Or.elim def: if Or.inl h, retruns left h, which just means running the (left: a → c), meaning c is what's ultimately returned

theorem and_comm {P Q : Prop} : ((P ∧ Q) → (Q ∧ P)) ∧ ((Q ∧ P) → (P ∧ Q)) := -- this is an and proposition
And.intro --just a formatting choice. Two args could be written on same line, but clearer this way.
  (λ ⟨ p, q⟩ => ⟨ q, p⟩ ) -- a func that returns a Q ∧ P given a P ∧ Q
  (λ ⟨ q, p⟩ => ⟨ p, q⟩ ) --to build an And, use a pair. To build an implies, use a function.
