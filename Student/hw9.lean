axiom em (P : Prop): P ∨ ¬ P --for em A and em B below

-- HOMEWORK: Complete this proof.

example (A B : Prop) : ¬(A ∧ B) -> ¬A ∨ ¬B :=
λ nab => --nab: ¬(A and B) is same as A and B → False. False elim is "rule" saying if you get a proof of false, then you're done/contradiction proved
let proof_of_aornota := em A --propositional logic doesn't have law of em by default, so we have to define this
let proof_of_bornotb := em B
match proof_of_aornota with
| Or.inl a => match proof_of_bornotb with
  | Or.inl b  =>  False.elim (nab (And.intro (a) (b)))--like saying given an (A ∧ B), apply nab to (A ∧ B) to "prove false". False.elim on this to finish contradiction.
  | Or.inr notb => Or.inr notb --do Or.inr notb since if you have a notb, then not a or not b must be true --notb is really a function (b → False)
| Or.inr na => match proof_of_bornotb with
  | Or.inl b => Or.inl na
  | Or.inr notb => Or.inr notb
