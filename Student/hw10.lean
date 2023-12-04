/-
Homework: Due Tuesday before class: Formalize the following logical arguments. Hint: use the variable command to introduce assumed types and such, as we did in class. Use #check to express the informal propositions that follow in the formal logic of Lean.

1. Every dog likes some cat.

2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.

3. If any cat, c, likes any cat, d, then d also likes c.

4. Every cat, c, likes itself.

5. If every cat likes every other cat, and c and d are cats, then c likes d.

Finally, give a formal proof in Lean of the proposition in problem #5.
-/
--for any = for every

-- #1
variable
  (Dog : Type)
  (Cat : Type)
  (Likes1 : Cat → Dog → Prop)
  (Likes2 : Dog → Dog → Prop)
  (Likes3 : Cat → Cat → Prop)
#check ∀ (d: Dog), ∃ (c: Cat), Likes1 c d

-- #2
#check ∀ (d g w: Dog), Likes2 d g ∧ Likes2 g w → Likes2 d w --for all just introduces variables we can refer to
--or
#check ∀ (d g w: Dog), Likes2 d g → Likes2 g w → Likes2 d w
--these are

-- a proof:
-- in lecture notes
-- pf in notes has 5 args: 3 are the dogs and 2 are the proofs/assumptions/givens taht d likes g and g likes w.

-- #3
#check ∀ (c d: Cat), Likes3 c d → Likes3 d c -- a symmetric relation

-- #4
#check ∀ (c: Cat), Likes3 c c -- reflexive relation: every cat is related to itself
-- (e.g. equality in math: every number is related to itself.
-- Btw, equality is reflexive, symmetric, and transitive: and when a relation is all three of those,
-- said to be "an equivalence relation")

-- #5
#check ∀ (c d: Cat), Likes3 c d

example: (∀ (cat1: Cat), ∀ (cat2: Cat), Likes3 cat1 cat2) → (c: Cat) → (d: Cat) → Likes3 c d
| a, w => fun (d: Cat) => a w d -- w and d are subbed in for cat1 and cat2
