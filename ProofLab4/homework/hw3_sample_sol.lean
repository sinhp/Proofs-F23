import ProofLab4



/-
# Sample Solutions to HW3
-/


/-
## Solution to Problem 1 
-/


/-
The CNF logically equivalent to the formula `P → (Q ∧ R)` is
`(¬P ∨ Q) ∧ (¬P ∨ R)`. Note that this formula is a CNF since it is a conjunction of `(¬P ∨ Q)` and `(¬P ∨ R)` each of which is a disjunction of literals. The list of literals in the first disjunct is `[¬P, Q]` and the list of literals in the second disjunct is `[¬P, R]`. The list of lists of literals that is the CNF is thus `[[¬P, Q], [¬P, R]]`.
-/


example : (P → (Q ∧ R)) ↔ ((¬P ∨ Q) ∧ (¬P ∨ R)) := 
by 
  -- To prove a logical equivalence (i.e. an iff statement), we prove each direction
  constructor
  -- The first subgoal is to prove the left-to-right direction, that is the implication `(P → (Q ∧ R)) →  ((¬P ∨ Q) ∧ (¬P ∨ R))`
  · intro h₁ 
    -- To prove the conjunction `(¬P ∨ Q) ∧ (¬P ∨ R)` we need to prove each conjunct separately
    constructor
    -- The first subgoal is to prove the left conjunct `(¬P ∨ Q)`
    · by_cases h₂₁ : P
      · have h₃ : Q ∧ R := h₁ h₂₁
        exact Or.inr h₃.left
      · exact Or.inl h₂₁
    · by_cases h₂₂ : P
      · have h₄ : Q ∧ R := h₁ h₂₂
        exact Or.inr h₄.right
      · exact Or.inl h₂₂
  · intro ⟨h₅ , h₆⟩  
    intro h₇
    constructor
    · cases h₅ with
      | inl h₅₁ => exfalso; contradiction
      | inr h₅₂ => assumption
    · cases h₆ with
      | inl h₆₁ => exfalso; contradiction
      | inr h₆₂ => assumption  
    

