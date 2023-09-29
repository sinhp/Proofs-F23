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
    


/-  # Solution to P1.Q2. -/

/- 
The CNF logically equivalent to the formula `(P₁ ∧ P₂) ∨ (Q₁ ∧ Q₂)` is
`(P₁ ∨ Q₁) ∧ (P₁ ∨ Q₂) ∧ (P₂ ∨ Q₁) ∧ (P₂ ∨ Q₂)`. Note that this formula is a CNF since it is a conjunction of `(P₁ ∨ Q₁)`, `(P₁ ∨ Q₂)`, `(P₂ ∨ Q₁)`, and `(P₂ ∨ Q₂)` each of which is a disjunction of literals. The list of literals in the first disjunct is `[P₁, Q₁]` and the list of literals in the second disjunct is `[P₁, Q₂]`. The list of lists of literals that is the CNF is thus `[[P₁, Q₁], [P₁, Q₂], [P₂, Q₁], [P₂, Q₂]]`.
-/ 


example : P ∨ (Q₁ ∧ Q₂) ↔ (P ∨ Q₁) ∧ (P ∨ Q₂) :=
by 
  constructor
  · intro h₁
    cases h₁ with
    | inl h₂ => exact ⟨Or.inl h₂, Or.inl h₂⟩
    | inr h₃ => exact ⟨Or.inr h₃.left, Or.inr h₃.right⟩
  · intro h 
    cases h.left with
    | inl hp => exact Or.inl hp 
    | inr hq => cases h.right with 
                | inl hp' => exact Or.inl hp'
                | inr hq' => exact Or.inr ⟨hq, hq'⟩



example : ((P₁ ∧ P₂) ∨ (Q₁ ∧ Q₂)) ↔ ((P₁ ∨ Q₁) ∧ (P₁ ∨ Q₂) ∧ (P₂ ∨ Q₁) ∧ (P₂ ∨ Q₂)) :=
by 
  constructor
  · intro h₁
    cases h₁ with
    | inl h₂ => exact ⟨Or.inl h₂.left, Or.inl h₂.left, Or.inl h₂.right, Or.inl h₂.right⟩
    | inr h₃ => exact ⟨Or.inr h₃.left, Or.inr h₃.right, Or.inr h₃.left, Or.inr h₃.right⟩  
  · intro h₄
    apply Or.inl 
    constructor
    · sorry
    · sorry 
    
