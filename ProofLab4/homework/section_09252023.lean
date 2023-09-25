import ProofLab4


example : ¬P ∨ ¬ (Q ∧ R) ↔  (¬ P ∨ ¬ Q ∨ ¬ R) := 
by 
  sorry 


example : (P ∨ (Q ∧ R)) ↔ (P ∨ Q) ∧ (P ∨ R)  := 
by 
  constructor 
  · intro h₁
    constructor
    · cases h₁ with 
      | inl hp => exact Or.inl hp
      | inr hqr => exact Or.inr hqr.1
    · cases h₁ with 
      | inl hp => exact Or.inl hp 
      | inr hqr => exact Or.inr hqr.2   
  · sorry  


example : (P ∨ (Q ∧ R)) ↔ (P ∨ Q) ∧ (P ∨ R)  := 
by 
  constructor
  · intro h₁
    constructor
    · cases' h₁ with hp hqr 
      · exact Or.inl hp
      · exact Or.inr hqr.1
    · cases' h₁ with hp hqr 
      · exact Or.inl hp 
      · exact Or.inr hqr.2  
  · intro h₂   
    cases' h₂ with hpq hpr   
    cases' hpq with hp hq 
    · exact Or.inl hp
    · cases' hpr with hp hr 
      · apply Or.inl hp
      · apply Or.inr ⟨hq, hr⟩   


example : (P ∨ (Q ∧ R)) ↔ (P ∨ Q) ∧ (P ∨ R)  := 
by 
  constructor 
  · rintro (hp | ⟨hq, hr⟩) <;> constructor
    repeat {apply Or.inl hp} 
    apply Or.inr hq  
    apply Or.inr hr
  · sorry 


example : (P ∨ (Q ∧ R)) ↔ (P ∨ Q) ∧ (P ∨ R)  := 
by 
  tauto 


-- example : False ↔ True := 
-- by 
--  tauto 

example : ¬ ¬ P  ↔  P := 
by 
  tauto 

