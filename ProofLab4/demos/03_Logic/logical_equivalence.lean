import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Have






example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry  


/-
If the proof is incomplete, the token by is decorated with a red squiggly line, and the error message contains the remaining goals. 
-/


theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro 
    . assumption   
    . assumption 

theorem test'' (p q : Prop) (hp : p) (hq : q) : p ∧ (p ∧ q ∧ p) := by
  apply And.intro hp; exact And.intro hq hp    