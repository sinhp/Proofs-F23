import ProofLab4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real 


/-
# Solutions to Problem 1 
-/

/-
1. The sum of two-thirds and three-fifths as a rational number
-/
#check (2/3 : ℚ) + 3/5 




/-
# Solutions to Problem 2 
-/

/-
1. `2 + 3 * 4 = 2 + (3 * 4)`
-/

#check 2 + 3 * 4
#check 2 + (3 * 4)

/- We conjecture that the two expressions above are the same, i.e. the multiplication operation has a higher binding priority than the addition operation. We can prove this by using the `rfl` tactic, which stands for reflexivity. It proves that two expressions are equal if they can be reduced/evalued to the same canonical form (in this case 14). -/   

example : 2 + 3 * 4 = 2 + (3 * 4) := 
by 
  rfl



/-
# Solutions to Problem 3
-/

def my_term₁ : List (Unit ⊕ ℕ) := [Sum.inr 1, Sum.inl ()]
