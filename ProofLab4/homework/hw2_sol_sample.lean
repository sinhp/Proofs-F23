import ProofLab4



/-
# Sample Solutions to HW2
-/


/-
## Solutions to Problem 1 
-/

/-
1. Define a sequence `a` of natural numbers where `a n = n^2`.
-/
def a (n : ℕ) : ℕ := n^2




/-
## Solutions to Problem 2 
-/

/-
1. A function `F₁` which takes a sequence of real numbers and returns the first term of the sequence. 
For instance if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₁ a` is `0`.
-/

def F₁ (a : ℕ → ℝ) : ℝ := a 0




