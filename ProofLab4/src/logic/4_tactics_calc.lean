
/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Mathlib.Data.Real.Basic


/-!
# Logic of Propositions: Tactics for Algebraic Identities 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2023   
-/


/-! ### Tactic `calc` 
One of the earliest kind of proofs one encounters in mathematics is proof by calculation. This usually involves a chaing of equalities using lemmas expressing properties of operations on numbers and other structures.  `calc` (short for calculation) is the tactic for this kind of proofs.

- Using `calc`, in order to prove our goal (`x + 1 = w + 1`) we introduce several __subgoals__ each of which needs a separate proof. The subgoals in the example below are 

1. `x + 1 = y + 1` this is true since `x = y` by virtue of `h₁`. 
2. `y + 1 = z + 2` is true and the proof is `h₂`.
3. `z = w ` is true and the proof is `h₃`.

Then the tactic `calc` takes advanatge of the transitivity of equality to bind all these proofs togehter and prove that `x + 1 = w + 2`. 

See [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html?highlight=calc#calculational-proofs) for the general syntax of `calc`. 
-/

example (x y z w : ℝ) (h₁ : x = y) (h₂ : y + 1 = z + 2) (h₃ : z = w) : x + 1 = w + 2 :=
calc 
  x + 1 = y + 1 := by rw [h₁] -- `x + 1 = y + 1` is the first subgoal. `by` converts tactics to terms which we need to supply as the justification for the subgoal. 
  _    = z + 2 := by exact h₂ -- the second subgoal is that `y + 1 = z + 2` 
  _    = w + 2 := by rw [h₃] -- the third subgoal is that `z + 2 = w + 2` 



/-! ### Tactic `ring` 
Tactic for solving equations in the language of commutative (semi)rings, that is whenever we have two binary operations of addition `+` and multiplication `*` which furthermore satisfy the followin axioms:
-/

section 
--#check add_assoc  -- associativity of addition
--#check mul_assoc -- asssociativity of multiplication
--#check add_comm -- commutativity of addition 
--#check mul_comm -- commutativity of multiplication 

--#check mul_add -- distributivity of multiplication over addition
--#check add_mul -- distributivity of addition over multiplication

--#check add_zero -- zero for addition 
--#check mul_one -- one for right multiplication 
--#check one_mul -- one for left 
--#check sub_self -- inverse for addition 
end 


-- Difference of two squares
example (a b : ℝ) : 
  (a + b) * (a - b) = a^2 - b^2 :=
by 
  ring

lemma binomial₂ (a b : ℝ) : (a + b)^2 = a^2 + 2 * (a * b) + b^2 :=
by 
  ring

lemma binomial₃ (a b : ℝ) : 
  (a + b)^3 = a^3 + 3 * a^2 * b + 3 * a * b^2 + b^3 :=
by 
  ring

lemma sum_of_cubes (a b : ℝ) :
  a^3 + b^3 = (a + b)^3 - 3 * a * b * (a + b) :=
by 
  ring

lemma sum_cubes_fac (a b : ℝ) :
a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := 
by 
  ring

lemma diff_of_cube (a b : ℝ) : 
  a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := 
by 
  ring  


/- Let `a` and `b` be rational numbers and suppose that `a - b = 4` and `a * b = 1`. Show that `(a + b) ^ 2 = 20`. -/
example {a b : ℚ} (h₁ : a - b = 4) (h₂ : a * b = 1) : (a + b) ^ 2 = 20 :=
calc
    (a + b)^2 = (a - b)^2 + 4 * (a * b) := by ring
    _ = 4^2 + 4 * 1 := by rw [h₁, h₂]
    _ = 20 := by rfl




