/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Real.Basic


/-! ## __Bonus Tactics__ -/


/-! ### Tactic `symmetry` -/ 
section
variable (x y z : ℕ) (h : x + y = z) 
#check eq_tsub_of_add_eq h
end 

example (m n k : ℕ) (h : m = n + k) : m - k = n :=
by
  symm 
  apply eq_tsub_of_add_eq h.symm



/-! ### Tactic `have`

`have` is a good tactic to use, if you want to add a new intermediate subgoal which, after proving it, can be used later as a new assumption in the (updated) context. 

There are two styles of using the tactic `have`.

- The term-style: 
` have hp : P, from ...  `


- The tactic-style: 
` have hp : P, by {tactic_1 ..., tactic_2 ...,  tactic_n ... } `

In the first style, we are introducing a new assumption `hp` (a proof of proposition `P`) from another proof (`...`) that we know how to construct.   
-/



example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
by
  intro h₁ -- we want to prove an implication, hence we use the implication introduction rule. 
  -- We now have `0 = 1` as our assumption. Using it we need to prove that `0 = n`.  
  have h₂ : 0 * n = 1 * n := by rw [h₁] -- We use the tactic `have` to create the intermediate subgoal `0 * n = 1 * n`, and we give a proof of it by rewriting `h₁`. 
  have h₃ : 0 = 0 * n := by rw [zero_mul] -- we add a new assumption that `0 = 0 * n` using the lemma `zero_lemma`.  
  have h₄ : n = 1 * n := by rw [one_mul] -- we add a new assumption that `n = 1 * n` using the lemma `zero_lemma`.
  rw [h₃.trans h₂] -- By the transitivity of equality `h₂: 0 * n = 1 * n` and `h₃ : 0 = 0 * n` imply that `0 = 1 * n`. We use this fact to simplify the goal to `n = 1 * n`
  exact h₄.symm




