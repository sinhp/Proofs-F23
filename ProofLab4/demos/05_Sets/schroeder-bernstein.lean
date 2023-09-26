/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 
-- import Mathlib.Data.Set

noncomputable section
open Classical 
/-
Schröder-Bernstein theorem: 
If we have injections `f : A → B` and `g : B →A` then `A` and `B` are in bijection which means we have a function `h : A → B` which is a bijective. 

Example: constructing a bijection between the closed interval `[0,1]` and the half-closed interval `[0,1)`. 

If we want to teach Lean about the Schröder-Bernstein theorem we need Lean to understand the following stuff: 

1. Injectivity of functions. 
2. Bijectivity of functions. 
2.1. The left and right inverses of a function

3. To construct `h` we need the notion of image "functor" of a function. 

4. Sets and their union 


For the example 
5. intervals of real numbers. 
-/
open Set
open Function 

#check Bijective



theorem schroeder_bernstein {f : A → B} {g : B → A} : (Injective f) →  (Injective g → ∃ (h : A → B), Bijective h) := 
by 
  -- we want to prove an implication, namely (Injective f) →  (Injective g → ∃ (h : A → B), Bijective h), therefore we introduce a hypothesis stating that `f` is injective. 
  -- Let `f` be an injective function 
  intro inj_f 
  -- Let `g` be an injective function 
  intro inj_g 
  -- Now we want to show that there __exists__ a function `h` which is both injective and surjective. 
  use sorry 
  sorry 

/- Left-closed right-closed interval  [0,1] -/
#check (Icc 0 1 : Set ℝ) 

/- Left-closed right-open interval  [0,1) -/
#check (Ico 0 1 : Set ℝ) 


/- 
Want to construct a bijection between the closed interval `Icc 0 1` and the half-closed interval `Ico 0 1`. 
-/


section 
variable ( x  : Icc (0 : ℝ) 1 ) -- x : { a : ℝ | 0 ≤ a ≤ 1}
#check x.val 
#check x.prop
end 

#check Ico  -- [0,1)
#check Ioc 
#check Ioo 

def F : Icc (0 : ℝ) 1 → Ico (0 : ℝ) 1 := fun x =>
  ⟨x.val/2, by
    obtain ⟨x, hx⟩ := x; simp at hx ⊢; constructor <;> linarith⟩

#check F

@[simp]
lemma inj_F : Injective F := by
  sorry

#check inj_F

/- instead of `x.val` in the output we can write `x` by coercion-/

def G : Ico (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x => ⟨x, by obtain ⟨x, hx⟩ := x; simp at hx ⊢ ;  constructor <;> linarith ⟩  

#check G

@[simp]
lemma inj_G : Injective G := by 
  sorry

#check inj_G

#check schroeder_bernstein


example : ∃ h : Icc (0 : ℝ)  1 → Ico (0 : ℝ)  1, Bijective h := 
by  
  apply schroeder_bernstein (f := F) (g := G) 
  apply inj_F 
  apply inj_G  

  
/-
A direct proof of bijection `[0,1] ≃ [0,1)` without using `schroeder_bernstein`  
-/


#check Set.insert

@[simp]
def Neg_pow_of_two : ℕ → Set ℝ 
| 0 => ( { 0 } : Set ℝ)
| (n+1) => Set.insert ((1:ℝ) / (2 ^ (n+1))) (Neg_pow_of_two n)

#check Neg_pow_of_two 5


-- example : Neg_pow_of_two 4 = {0, 1/2, 1/4, 1/16} := 
-- by 
--   simp
--   apply?


--example : 




def h : Icc 0 1 → Ico 0 1 := 
sorry 
--fun x => {
--   val := _
--   property := _
-- }



/- An recursive definition of a family of subsets of `X` from the Schroder-Bernstein construction -/
def SBFam {f : X → Y} {g : Y → X} : ℕ → Set X
  | 0 => univ \ g '' univ -- X_0 := X \ g(X)
  | n + 1 => g '' (f '' SBFam n) -- X_{n+1} := g(f(X_n))












