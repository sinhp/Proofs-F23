/- 
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

import ProofLab4

open Nat
open Function
open Real

section parsing
variable (P : Prop) (A B : X → Prop) (x : X)
#check (∀ x, A x) → P
#check ∀ x, (A x → P)
#check ∀ x, A x → P
--The last two are synonymous.

#check ∀ x, A x → B x
--#check (∀ x, A x) → B -- this is wrong because the implication is only between propositions, and `B` is a predicate. 
#check (∀ x, A x) → B x

#check ∃ x, (A x → P)
#check ∃ x, A x → P
--The last two are synonymous.

#check ∃ z, A z → B z
-- #check (∃ z, A z) → B z

--General rule: anything after "∃ x" or "∀ x" can use "x", unless the scope of ∃ or ∀ is restricted by parentheses.


example: (∀ x, A x → B x) → (∀ x, A x) → (∀ x, B x) := 
by 
  intros hab ha x 
  apply hab x
  exact ha x 

end parsing

theorem a : ℕ := 1 




#check Even 1 -- the proposition "1 is an even number"
#check Even 2 -- the proposition "2 is an even number "
#check Even 1000 -- the  proposition "1000 is an even number", and so on. 

#check (Even : ℕ → Prop) -- The predicate of evenness on natural numbers. 

#check Even 2






/- if we fix types `A` and `B` then __injectivity__ is a predicate on the type of functions `A → B`.   -/
def is_injective (f : A → B) :=  
∀ (x y : A), (x ≠ y) → (f x ≠ f y) 
-- a proposition saying `f` is injective:  all distinct elements in `A` are mapped to distinct elements in `B`. In other words, injective functions preserve distinctions.  

section 
variable (x y : A) (f : A → B)
#check ∀ (x y : A), (x ≠ y) → (f x ≠ f y) 
end --section 

/- 
Our formulation of injectivity uses the implication `(x ≠ y) → (f x ≠ f y) ` which is the __contrapositive__ of Mathlib's `f x = f y → x = y`.   
-/

#check Injective







/- ∀ -/

/- 
A function f : A → B is __injective__ (also called __one-to-one__) whenever the following sentence holds.
  ` ∀ a, b : A,  f(a) = f(b) → a = b `
An injective function is said to be an __injection__.
-/

@[simp] 
def is_inj {X Y : Type u} (f : X → Y) :=
∀ ⦃a b⦄, f a = f b → a = b

-- what is @[simp]?
-- what is {}?
-- what is ⦃ ⦄?

section injection 

#check Injective 
#reduce Injective 
#print Injective

variable (f : X → Y)

#check Injective f
#reduce Injective f 

end injection -- end section 



/- 
We can make the variables `a b : X` implicit by putting it between curly brackets `{` `}` instead of the usual round ones (for explicit argument).  The advanatage of implicit arguments is that in application/elimination they are supposed to be left out and inferred by other means, such as later arguments and hypotheses. 
-/

lemma injection_respect_distinction {X Y : Type} {f : X → Y} (inj : Injective f) : 
  ∀ ⦃a b⦄, (a ≠ b)  → (f a ≠ f b) := 
by 
  sorry 



/- Let's prove that the __identity__ function is __injective__ -/ 

lemma inj_id : Injective (id : X → X) :=
by 
  unfold Injective
  intros a b -- Let `a` and `b` be arbitrary elements of `X` (by the introduction rule of for all)
  intro h -- introduce a proof of `id a = id b` by the introduction rule of elimination
  exact h --`id a` is definitionally identical to `a`, so `h : id a = id b` is identical to the goal `a = b`

#check Nat.noConfusion

#check succ
#check pred 

lemma inj_succ : Injective succ := 
by 
  sorry 
  




example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  unfold Injective
  push_neg -- a non-constructive tactic 
  use -1, 1
  constructor
  · linarith
  · linarith




-- **Injections are closed under composition**, that is the composite of injective functions is injective. Here is a forward proof.
lemma inj_comp {X Y Z : Type} (f : X → Y) (g : Y → Z) (inj_f : Injective f) (inj_g : Injective g): 
  Injective (g ∘ f) := 
by 
  sorry 

/-
In below we prove that 

-/

section 
variable (a b : ℝ) (h : a - b = 0)
#check sub_eq_zero.mp h
#check mul_eq_zero
end 




/- 
In below we prove the following:

"The function which cubes a real number is injective."

__Proof sketch__: 
To prove the injectivity we have to show that given arbitrary real numbers `a b : ℝ` if their cubes are equal then they are the themselves equal, i.e. we must prove the implication `a^3 = b^3 → a = b`.  A main observation in the proof below is that `a ^ 3 - b ^ 3` factors as `(a - b) * (a ^ 2 + ab + b ^ 2)`, i.e.
` a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + ab + b ^ 2) `. 
From this we conclude that either `(a - b) = 0` which immediately implies that `a = b` or that `(a ^ 2 + ab + b ^ 2) = 0`. In the second case, we argue by cases: either `a = 0` or `0 < a`. In the first case, we conclude `b = 0` since `0 = (a ^ 2 + ab + b ^ 2) = b ^ 2 `. In the latter case, we notice that  `0 = 2 * (a^2 + a * b + b^2) = a^2 + (a + b)^2 + b^2 > 0` since `a^2 >0` and `(a + b)^2 + b^2` is non-negative. But this is clearly false from which we can conclude anything including that `a = b`.
-/

lemma inj_cube : Injective (fun (x:ℝ) ↦ x ^ 3) := 
by
  intro a b h
  dsimp at h
  have : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0
  · calc (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by ring
      _ = b ^ 3 - b ^ 3 := by rw [h]
      _ = 0 := by ring
  rw [_root_.mul_eq_zero] at this
  obtain h₁ | h₂ := this
  · linarith -- case 1: a - b = 0
  · -- case 2: a^2 + a * b + b^2  = 0
    by_cases ha : a = 0 -- case 2a: a = 0
    · have hb : b = 0 
      · apply pow_eq_zero (n := 3); rw [← h, ha]; ring
      rw [ha, hb]   
    · have := -- case 2b: x1 ≠ 0
      calc 0 < a^2 + ((a + b) ^ 2 + b ^ 2) := by sorry
          _ = 2 * (a^2 + a * b + b^2) := by ring
          _ = 2 * 0 := by rw [h₂]
          _ = 0 := by ring
      linarith -- contradiction!



/-
Note that the proof above is nonconstructive; can you give a constructive proof instead? 
-/


lemma pow_nine_comp_pow_three : 
(fun (x:ℝ) => x^9) = (fun (x:ℝ) => x ^ 3) ∘ (fun (x:ℝ) => x ^ 3) := 
by 
  funext x; dsimp; ring


example : Injective (fun (x:ℝ) ↦ x ^ 9) := 
by 
  rw [pow_nine_comp_pow_three]
  apply inj_comp; repeat {apply inj_cube}




/- __∃ (exists)__  -/

-- Let's prove `nonzero_of_succ` with `linarith`

lemma nonzero_of_succ (x : ℕ) : 
  (∃ y : ℕ, y + 1 = x) → (x ≠ 0) :=
by 
  intro h₁
  intro h₂
  cases' h₁ with y hy
  rw [h₂] at hy
  apply Nat.noConfusion hy
  

/- `Odd : ℕ → Prop` is a predicate  -/
example (n : ℤ) : Odd n = ∃ k : ℤ, n = 2 * k + 1 := 
by 
  rfl 




/- ∃ elim -/
example (n : ℤ) (hn : Odd n) : Odd (n^2) :=
by 
  simp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  sorry 


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := 
by
  sorry 

example (n : ℤ) : Even (n ^ 2 + 3 * n + 4) := 
by
  sorry 




example (a b : ℤ) (h : ∃ x, 2 * a ≤ x ∨ x ≤ 2 * b) : a ≤ b := 
by
  sorry 









