/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic


/- 
Towards our goal to the proof of Cantor-Schröder-Bernstein theorem, we need to understand the basic notions of image and inverse-image of sets under functions.

Please refer to the src file for many more examples.
[ProofLab4/src/set/2_function.lean]
-/

open Nat
open Set 
open Function




section 
universe u
variable {A B : Type u} {f : A → B}
variable {S T : Set A}
variable {S' T' : Set B}
#check {f a | a ∈ S} -- the image of set `S` under `f`
#check f '' S -- the image f(S)
end 


/- 
## Image of a function  
-/

def image (f : A → B) (S : Set A) := {f a | a ∈ S} 



#check ext 

example : {1} = setOf Odd ∩ {n | n ≤ 2} := 
by 
  ext n 
  constructor 
  · intro h
    rw [mem_singleton_iff] at h
    rw [mem_inter_iff]
    rw [h]
    constructor 
    · use 0; rfl 
    · dsimp; norm_num 
  -- the more difficult direction   
  · intro h 
    rw [mem_inter_iff] at h
    obtain ⟨d, hd⟩ := h.1 
    have hn : n ≤ 2 := h.2 
    have d_le_one : d ≤ 1 := by linarith
    simp 
    have d_not_one : d ≠ 1 := by intro h; rw [h] at hd; linarith
    have d_zero : d = 0 := by linarith
    rw [d_zero] at hd
    assumption

 
-- f '' S = { y : B | ∃ x : A, x ∈ S ∧ f x = y }
-- f a ∈ f '' S ↔ ∃ x : A, x ∈ S ∧ f x = f a
example (f : A → B) {a : A} {S : Set A} (h : a ∈ S) : f a ∈ f '' S :=
by 
  exact ⟨a, h, rfl⟩


example (f : A → B) {a : A} {S : Set A} (h : a ∈ S) : f a ∈ f '' S :=
by 
  use a, h 


#check mem_image_of_mem


example (f : A → B) (S T : Set A) : 
S ⊆ T → f ''  S ⊆ f ''  T := 
by 
  intro h 
  intro y hy 
  obtain ⟨x, hx₁, hx₂⟩ := hy
  use x
  exact ⟨h hx₁, hx₂⟩  

#check image_subset 



example (f : A → B) : f '' (S ∪ T) = f '' (S) ∪ f '' (T) := 
by 
  ext b -- this is the principle of extensionality of sets   
  constructor 
  · intro h -- let `b` be in the image of the union `S ∪ T`, that is there exists some `a` in `S ∪ T` such that `f a = b`. 
    cases' h with a hab 
    cases' hab.left with haS haT -- either `a ∈ S` or `a ∈ T` 
    · left
      simp 
      use a 
      exact ⟨haS, hab.right⟩ 
    · right 
      simp 
      use a 
      constructor
      exact haT 
      exact hab.right    
  · sorry 


example : f '' (A ∪ B) = f '' A ∪ f '' B := by
  ext y; constructor
  · rintro ⟨x, xa | xb, rfl⟩  -- this combines `intro` and two `cases' ` tactics. 
    · left
      use x, xa
    right
    use x, xb
  rintro (⟨x, xa, rfl⟩ | ⟨x, xb, rfl⟩)
  · use x, Or.inl xa
  · use x, Or.inr xb


#check image_union


/- 
## Inverse image 
For a function `f : A → B` then the inverse image `f⁻¹' : Set B → Set A`.   
-/


#check (setOf Even : Set ℕ)

def inv_image (f : A → B) : Set B → Set A := fun T => { a : A | f a ∈ T } -- we assign to every subset `T` of `B` the subset of elements of `A` whose image land in `T`. 


example (f : A → B) (a : A) (T : Set B) : a ∈ f⁻¹' T ↔ f a ∈ T := 
by 
  rfl 


#check Nat.succ 
#check (Nat.succ)⁻¹'  (setOf Even : Set ℕ) -- this is the set of odd numbers. 


#check Nat.succ.inj
-- #check succ x = succ y → x = y 

#check sub_add_cancel
#check mul_add
#check mul_sub


example (m : ℕ) (h : 0 < m + m) : 0 < m := 
by 
  linarith


example (m : ℕ) (h : 0 < m) : ∃ d : ℕ, m = d + 1 :=
by 
  exact exists_eq_add_of_le' h


example : (Nat.succ)⁻¹'  (setOf Even : Set ℕ)  = setOf Odd := 
by 
  ext x 
  constructor 
  · intro h -- this is the proof that `x` is in the inverse image of even numbers under the successor function. By the definition of the inverse image, this means that `succ x` is an even number. 
    simp at h
    cases' h with m hm 
    simp [Odd]
    use (m-1)
    have hm' : x = (m + m) - 1 := by exact eq_tsub_of_add_eq hm
    have : 0 < m := by linarith             
    rw [hm']
    symm 
    obtain ⟨d, hd⟩ := exists_eq_add_of_le' this
    rw [hd]
    -- ring does not work here 
    simp 
    ring
  · intro h 
    dsimp at *
    cases' h with m hm
    simp [Even] at hm
    use m + 1
    simp [hm]
    rw [Nat.succ_add]; apply congrArg succ; rw [← add_assoc, two_mul]


example (f : A → B) {S T : Set B} (h : S ⊆ T) : f ⁻¹' S ⊆ f ⁻¹' T := 
by 
  intro x hx 
  exact h hx



#check preimage_mono 



/- unit -/
example : A ⊆ f ⁻¹' (f '' A) := by
  intro x xa
  show f x ∈ f '' A
  use x, xa

#check subset_preimage_image


/- counit -/
example : f '' (f⁻¹' C)  ⊆ C := 
by
  rintro y ⟨x, hxa, rfl⟩ 
  exact hxa


#check image_preimage_subset



#check preimage_mono
#check image_subset 


/- write a compositional proof by using the lemmas above. -/
example {X Y : Type} {f : X → Y} {A : Set X} {C : Set Y} : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C  := 
by 
  constructor 
  · intro h; exact Subset.trans (subset_preimage_image f A) (preimage_mono h)  
  · intro h 
    apply Subset.trans (image_subset f h)
    apply image_preimage_subset


example {X Y : Type} {f : X → Y} {A : Set X} {C : Set Y} : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C  := 
by 
  constructor 
  · intro h; exact (subset_preimage_image f A).trans (preimage_mono h)  
  · intro h 
    apply Subset.trans (image_subset f h)
    apply image_preimage_subset


example {X Y : Type} {f : X → Y} {A : Set X} {C : Set Y} : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C  := 
by 
  constructor 
  · intro h a ha
    apply (preimage_mono (f := f) (s := f '' A) (t := C))
    exact h
    apply subset_preimage_image f A
    assumption 
  · intro h 
    apply Subset.trans (image_subset f h)
    apply image_preimage_subset




#check image_subset_iff
