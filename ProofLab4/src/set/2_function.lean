import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic


open Set

section

variable {X Y : Type}
variable {f : X → Y}
variable (A B : Set X)
variable (C D : Set Y)

open Function
open Set

namespace Function

def im (f : X → Y) (U : Set X) : Set Y := {f a | a ∈ U}
#check f.im 

end Function


#check f.im 




/- f ⁻¹'  : Set Y → Set X  -/
example : f ⁻¹' (C ∩ D) = f ⁻¹' C ∩ f ⁻¹' D := by
  ext
  rfl


/- f⁻¹' : Set Y → Set X-/
lemma preimage_functoriality (hi : C ⊆ D) : f ⁻¹' C ⊆ f ⁻¹' D := 
by
  intro x hx
  exact hi hx  


#check preimage_functoriality

#check preimage_mono -- From Mathlib






/- f '' : Set X → Set Y  -/
lemma image_functoriality (hi : A ⊆ B) : f '' A ⊆ f '' B := 
by
  rintro y ⟨x, hx, rfl⟩ 
  use x, hi hx   

#check  image_subset

example : f '' (A ∪ B) = f '' A ∪ f '' B := by
  ext y; constructor
  · rintro ⟨x, xa | xb, rfl⟩
    · left
      use x, xa
    right
    use x, xb
  rintro (⟨x, xa, rfl⟩ | ⟨x, xb, rfl⟩)
  · use x, Or.inl xa
  · use x, Or.inr xb

#check image_union


/- unit -/
lemma image_preimage : A ⊆ f ⁻¹' (f '' A) := by
  intro x xa
  show f x ∈ f '' A
  use x, xa

/- counit -/
lemma preimage_image : f '' (f⁻¹' C)  ⊆ C := 
by
  rintro y ⟨x, hxa, rfl⟩ 
  exact hxa


lemma image_preimage_equiv {X Y : Type} {f : X → Y} {A : Set X} {C : Set Y} : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C := 
by
  constructor
  · intro hi; have this := preimage_mono (f := f) (s := f '' A) (t := C) hi ; apply Subset.trans (image_preimage A) this
  · intro hi; have this := image_subset  (a := A) (b := f⁻¹' C) (f := f) hi ; apply Subset.trans this (preimage_image C)



example {X Y : Type} {f : X → Y} {A : Set X} {C : Set Y} : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C  := 
by 
  constructor 
  · intro h; exact Subset.trans (image_preimage A) (preimage_mono (f := f) (s := f '' A) (t := C) h)  
  · intro h 
    apply Subset.trans (image_subset f h)
    apply preimage_image 




example (inj : Injective f) : f ⁻¹' (f '' A) = A := 
by
  apply Subset.antisymm
  · rintro x ⟨a, ha, hax⟩; have this : a = x := inj hax ; rwa [this] at ha
  · apply image_preimage



example (h : Surjective f) : C = f '' (f ⁻¹' C) := 
by
  apply Subset.antisymm
  · intro y hy
    cases' h y with x hx
    use x
    constructor
    · rw [←hx] at hy; exact hy 
    · assumption
  · apply preimage_image


example : f ⁻¹' (C ∪ D) = f ⁻¹' C ∪ f ⁻¹' D := 
by
  apply Subset.antisymm
  · intro x hx 
    have h₁ : { x } ⊆   f ⁻¹' (C ∪ D) := by intro t ht; rw [ht]; assumption   
    -- rw [mem_singleton_iff] at ht; rw [ht]; assumption   
    have h₂ : f '' { x } ⊆ C ∪ D :=  image_preimage_equiv.mpr h₁
    have h₃ : f x ∈ C ∪ D := by rw [image_singleton] at h₂; rw [  singleton_subset_iff] at h₂; exact h₂
    cases' h₃ with h₄ h₅
    · left; assumption 
    · right; assumption   
  · rw [← image_preimage_equiv, image_union] 
    apply union_subset 
    · suffices f '' (f ⁻¹' C) ⊆ C from Subset.trans this (subset_union_left C D)
      apply preimage_image
    · suffices f '' (f ⁻¹' D) ⊆ D from Subset.trans this (subset_union_right C D)
      apply preimage_image


/- Sometimes it is easier to not use the lemmas: -/  

example : f ⁻¹' (C ∪ D) = f ⁻¹' C ∪ f ⁻¹' D := 
by 
  ext 
  constructor 
  · intro h 
    cases' h with h₁ h₂ 
    · left 
      assumption 
    · right 
      assumption 
  · intro h 
    cases' h with h₁ h₂
    · left 
      assumption         
    · right 
      assumption 

 
#check preimage_union -- Mathlib 

example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := 
by
  sorry

#check image_inter


example (h : Injective f) : f '' A ∩ f '' B = f '' (A ∩ B) := by
  sorry




example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type _} (S : I → Set X) (T : I → Set Y)

example : (f '' ⋃ i, S i) = ⋃ i, f '' S i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
    exact ⟨xAi, fxeq⟩
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩


example : (f '' ⋂ i, S i) ⊆ ⋂ i, f '' S i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩


example (i : I) (injf : Injective f) : (⋂ i, f '' S i) ⊆ f '' ⋂ i, S i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, _, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, T i) = ⋃ i, f ⁻¹' T i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, T i) = ⋂ i, f ⁻¹' T i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x => x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x => x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type _} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β =>
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]; dsimp; rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type _}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end




/- maybe wwant to say if we have an equivalance `f : X ≃ Y`  then we can take the inverse image of f.invFun  -/

#check Subset.antisymm


lemma inv_image_of_inv{f : X ≃ Y } {A : Set X} : f.invFun⁻¹' A = f.toFun '' A := 
by 
  apply Subset.antisymm
  intro x hx 
  calc 
  x   = f.toFun '' f.invFun ⁻¹' x := left_inv 
  sorry  


