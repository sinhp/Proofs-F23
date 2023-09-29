import Mathlib.Tactic

noncomputable section
open Classical
variable {X Y : Type} [Nonempty Y] (f : X → Y) (g : Y → X)

open Set Function

section 
variable (x : X)
#check (invFun g : X → Y)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)
end 




/- An recursive definition of a family of subsets of `X` from the Schroder-Bernstein construction -/
def SBFam : ℕ → Set X
  | 0 => univ \ g '' univ -- X_0 := X \ g(X)
  | n + 1 => g '' (f '' SBFam n) -- X_{n+1} := g(f(X_n))


/- 
The union of the sequence of shaded regions, and define as the union `⋃ n, X_n` of the family of subsets of `X` from the Schroder-Bernstein construction  -/
def SBFam_union :=
  ⋃ n, SBFam f g n

/- The proposed bijection `X → Y` 
we use `f` on the shaded parts, and we use the inverse of `g` everywhere else.
 -/
def SBFun (x : X) : Y :=
  if x ∈ (SBFam_union f g) then f x else invFun g x


/- We need to prove that `SBFun` is a bijection -/

#check invFun_eq

/- First: we prove that `SBFun` is a right inverse of `g` on the complement of `SBFam_union`.  -/
theorem sb_right_inv {x : X} (hx : x ∉ SBFam_union f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [SBFam_union, mem_iUnion]
    use 0
    rw [SBFam, mem_diff]
    constructor 
    · trivial
    · exact hx
  have : ∃ y, g y = x := by
    cases' this with y hy
    use y
    exact hy.right
  exact invFun_eq this
   


/-  
In other words,  The resulting map  is injective because each component is injective and the images of the two components are disjoint.
-/

theorem sb_injective (inj_f : Injective f) (inj_g : Injective g) : Injective (SBFun f g) := 
by
  set A := SBFam_union f g with A_def -- we define A := ⋃ n, X_n
  set h := SBFun f g with h_def -- we define h := SBFun f g
  intro x₁ x₂ 
  intro (hxeq : h x₁ = h x₂) -- we assume that `h(x₁) = h(x₂)` 
  show x₁ = x₂ -- and want to prove that `x₁ = x₂`
  simp only [h_def, SBFun, ← A_def] at hxeq -- we simplify the assumption
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A -- we do a case analysis on `x₁ ∈ A ∨ x₂ ∈ A`
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, SBFam_union, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        rw [hxeq, sb_right_inv f g x₂nA]
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, SBFam_union, mem_iUnion]
      use n + 1
      simp [SBFam]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact inj_f hxeq
  push_neg  at xA
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]





theorem sb_surjective (inj_f : Injective f) (inj_g : Injective g) : Surjective (SBFun f g) := by
  set A := SBFam_union f g with A_def
  set h := SBFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, SBFam_union, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [SBFam] at hn
    simp [SBFam] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, SBFam_union, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, SBFun, if_pos this]
    exact inj_g hx
  use g y
  simp only [h_def, SBFun, if_neg gyA]
  apply leftInverse_invFun inj_g

  