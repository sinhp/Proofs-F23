/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 
-- import Mathlib.Data.Set

import Mathlib.Tactic


noncomputable section
open Classical 
/-
Schröder-Bernstein theorem: 
If we have injections `f : A → B` and `g : B → A` then `A` and `B` are in bijection which means we have a function `h : A → B` which is a bijective. 

Example: constructing a bijection between the closed interval `[0,1]` and the half-closed interval `[0,1)`.  
-/

open Nat
open Set
open Function 

#check Bijective



theorem cantor_schroeder_bernstein {f : A → B} {g : B → A} : (Injective f) →  (Injective g) → ∃ (h : A → B), Bijective h := 
by 
  -- we want to prove an implication, namely (Injective f) →  (Injective g → ∃ (h : A → B), Bijective h), therefore we introduce a hypothesis stating that `f` is injective. 
  -- Let `f` be an injective function 
  intro inj_f 
  -- Let `g` be an injective function 
  intro inj_g 
  -- Now we want to show that there __exists__ a function `h` which is both injective and surjective. 
  use sorry -- here we provide the function `h`
  sorry -- here we show that `h` is bijective. 

/- Left-closed right-closed interval  `[0,1]` -/
#check (Icc 0 1 : Set ℝ) 

/- Left-closed right-open interval  `[0,1)` -/
#check (Ico 0 1 : Set ℝ) 


/- 
Want to construct a bijection between the closed interval `Icc 0 1` and the half-closed interval `Ico 0 1`. 
-/


section 
#check Icc 0 1 -- `{ a : ℕ  | 0 ≤ a ≤ 1} = {0 ,1}`
variable ( x  : Icc (0 : ℝ) 1 ) -- x : { a : ℝ | 0 ≤ a ≤ 1}
#check x.val 
#check x.prop
end 

/-
Icc 0 1 : Set ℕ -- what is `Set ℕ`?  
-/
#check Icc 0 1
#check (Icc 0 1 : Set ℝ)

section 
example : Ico (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := 
by 
  intro x hx
  dsimp [Icc]
  dsimp [Ico] at hx
  constructor 
  · exact hx.1
  · apply le_of_lt; exact hx.2  


-- x ≤ 1 := x < 1 ∨ x = 1 
end 


#check Ico  -- [0,1)
#check Ioc 
#check Ioo 

#check Icc (0 : ℝ) 1 --  { a : ℝ | 0 ≤ a ≤ 1}
def one_half : Icc (0 : ℝ) 1 where
  val := ((1 : ℝ) / 2)
  property := by 
    simp
    constructor 
    linarith
    norm_num 


def one_half_alt : Icc (0 : ℝ) 1 := ⟨ ((1 : ℝ) / 2), by  
    simp
    constructor 
    linarith
    norm_num ⟩ 



-- F : A → B
def F : Icc (0 : ℝ) 1 → Ico (0 : ℝ) 1 := fun x => ⟨x.val/2, by obtain ⟨val, prop⟩ := x; simp at prop ⊢ ; constructor <;> linarith⟩



/- The function `F` has two parts because we need to provide an output, namely `x/2` and a proof that `x/2` is in `[0,1)`. -/

#check F


@[simp]
lemma inj_F : Injective F := by
  unfold Injective
  -- let `a b` be two arbitrary elements of `[0,1]` such that `F(a) = F(b)`
  intro a b h
  -- we want to show that `a = b`
  simp [F] at h
  -- `a` and `b` are pairs of the form `⟨a.val, a.prop⟩` and `⟨b.val, b.prop⟩` respectively. `a = b` therefore means that `a.val = b.val` and `a.prop = b.prop`.
  ext  
  linarith



#check inj_F

/- instead of `x.val` in the output we can write `x` by coercion-/
-- G : B → A is the embedding of the half-closed interval [0,1) into the closed interval [0,1]
def G : Ico (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x => ⟨x, by obtain ⟨x, hx⟩ := x; simp at hx ⊢ ;  constructor <;> linarith⟩ 



#check G

@[simp]
lemma inj_G : Injective G := by 
  unfold Injective
  intro a b h
  simp [G] at h
  ext 
  linarith


#check inj_G

#check cantor_schroeder_bernstein

-- [0,1] ≅ [0,1) 
example : ∃ h : Icc (0 : ℝ)  1 → Ico (0 : ℝ)  1, Bijective h := 
by  
  apply cantor_schroeder_bernstein (f := F) (g := G) 
  apply inj_F 
  apply inj_G  

  
/-
A __direct proof__ of bijection `[0,1] ≃ [0,1)` without using `schroeder_bernstein`. We want to construct a bijection `H : [0,1] → [0,1)` without recourse to the theorem which we have not proved yet. 
-/
-- the function below is not injective 
def H_bad : Icc 0 1 → Ico 0 1 := fun x => ⟨0, by trivial⟩   

def H_bad_inj : Icc (0 : ℝ) 1 → Ico (0 : ℝ) 1 := F 

example : ¬ Surjective H_bad_inj := 
by 
  simp only [H_bad_inj] 
  unfold Surjective  
  -- ¬∀ ↔ ∃¬     
  push_neg 
  use ⟨(3:ℝ)/4, by sorry⟩
  -- because we are proving a universally-quatified statement we have to fix an arbitrary `a`
  intro a    
  -- suppose that `F a = 3/4` and get `False` 
  intro ha
  have ha' : (0:ℝ) ≤ a ∧ a ≤ (1 :ℝ) := by exact a.prop 
  have ha'' : ((0:ℝ) ≤ F a) ∧ (F a ≤ (1/2 :ℝ)) := by constructor <;> sorry 
  have ha''' : F a ≤ (1/2 : ℝ) := by exact ha''.right
  have : (F a).val = (3/4 : ℝ) := by injection ha
  linarith
  --contradiction

#check Set.insert -- Set.insert 1 {2,3,4} = {1,2,3,4}
#check List.cons -- List.cons 1 [2,3,4] = [1,2,3,4]

example : Set.insert 1 {2} = Set.insert 2 {1} := 
by 
  ext n 
  constructor 
  · intro h -- `h` is a proof of the statement `n =1 ∨ n ∈ {2}`
    cases' h with h₁ h₂
    · right
      exact h₁ 
    · left 
      exact h₂
  · sorry  

example : Set.insert 1 {2} = Set.insert 2 {1} := 
by 
  refine eq_of_subset_of_subset ?_ ?_
  · intro n h -- `h` is a proof of the statement `n =1 ∨ n ∈ {2}`
    cases' h with h₁ h₂
    · right
      exact h₁ 
    · left 
      exact h₂
  · sorry -- exactly the same proof works

example : Set.insert 1 {1} = {1} := 
by 
  exact Iff.mp toFinset_inj rfl  

example : List.cons 1 [2] ≠ List.cons 2 [1] := 
by 
  intro h 
  injection h
  contradiction  

example : List.cons 1 [1] ≠ [1] := 
by 
  intro h 
  injection h
  contradiction 

-- def H : Icc (0 : ℝ) 1 → Ico (0 : ℝ) 1 := sorry 

-- carve out the set `𝕊 = {1,1/2,1/4, ...} : Set Icc (0 : ℝ) 1` of negative powers of 2 from `Icc (0 : ℝ) 1` and define `H` on 𝕊 to be `F`. So, `H '' 𝕊 = {1/2, 1/4, ...} ` and for the rest of the closed interval, i.e. `Icc 0 1 ∖ 𝕊`   we define `H` to be simply the identity function. 


-- 0 ... 1/8 ... 1/4 ... 1/2 ... x ... 1  ↦   1/8 ...  1/4 ... 1/2 ... x : Ico 0 1

-- an inductive family of subsets of `[0,1]`
-- S'0 = {1}, S'1 = {1/2,1}, S'2 = {1/4,1/2,1}, ..., S' n = {1/(2^n), ..., 1}
@[simp]
def S' : ℕ → Set (Icc (0 : ℝ) 1)
| 0 =>  ( { ⟨1, by dsimp [Icc]; constructor <;> simp⟩ } : Set (Icc (0 : ℝ) 1))  -- S' 0 = {1}
| (n+1) => Set.insert ( ⟨(1: ℝ) / (2 ^ (n+1)), by sorry ⟩  ) (S' n) -- S' (n + 1) = {1/2^(n+1)} ∪ S' n

def 𝕊' := ⋃ n, S' n  

#check 𝕊' 

@[simp]
def S : ℕ → Set (Icc (0 : ℝ) 1)
  | 0 => univ \ (G '' univ) -- S_0 := X \ g(X) = {1} -- [0,1] ∖ [0,1)
  | n + 1 => G '' (F '' S n) -- S_{n+1} := g(f(S_n)) = {1/2^(n+1)}

def 𝕊 := ⋃ n, S n   -- 𝕊 = {1,1/2, ... }

/- 
The function `G : Ico (0 : ℝ) 1 → Icc (0 : ℝ) 1` has a partial inverse `invFun G : Icc (0 : ℝ) 1 → Ico (0 : ℝ) 1` which is defined on the image of `G` as an identity map: the inverse `invFun G` takes any element of `Icc (0 : ℝ) 1` which is not equal to `1`  to itself. 

The definition of `invFun` in Lean is very general, uses the non-constructive axiom of choice, and it assumes the domain of the function of which we take the inverse is nonempty. 

The `invFun f` is a left inverse if `f` is injective and a right inverse if `f` is surjective.

-/
instance :  Nonempty (Ico (0: ℝ) 1) := ⟨⟨0, by dsimp [Ico]; constructor; positivity; positivity ⟩⟩

-- Our goal was to define `H : [0,1] → [0,1)` which is injective and bijective
-- `F : [0,1] → [0,1)` takes `x` to `x/2`
-- `G : [0,1) → [0,1]` for every `y : [0,1)`, `G y = y`. So there is a partial inverse for `G`, namely `invFun G : [0,1] → [0,1)`.   
-- `(invFun G) y = y ↔  ∃ x ∈ Ico (0 : ℝ) 1, G x = y ↔ y ∈ Ico (0 : ℝ) 1` 
-- otherwise (i.e. when `y ≠ 1`),  `(invFun G) y` is some arbitrary element of `Ico (0 : ℝ) 1` 
-- if `y ∈ 𝕊` then `H y = y/2`, and otherwise `H y = y` 

def H (y : Icc (0 : ℝ) 1) : Ico (0 : ℝ) 1  :=
  if y ∈ 𝕊 then (F y) else (invFun G y) 

#check Icc

#check univ

#check mem_iUnion
#check iUnion
#check mem_diff


-- in our special case `𝕊ᶜ = [0,1] ∖ {1,1/2, ...}` and `G '' univ = [0,1)`.
lemma fam_union_compl_subset_univ_img  {x : Icc (0 : ℝ) 1} : 𝕊ᶜ ⊆  G '' univ := 
by 
  -- Let x be in the complement of the set `𝕊`. We show that it belongs to the image of function `G`. 
  intro x hxnS   
  contrapose! hxnS 
  -- we simplified the goal from `¬ x ∈ 𝕊ᶜ` to `x ∈ 𝕊`.  
  simp 
  rw [𝕊, mem_iUnion]
  -- observe that `S 0` is the universe (i.e. [0,1]) minus the image of the function `G` 
  use 0 
  rw [S, mem_diff]
  constructor 
  · trivial 
  · assumption   


-- `invFun G : [0,1] → [0,1)`, and by definition, `(invFun G) y = y` if y ≠ 1 and otherwise `(invFun G) y` is some arbitrary element in `[0,1]` 

#check invFun_eq


-- `G (invFun G 1) ≠ 1` 
theorem SBRightInv {x : Icc (0 : ℝ) 1} (hx : x ∉ 𝕊) : G (invFun G x) = x := 
by 
  obtain ⟨y, hy⟩ := fam_union_compl_subset_univ_img (x:= x) hx
  -- all we need to prove is that `x` is in the image of `G` because in that case the lemma `invFun_eq` tells us that  `G (invFun G x) = x`. 
  apply invFun_eq 
  use y 
  exact hy.right 



-- `H : [0,1] → [0,1)`
theorem inj_H : Injective H := 
by 
  -- let `x,y` be arbitrary elements of `[0,1]` such that `Hx = Hy`. 
  intro x y heq
  simp only [H] at heq 
  -- case analysis on x ∈ 𝕊 and y ∈ 𝕊   
  -- strategy: if `x ∈ 𝕊` then `H x = F x` and we shall show that `y ∈ 𝕊` using the assumption `heq : H x = H y`. Therefore, `H y = F y` and hence the equation `H x = H y` simplifies to `F x = F y`, and since `F` is injective we conclude that `x = y`.
  by_cases hxS : x ∈ 𝕊 
  -- proving `x= y` under the positive assumption that `x ∈ 𝕊`
  · have hyS : y ∈ 𝕊 := by 
                          -- using proof by contradiction
                          by_contra hynS 
                          rw [if_pos hxS, if_neg hynS] at heq
                          rw [𝕊, mem_iUnion] at hxS
                          -- from `heq: F x = invFun G y` we conclude that 
                          -- `G (F x) = G (invFun G y)` by applying the -- function `G` to both sides.  
                          have heq' : G (F x) = G (invFun G y) := by congr! 1
                          have heq'' : G (F x) = y := heq'.trans (SBRightInv hynS) 
                          obtain ⟨n, hn⟩ :=  hxS
                          -- So, if x ∈ 𝕊 then that mean x ∈ S n for some n : ℕ, and therefore G F x ∈ S (n+1), and hence G F x ∈ 𝕊 
                          have : G (F x) ∈ 𝕊 := by rw [𝕊, mem_iUnion] ; use (n + 1) ; apply mem_image_of_mem; apply mem_image_of_mem; exact hn
                          rw [heq''] at this
                          contradiction 
    have hFxy : F x = F y := by rw [if_pos hxS, if_pos hyS] at heq ; assumption 
    apply inj_F 
    assumption
  -- proving `x= y` under the negative assumption that `x ∉ 𝕊`   
  -- since x ∉ 𝕊 heq tells us invFun G x = if y ∈ 𝕊 then F y else invFun G y
  · rw [if_neg hxS] at heq 
    by_cases hyS : y ∈ 𝕊
    · rw [if_pos hyS] at heq 
      exfalso 
      --rw [𝕊, mem_iUnion] at hxS
      -- from `heq: F x = invFun G y` we conclude that 
      -- `G (F x) = G (invFun G y)` by applying the -- function `G` to both sides.  
      have heq' : G (invFun G x) = G (F y) := by congr! 1
      -- x = G (invFun G x) and G (invFun G x) = G (F y)
      have heq'' : x = G (F y) := (SBRightInv hxS).symm.trans heq'
      --obtain ⟨n, hn⟩ :=  hxS
      -- because y ∈ 𝕊 then that mean y ∈ S n for some n : ℕ, and therefore G F y ∈ S (n+1). We laos know that `x = G (F y)`. Therefore, x ∈ S (n + 1) and hence ` x ∈ 𝕊 = ∪ n, S n`. This contradicts `hxS`  
      rw [𝕊, mem_iUnion] at hyS 
      obtain ⟨n, hy⟩ := hyS 
      have : G (F y) ∈ 𝕊 := by rw [𝕊, mem_iUnion] ; use (n + 1) ; apply mem_image_of_mem; apply mem_image_of_mem; exact hy 
      rw [← heq''] at this
      contradiction 
    -- when y ∉ 𝕊 
    · sorry 

/- 
@[simp]
def S : ℕ → Set (Icc (0 : ℝ) 1)
  | 0 => univ \ (G '' univ) -- S_0 := X \ g(X) = {1} -- [0,1] ∖ [0,1)
  | n + 1 => G '' (F '' S n) -- S_{n+1} := g(f(S_n)) = {1/2^(n+1)}

def 𝕊 := ⋃ n, S n   -- 𝕊 = {1,1/2, ... }

So, if x ∈ 𝕊 then that mean x ∈ S n for some n : ℕ, and therefore G F x ∈ S (n+1), and hence G F x ∈ 𝕊 

-/ 








