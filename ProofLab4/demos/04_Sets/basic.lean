/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 
-- import Mathlib.Data.Set

noncomputable section
open Classical 

open Set 

set_option push_neg.use_distrib true

-- attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
-- attribute [-simp] Set.setOf_eq_eq_singleton


/- `Set X := X → Prop` 
A function `f : X → Prop` is a predicate on `X`.  
-/

#check (Even : ℕ → Prop)



/-
A __set__ `S` in `X` is just a predicate `S : X → Prop`. You should think of `S` as a collection of all elements `x : X` satisfying the property `S`, that is all those `x` for which `S x` is true.  Following this line of thinking we might like to notate `S` using the __set-builder__ notation 
`S = { x : X ∣ S x}`
-/ 

#check (Even : Set ℕ)  -- The subset of even natural numbers.  `Set ℕ` means the the type of all subsets of natural numbers, and `Even` is one such subset.  

/-
Since sets are defined as predicates, to prove things about sets is very similar to proofs about predictaes. 
-/




section
variable (A B : Set ℕ)

#check A ⊆ B -- For every `n : ℕ` if `n` is in `A` then `n` is in `B`. To say that `n` is in `A` is the same things as `A n` is true. For example if `n` is in the subset `Even` then `Even n` is true.  `Even = {n | Even n}`. 
-- Therefore the statement that every `n : ℕ` if `n` is in `A` then `n` is in `B` translates into the following: 
-- `∀ n : ℕ, A n → B n` 

/- Let's define all natual numbers which are divisible by four. First we define it as a predicate -/
def Div_by_four (n : ℕ) := 4 ∣ n -- ∃ k, n = 4 * k  

#check (Div_by_four : Set ℕ) -- this works because `Set ℕ := ℕ → Prop`, and `Div_by_four :  ℕ → Prop`

#check setOf --def setOf (P : X → Prop) : Set X := P -- this function turns any predicate `P` on `X` to the set of elements in `X` which satisfy `P`. 

example : (setOf Div_by_four) ⊆ (setOf Even) := 
by 
  -- let `n` be an arbitrary natual number
  intro n 
   -- it simplifies the membership of setOf
  dsimp
  -- suppose that `n` is divisble by four
  intro h 
  -- break down `h` into two parts: a number `k` and a proof that `n = 4 * k`
  obtain ⟨k, hk⟩ := h 
  -- use `hk` to prove `Even n` 
  have : n = 2 * (2 * k) := by rw [hk]; rw [← mul_assoc]
  unfold Even  
  -- we prove the existentially quanitified goal by providing a number `r` which has the property that `n = r + r` 
  use (2 * k)
  rwa [← two_mul] -- rewrites `2*k + 2*k` in the RHS of the goal by `2* (2*k)`

end -- section


/- Special subsets-/


-- singleton set
#check Set.singleton -- singleton (a : X) : Set X := {x | x = a}
#check ({0} : Set ℕ)  
#check setOf_eq_eq_singleton -- proves {x : X | x = a} = {a}
#check mem_singleton_iff -- a ∈ {b} ↔ a = b

-- the empty set
#check (∅ : Set ℕ)  -- empty : Set X := {x | false}
#check Set.univ -- the universal subset of `X` is the set of all elements of `X`, i.e. `univ : Set X := {x | true}`
#check subset_univ 


example : ∀ (n : ℕ), n ∈ (∅ : Set ℕ) → False :=
by 
  intro x hx 
  exact hx 

example : ∀ (n : ℕ), n ∈ (univ : Set ℕ) := 
by 
  intro 
  trivial


example (x : ℤ) : x ∉ (∅ : Set ℤ)  := 
by 
  intro h 
  exact h

example [Nonempty X] : ∃ (S : Set X), (∅ : Set X) ≠ S :=
by 
  obtain ⟨x⟩ := ‹Nonempty X›
  use {x}
  intro h 
  have : x ∈ {x} := by rw [mem_singleton_iff] 
  rw [← h] at this
  exact this

example [Nonempty X] : ∅ ≠ (univ : Set X) :=
by 
  sorry

  
example (P : Prop) : P → { x : Unit | P} = univ := 
by 
  intro h 
  ext x
  constructor 
  · intro ; trivial
  · intro ; dsimp; exact h 



/- Operations on sets -/

section 
variable (A B : Set ℕ)
#check Set.union -- union (A B : Set X) : Set X := {x | x ∈ A ∨ x ∈ B}
#check Set.inter -- inter (A B : Set X) : Set X := {x | x ∈ A ∧ x ∈ B}
#check Set.diff -- diff (A B : Set X) : Set X := {a ∈ A | a ∉ B}

#check A \ B -- this is the same as `Set.diff A B`

#check Set.compl -- compl (S : Set X) : Set X := {x | x ∉ S} 

#check Aᶜ -- this is the same as `Set.compl A`, namely all the natural numbers which are not in `A`.
end --section 

example (h : A ⊆ B) : ∀ (C : Set ℕ),  C ∩ A ⊆ C ∩ B := 
by  
  intro C -- C is a set of natural numbers. 
  intro x 
  -- simplify the goal by unfolding the definition of intersection 
  rw [mem_inter_iff, mem_inter_iff] 
  intro ⟨hxC, hxA⟩ 
  constructor 
  · exact hxC
  · apply h 
    exact hxA


example (A B C : Set X) : A ∩ B ∪ A ∩ C ⊆  A ∩ (B ∪ C) := 
by
  apply union_subset 
  · apply subset_inter
    · apply inter_subset_left
    · apply Subset.trans (inter_subset_right A B) (subset_union_left B C)
  · apply subset_inter
    apply inter_subset_left
    apply Subset.trans (inter_subset_right A C) (subset_union_right B C)


/- More advanced example -/
example (A B C : Set X) : (A \ B) \ C ⊆ A \ (B ∪ C) := 
by 
  intro x
  simp only [mem_diff, mem_union, not_or, and_imp]
  -- Use LHS's of implications when simplifying RHS's
  simp (config := {contextual := true}) 


/- Two sets are equal if they have the same elements. This is known as the principle of extensionality. The tactic `ext` is used to prove equalities of sets. -/
example (A B : Set ℕ) : A ∪ B = B ∪ A := 
by 
  -- We prove for every `x : ℕ`, `x ∈ A ∪ B ↔ x ∈ B ∪ A`.
  ext x
  rw [mem_union, mem_union, or_comm]


example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := 
by
  obtain (h₁ | h₂) := le_or_lt t 0
  · right
    dsimp; linarith
  · left
    dsimp; linarith


#reduce ({2, 3} : Set ℕ)

example : ({-2, 3} : Set ℚ)  = {-2} ∪ {3} := 
by 
  rfl


example : {-1, 0} ∪ {0, 1} = ({-1, 0, 1} : Set ℤ) := 
by 
  -- `rfl` does not work here because the sets are not definitionally equal.
  dsimp
  ext n 
  constructor
  · intro h
    obtain (h₁ | h₁') | (h₂ | h₂') := h
    · left
      apply h₁
    · right
      left
      apply h₁'
    · right
      left
      apply h₂
    · right
      right
      apply h₂'
  · intro h
    obtain h₁ | h₂ | h₃ := h
    · left
      left
      apply h₁
    · left
      right
      apply h₂
    · right 
      right 
      apply h₃     


example : {-1, 0} ∪ {0, 1} = ({-1, 0, 1} : Set ℤ) := 
by 
  dsimp
  ext n 
  aesop

-- `aesop` stands for "Automated Extensible Search for Obvious Proofs". To see how `aesop` works see the following link: https://github.com/JLimperg/aesop


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := 
by
  intro t h
  obtain ⟨(h₁₁ | h₁₂), h₂⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h₁₁]
      _ = 9 := by rw [h₂]
    linarith -- this does exfalso automatically 
  · dsimp at *; rw [mem_singleton_iff] at h₁₂; positivity  



namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := 
by
  ext n
  dsimp
  rw[mem_compl_iff]
  rw [odd_iff_not_even]
  dsimp 
  trivial

/- A shorter proof -/

example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := 
by
  ext n 
  simp_rw [mem_compl_iff, odd_iff_not_even]
  trivial

end Int




#check Icc 0 1 -- the closed interval `[0, 1]` in `ℕ`, that is the set of all natural numbers `n` such that `0 ≤ n ≤ 1`.

#check Icc (0 : ℝ) 1  -- the closed interval `[0, 1]` in `ℝ`, that is the set of all real numbers `r` such that `0 ≤ r ≤ 1`.

#check Ico (0 : ℝ) 1 -- the open interval `(0, 1]` in `ℝ`, that is the set of all real numbers `r` such that `0 < r ≤ 1`.

section 
example : Ico (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := 
by 
  intro x hx
  dsimp [Icc]
  dsimp [Ico] at hx
  constructor 
  · exact hx.1
  · apply le_of_lt; exact hx.2  




  













