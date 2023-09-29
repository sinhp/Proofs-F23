/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin -- Some results about products and sums over the type `Fin`.
import Mathlib.Algebra.BigOperators.Option
/- Project: show that the finite subsets of a given set form a distributive lattice (_finite_ meets and joins, meets dist over joins  ). -/



section

open Set


#check Finset -- this is defined as a structure in the core library -- it is a multiset with no duplicates. -- recall that a multisets is a list with no ordering, it is quotiented by permutations (`List.Nodup`)

#check List.Nodup

namespace Finset

universe u

variable (A B C : Finset ℕ)
variable (n : ℕ)

#check A.1 -- this is the underlying multiset of A
#check A.2 -- this is the proof that A is a multiset with no duplicates

#check ({1,2,3,4,4} : Multiset ℕ) 
#check ({1,2,3,4,5} : Multiset ℕ) 
#check ({} : Multiset ℕ) 


def my_finite_set : Finset ℕ where
  val := {1,2,3,4,5}
  nodup := by exact Iff.mp Multiset.dedup_eq_self rfl -- this is a proof that the multiset {1,2,3,4,5} has no duplicates


example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by 
  rw [Finset.inter_distrib_left]



/- `range n` is the set of natural numbers less than `n`. -/

#check range -- this is `Finset.range` do not mistake it for `set.range`!
#check Finset.range

#check range 5
#reduce range 5 -- { val := Quot.mk List.Perm [0, 1, 2, 3, 4], nodup := (_ : List.Nodup (List.range 5)) }

#print inferInstance

example : 1 ∈ [1,2,3] := 
by 
  apply List.mem_cons_self

def my_finset : Finset ℕ where
  val := [0, 1,2,3]
  nodup := by exact Iff.mp Multiset.dedup_eq_self rfl

example : my_finset = {0,1,2,3} :=
by 
  rfl
 
example : my_finset = range 4 := 
by 
  rfl
  

example : 1 ∈ ({1, 2, 3} : Finset ℕ) := 
by 
  exact mem_insert_self 1 {2, 3} 



/- `#synth` command to synthesize an instance and print its name -/
#synth Inhabited Nat -- successfully synthesizes an instance and prints `instInhabitedNat` in the infoview, which is the name of this instance. 

#check instInhabitedNat  --Init/Prelude.lean

#check Membership

#synth Membership ℕ (List ℕ) -- List.instMembershipList
#check List.instMembershipList  --Init/Data/List/Basic.lean

#synth Membership _ (List _) -- prints the same thing


/- this works because of a coercion from `Finset` to `Set` -/
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by 
  ext x 
  simp only [mem_inter, mem_union]
  tauto


example (A : Finset ℕ) : Set ℕ := 
  A -- this is a coercion from `Finset` to `Set`

/- the explicit coercion term from `Finset` to `Set` -/
#check toSet 





#check card_union_eq --  is two finite sets `S` and `T` are disjoint then `card (S ∪ T) = card S + card T`

#check Finset.image -- image of a function on a finite set is finite
#check (range n).image 
#check mem_range -- Finset.mem_range {n m : ℕ} : m ∈ range n ↔ m < n

example (m : ℕ) (h : m ≥ n) : card (range n ∪ (range n).image (fun i => m + i)) = 2 * n :=
by 
  rw [card_union_eq]
  · rw [card_range, card_image_of_injective, card_range]
    ring
    apply add_right_injective 
  · simp only [Disjoint]
    intro F 
    simp 
    intro hF₁ hF₂ x hxF 
    have u := hF₁ hxF
    have h₁ : x < n := by simpa [mem_range] using u
    simp
    have h₂ : x ≥ n := by simp
                          have h₃ := by simpa [mem_range] using (hF₂ hxF)
                          cases' h₃ with k hk
                          rw [← hk.2]
                          linarith  
    linarith


open BigOperators

variable (n : ℕ)
 
#check ∑ i in range 10, (i^2 + i + 1)
#eval ∑ i in range 10, (i^2 + i + 1)


variable (F : Type) [Fintype F]

/- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems : Finset` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
#check @Fintype.elems

#check (univ : Finset F)
--#check (univ : Finset ℕ)

variable (f : F → ℕ) -- F is a finite type 
variable (g : A → ℕ) -- A is a finite set 

#check f
#check g

#check ∑ i : A, g i
#check ∑ i : F, f i
#check ∏ i : F, f i


end Finset


-- variable f : F → ℕ
-- #check ∑ i : F, f i
-- #check ∏ i : F, f i

-- #check fin n
-- #check fin 5

-- variable i : fin 5
-- #check i.val
-- #check i.is_lt

-- #check n + i
-- #check i + n

-- #eval ∑ i : fin 11, i.val
-- end

-- open finset

-- example (n : ℕ): fintype.card (fin n) = n :=
-- by rw fintype.card_fin

-- example (n : ℕ): card (univ : finset (fin n)) = n :=
-- begin
--   simp only [card_fin],
-- end

-- lemma nat.antidiagonal_eq_image (n : ℕ) :
--   nat.antidiagonal n = (range (n + 1)).image (λ i, (i, n - i)) :=
-- begin
--   ext p, simp, split,
--   { rintros rfl,
--     use [p.fst], simp, linarith },
--   rintros ⟨i, ilt, rfl⟩,
--   exact nat.add_sub_of_le (nat.le_of_lt_succ ilt),
-- end

-- theorem sum_antidiagonal_eq (n : ℕ) (f : ℕ × ℕ → ℕ) :
--   ∑ p in nat.antidiagonal n, f p = ∑ i in range (n + 1), f (i, n - i) :=
-- begin
--   rw [nat.antidiagonal_eq_image, sum_image], simp,
--   intros; assumption
-- end

-- theorem sum_antidiagonal_eq' (n : ℕ) (f : ℕ × ℕ → ℕ) :
--    ∑ p in nat.antidiagonal n, f p = ∑ i : fin n.succ, f(↑i, n - ↑i) :=
-- by rw [sum_antidiagonal_eq, finset.sum_range]

-- -- without notation
-- example (n : ℕ) (f : ℕ × ℕ → ℕ) :
--    ∑ p in nat.antidiagonal n, f p = finset.univ.sum (λ (i : fin n.succ), f(↑i, n - ↑i)) :=
-- sum_antidiagonal_eq' _ _


-- -- had to import algebra.big_operators.basic!
-- open finset

-- example (n : ℕ) :
--   card (univ.filter (λ p : fin (n + 1) × fin (n + 1), p.1 < p.2)) = n * (n + 1) / 2 :=
-- begin
--   have : univ.filter (λ p : fin (n + 1) × fin (n + 1), p.1 < p.2) =
--     finset.bUnion univ
--       (λ j : fin (n + 1),
--         finset.image (λ i : fin j, (⟨i.val, i.property.trans j.property⟩, j)) univ),
--     begin
--       ext x, simp [prod.ext_iff], split,
--       { intro h, use ⟨x.fst, h⟩, simp },
--       rintros ⟨x', h⟩,
--       rw ←h,
--       apply x'.property
--     end,
--   rw [this, finset.card_bUnion],
--   clear this, swap,
--   { intros x _ y _ xney z,
--     simp only [inf_eq_inter, mem_inter, mem_image, mem_univ, prod.ext_iff],
--     rintros ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩,
--     contradiction },
--   transitivity ((univ : finset (fin (n + 1))).sum (λ u, ↑u)),
--   { congr,
--     ext x,
--     rw [finset.card_image_of_injective],
--     { rw finset.card_fin },
--     intros i1 i2, simp [fin.ext_iff] },
--   symmetry,
--   apply nat.div_eq_of_eq_mul_left (show 0 < 2, by norm_num),
--   induction n with n ih,
--   { simp },
--   rw [fin.sum_univ_cast_succ, add_mul],
--   simp only [fin.coe_cast_succ, fin.coe_last],
--   rw [←ih, nat.succ_eq_add_one],
--   ring
-- end

-- -- Floris' shorter version

-- -- for some reason `simp` doesn't do this
-- @[simp] theorem forall_forall_eq' {α β : Sort*} {p : α → β → Prop} {b' : β} :
--   (∀ a b, b' = b → p a b) ↔ ∀ a, p a b' :=
-- forall_congr $ by simp

-- example (n : ℕ) :
--   card ((range (n+1) ×ˢ range (n+1)).filter (λ p, p.1 < p.2)) = n * (n + 1) / 2 :=
-- begin
--   have : (range (n+1) ×ˢ range (n+1)).filter (λ p, p.1 < p.2) =
--     (finset.range (n+1)).bUnion (λ j : ℕ, (range j).image $ λ i, (i, j)),
--   { simp [finset.ext_iff, prod.ext_iff, @and.left_comm _ (_ = _), iff_true_intro lt_trans] },
--   rw [this, finset.card_bUnion]; clear this,
--   swap,
--   { intros x _ y _ xney,
--     simp [disjoint, finset.subset_iff, prod.ext_iff, @imp.swap (_ < _) (_ = _), eq_comm, xney] },
--   transitivity (∑ i in range (n+1), i),
--   { congr,
--     ext x,
--     rw [finset.card_image_of_injective, card_range],
--     intros i1 i2, simp },
--   rw [finset.sum_range_id, add_tsub_cancel_right, mul_comm],
-- end

