import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
import Mathlib.Data.Real.Basic



/- `set U := U → Prop` -/

/-
A __set__ `S` in `U` is just a predicate `S : U → Prop`. You should think of `S` as a collection of all elements `u : U` satisfying the property `S`, that is all those `u` for which `S u` is true.  Following this line of thinking we might like to notate `S` using the set-builder notation 
`S = { x : U ∣ S x}`

Thus If `U` is any type, the terms of the type `set U` are subsets of `U`. 

Since we defined sets as predicates, two sets `A` and `B` are equal when  they are the same considered as predicates. That is `A = B` when 
`A x ↔ B x` for all `x : U`.  

Therefore, to prove that two sets are equal, it suffices to show that every element of one is an element of the other. This principle is known as “extensionality” and, unsurprisingly, the `ext` tactic is equipped to handle it.

-/ 

/- Among the subsets of `U`, there is  the set `univ`, which consists of all the elements of type `U`, and the empty set, `∅`, which can be typed as `\empty`.-/


/- For a set `S : set U` and `x : U` we write `x ∈ S` for the proposition `S x`. 
-/


variable {U : Type _}
variable (A B S T : Set U)
open Set


#check ( { 0 } : Set ℕ) 
#check ( { 0 } : Set ℤ)
#check ( { 0 } : Set ℝ) 


-- The subset relation can be typed with \sub

#check A ⊆ B 
-- `A ⊆ B` is defined by the logical statement `∀  x : U , (x ∈ A → x ∈ B)`

#check subset_def -- unfolds the definition of `A ⊆ B`

-- intersection can be typed with `\i` or `\cap`.
#check A ∩ B -- 

--Union can be typed with `\un` or `\cup`.
#check A ∪ B 

lemma subset_reflexivity : A ⊆ A := 
by
  intro x 
  intro h
  exact h 

lemma subset_transitivity {h₁ : A ⊆ B} {h₂ : B ⊆ C} : A ⊆ C 
:=
by 
  rw [subset_def]
  intro x hxa
  have hxb := h₁ hxa
  exact h₂ hxb


#check Subset.trans

/- 
Lean is smart and it lets us further simplify the proof above by deleting the calls to `rw` entirely. 
To do this, under the hood, Lean uses something called **definitional reduction**: to make sense of the `intros` command and the anonymous constructors Lean is forced to expand the definitions automatically so that we don't have to.
-/

example {h₁ : A ⊆ B} {h₂ : B ⊆ C} : A ⊆ C 
:=
by 
  intros x hxa
  have hxb := h₁ hxa
  exact h₂ hxb



#check Iff.intro

/- If we prove `A ⊆ B` and `B ⊆ A` then it follows that `A = B`. -/ 

example : A ⊆ B → B ⊆ A → A = B := 
by 
  intro h₁ h₂ 
  ext x 
  apply Iff.intro
  · intro xa ; exact h₁ xa 
  · intro xb ; exact h₂ xb 


#check Subset.antisymm



example : A ∩ B = B ∩ A := 
by 
  ext x
  simp [and_comm]




/-! ### Intersections -/

section 
#check inter_def -- unfolding the defn of intersection 
#check mem_inter -- says if `x ∈ A` and `x ∈ B` then `x ∈ A ∩ B`.  
#check mem_of_mem_inter_left
#check mem_of_mem_inter_right
#check inter_subset_left
#check inter_subset_right
end 



example {A B C : Set U} (hca : C ⊆ A) (hcb : C ⊆ B) : C ⊆ A ∩ B := 
by 
  intro x h 
  constructor 
  · apply hca; assumption  
  · apply hcb; assumption


example {A B C : Set U} (rs : C ⊆ A) (rt : C ⊆ B) : C ⊆ A ∩ B := 
fun _ h =>
  ⟨rs h, rt h⟩


#check subset_inter


lemma inter_super (h : A ⊆ B) : A ∩ B = A := 
by 
  apply Subset.antisymm
  · apply inter_subset_left
  · apply subset_inter; rfl; assumption 


/- Convince yourself that the following is true by drawing a picture. -/
example (h : A ⊆ B) : A ∩ S ⊆ B ∩ S := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  dsimp
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

/- 
The `rintro` combines the introducing and destrcturing in one tactic. 
-/
example (h : A ⊆ B) : A ∩ S ⊆ B ∩ S := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩


/- Still more compact: -/

example (h : A ⊆ B) : A ∩ S ⊆ B ∩ S := by
  intro x xas
  exact ⟨h xas.1, xas.2⟩

/-
Let's reflect on what happened in the proof above: we introduced `x : U` with the assumption that `xas : x ∈ A ∩ S`. This is the same as  `x ∈ A ∧ x ∈ S`. Then we destrctured `xas` into `xas.1 :  x ∈ A` and `xas.2 : x ∈ S `. Since `A ⊆ B` we conclude that `x ∈ B`. So `x ∈ B ∧ x ∈ S`. So `x ∈ B ∧ S`.   
-/


/-! ### Union -/

#check Set.union

-- The goal is to prove that A ∪ B ⊆ A' ∪ B'
theorem subset_union {A A' B B' : Set U} (hA : A ⊆ A') (hB : B ⊆ B') :
  A ∪ B ⊆ A' ∪ B' :=
by
  -- Assume x is an arbitrary element in A ∪ B
  intro x (h : x ∈ A ∪ B)
  -- We need to prove that x ∈ A' ∪ B'

  -- We have two cases to consider: either x ∈ A or x ∈ B
  cases' h with hxA hxB

  -- Case 1: x ∈ A
   -- x is in A, and A ⊆ A', so x ∈ A'
  · exact Or.inl (hA hxA) 
  
  -- Case 2: x ∈ B
  -- x is in B, and B ⊆ B', so x ∈ B'
  · exact Or.inr (hB hxB) 

/-
The proposition `x ∈ A ∪ B` unfolds to `x ∈ A ∨ x ∈ B`. 
To deal with unions, we can use `set.union_def` and `set.mem_union`. We can also use the cases tactic to force a definitional reduction.
-/

lemma union_super (h : A ⊆ B) : A ∪ B = B
:= 
by 
  apply Subset.antisymm
  -- now we have 2 goals  A ∪ B ⊆ B and B ⊆ A ∪ B
  · rintro x (xa | xb)
    · apply h; assumption
    · assumption
  · intro x xb; right; assumption




example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
by 
  rintro x ⟨xa, (xb | xc)⟩  
  · left; exact ⟨xa, xb⟩  
  · right; exact ⟨xa, xc⟩


#check union_subset
#check inter_subset_left
#check subset_union_left


/- Challenge: prove `subset_union` from `union_subset`. -/



example : A ∩ B ∪ A ∩ C ⊆  A ∩ (B ∪ C) := 
by
  apply union_subset 
  apply subset_inter
  apply inter_subset_left
  apply Subset.trans (inter_subset_right A B) (subset_union_left B C)
  apply subset_inter
  apply inter_subset_left
  apply Subset.trans (inter_subset_right A C) (subset_union_right B C)



#check mem_union_left
#check mem_union_right
#check mem_or_mem_of_mem_union
#check not_mem_empty


#check subset_union_left




/-! ### Relative Complement -/


/- 
The __relative complement__ (aka set difference) collects elements that are in one set but not in another. The set difference is denoted by `A \ B`; it is  the complement of `B` relative to `A`. The backslash is a special unicode character entered as `\\`. 

`A \ B = {x | x ∈ A and x ∉ B}`

Example: Let `A = {1, 2, 3, 4, 5, 8}` and `B = {5, 4, 6, 7, 8}`.
The relative complement `A \ B` consists of the elements that are in `A` but not in `B`. Therefore, `A \ B = {1, 2, 3}`.

By the definition of relative complement, the expression `x ∈ A \ B` is by definition the same as `x ∈ A ∧ x ∉ B`. (The `∉` can be entered as `\notin`.) 
The operation of set difference is left-associative, that is  A \ B \ C by default reads as 
`(A \ B) \ C`. Therefore, for instance, 
`x ∈ A \ B \ C ↔ (x ∈ A ∧ x ∉ B) ∧ x ∉ C ` 
-/

/-
In below we show that `(A \ B) \ C ⊆ A \ (B ∪ C)`. To do this, we prove that every elemnt of `(A \ B) \ C` belongs to`A \ (B ∪ C).` Take an arbitrary element `x` in `(A \ B) \ C`, that is let us assume `x ∈ (A \ B) \ C` : This means that `x` is in `A` but not in `B`, and then further, it is not in `C`.

To show that x is in `A \ (B ∪ C)`, we need to demonstrate that `x` is in `A` but not in the union of `B` and `C`, that is we need to prove that `x ∈ A \ (B ∪ C)`

Now, since `x` is in `A` but not in `B` the proposition `x ∈ A ∧ x ∉ B` is true which in particular implies that `x ∈ A`. We now show that that `x` is not in the union of `B` and `C`: Let's assume it is. If `x ∈ B` holds we arrive at a contradiction since we already know that `x ∉ B`. If `x ∈ C` holds we again arrive at a contradiction since we already know that `x ∉ C`. Therefore, it cannot be that `x ∈ B ∪ C`. Hence `x ∉ B ∪ C` and therefore, `x ∈ A \ (B ∪ C)`. 


Since x was an arbitrary element in `(A \ B) \ C`, we have shown that any element in `(A \ B) \ C` is also an element of `A \ (B ∪ C)`. Hence, `(A \ B) \ C ⊆ A \ (B ∪ C)`.
-/

example : (A \ B) \ C ⊆ A \ (B ∪ C) := by
  intro x h -- Take 
  have xa : x ∈ A := h.1.1
  have xnb : x ∉ B := h.1.2
  have xnc : x ∉ C := h.2
  constructor
  · exact xa
  intro xbc
  -- x ∈ B ∨ x ∈ C
  cases' xbc with xb xc
  · show False
    exact xnb xb
  · show False; exact xnc xc



/- Let's give a more compact proof.  -/

example : (A \ B) \ C ⊆ A \ (B ∪ C) := by
  rintro x ⟨⟨xa, xnb⟩, xnc⟩
  constructor 
  · assumption  
  · rintro (xa | xc) <;> contradiction


example : (A \ B) \ C ⊆ A \ (B ∪ C) := by
  rintro x ⟨⟨xa, xnb⟩, xnc⟩
  use xa -- uses the fact that conjunction is a special case of existential quantification
  rintro (xt | xc) <;> contradiction


/-! 
The symmetric difference of two sets collects all elements that are exclusively in one set or the other but not in both.
-/



example : A \ B ∪ B \ A = (A ∪ B) \ (B ∩ A) := by
  sorry

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply Classical.em



/-! ## The empty set and the universal set -/

/- 
The sets `∅` and `univ` are defined relative to the domain of discourse. For instance if the domain of discourse is natural numbers then `∅ : set ℕ` but if the domain of discourse is integers then `∅ : set ℤ`. 
-/

/-
We often need to indicate the type of `∅` and `univ` explicitly, because Lean cannot infer which ones we mean. The following examples show how Lean unfolds the last two definitions when needed. In the second one, we remind that `trivial` is the canonical proof of the proposition `True`.
-/


example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial


/- `univ` has type
{α : Type u_1} → Set α
-/
#check Set.univ 


/- For every type `X`, `univ : set X` is defined by the predicate which is everywhere true, i.e. 
`fun _a => True` 
-/
#reduce univ


/-every subset of `X` is included in the universal one (namely `X` itself). -/
#check subset_univ 




/-! ###  Examples -/


example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry



#print Nat.Prime

def primes : Set ℕ :=
  { x | Nat.Prime x }

  

#check Irreducible

#check Iff.mpr

example : 2 ∈ primes := 
by 
  dsimp [primes]  
  unfold Nat.Prime
  constructor 
  · intro h 
    cases' h with n hn
    cases' n with a b hab hba
    have H1 : 1 < a := by linarith 
    have H2 : 0 < b := by sorry 
    have H3 : a ≤ 1 := by calc a ≤ a * b := Nat.le_mul_of_pos_right H2
                            _ = 1 := by linarith 
    linarith -- combining H1 and H3 we get a contradiction                        
  · intro a b h; sorry  
  
  

/-! ### Cartesian binary product of sets -/

section prod
variables {U V: Type} {A : Set U} {B: Set V} {a : A} {b : B}

/- 
The cartesian product `A ×ˢ B` is the set of `(a, b)`
  such that `a ∈ A` and `b ∈ B`.
In the Lean core library this is defined as in below:
`instance : has_set_prod (set α) (set β) (set (α × β)) := ⟨λ s t, {p | p.1 ∈ s ∧ p.2 ∈ t}⟩`
-/


#check SProd
#check Set.prod

-- some useful theorems about cartesian product of sets
#check mem_prod 
#check mem_prod_eq 
#check prod_mk_mem_set_prod_eq 

#check and_false
-- Let's prove that the product of any set with the empty set is empty again. 

theorem product_with_empty_right {A : Set U} : A ×ˢ (∅ : Set U) =  ∅ 
:=
by 
  ext  p
  rw [mem_prod_eq]
  simp [and_false]









/-! ## Indexed Sets (akd Families) 

__Indexed unions__ and __indexed intersections__ are set-theoretic operations which generalize the binary intersection and union of sets.  

Cosnider a type `U`. We model an __indexed family of subsets__ of `U` as a function `A : I → Set U`, where `I` is a (small) type. The set `⋃ i, A i` denotes their union, and `⋂ i, A i` denotes their intersection. 
-/

/- The intersection of a union is the union of intersections. -/

section
variable {U V : Type _} {I : Sort _}
variable (A B : ℕ → Set U) -- A sequence of A₀, A₁, A₂, ⋯       
variable (C : Set U)


example : (C ∩ ⋃ i, A i) = ⋃ i, C ∩ A i := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xc, ⟨i, xAi⟩⟩
    exact ⟨i, ⟨xc, xAi⟩⟩ 
  · rintro ⟨i, xc, xAi⟩
    exact ⟨xc, i, xAi⟩



example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (C ∪ ⋂ i, A i) = ⋂ i, C ∪ A i := by
  sorry


#check mem_iUnion
#check mem_iUnion₂


example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

/- the left hand side is the set of all natural numbers not divisible by any prime. -/
example : (⋂ p ∈ primes, { x | ¬ p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  dsimp
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {U : Type _} (𝓕 : Set (Set U)) -- An element of 𝓕 is a set of subsets of `U`. `⋃₀ 𝓕` is defined as the smallest subset containing all elements of `𝓕` as its susbet. 

example : ⋃₀ 𝓕 = ⋃ A ∈ 𝓕, A := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ 𝓕 = ⋂ A ∈ 𝓕, A := by
  ext x
  rw [mem_iInter₂]
  rfl

end -- end of section 



#check  decidableMemDiagonal

#check Disjoint