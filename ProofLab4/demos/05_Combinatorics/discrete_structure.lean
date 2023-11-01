import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole

/-!
# Basic Discrete Structures in Lean
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2023
-/


/-
The most fundamental discrete structures are finite sets. Finite sets in Lean are implemented as multisets (lists up to permutation) which has no duplicate elements.

Multisets are in turn implemented as lists.
-/


#check Set
#check Set ℕ -- The type of subsets of natural numbers including the infinite subsets

#check Finset
#check Finset ℕ -- The type of finite subsets of `ℕ`. A finite set is implemented as a multiset (a list up to permutation) which has no duplicate elements.


/- The API for finite sets is very close to the API for sets. -/


def my_first_finset : Finset ℕ := {1,2,6}

def my_second_finset : Finset ℕ := {1,2,2}

#eval my_first_finset
/-
{ val := Quot.mk List.Perm [1, 2, 6], nodup := (_ : List.Nodup (1 :: List.insert 2 [6])) }
-/
#reduce my_first_finset

#eval my_second_finset
#reduce my_second_finset


def my_third_finset : Finset ℕ := {27,2}

#eval my_first_finset ∪ my_third_finset



#check Set.union
#check Set.mem_union

example : my_first_finset ∪ my_third_finset  = {6, 1, 27, 2} :=
by
  rw [my_first_finset, my_third_finset]
  ext x
  constructor
  · intro h
    sorry
  · sorry


#check Finset.pair_comm
-- simp in below uses `Finset.pair_comm`
example : my_first_finset ∪ my_third_finset  = {6, 1, 27, 2} :=
by
  rw [my_first_finset, my_third_finset]
  simp


section
#synth Union (Finset ℕ)           --  `∪` instance on Finsets
#synth Inter (Finset ℕ)           --  `∩` instance on Finsets
#synth Insert ℕ (Finset ℕ)        --  inserting/adding an element
#synth EmptyCollection (Finset ℕ) --  the empty instance of Finset
#synth HasSubset (Finset ℕ)       --  `⊆` instance on Finsets
#synth SDiff (Finset ℕ)           -- `\` (set difference) instance
#synth Singleton ℕ (Finset ℕ)     -- `{x}` (singleton) instance


#check Finset.instUnionFinset

#check Set.iUnion -- indexed union
#check Finset.biUnion   -- bounded indexed union
variable (s : Finset ℕ) (a : ℕ)
#check s.erase a              -- erase an element
#check Finset.image
#check Finset.filter
#check Finset.range
#check (· ⁻¹' ·)
end

section bounded_indexed_union
variable (S := ({1,2} : Finset ℕ ))
-- an exmaple of bounded indexed union
end bounded_indexed_union



/- ##  Lists -/

/- In below we define the type of the lists of natural numbers .-/
-- inductive NatList where
-- | nil : NatList
-- | cons (n : ℕ) (l : NatList) : NatList -- If `n : ℕ` and `l : NatList`, then `cons a l` is the list whose first element (aka head) is `n` and with `l` as the rest of the list (aka tail). a :: l


def NatList := List ℕ

#check NatList

namespace NatList

def Mylist1 : NatList := [] -- nil
def Mylist2 : NatList := [1,2,3] -- cons 1 (cons 2 (cons 3 nil)) -- [1,2,3]

#reduce Mylist2

#eval 1 :: [10,50]

/-
How to add a natural number to the start of a list?
-/
def append_head (m : ℕ) : NatList → NatList := fun l => m :: l -- `m : ℕ` appended to the list `l` as the head of the new list

#eval append_head 1 [3,2]


/-
How to add a natural number to the end of a list?
-/
def append_tail (m : ℕ) : NatList → NatList
| [] => [m]
| (n :: l) => n :: append_tail m l

#eval append_tail 1 [3,2] -- [3,2,1]
-- append_tail 1 [3,2] = append_tail 1 (3 :: [2]) = 3 :: append_tail 1 [2] =
-- 3 :: append_tail 1 (2 :: []) = 3 :: 2 :: append_tail 1 [] = 3 :: 2 :: [1] = [3,2,1]


/-
How to reverse a list? e.g. `reverse [1, 2, 3, 4] = [4, 3, 2, 1]`
-/

def reverse : NatList → NatList
| [] => []
| (n :: l) => append_tail n (reverse l)

-- [2] = 2 :: []

#eval reverse [1,5,7]


def head_of : NatList → ℕ
| [ ] => 0
| n :: l' => n

example (l l' : NatList) (h : l = l') : head_of l = head_of l' :=
by
  rw [h]

-- the length of a list counts the number of elements in the list
def length : NatList → ℕ
| [ ] => 0
| n :: l => 1 + length l

def sum : NatList → ℕ
| [ ] => 0
| n :: l => n + sum l

#eval sum [1,3,5,2]

-- we want to define a function that outputs an initial segment of a given length of any list , e.g. initseg [3,9,7,2,20,10] 4 = [3,9,7,2]
-- e.g. initseg [3,9,7,2,20,10] 7 = [3,9,7,2,20,10]
def initseg : NatList → ℕ → NatList
| [], _ => []
| (n :: l), 0 => []
| (n :: l), (m + 1) => n :: (initseg l m)

#eval initseg [3,9,7,2,20,10] 7


/-
`erase a l` removes the first occurrence of `a` from `l`.
* `erase 5 [1, 5, 3, 2, 5] = [1, 3, 2, 5]`
* `erase 6 [1, 5, 3, 2, 5] = [1, 5, 3, 2, 5]`
-/

def erase : ℕ → NatList → NatList
| _ , []  => []
| m, (n :: l) =>  if m = n then l else n :: erase m l

#eval erase 5 [1, 5, 3, 2, 5]
#eval erase 6 [1, 5, 3, 2, 5] -- 1 :: erase 6 [5, 3, 2, 5] = 1 :: 5 :: erase 6 [3,2,5] = ... = 1 :: 5 :: 3 :: 2 :: 5 :: []


-- three layers of induction
-- MyPerm' -- nil, cons, swap
-- NatList -- two constructors [], (n :: l)
-- ℕ -- two constructors zero, succ (n)


end NatList



/- The type `NatList` is an  adhoc type for pedagogical reason and we shall use Mathlib's `List` type instead for formalization and hw exercises. -/

#check List ℤ
#check List ℕ


#check NatList.reverse



/- ##  Multisets from Lists -/

/-
A multisets is a list up to permutation. That means the two lists `[a,b,c,c]` and `[c,b,c,a]` are considered to give rise the same multiset. Another way to think about multisets is that they are finite sets where elements have multiplicities. For example, the multiset `[a,b,c,c]` is the set `{a,b,c}` with the multiplicity of `2` for the element `c`.
-/


/-
We first define what it means for two lists to be permutations of each other.
-/




/-
`Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps.
-/


/-
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-/

/-
The Principle of induction for natural numbers (`Nat`) says that
∀ (P : ℕ → Prop), P (zero) → (∀ (n : Nat) P n → P (succ n) ) → ∀ n, P n

Suppose our goal is to prove that the square of every odd number is odd

-/


#check Nat

/-
Nat.rec.{u} {motive : ℕ → Sort u} (zero : motive Nat.zero) (succ : (n : ℕ) → motive n → motive (Nat.succ n)) (t : ℕ) :
  motive t
-/
#check Nat.rec

inductive MyPerm' : NatList → NatList → Prop
| nil : MyPerm' [] []
| cons (n : ℕ) {l₁ l₂ : NatList} : MyPerm' l₁ l₂ → MyPerm' (n :: l₁) (n :: l₂) -- n :: l₁ , n :: l₂ are permutation of each other if `l₁` and `l₂` are already permutation of each other. using this rule we can prove [c, a, b] ∼ [c, b, a]
| swap  (m n : ℕ) (l : NatList) : MyPerm' (m :: n :: l) (n :: m :: l)


example : MyPerm' [2,3] [3,2] :=
MyPerm'.swap 2 3 []

lemma perm₁ : MyPerm' [1,2,3] [1,3,2] :=
MyPerm'.cons 1 (MyPerm'.swap 2 3 [])

lemma perm₂ : MyPerm' [1,3,2] [3,1,2] :=
MyPerm'.swap 1 3 [2]

/- MyPerm' does not provide a good notion of permutation because this notion of pemutation is not transitive.
As a result the following two lists which are in permutation are not under the relation ` MyPerm' `.
 -/
lemma perm₃ :  ¬ MyPerm' [1,2,3] [3,1,2] :=
by
  intro h
  contradiction



-- defining permutations based on transpositions instead of swaps of the first two elements. This is a more natural definition of permutations.
def transposition (m n : ℕ) (l : List ℕ) ( h : (m ∈ l) ∧ (n ∈ l)): List ℕ :=
sorry

-- theorem transpose_perm (m n : ℕ) (l : List ℕ) ( h : (m ∈ l) ∧ (n ∈ l)) : Perm l (transposition m n l h) :=
-- sorry

-- [a,b,c] ∼ (MyPerm'.cons 1 (MyPerm'.swap 2 3 []))
-- [a,c,b] ∼
-- [c,a,b]



-- [a,b,c,d] ∼  (swap a b [c,d])
-- [b,a,c,d] ∼  (cons b; swap a c [d])
-- [b,c,a,d] ∼  (cons b; cons c; swap a d [])
-- [b,c,d,a] ∼  (cons b; swap c d [a])
-- [b,d,c,a] ∼ (swap b d [c,a])
-- [d,b,c,a]





/-
MyPerm'.rec {motive : (a a_1 : NatList) → MyPerm' a a_1 → Prop} (nil : motive [] [] MyPerm'.nil)
  (cons :
    ∀ (n : ℕ) {l₁ l₂ : NatList} (a : MyPerm' l₁ l₂),
      motive l₁ l₂ a → motive (n :: l₁) (n :: l₂) (_ : MyPerm' (n :: l₁) (n :: l₂)))
  (swap : ∀ (m n : ℕ) (l : NatList), motive (m :: n :: l) (n :: m :: l) (_ : MyPerm' (m :: n :: l) (n :: m :: l)))
  {a✝a✝¹ : NatList} (t : MyPerm' a✝ a✝¹) : motive a✝ a✝¹ t
-/
#check MyPerm'.rec


/-
- `MyPerm'` is the smallest relation satisfying the inductive rules above, i.e. if `C` is  proposition depending on lists `l₁`, `l₂`, and the fact that `l₁ ∼ l₂` and furthermore satisfies the following rules
- `C [] []`
- `∀ (n : ℕ) {l₁ l₂ : NatList} (l₁ ∼ ), C l₁ l₂ → C (n :: l₁) (n :: l₂)`
- `∀ (m n : ℕ) (l : NatList), C (m :: n :: l) (n :: m :: l)`
Then `C` is true for all permutations of a list, that is `∀ (l₁ l₂ : NatList), MyPerm' l₁ l₂ → C l₁ l₂`.
-/

#check MyPerm'.rec

open NatList




-- infix :50 " ∼ " =>  MyPerm'

-- #check [1,2] ∼ [2,1]




theorem MyPerm'.refl : ∀ (l : NatList),  MyPerm' l l
| [ ]  => MyPerm'.nil
| (n :: l) => MyPerm'.cons n (MyPerm'.refl l) -- n :: (m :: l') ∼ n :: (m :: l')


#check MyPerm'.nil


theorem MyPerm'.refl_alt : ∀ (l : NatList),  MyPerm' l l :=
by
  intro l
  cases l with
  | nil => exact MyPerm'.nil
  | cons n l => exact MyPerm'.cons n (MyPerm'.refl l)


#check MyPerm'.rec




-- term-style proof
theorem MyPerm'.symm {l l' : NatList} (h : MyPerm' l l') : MyPerm' l' l :=
h.rec
  (MyPerm'.nil)
  (fun n l₁ l₂ h ih => MyPerm'.cons n ih) -- l = n :: l₁ and l' = n :: l₂
  (fun m n l => MyPerm'.swap n m l) -- l = m :: n :: l and l' = n :: m :: l


#check MyPerm'.symm


-- tactic-style proof
theorem MyPerm'.symm_alt :  ∀ ⦃ l l' : NatList ⦄,  MyPerm' l l' → MyPerm' l' l :=
by
  intro l l' h
  induction h with
  | nil => exact MyPerm'.nil
  | cons n h ih => exact MyPerm'.cons n ih
  | swap m n l => exact MyPerm'.swap n m l



-- l= [] l' = []
-- l = n :: l₁ and l' = m :: l₂

theorem MyPerm'.of_eq (l l' : NatList) (h : l = l') : MyPerm' l l' :=
by
 rw [h]
 exact MyPerm'.refl l'


def head_of : NatList → ℕ
| [ ] => 0
| n :: l' => n




#check @NatList.head_of


example (l l' : NatList) (h : l = l') : NatList.head_of l = NatList.head_of l' :=
by
  rw [h]



-- good exercises for understanding induction on Permutation of Lists
theorem MyPerm'.not_trans : ¬ (∀ ⦃l₁ l₂ l₃ : NatList⦄, MyPerm' l₁ l₂ → MyPerm' l₂ l₃ → MyPerm' l₁ l₃) :=
by
  push_neg
  use [1,2,3], [1,3,2], [3,1,2]
  exact ⟨perm₁, perm₂, perm₃⟩


-- Therefore MyPerm' is not a good specification/definition for the idea of permutation.

#check List.Perm


example (l₁ l₂ : List ℕ) : List.Perm l₁ l₂ → List.length l₁ = List.length l₂ :=
by
  sorry

open List

#check Perm
#check Perm.nil
#check Perm.cons
#check Perm.swap
#check Perm.trans


lemma perm₄ : Perm [1,2,3] [3,1,2] :=
by
  apply Perm.trans (l₂ := [1,3,2])
  · exact Perm.cons 1 (Perm.swap 3 2 [])
  · exact Perm.swap 3 1 [2]


/-
## Multisets : Quotients of lists up to permutations
-/


/-
RECALL:

1. A __binary relation__ on a type `X` is a two-variable predicate `R : X → X → Prop`, that is, a proposition `R x y` attached to each pair of elements of `X`. -- `R x y` says whether `x` is related to `y` via `R`

In mathematics, we often use __infix notation__, writing  `a R b` instead of `R a b`, e.g. `a = b`, `a ≤  b`, etc. Equality an inequality are relations.

2. A __reflexive relation__ on a type `X` is a binary relation `R : X → X → Prop` such that `R x x` is true for every `x : X`.

3. A __symmetric relation__ on a type `X` is a binary relation `R : X → X → Prop` such that `R x y → R y x` for every `x y : X`.

4. A __transitive relation__ on a type `X` is a binary relation `R : X → X → Prop` such that `R x y → R y z → R x z` for every `x y z : X`.

5. An __equivalence relation__ on a type `X` is a binary relation `R : X → X → Prop` that is reflexive, symmetric, and transitive.
-/

/- ## Example of Equivalence Relation -/

def divides (m n : ℤ) := ∃ k : ℤ, n = m * k -- `n` is a multiple of `m`, or in other words `m` divides `n`

example : divides 2 4 :=
by
  simp only [divides]
  use 2
  rfl

#check @divides

-- `divides` (divisibility relation) is reflexive
lemma divides_refl : ∀ n : ℤ, divides n n :=
by
  simp only [divides]
  intro n
  use 1
  rw [mul_one]


-- `divides` (divisibility relation) is not symmetric

example : ¬ (∀ {m n : ℤ}, divides m n → divides n m) :=
by
  push_neg
  use 2, 4
  constructor
  · simp only [divides]
    use 2
    rfl
  · intro h
    simp only [divides] at h
    obtain ⟨k, hk⟩ := h
    -- linarith
    sorry

-- `divides` (divisibility relation) is transitive?
lemma divides_transitive :  ∀ {m₁ m₂ m₃ : ℤ}, divides m₁ m₂ → divides m₂ m₃ → divides m₁ m₃ :=
by
  intro m₁ m₂ m₃ h₁ h₂
  simp only [divides] at *
  obtain ⟨k₁, hk₁ ⟩ := h₁
  obtain ⟨k₂, hk₂ ⟩ := h₂
  use k₁ * k₂
  rw [← mul_assoc]
  --  rw [← hk₁]
  -- assumption
  rw [hk₂]
  rw [hk₁]



/-- Modular Congruence: Two integers are congruent modulo `n`, if their difference is a multiple of `n`. -/
@[simp]
def mod_cong (n a b : ℤ) : Prop := divides n (a - b)


notation:50  a " ≡ " b " [mod " n "]" => mod_cong n a b

example : mod_cong 12 (11+2) 1 :=
by
  sorry


example : 11 + 2 ≡ 1 [mod 12] :=
by
  -- Want to prove that 12 divides  (11 + 2) - 1
  use 1
  ring


-- the relation of modular congruence is an equivalence relation on integers


theorem mod_refl : ∀ x, x ≡ x [mod n] :=
by
  intro x
  -- `n` divides `x - x`
  use 0
  ring


theorem mod_symm {n : ℤ} : x ≡ y [mod n] →  y ≡ x [mod n] :=
by
  intro h
  -- `h` states that n divides x - y
  simp only [ mod_cong, divides ] at h
  obtain ⟨k, hk ⟩ := h
  use (-k)
  linarith [hk]


theorem divides_sum (a b c : ℤ) :
  a ∣ b → a ∣ c → a ∣ b + c :=
by
  intro h₁ h₂
  sorry

theorem mod_trans {n : ℤ} : x ≡ y [mod n] → y ≡ z [mod n] →  x ≡ z [mod n] :=
by
  intro h₁ h₂
  have : n ∣ (x - y) + (y - z)  := divides_sum _ _ _ h₁ h₂
  simpa using this

#check Equivalence

theorem mod_equiv : ∀ n : ℤ, Equivalence (mod_cong n) :=
by
  intro n
  exact ⟨mod_refl, mod_symm, mod_trans⟩




/- A setoid is a type equipped with an equivalence relation. -/
#check Setoid


/-
Let's give the type of integers the structure of a setoid using modular congruence.
-/


-- @[simp]
-- instance mod_cong_equiv (n : ℤ) : HasEquiv ℤ where
--   Equiv := mod_cong n

-- We define a constant family of types such that for each index `n` the family returns the type `ℤ`. We do this so that we have an instance of the type class `Setoid ℤ` works for every integer `n`.


-- def Z (n : ℤ) : Type := ℤ
-- seems `abbrev` is better-suited than `def` since it also carries the instances of the type classes (e.g. ` OfNat` ) defined on `ℤ` to `Z n`, whereas `def` does not.
abbrev Z (n : ℤ) := ℤ

#check OfNat





instance mod_cong_setoid (n : ℤ) : Setoid (Z n) :=
{
  r := mod_cong n,
  iseqv := mod_equiv n
}

#check (mod_cong_setoid 3)
#check (mod_cong_setoid 3).r


/-
Constructing the cylic group of order n using the quotient of the modular congruence
-/

-- from Init.Core
#check Quotient

@[simp]
def CMod (n : ℤ) := Quotient (mod_cong_setoid n)

#check CMod






#check Quot.mk
#check Quotient.mk


#check Quot.sound
#check Quotient.sound


#check (⟦ 3 ⟧ : CMod 4)

#check CMod

#reduce (CMod 4)


example : (⟦ 3 ⟧ : CMod 4) = (⟦ 7 ⟧ : CMod 4) :=
by
  apply Quotient.sound
  simp only [CMod]
  use -1
  ring


example : ∀ n : ℤ, (⟦ n ⟧ : CMod 4) = (⟦ (n + 4) ⟧ : CMod 4) :=
by
  intro n
  apply Quotient.sound
  simp only [Setoid.r]
  use -1
  ring


example : ∀ n : ℤ, (⟦ n ⟧ : CMod 4) = (⟦ (n - 4) ⟧ : CMod 4) :=
by
  intro n
  apply Quotient.sound
  simp only [Setoid.r]
  use 1
  ring


#check Quotient.lift -- : {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) (a✝ : ∀ (a b : α), a ≈ b → f a = f b)(a✝¹ : Quotient s) : β
#check Quotient.liftOn

#check mod_cong

lemma mod_cong_zero : ∀ a b : Z 0,  a ≈  b →  a = b :=
by
  intro a b
  · intro h
    obtain ⟨k, hk⟩ := h
    linarith [hk]


#check Quotient.lift

/- The compostion of `Quotient.lift` and `Quotient.mk` is the identity function. -/

example (X : Sort u) (Y : Sort v) (f : X → Y)  (s : Setoid X) (h : ∀ (a b : X), a ≈ b → f a = f b) (x : X) : Quotient.lift f h (Quotient.mk s x) = f x :=
by
  rfl


#check Quotient.exists_rep

example : CMod 0 ≃ ℤ where
  toFun := Quotient.lift (fun n => n) (mod_cong_zero)
  invFun := Quotient.mk (mod_cong_setoid 0)
  left_inv := by simp only [Function.LeftInverse]; intro x; cases' (Quotient.exists_rep x) with w h; rw [← h]; rfl
  right_inv := by simp only [Function.RightInverse]; intro x; rfl


example : CMod 1 ≃ Unit where
  toFun := Quotient.lift (fun n => ()) (fun a b h => by trivial)
  invFun := fun _ => ⟦ 0 ⟧
  left_inv := by simp only [Function.LeftInverse]; intro x; cases' (Quotient.exists_rep x) with w h; rw [← h]; apply Quotient.sound; use -w ; ring
  right_inv := by simp only [Function.RightInverse]

#check Fin



example (a b c  : ℤ) (h : a - b  = c) : a = c + b :=
add_eq_of_eq_add_neg h.symm |> .symm

example : CMod 2 ≃ Bool where
  toFun := Quotient.lift (fun n =>
                                  n % 2 = 0)
                         (fun a b h =>
                                      by
                                        obtain ⟨k, hk⟩ := h
                                        have : a = 2 * k + b := add_eq_of_eq_add_neg hk.symm |> .symm
                                        rw [this]
                                          )
  invFun := fun b =>
                   if b then ⟦ 0 ⟧ else ⟦ 1 ⟧
  left_inv := by simp only [Function.LeftInverse]; intro x; cases' (Quotient.exists_rep x) with w h; rw [← h]; apply Quotient.sound; use -w ; ring
  right_inv := by simp only [Function.RightInverse]; intro x; cases' x with w h; simp only [if_true, if_false]; cases' w with w; simp only [if_true, if_false]; apply Quotient.sound; use -w ; ring


#check add_eq_of_eq_add_neg
#check add_neg_eq_of_eq_add
#check Eq.symm








#check AddMonoid

/- We want to define a function `add` on `CMod n` that adds two elements of `CMod n` and returns an element of `CMod n`. -/

@[simp]
def CMod.add_aux (n : ℤ) : Z n → Z n → CMod n := fun x y => ⟦ x + y ⟧

-- We want to prove that `add_aux` is well-defined, i.e. if `m ≈ m'` and `n ≈ n'` then `m + n ≈ m' + n'`
@[simp]
lemma add_aux_resp_cong (n : ℤ) : ∀ (a b a' b': Z n) ,  a ≈ a' →  b ≈ b' →  (⟦ a + b ⟧ : CMod n)  = ⟦ a' + b' ⟧ :=
by
  intro a b a' b' h₁ h₂
  apply Quotient.sound
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  use k₁ + k₂
  linarith [hk₁, hk₂]


#check Quotient.lift --: (f : α → β) (h : ∀ (a b : α), a ≈ b → f a = f b) (q : Quotient s) : β

#check Quotient.lift₂ --: (f : α → β → φ) (h : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) (q₁ : Quotient s₁) (q₂ : Quotient s₂) : φ


section
variable (n : ℤ)
#check Quotient.lift₂ (CMod.add_aux n) (add_aux_resp_cong n) -- : Quotient (mod_cong_setoid n) → Quotient (mod_cong_setoid n) → CMod n
end


#check Quotient.ind -- :  (a✝ : ∀ (a : α), motive (Quotient.mk s a)) (q : Quotient s) : motive q
                    -- if we know a unary property holds for all the representatives of the equivalence classes, then it holds for all the elements of the quotient type.

#check Quotient.inductionOn

#check Quotient.ind₂ -- : (h : ∀ (a : α) (b : β), motive (Quotient.mk s₁ a) (Quotient.mk s₂ b)) (q₁ : Quotient s₁) (q₂ : Quotient s₂) : motive q₁ q₂
                     -- if we know a binary property holds for all the representatives of the equivalence classes, then it holds for all the elements of the quotient type.

#check Quotient.ind

#check Quotient.inductionOn₃




#check Add

#check HAdd


#print HAdd





instance mod_cong_add (n : ℤ) : Add (CMod n) where
  add := Quotient.lift₂ (CMod.add_aux n) (add_aux_resp_cong n)

#check  CMod 4

#check (⟦ 2 ⟧ : CMod 4)

#check mod_cong_add 4

#check Add.add (⟦ 2 ⟧ : CMod 4) (⟦ 3 ⟧ : CMod 4)



lemma add_assoc_aux (n : ℤ) : ∀ (a b c : Z n), (( (⟦ a ⟧ : CMod n) + ⟦ b ⟧) + ⟦ c ⟧) = ( ⟦ a ⟧  + (⟦ b ⟧ + (⟦ c ⟧ : CMod n) )) :=
by
  intro a b c
  apply Quotient.inductionOn₃ a b c
  intro a b c
  simp only [CMod.add_aux]
  rw [add_assoc]
  rfl



@[simps!]
instance mod_cong_add_monoid (n : ℤ) : AddMonoid (CMod n) where
  add := Quotient.lift₂ (CMod.add_aux n) (add_aux_resp_cong n)
  add_assoc := by intro a b c; apply Quotient.inductionOn₃;
  --simp; apply Quotient.inductionOn₃ a b c;
  zero := _
  zero_add := _
  add_zero := _
  nsmul := _
  nsmul_zero := _
  nsmul_succ := _


#check SubNegMonoid


#check Group
#check AddGroup

instance mod_cong_group  {n : ℤ} : Group (CMod n) where
  mul q q' := Quotient.liftOn₂ q q' (λ a b => ⟦ a * b ⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂ => Quot.sound (by
    simp only [Setoid.r] at *
    use (a₁ * b₁) - (a₂ * b₂)
    ring))
  mul_assoc := _
  one := _
  one_mul := _
  mul_one := _
  npow := _
  npow_zero := _
  npow_succ := _
  inv := _
  div := _
  div_eq_mul_inv := _
  zpow := _
  zpow_zero' := _
  zpow_succ' := _
  zpow_neg' := _
  mul_left_inv := _








inductive MyPerm : NatList → NatList → Prop
| nil : MyPerm [] []
| cons (n : ℕ) {l₁ l₂ : NatList} : MyPerm l₁ l₂ → MyPerm (n :: l₁) (n :: l₂) -- n :: l₁ , n :: l₂ are permutation of each other if `l₁` and `l₂` are already permutation of each other. using this rule we can prove [c, a, b] ∼ [c, b, a]
| swap  (m n : ℕ) (l : NatList) : MyPerm (m :: n :: l) (n :: m :: l)
| trans {l₁ l₂ l₃ : NatList} : MyPerm l₁ l₂ → MyPerm l₂ l₃ → MyPerm l₁ l₃


/- A good notion of permutation has to be an equivalence relation and we prove this for MyPerm. -/


theorem MyPerm_refl : ∀ (l : NatList),  MyPerm l l :=
by
  intro l
  -- we want to prove that `l` is a permutation of itself
  cases l with
  | nil => exact MyPerm.nil -- the case when `l = []`
  | cons n l' => exact MyPerm.cons n (MyPerm_refl l')-- the case when ` l = n :: l' ` and the goal `MyPerm l l` becomes `MyPerm (n :: l') (n :: l')`


so this is a nice p
theorem MyPerm_symm :  ∀ { l l' : NatList },  MyPerm l l' → MyPerm l' l :=
by
  sorry

theorem MyPerm_trans : ∀ {l₁ l₂ l₃ : NatList}, MyPerm l₁ l₂ → MyPerm l₂ l₃ → MyPerm l₁ l₃ :=
by
  exact MyPerm.trans


theorem MyPerm_equiv : Equivalence MyPerm :=
by
  exact ⟨MyPerm_refl, MyPerm_symm, MyPerm_trans⟩
