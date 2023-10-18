
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


section bounded_indexed_union
variable (S := ({1,2} : Finset ℕ ))
-- an exmaple of bounded indexed union 
end bounded_indexed_union



/- ##  Lists -/

/- In below we define the type of the lists of natural numbers .-/ 
-- inductive NatList where 
-- | nil : NatList 
-- | cons (n : ℕ) (l : NatList) : NatList -- If `n : ℕ` and `l : NatList`, then `cons a l` is the list whose first element (aka head) is `n` and with `l` as the rest of the list (aka tail). a :: l 


abbrev NatList := List ℕ 


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



end NatList 

#check List ℤ
#check List ℕ  