import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
import ProofLab4


variable {U : Type _}
variable (A B S T : Set U)
open Set

/- We show that given a set S the subsets of S form a poset. -/


/- The type of __preorder__ structure on a type `X`. Note that this structure depends on the parameter `X`. -/

structure preorder (X : Type) :=
(R : X → X → Prop) -- a binary relation `R` on `X` 
(rflx : Reflexive R) -- a proof that `R` is reflexive
(trns : Transitive R) -- a proof that `R` is transitive

#check preorder -- a function which assigns to every type `X` the type of preorder structures on `X` 

/- 
Given a type `X` to put a preoder structure on `X` we need to provide the followings: 
  -  a binary relation `R` on `X`
  - a proof that `R` is reflexive. 
  - a proof that `R` is transitive. 
-/


def Nat.preorder_le : preorder ℕ where
  R m n := m ≤ n 
  rflx := by 
            unfold Reflexive
            intro x
            rfl
  trns := by
            unfold Transitive
            intro x y z h₁ h₂
            exact h₁.trans h₂


def Nat.preorder_le_alt : preorder ℕ where
  R m n := m ≤ n 
  rflx := by 
            apply Nat.le_refl
  trns := by
            apply Nat.le_trans


#check Bool.and_assoc

/- In below we define the preorder structure on the type of booleans  -/
def Bool.preorder_le : preorder Bool where 
  R b b' := (b && b') = b' 
  rflx := by 
              unfold Reflexive
              intro x  -- we need to prove x && x = x
              cases x -- we have two cases: x = tt and x = ff
              repeat {rfl} -- in both cases the goal is trivial
               
  trns := by 
               unfold Transitive
               intros x y z h₁ h₂
               let H₂ := h₂
               rw [← h₁] at h₂
               rw [Bool.and_assoc] at h₂ 
               rw [H₂] at h₂
               exact h₂

              
/-
Given a preoder structure on a type `X`, we can extract the binary relation `R` on `X` as follows:
-/

def preorder.rel (σ : preorder X) : X → X → Prop := σ.R

#check preorder.rel -- a function which assigns to every preorder structure on `X` the binary relation on `X` associated to that preorder structure.

/-
For instance the binary relation `R` on `Bool` defined as part of the structure of the preorder on `Bool` can be extracted as follows:
-/

#check Bool.preorder_le.R false true


/- 
 A __partial order__ on a type `X` is a preorder relation which is antisymmetric. 
 Let's prove that the preoder on the natural number we defined above is in fact a partial order.
 -/

def Antisymmetric (R : X → X → Prop) :=  ∀ x y : X, R x y → R y x → x = y

structure partial_order (X : Type) extends preorder X where 
  antisymm : Antisymmetric R

#check Nat.le_antisymm -- a proof that the relation `≤` on `ℕ` is antisymmetric

def nat.partial_order_le : partial_order ℕ where 
  R := Nat.preorder_le.R
  rflx := Nat.preorder_le.rflx
  trns := Nat.preorder_le.trns
  antisymm := by 
                apply Nat.le_antisymm 





/-! ## Preorder in Mathlib -/

#check Preorder   

#check PartialOrder


/- Let's prove that the subsets of a given set admit a partial order structure. 
Hint: to generate a skeleton for your structure use `:=` instead of `where`, click on the star button appearing on the left of the `instance`, and then fill in the missing parts.
-/


instance set.preorder (X : Type) : Preorder (Set X) where
  le A B := A ⊆ B 
  lt A B := A ⊆ B ∧ ¬ B ⊆ A  
  le_refl := by intro A 
                rfl
  le_trans := by apply Subset.trans
  lt_iff_le_not_le := by intros; rfl
                        
#check set.preorder                     


instance set.partial_order (X : Type) : PartialOrder (Set X) where
  le_antisymm := by apply Subset.antisymm

#check set.partial_order


/- 
We say two sets are __disjoint__ if they have no element in common, i.e. their intersection is the empty set.  

There is a more general definition of disjointness in mathlib, namely the predicate `Disjoint`. This is defined for all preorders. 

As we observed above there is a preorder structure on the subsets of a given set.

If we specialize the predicate `Disjoint` to the preorder structure on the subsets of a given set, we recover the usual definition of disjointness in terms of the intersection of two sets.

We want to relate our intuition of the disjoint sets to this more general definition. See `disjoint_iff_inter_eq_empty` 
-/

def disjoint_sets (A B : Set U) : Prop := A ∩ B = ∅

#check Disjoint 

#check disjoint_iff_inter_eq_empty


 
/- The partial order of the subsets of a given set has the greatest element, namely the whole set. -/

class has_top (X : Type) extends PartialOrder X where
  top : X
  le_top : ∀ a : X, a ≤ top

instance : has_top (Set X) where
  top := Set.univ
  le_top := by 
              intro A
              apply subset_univ


/- The partial order of the subsets of a given set has the least element, namely the empty set. -/

class has_bot (X : Type) extends PartialOrder X where
  bot : X
  bot_le : ∀ a : X, bot ≤ a

instance : has_bot (Set X) where
  bot := ∅
  bot_le := by 
              intro A
              apply empty_subset


#check OrderTop
#check OrderBot

#synth OrderTop (Set _)
#synth OrderBot (Set _) 
#synth OrderBot (Finset _)

#check instOrderTopSetInstLESet
#check BoundedOrder.toOrderBot
#check Finset.instOrderBotFinsetToLEToPreorderPartialOrder



/-! ### Lattices -/



class semilattice_join (X : Type) where
  join : X → X → X -- this function specifies the least upper bound of any two elements
  join_assoc : ∀ a b c : X, join (join a b) c = join a (join b c) -- the least upper bound function is associative
  join_comm : ∀ a b : X, join a b = join b a
  join_idem : ∀ a : X, join a a = a -- the least upper bound of an element with itself is itself (idempotency) ) 

/-
Example : the subsets of a given set form a join semilattice.
-/

instance : semilattice_join (Set X) where
  join := Set.union
  join_assoc := by 
                  intros A B C
                  apply union_assoc
  join_comm := by 
                  intros A B
                  apply union_comm
  join_idem := by 
                  intro A
                  apply union_self


class semilattice_meet (X : Type) where
  meet : X → X → X -- this function specifies the greatest lower bound of any two elements
  meet_assoc : ∀ a b c : X, meet (meet a b) c = meet a (meet b c) -- the greatest lower bound function is associative
  meet_comm : ∀ a b : X, meet a b = meet b a
  meet_idem : ∀ a : X, meet a a = a -- the greatest lower bound of an element with itself is itself (idempotency) ) 


instance : semilattice_meet (Set X) where
  meet := Set.inter
  meet_assoc := by 
                  intros A B C
                  apply inter_assoc
  meet_comm := by 
                  intros A B
                  apply inter_comm
  meet_idem := by 
                  intro A
                  apply inter_self


/- 
Every join semilattice in the sense above is also a partial order. Note that the definition of join semilattice does not require any relation on the type `X`, only an operation on `X`.
-/
set_option trace.Meta.synthInstance true in
instance partial_order_of_join_semilattice (X : Type) [semilattice_join X] : PartialOrder X where
  le a b := join a b = b
  lt := _
  le_refl := _
  le_trans := _
  lt_iff_le_not_le := _
  le_antisymm := _





#exit


#check SemilatticeSup
#check SemilatticeInf
#check Lattice

#check semilattice_join
#check semilattice_join.toPartialOrder -- projecting out the underlying partial order structure from the semilattice_join structure





/-! ## Lattices in Mathlib -/




-- example (A B : Finset ℕ) (h : A ∩ B = ∅) : card (A ∪ B) = card A + card B :=
-- by  
--   apply card_union_eq
--   apply disjoint_iff_inter_eq_empty.mpr
--   exact h



namespace SetOrder

#check 1


end SetOrder