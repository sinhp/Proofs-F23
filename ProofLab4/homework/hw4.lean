import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 


open Nat
open Set
open Function 


/-! 
# Homework 4
Homework must be done individually. All codes and comments must be your own work. 

- Your task is to replace the `sorry` placeholders in the following proofs with your own proofs until there is no remaining goal. 

- All proof steps must be appropriately commented. Half of your grade comes from the quality of your comments! Even if you don't know how to complete a proof in Lean, you can get partial credit if your comments show that you understand what needs to be done. Therefore, I recommend that you write your comments as if you were writing a paper proof. Then translate your commment. 

- You are not allowed to use the following tactics: `aesop`. 
-/



/- 
## Problem 1 
-/

/-
In this problem we will see that a set cannot see the multiplicity of an element in a set and the order of appearance of two elements. 

Give proofs of the lemmas `no_multiplicity` and `no_order` below.
-/

lemma no_multiplicity : ∀ (A : Set ℕ) (n : ℕ), A ∪ {n} = A ∪ {n,n} := 
by  
  sorry 


lemma no_order : ∀ (A : Set ℕ) (m n : ℕ), A ∪ {m,n} = A ∪ {n,m} := 
by 
  sorry



/- 
## Problem 2 
-/

/- 
1. Define in Lean what it means for a subset of natural numbers to have at least two elements. 

2. Define in Lean what it means for a subset of any type `X` to have exactly two elements.

3. Define in Lean what it means for a subset of natural numbers to have infinitely many elements.

**In 1-3 above you should not borrow any definition from Mathlib.** There are possibly many ways to define these concepts. You should do it your own way, and what feels most natural to you.

Then verify that your definitions are correct according to the specification above by proving the followings test cases. 

1. Prove that the set of prime number has at least two elements.
2. Prove that the closed interval `Icc (0 : ℕ) 1` has exactly two elements. 
3. Prove that the set of injective functions `Bool → Bool` has exactly two elements.
4. Prove that the set of odd natural numbers has infinitely many elements.
-/ 


def at_least_two_elems (A : Set ℕ) : Prop := sorry 

def exactly_two_elems {X : Type} (A : Set X) : Prop := sorry 

def inf_elems (A : Set ℕ) : Prop := sorry 


example : at_least_two_elems {p : ℕ | Nat.Prime p} :=
by 
  sorry 


example : exactly_two_elems (Icc (0 : ℕ) 1) := 
by 
  sorry 



example : exactly_two_elems {f : Bool → Bool | Injective f} :=
by 
  sorry 


example : inf_elems {n : ℕ | Odd n} :=
by 
  sorry  






/-
## Problem 3
-/

/-
Prove that for every function `f : X → Y` and `g : Y → Z`, if the composition `g ∘ f : X → Z` is injective then `f` is injective.  
-/

/-
Note: This questions relies on your understanding of function composition. You can recall the basic concept and the examples from  ProofLab4/demos/02_Functions/composition.lean 
-/

lemma inj_right_of_inj_comp (f : X → Y) (g : Y → Z) : 
  Injective (g ∘ f) →  Injective f := 
by 
  sorry




/-
## Problem 4 (Bonus)
-/

/- 
Given a function `s : Y → Y` we say that `y : Y` is a __fixed point__ of `s` if `s y = y`. We defined the set of fixed points of `s` as `Fix s := { y : Y | s y = y}`.
-/

def Fix (s : Y → Y) := { y : Y | s y = y} 

/-
Given a function `f : A → A → B`, we say a function `g : A → B` is __represetable__ by `f` if there exists an element `a : A` such that `g = f a`. 
-/

def representable (f : A → A → B) (g : A → B) := ∃ a : A, g = f a


theorem cantor_diagonal (f : A → A → Y) (hrep : ∀ g : A → Y, representable f g) : ∀ (s : Y → Y),  (Fix s) ≠ ∅ := 
by 
  sorry 








