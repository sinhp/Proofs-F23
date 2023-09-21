import ProofLab4
open Function 
open Nat

/-! 
# Homework 3
Homework must be done individually.

- Your task is to replace the `sorry` placeholders in the following proofs with your own proofs until there is no remaining goal. 

- All proof steps must be appropriately commented. Half of your grade comes from the quality of your comments! Even if you don't know how to complete a proof in Lean, you can get partial credit if your comments show that you understand what needs to be done. Therefore, I recommend that you write your comments as if you were writing a paper proof. Then translate your commment. 
-/



/- 
## Problem 1 
-/

/- ### Preliminaries
In automated mathematical reasoning, an in particular order resolution, it is useful to know that formulas can be expressed in particularly simple or convenient forms.

Recall that an __atomic formula__ is a propositional variable (like `P`, `Q`, etc) or one of the constants `True` or `False` . 

A __literal__ is an atomic formula or a negated atomic formula, like `P`, `¬P`, `Q`, `¬Q`, `¬False` etc  



We say a propositional formula is a __Conjunctive Normal Form__(CNF) if it is a conjunction of disjunctions of literals. 

This means a formula is in conjunctive normal form if it has the form  `A1 ∨ ... ∨ Am` , where each `Ai` is a  disjunctions of literals (atoms or negated atoms).


Example: 
Let `P, Q, R` be propositional atoms. Consider the propositional formula 

` P → (Q ∧ R) `

Classically, this formula is equivalent to 

` ¬ P ∨ (Q ∧ R) `

By the distributivity of disjunction (`∨`) over conjunction (`∧`), we obtain the following logically equivalent formula 

` (¬P ∨ Q) ∧  (¬ P ∨ R) ` 

Whereas ` P → (Q ∧ R) ` is not a CNF its logical equivalent ` (¬P ∨ Q) ∧  (¬ P ∨ R) ` is a CNF.
-/


/-
### Find CNF
For each of the following propositional formulas find a logically equivalent formula in CNF. Then prove that your CNF formula is logically equivalent to the given formula.


1. ` P → (Q ∧ R) ` 
2. ` (P₁ ∧ P₂) ∨ (Q₁ ∧ Q₂) `
3. ` ¬¬P ∧ ¬ Q `
4. `¬P ∧ ¬Q`
-/




/-
## Problem 2
-/

/-
In the lecture on predicates we defined the predicate `is_injective` as follows 
-/
def is_injective (f : A → B) :=  
∀ (x y : A), (x ≠ y) → (f x ≠ f y) 

/-
In this problem you are going to prove that the Mathlib's definition of injectivity is logically equivalent to ours. 
-/
section 
variable (f : A → B)
#check Injective f
#reduce Injective f
end 

/-
To prove the logical equivalence replace the `sorry` placeholders in the following proof with your proofs. 
-/
example : ∀ (f : A → B), (is_injective f) ↔ (Injective f) := 
by 
  -- Let `f` be an arbitrary function from `A` to `B`
  intro f
  -- to prove an iff statement, we prove the two implications separately, therefore we will have two subgoals, corresponding to the two directions of the implication 
  constructor
  -- first we prove the implication from left to right. 
  · unfold is_injective Injective 
  -- Assume that `f` is injective the sense of `is_injective`. We need to prove that `f` is injective in the sense of the sense of MathLib.
    intro h_inj
    -- Let `x` and `y` be arbitrary elements of `A`. 
    intro x y 
    -- And suppose that `f x = f y`. 
    intro hxy 
    -- We need to prove that `x = y`. We prove this by contradiction, that is we assume that `x = y` is not the case and we derive a contradiction.
    by_contra'
    sorry 
  -- Now we prove the converse.
  · unfold is_injective Injective 
    -- Assume that `f` is injective the sense of MathLib. We need to prove that `f` is injective in the sense of `is_injective`.
    intro hInj 
    -- Let `x` and `y` be arbitrary elements of `A` which are distinct. 
    intro x y hxy
    -- We need to prove that `f x ≠ f y`. Since we prove a negation, we assume a proof of `f x = f y` and 
    intro hfxy
    have : x = y := hInj hfxy 
    sorry 




/- 
## Problem 3
-/


/-
In this problem we show that the successor function `succ : ℕ → ℕ` is injective. We do this by first proving that `succ` has a __retract__, that is it has a left inverse, namely the predecessor function `pred : ℕ → ℕ`.
-/

section 
variable (f : A → B) (g : B → A)
#check LeftInverse g f -- this means for all `x : A` we have `g (f x) = x`. We read this as "g is a left inverse of f". 
/-  
x : A ⊢ f x : B ⊢ g (f x) = x : A 
  ----- [f] --- [g] --- = ----[id] --- 
Note that In the diagramatic order `g` is on the right-hand side of `f`, but in the equation `g (f x) = x` `g` is on the left-hand side of `f`. The latter is the reason we call `g` a left inverse of `f`.
-/
end 


structure Retract (f : X → Y) where
  /-- The map splitting `f` -/
  retraction : Y → X
  /-- `f` composed with `retraction` is the identity -/
  eq : LeftInverse retraction f -- this means for all `x : X` we have `retraction (f x) = x`. We read this as "retraction is a left inverse of f".

/-
Given a function `f : X → Y`,  a term `Rf` of type `Retract f`, if it exists,  consists of a function `Rf.retraction : Y → X` and a proof `Rf.eq` of the proposition that the retraction `Rf.retraction` is a left inverse of `f`. 
-/


theorem injective_of_HasRetract (f : X → Y) (Rf : Retract f) : Injective f :=
by 
  -- Let `x` and `y` be arbitrary elements of `X` with the property that `f x = f y`. We need to prove that `x = y`.
  intro x y hfxy 
  -- Since `Rf` is a retract of `f`, we have a function `r : Y → X` such that `r ∘ f = id`.
  have : x = Rf.retraction (f x) := by rw [Rf.eq x]  
  have : y = Rf.retraction (f y) := sorry
  sorry 


#check @pred -- see the type of `pred`
#reduce pred
#print pred -- see the definition of `pred` in full detail


theorem succ_inj : Injective succ := 
by 
  -- We want to show that the function `succ : ℕ → ℕ` is injective. To this end, we use the lemma `injective_of_HasRetract` above and specialize it to the function `succ` and the retraction `pred`. 
  apply injective_of_HasRetract 
  -- We propose `pred` as a retract of `succ`.
  use pred 
  -- We need to prove that `pred` is a left inverse of `succ`. That is, we need to prove that for all `n : ℕ` we have `pred (succ n) = n`.
  unfold LeftInverse
  sorry 




/-
## Problem 4
-/

/-
We want to prove that for a real number `x` if the absolute value `|x|` is less than `y`  then  `x` is somewhere between `-y` and `y`.

Here's our proof strategy:

1. Either `x` is non-negative or it is negative.
2. If `x` is non-negative then `abs x = x` and therefore, our assumption `abs x < y` simplifies to `x < y`.
3. It follows that `-y < x` by multiplying the inequality `x < y` by `-1`.
4. If `x` is negative then `abs x = - x` and therefore, our assumption `abs x < y` simplifies to `- x < y`. It follows that `- y < x` by multiplying the inequality `x < y` by `-1`.
-/


/-
Translate the following informal proof strategy to a formal proof in Lean. 
-/

-- Here's our proof strategy: 
-- 1. either `x` is non-negative or it is negative. 
-- 2. If `x` is non-negative then `abs x = x` and therefore, our assumption `abs x < y` simplifies to `x < y`. 
-- 2.1. ...
-- 3. If `x` is negative then `abs x = - x` and therefore, our assumption `abs x < y` simplifies to `- x < y`. It follows that `- y < x` by multiplying the 


example (x y : ℝ ) : 
  abs x < y → - y < x ∧ x < y :=
by 
  intro hxy
  cases le_or_gt 0 x with 
  | inl hx₁ => 
    constructor    
    · rw [abs_of_nonneg hx₁] at hxy 
      sorry 
    · sorry 
  | inr hx₂ => sorry  



example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h













