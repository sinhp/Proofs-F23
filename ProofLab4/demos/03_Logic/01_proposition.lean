/- 
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4


/-!
# Logic of Propositions 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2023   
-/


#check Prop -- The type of all propositions in Lean

-- Examples of propositions in mathematics:

section 
variable {x y z : ℕ}

#check (2 = 3) /- equality (between terms of the same type) is a proposition. In this example the whole expression `(2 = 3)` is a proposition and therefore a term of the type `Prop`-/

#check x = 2  -- A proposition depending on a variable `x` (called a free variable). We can judge this proposition to be true or false when we provide a value for `x`. 

/- Not all propositions are made out of equalities: they can be about other relations. -/
#check x < 2 -- the relation is `<` (less than)

#check 3 ≤ 2

#check x + 2 -- not a proposition 
#check x + 2 = 0 -- this is a  proposition depending on a variable `x`, and in this case, we say the proposition `x + 2 = 0` has a free variable `x`. 
#check x = y
#check x^2 = y^2 -- with two free variables



#check (x < 2) ∧ (y < x) -- `∧` means `and` and is a __connective__ which makes a compund proposition.

#check x ≤ 2 -- x < 2 or x = 2 is a compund proposition 


#check x ∣ y -- x divides y is a proposition 
#check ∀ x y : ℤ, x ∣ y ∧ y ∣ x → x = y   
#check ∀ x : ℝ, 0 ≤ x → abs x = x
#check ∀ x : ℕ, ∃ y : ℕ,  x < y
#check ∃ x : ℕ, ∀ y : ℕ,  x < y
#check 2 + 2 < 5 ∧ (isOne 3 = "no")

-- note that we checked that these are well-formed propositions, we did not say anything about their truth.
end -- of section 





#eval (3,4).2

def swap (p : A × B) : B × A := 
(p.2, p.1)

#eval swap (3,4)

#check @swap -- is a function of the type `A × B → B × A`

/- We know that `P ∧ Q` is true, and we want to show that `Q ∧ P` is true. -/
example (P Q R : Prop) (hpq : P ∧ Q) : Q ∧ P := 
-- this is the start of the proof mode
by 
  exact ⟨hpq.2, hpq.1⟩ -- `⟨hpq.2, hpq.1⟩` is a proof of `Q ∧ P`. `exact` is a tactic. `⟨hpq.2, hpq.1⟩ : Q ∧ P`


example (P Q : Prop) (hpq : P ∧ Q) : Q ∧ P := 
-- this is the start of the proof mode
  ⟨hpq.2, hpq.1⟩ -- `⟨hpq.2, hpq.1⟩` is a proof of `Q ∧ P`. `exact` is a tactic. `⟨hpq.2, hpq.1⟩ : Q ∧ P`


/- 
        h: P ∧ Q
------------------- (∧-right elim; ∧-left elim)
  h.right :Q     h.left: P  
-------------------(∧-intro)
         Q ∧ P 

-/

/- We know that `P ∧ Q` is true, and we want to show that `Q ∧ P` is true. -/
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := 
by 
  constructor -- constructor is a tactic (which means it is a way to manipulate the state of proofs)
  · exact h.right
  · exact h.left


/- top to bottom (forward) proof-/
example (P Q : Prop) (hpq : P ∧ Q) : Q ∧ P := 
by 
  have hp := hpq.1 -- adding a new assumption `hp` to the list of our assumptions (context)
  have hq := hpq.2 -- adding a new assumption `hq` to the list of our assumptions (context)
  exact ⟨hq,hp⟩  

example (P Q : Prop) (hpq : P ∧ Q) : Q ∧ P := 
by 
  have hp := hpq.1 -- adding a new assumption `hp` to the list of our assumptions (context)
  have hq := hpq.2 -- adding a new assumption `hq` to the list of our assumptions (context)
  constructor 
  · exact hq
  · exact hp



example : 
  False → False := 
by -- I start my tactic proof 
  /-
  We want to prove an implication therefoe we assume a hypothetical proof of `False` and try to prove the goal (i.e. `False`)
  -/
  intro hf 
  exact hf -- just copying the assumption 


example : 
  False → False := 
by 
  intro hf 
  assumption'  


/-
False
--- 
P
-/

example (P : Prop) : 
  False → P := 
by 
  intro hf 
  exfalso 
  assumption 


-- Depenedent Modus Ponens
-- Want to prove that if `P` then if `P implies that P implies Q` then `Q`. 
lemma dep_modus_ponens: 
  P → ((P → P → Q) → Q) :=
by 
  intro hp 
  intro hppq 
  have hpq : P → Q := hppq hp -- the elimination of implication      
  exact hpq hp


lemma dep_modus_ponens_alt: 
  P → ((P → P → Q) → Q) :=
by 
  intro hp hppq 
  exact hppq hp hp -- binding left to right 


example (h : A → B) (ha :  A) : B := 
by 
  exact h ha


example (h : A → B) (ha :  A) : B := 
by 
  apply h -- backward 
  exact ha

lemma dep_modus_ponens_alt_alt: 
  P → ((P → P → Q) → Q) :=
by 
  intro hp hppq 
  apply hppq 
  exact hp 
  exact hp





/- __Equality__ -/


/- Give another proof of `symmetry_of_equality` by replacing `y` with `z` (in virtue of `h₂`) in hypothesis `h₁` to get a new hypothesis `x = z` which is our goal.  

This proof uses the following variant of the rewrite tactic: 
`rw h₁ at h₂` (rewrites hypothesis `h₁` in the hypothesis `h₂`)
-/


-- write a different proof using `rw ... at ...`. 
example (x y z : ℝ) (h₁ : x = y) (h₂ : y = z) : 
  x = z := 
by 
  sorry



/- __And__ -/

example (h : P ∧ Q ∧ R) : 
  Q ∧ P ∧ R := 
sorry 


example (h : P ∧ Q) : 
  Q ∧ P ∧ Q := 
sorry


/- __If ... then ...__ -/



-- Can you prove the following statements by `rfl`? Explain why.

example (a b c d : ℕ) : 
  (c + d) * (a + b)  = (a + b) * (c + d) := 
by    
  sorry

example : (0 : ℤ) + (0 : ℕ) = (0 : ℕ) := 
by 
  sorry

example : (0 : ℕ) + (0 : ℕ) = (0 : ℤ) := 
by 
  sorry

example : (0 : ℤ) + (0 : ℕ) = (0 : ℤ) := 
by 
  sorry 


example : (2 : ℝ) + (2 : ℕ) = (4 : ℝ) :=
sorry 

-- try `rfl` in below; does it work?
example (x y : ℝ) : x + y = y + x :=
sorry 

-- what about here? does `rfl` work?
example : ∀ x y : ℝ, (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 :=
sorry 



example (h : 2 + 2 = 5) : 
  2 + 2 = 4 :=
sorry



example (x : ℕ) (h₁ : 5 = 2 + x) (h₂ : 2 + x = 4) : 
  5 = 2 + x :=
  -- The goal is to construct a proof of ` 5 = 2 + x `.
sorry   


-- try refl first; what do you get?
example (x y : ℕ) (h₁ : x = 0) (h₂ : y = 0) :
  x + y = 0 := 
by
  -- refl
  rw [h₁,h₂] -- We use the hypothesis `h₁ : x = 0` to change all x's to 0's in the goal. Then we use the hypothesis `h₂ : y = 0` to change all y's to 0's in the goal. Leans knows 0 + 0 = 0. We are done  


/- Explain why the following is not a proof-/
example (hpq : P → Q) (hqr : Q → R) (hp : P) : 
  R :=
  sorry
--hqr hpq hp

