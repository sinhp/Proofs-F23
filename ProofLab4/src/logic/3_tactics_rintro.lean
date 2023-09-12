/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Mathlib.Data.Real.Basic


/-!
# Logic of Propositions: More Advanced Tactics 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2023   
-/


/- Tactics are instructions and more advanced tactics are series of instructions which automate our manual writing of proofs with simple tactics. In below we shall discuss some more advanced tactics which give us the ability to prove more with writing less, and the proofs will look more compact. -/

/-! Tactic __`assumption`__ 

The `assumption` tactic looks through the assumptions in the context of the current goal, and if there is one matching the conclusion, it applies that asssumption. Here is an example:
-/

example (hp : P) (hqr : Q ∧ R) : 
  P ∧ Q ∧ R := 
by 
  constructor 
  assumption -- to prove `P` we use `hp` from the assumptions. 
  assumption -- to prove `Q ∧ R` we use `hqr` from the assumptions. 


-- We use `repeat {assumption}` instead of many instances of `exact`.

example (hp : P) (hqr : Q ∧ R) : 
  P ∧ Q ∧ R := 
by 
  constructor 
  repeat{assumption}


example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
by
  constructor -- we split the proof into two proofs: first we prove `(P ∧ Q)` and then `(P ∧ R)`
  · constructor -- to prove `P ∧ Q` we first prove `P` and then `Q`; another split!
    repeat{assumption} -- `P` and `Q` are assumed to be true
  · constructor --to prove `P ∧ R` we first prove `P` and then `R`; another split!
    repeat{assumption}  -- `P` and `R` are assumed to be true



/-! __Concataneation of tactics with `<;>`__

Let's make the proof above even more compact using concataneation of tactics with `<;>` : the command 
` tac1 <;> tac2 ` 
runs tactic `tac1` on the main goal and tactic `tac2` on each produced goal, concatenating all goals produced by `tac2`.
-/ 

example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
by
  constructor <;> constructor <;> assumption



/-! ### Tactic `rintro` 

`rintro` tactic is a combination of the `intros` tactic with `rcases` to allow for destructuring patterns while introducing variables. For example,
`rintro ⟨hp, hp | hr⟩` below matches the subgoal `P ∧ (Q ∨ R)` and introduces the new hypothesis `hp : P` and breaks the Or `Q ∨ R` into two left and right sub-goals each with
hypothesis `hq : Q` and `hr : R`.

Notice here that you can use a semi-colon to separate multiple tactics on the same line. Again we take advanatage of concatenation tactic: Note that `constructor` produces two sub-goals we need 2 `assumption`, but isntead of `left; constructor; assumption; assumption` tactics we just write `<;> assumption` which runs `assumption` on both sub-goals.
-/ 

-- For propositions `P`, `Q` and `R` we have `P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R).`

lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · rintro ⟨hp, hq | hr⟩
    left; constructor <;> assumption
    right; constructor <;> assumption   
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · constructor; assumption; left; assumption
    · constructor; assumption; right; assumption



/-! ### Tactic `suffices` 
this is very much like apply; it changes the goal to the assumption of the implication. See the examples below: 
-/

example 
  : (P → Q) → (¬Q → ¬P) := 
by 
  intros hpq hnq hp
  suffices hq : Q from hnq hq -- `suffieces` says that we only need to prove `hq : Q` becasue once we do that we can apply `hnq : ¬Q` to `hq` to get a proof of `False`. 
  apply hpq
  exact hp

-- Another example of `suffices`
example : 
  P → (Q ∧ R) → P ∧ Q := 
by
  rintro hp ⟨hq , hr⟩
  suffices hq : Q from ⟨hp , hq⟩
  exact hq



