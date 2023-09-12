/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LeftRight


/-!
# Logic of Propositions: Proofs with Tactics 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


/-! ## Proofs with tactics

- There is another way of writing of proofs which is closer to how mathematicians write their proofs in maths books and journal papers. For instance, you might have seen a proof being written in the following style: "To prove the _forward direction_, first _unfold_ the definition. Suppose `x` is an arbitray blah which satisfy the property blah blah. By definition there is some `y` which satisfies the property blah blah blah. Now, _apply_ the previous lemma to `y`, and _specialize_ the result to when `y` is `y₀`."

- These are __instructions__ given by the author to the reader for finding find the relevant proof that the author has in mind. In a similar way, tactics are instructions that we tell proof assistants (in our case Lean) to construct a proof term. __Tactics__ are like cooking recipes for making a dish while the __term proofs__ are the food. 

- The point of tactics -- and this point becomes clear after the third lecture -- is when we are faced with constructing a complicated proof, we can break down the process into __multiple intermediary easier goals__ which we know how to solve. This is such a crucial technique not only in Lean but in all of mathematics. And while we are constructing these smaller proofs to be later composed, we interact with Lean to see the result of our instructions.

- Like informal proofs, proof tactics support an incremental style of writing proofs, in which you unfold a proof and work on goals one step at a time.

- A general form of an `example` in __tactic style__: 

example (context_of_our_assumptions) : 
  statement_we_wanna_prove := 
by
  tactic_1 [...] 
  tactic_2 [...] 
  ⋮ 
  tactic_n [...]

Note that the keyword `by` indicates the start of the proof: It tells Lean whatever that follows is supposed to be a proof of the proposition we are trying to prove. 


**Note**: Even if we prove a theorem in tactic mode, what is __stored__ in Lean is the __proof term__ corresponding to this tactic proof. Lean has an automatic way of converting a tactic proof to a term proof and we usually do not see this unless we use the command `show_term`. 
-/


/-
TL;DR: 
A proof term is a representation of a mathematical proof; tactics are commands, or instructions, that describe how to build such a proof. 
-/

/-! ### Tactic refl
The equality symbol `=` is meant to formalize what we mean when we say “something is the same as something else” (e.g. “ascorbic acid is vitamin C” or “5+7=12” ). We are asserting that two different descriptions refer to the same object. Since the notion of equality is very general and can be applied to virtually any domain of discourse, it is falling under the purview of logic.

We have seen that expressions like `s = t` are examples of atomic propositions. The simplest way to prove such propositions are to use the __reflexitivity__ of equality relation. 
-- `rfl` is a __tactic__ corresponding to reflexitivity of equality relation. This will be able to prove statements that are true direclty from unfolding the definitions of terms, types, and operations involved in the statement and nothing else. 
-/

example : 
  3 = 1 + 2 :=
by 
  rfl 
  

example (a b c d : ℕ) : 
  (a + b) * (c + d) = (a + b) * (c + d) := 
by    
  rfl  



example : 
  2 + 3 = 5 := 
by 
  rfl


example : (0 : ℕ) + (0 : ℕ) = (0 : ℕ) := 
-- experiment with changing the first/last ℕ to ℤ 
by 
  rfl 


example (x : ℕ) : 
  x + 0 = x :=
by 
 rfl



/-! ### Tactic exact 
`exact` tactic allows to provide direct proof terms. If the goal is ` ⊢ X ` then `exact hp` will close the goal if and only if `hp : X`.
-/ 

-- For the expert: 
-- Comment out the below lines to see various other ways that lean can display info: 
--set_option pp.notation false

example (h : 2 + 2 = 5) : 
  2 + 2 = 5 :=
  -- The goal is to construct a proof of ` 2 + 2 = 5 `. We already have this. 
by
  exact h -- this is like copying; we copy `h` from the local context of our hypotheses. 



/-! ### Tactic rewrite 

We saw that `rfl` introduces the proof of definitional equalities. But how can we use the proofs of equalities, i.e. how do we substitute one term for its equal counterpart? Substitution is the fundamental property of equality: 
  
  If two terms denote the same thing, then we should be able to substitute one for any other in any expression: Let's say `E` is an expression containing `a` somewhere: `E = ... a ...`.
  Suppose `a'` is another term. Write `E'` for the result of substituting `a'` for `a` every instance of `a` in `E`. If ` a = a' ` then `E = E'`  

  Example: if `x = y` then `2 + x * x  = 2 + y * y`. 

  The operation of substitution is called rewriting, and the Lean "tactic" for this is `rw`.

-/


example (m n : ℕ) (h₁ : m + 1 = 7) (h₂ : n = m) : 
  n + 1 = 7 := 
by
  -- we want to prove that `n + 1 = 7`. Since we know that `n = m` we need to replace `n` by `m` in the goal. Then we use hypothesis `h₁`. 
  rw [h₂] -- replaces `n` by `m` in the goal.
  exact h₁ -- use the hypothesis `h₁` to finish the proof.


example (x y : ℕ) (h : x = y) : 
  x + 0 = y + 0 := 
by  
  rw [h]   


-- Transitivity of equality via `rw`
lemma transitivity_of_equality (x y z : ℝ) (h₁ : x = y) (h₂ : y = z) : 
  x = z := 
by
  rw [h₁] -- changes the goal `x = z` to `y = z` by replacing `x` with `y` in virtue of `h₁`. 
  -- all we need to prove now is `y = z` which we do by `h₂`.  
  exact h₂

#check Eq.trans -- already in Lean's MathLib


-- Symmetry of equality via `rw`
lemma symmetry_of_equality (x y :  ℝ) (h₁ : x = y) : 
  y = x := 
by 
  rw [h₁] 


#check Eq.symm


section 
variable (A : Type) (a b c : A) (h₁ : a = b) (h₂ : b = c)
#check h₁.symm 
#check h₁.trans h₂ -- shorthand for `Eq.trans h₁ h₂`
end 


example (x y : ℕ) (h₁ : x = 0) (h₂ : y = 0) :
  x + y = 0 := 
by 
  rw [h₁] -- Uses the hypothesis h₁ : x = 0 to change all x's to 0's in the goal.
  rw [h₂] -- Uses the hypothesis h₂ : y = 0 to change all y's to 0's in the goal.
  -- 0 + 0 = 0 is done  

-- a more compact form; sequential rewriting
example (x y : ℕ) (h₁ : x = 0) (h₂ : y = 0) :
  x + y = 0 := 
by 
  rw [h₁, h₂] 

 



/-! #### Variants of rewrite tactic-/

/- 
We already have seen the simple version of the rewrite tactic: 
1. `rw [h₁]` (rewrites `h₁` in the current goal)

We now see some useful variants of `rw` tactic: 
2. `rw [← h₁]` (backward rewrite)
3. `rw [h₁] at h₂` (rewrites hypothesis `h₁` in the hypothesis `h₂`)
4. `rw [← h₁] at h₂` (backward rewrites hypothesis `h₁` in the hypothesis `h₂`)
5. `rw [h] at *` (rewrites hypothesis `h` everywhere)
-/

/- Rewrite in the opposite direction-/
example (m n : ℕ) (h₁ : m + 1 = 7) (h₂ : m = n) : 
  n + 1 = 7 := 
by
-- we want to prove that `n + 1 = 7`. Since, by `h₂` we know that `m = n` we need to replace `n` by `m` in the goal. However, for this we need to use `h₂` in the opposite direction of `h₂`. Then we use the hypothesis `h₁`. 
  rw [← h₂]
  exact h₁


example (x : ℕ) (h₁ : 5 = 2 + x) (h₂ : 2 + x = 40) : 
  5 = 40 :=
   
by 
 rw [h₂] at h₁ -- we substitute `2 + x` in `h₁` for `4` because of h₂.
 exact h₁


/-
`rw h at *` rewrites `h` everywhere, in the goal and all hypotheses.
-/

example (x y z : ℕ) (h₁ : x = 2) (h₂ : 2 + x = y) (h₃ : z = x + 2): 
  x + z = x + y := 
by
  rw [h₁] at * 
  rw [h₃]
  rw [h₂]





/-! ### Tactic change -/

/- If we tweak our assumptions a little bit as follows, we are not able to directly use `rw` anymore.  -/
example (x y z : ℕ)
  (h₁ : x + 0 = y) (h₂ : y = z) : x = z :=
by 
--  rw h₁, -- fails because rw works up to syntactic equality
  change x = y at h₁ -- change works up to _definitional_ equality
  rw [h₁] -- now it works
  exact h₂ 



/-! ### Tactic constructor : ∧-Intro
If the main goal's target type is `⊢ P ∧ Q` the tactic `constructor` finds the matching constructor `And.intro`
which has 2 parameters, so it solves the goal with two sub-goals, namely `⊢ P` and `⊢ Q`.

If your *goal* is `P ∧ Q` then you can make progress with the `constructor` tactic which turns one goal `⊢ P ∧ Q` into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a `constructor`, you can finish off the two new sub-goals with the `exact` tactic since both `hp` and `hq` provide exactly what we need. 
-/

-- If `P` and `Q` are true, then `P ∧ Q` is true.
example (hp : P) (hq : Q) : P ∧ Q := 
by
  constructor
  · exact hp -- type · with `\.`. This indicates we are focusing on the first subgoal first and ignore the second subgoal for a moment. 
  · exact hq
 
  
-- introduction example
example (hp : P) : 
  P ∧ P := 
by 
  constructor 
  · exact hp 
  · exact hp  

-- introduction example  
example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
by 
  constructor 
  · constructor 
    . exact hp 
    . exact hq 
  · constructor 
    . exact hp 
    . exact hr 

  


/-! ### Tactic cases : ∧-Elim

We use the tactic __cases__ in order to use a proof of `P ∧ Q` in the assumption in order to prove some other proposition. The tactic `cases` replaces `h : P ∧ Q` by a pair of assumptions, `hp : P` and `hq : Q`. 
-/



/-
In the example below  `hpq : P ∧ Q` is a hypothesis, and we can extract the parts of this `And.intro` using the [`cases` tactic](../Tactics/cases.lean.md)

`cases h with`

This will give us two hypotheses `p` and `q` proving `P` and `Q` respectively.  So we hold onto
these, the goal is now `⊢ Q ∧ P` which we can split using the `constructor` tactic, then we can
easily pick off the two sub-goals `⊢ Q` and  `⊢ P` using `q` and `p` respectively.
-/

-- Suppose `P ∧ Q` is a true proposition. Then so is `Q ∧ P`.
example (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro hp hq =>
    constructor
    · exact hq
    · exact hp

-- The variant ` case' ` is similar to `cases` except we do not need `| ` and `intro`  
example (h : P ∧ Q ∧ R) : 
  Q ∧ R ∧ P := 
by 
  cases' h with hp hq 
  constructor 
  · exact hq.left  
  · constructor 
    · exact hq.right 
    · exact hp    




/-!  ### Tactic `apply` for implication elimination

Suppose you have the goal `⊢ Q` and you have the hypothesis
`h : P → Q`. If we have a proof `hp : P` then `h hp` is a proof of `Q` and we are done. However, in backward reasoning, we would say that since we know `P → Q` is true then in order to know `Q` is true we need to know `P` is true. 

`apply h` will construct the path backwards, moving the goal from  `Q` to  `P`. Imagine going upwards from the root (bottom) of the tree below:
          .
          .
          .
        -----
  P → Q   P 
------------- (→ elim)
      Q

-/

example (hpq : P → Q) (hqr : Q → R) (hp : P) : R :=
by 

  apply hqr -- We prove `R` using backward reasoning as follows. To prove `R`, by hypothesis `hqr` it suffices to prove `Q`. 
  -- The goal is now Q`.
  apply hpq -- To prove `Q`, by hypothesis `hpq` it suffices to prove `P`.  
  exact hp -- To prove `P` we use assumption `hp`. 


/- 
If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
two goals! Note that tactics operate on only the first goal.
-/
example : (P → Q → R) → (P → Q) → (P → R) := 
by
  intros hPQR hPQ hP
  apply hPQR
  · exact hP 
  · apply hPQ
    exact hP


-- We are trying to prove that "if P then if not P then false"
example : 
  P → ¬P → False := 
by
  intro hp -- we want to prove the implication `P → (¬P → False)`, therefore we use the implication introduction rule. 
  intro hnp -- we want to prove the implication `¬P → False`, therefore we again use the implication introduction rule. 
  apply hnp        -- we have a proof of ¬P, so we use the elimination for negation to construct a proof of false.
  exact hp


example : 
  (P ∧ ¬ Q) → ¬ (P → Q) := 
by
  intro hpnq-- we are trying to prove the implication (P ∧ ¬ Q) → (¬ (P → Q))
  intro hpq -- we want to prove  the negation ¬ (P → Q), so we use the intro rule for negation 
  cases' hpnq with hp hnq -- we eliminate the conjunction `P ∧ ¬ Q`
  apply hnq  -- we use the elim rule for `¬ Q` to change the goal from false to Q
  apply hpq --we use the elim rule for `P → Q` after which we just need to prove `P`.  
  exact hp




/-! ## Tactics `left` and `right` for disjunction introduction

- Tactic for disjunction introduction:  We use the tactic __left__ or __right__ in order to prove a propositional formula of the form `P ∨ Q`. 


      P
   -------- ∨-intro-left 
    P ∨ Q
 


      Q
   -------- ∨-intro-right
     P ∨ Q


- If `⊢ P ∨ Q` is our goal, then `left` changes this goal to `⊢ P`, and `right` changes it to `⊢ Q`. 
-/


-- introduction example 
example (hq : Q) : 
  P ∨ Q ∨ ¬ P :=
by 
  right
  left 
  exact hq

-- introduction example 
example (P Q : Prop) : Q → (P ∨ Q) := by
  intro hq
  right
  exact hq

-- ∧-elimination and ∨-introduction 
example (h : P ∧ Q) : 
  P ∨ Q :=
by
  left 
  exact h.left




/-! ## Tactic  `cases` for disjunction elimination

We use the tactic ` cases' ` in order to use a proof of `P ∨ Q` to prove some other proposition. Again here is the tree representation of the derivation of an arbitrary proposition `R` from a proof of `P ∨ Q`.  

  P ∨ Q     P        Q
            .        .
            .        .
            .        . 
            R        R
----------------------------
            R   

`cases' h with hp hq` gives customary name to the branches of a disjunction: in the first branch we have `hp : P` as our assumption and in the second  branch we have `hq : Q` as our assumption. A derivation of `R` from `P ∨ Q` is complete when both branches have complete proofs.                   
-/

lemma or_symm_alt (h : P ∨ Q) : Q ∨ P := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq 
  
 


/-! ### Tactic `exfalso` 

In lecture logic.zero we prove the lemma `false_elim` which states that `False` implies any proposition `P` using the elimination principle of `False`.  There is a tactic for this: `exfalso` changes any goal at all to `False`. 
-/


example : 
  P ∧ ¬ P → Q :=
by 
  intro hpnp-- we want to prove the implication `(P ∧ ¬ P) → Q`, so we use the intro rule of implication
  exfalso -- the backward elimination of `False`. This means from a proof of `False` everything follows. 
  cases' hpnp with hp hnp 
  apply hnp 
  exact hp



/-! ### Tactic __`contradiction` 

A __contradiction__ is a collection of propositions which together lead an absuridty, i.e. a proof of `False`. For instance if we have a proof of a proposition `P` and a proof of `¬ P` then we can prove `False` as seen in the above exmaple. In virute of this, we say `¬ P` contradicts `P`. 

The `contradiction` tactic searches for a contradiction among the assumptions of the current goal. 
-/

example : 
  P ∧ ¬ P → Q :=
by
  intro h
  cases h 
  contradiction


