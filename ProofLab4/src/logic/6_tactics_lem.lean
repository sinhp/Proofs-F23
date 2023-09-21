/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Real.Basic

/-! # Classical Logic 

The __law of Excluded Middle__ says that for every proposition `P`, either `P ∨ ¬P` is true. To many people this is a self-evident truth. For instance, Aristotle assumed it to be self-evident, although he did not explicitly give a name to this principle. However, given the rules of inference (the intro/elim rules) we have learned so far you cannot prove `P ∨ ¬P` no matter how hard you try! 

Note: In Latin, the law of Excluded Middle is called _tertium non datur_ (“no third possibility is given”), and sometimes, principium tertii exclusi (“the principle of excluded third”). We shall use the abbreviation LEM for the Law of Excluded Middle.

Intuitionist and constructive mathematicians reject LEM. The 20-th century Dutch mathematician L.E.J. Brouwer proposed that the law of Excluded Middle should not be regarded as an admissible logical principle, and he had serious doubts concerning the truth of this law. In Brouwer’s view, the law of Excluded Middle is an instance of a hasty and ultimately wrong generalization of logic of finite mathematics to the logic of infinite mathematics.

But note that this does not mean intuitionists admit the negation of LEM as a logical principle! The sense in which LEM is rejected is more subtle and we will know more about it as we progress. Note that no matter how hard we try, we fail to construct, for every proposition `P`, a proof of `P ∨ ¬P` using the intuitionistic rules of inference we have learnt. In fact, it can be proven that `P ∨ ¬P` cannot be proven in the intuitionistic logic, but for this we need more advanced tools such as the Kripke semantics (aka many-world semantics) of propositional logic, and the fact that it is a complete semantics, which is beyond the scope of this short lesson.
-/


/- 
Constructively, every proposition implies its __double negation__.
-/
example :
  P → ¬¬ P :=
by 
  intros hp hnp 
  apply hnp 
  exact hp

/-
However, the converse implication is not constructively valid, we need to use the LEM.  
-/

theorem em_implies_dn : (P ∨ ¬P) → ¬¬P → P:= 
by 
  rintro (hp | hnp) dnp 
  · exact hp
  · exfalso; apply dnp; exact hnp 


example : ¬ ¬ P → P := 
by 
  intro h
  push_neg at h
  trivial



/-! ## Other derived classical principles of reasoning -/

--Proof by contrapositive---

/-
In `logic.one` and `logic.two` We saw this already that constuctively we can prove the forumla 
`(P → Q) → (¬ Q → ¬P)` for all propositions `P` and `Q`. 

But the converse implication can only be proved using the law of Excluded Middle. Therefore, the proof below is classical. 
-/

lemma proof_by_contrapositive_classical
{P Q : Prop} : (¬ Q → ¬ P) →  P → Q := 
by
  intros h hp -- we start with the usual`intros` to turn the implication into hypotheses `h : ¬ Q → ¬ P` and `hp : P` which leaves us with the goal of `⊢ Q`.  But how can you prove `Q` using these hypotheses?
  by_cases emq : Q -- Here we use LEM: `by_cases hq` creates two sub-goals `pos` and `neg` with the first one assuming `Q` is true - which can easily satisfy the goal! and the second one assuming Q is false.
  · assumption  
  · exfalso; apply h emq; exact hp