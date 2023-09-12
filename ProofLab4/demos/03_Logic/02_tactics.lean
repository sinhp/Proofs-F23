/- 
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4


/-! ### Equality and rw -/

example (x y z : ℕ) (h₁ : x = 2) (h₂ : 2 + x = y) (h₃ : z = x + 2): 
  x + z = x + y := 
by
  sorry 
  --rw [h₃] -- this changes the goal by replacing `z` with `x + 2`
  --sorry
  --rw [h₁]
  




/-! ### Conjunction (∧) -/

example (hp : P) : 
  P ∧ P := 
by 
  constructor
  assumption'


example (P Q R : Prop) (hp : P ∧ Q) (h : Q ∧ R) : 
  P ∧ R := 
sorry 




/-! ### Disjunction (∨) -/

/- 
Proving that `(P ∨ Q) → (Q ∨ P)` involves an element of danger. `intro h` is the obvious start. But now, even though the goal is a disjunction, both `left` and `right` put you in a situation with an impossible goal.
-/ 

example (P Q : Prop) : P ∨ Q → Q ∨ P := 
by
  intro h
  left 
  sorry -- we got stuck.  

/-
 Fortunately, after `intro h` we can eliminate the `h`, a proof of a disjunction. This we do by `cases h with`. The `cases` tactic turns one goal into two, one for each case. Each branch is easy to solve
using the `left` and `right` tactics. 
-/ 
example (P Q : Prop) : P ∨ Q → Q ∨ P := 
by
  intro h
  cases' h with hp hq 
  · right 
    exact hp 
  · left
    exact hq 



/- 
We can make the variables `x : ℤ` implicit by putting it between curly brackets `{` `}` instead of the usual round ones which treats `x` explicit argument. -/
example {x : ℤ} (h : x = 1 ∨ x = -1) : 
  x^2 = 1 := 
by
  cases' h with h₁ h₂
  · rw [h₁]; rfl
  · rw [h₂]; rfl 


-- Use the lemma `eq_zero_or_eq_zero_of_mul_eq_zero` to prove the converse. 
section 
variable (m n : ℕ) (h : m * n = 0)
#check eq_zero_or_eq_zero_of_mul_eq_zero h
end 


example {x : ℤ} (h : x^2 = 1) : 
  x = 1 ∨ x = -1 :=
by 
  sorry 





/-! ### Negation -/

/- We proved the proposition `(P → Q) → (¬Q → ¬P)` in term-mode. Construct a tactic-mode proof of it. -/
--#check proof_by_contrapositive

example 
  (P Q : Prop) : (P → Q) → (¬Q → ¬P) := 
by 
  sorry 


section 
variable (a b : ℝ)
#check (mul_comm : ∀ (a b : ℝ), a * b = b * a)
#check (two_mul : ∀ (a: ℝ),  2 * a = a + a)

#check mul_two

#check (mul_comm a b : a * b = b * a)
#check (two_mul a : 2 * a = a + a)
end 

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
by 
  constructor 
  · exact h₀
  · intro h 
    rw[h] at h₁ 
    apply h₁
    rfl 

-- here's a shorter proof which uses term-mode: 

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : 
  x ≤ y ∧ x ≠ y :=
⟨h₀, fun h => h₁ (by rw [h])⟩



/-! ### Tactic `have` -/

-- replace `sorry`s with appropriate terms to complete the proof below. 
example (P Q : Prop) : 
  (P → Q) → (¬ Q → ¬P) := 
by 
  intro hpq
  intro hnq
  intro hp
  have hq : Q := sorry
  have f : False := sorry
  exact f     




/-! ### Tactic `apply` -/

-- replace `sorry` with an appropriate term and uncomment the last line to complete the proof below.  
example (P Q : Prop) : 
  (P → Q) → (¬ Q → ¬P) := 
by 
  intro hpq 
  intro hnq 
  intro hnp 
  apply sorry
  --exact hpq hnp



-- De Morgan Laws

/-
The implications 
¬ P ∨ ¬ Q → ¬ (P ∧ Q)
¬ P ∧ ¬ Q → ¬ (P ∨ Q)
¬ (P ∨ Q) → ¬ P ∧ ¬ Q 
are all constructively valid.
-/

theorem deMorgin 
(P Q :Prop): ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := 
begin 
intro hnpq,
cases hnpq, 
{intro hpq,
have hp, from and.left hpq, 
have this, from hnpq hp, 
exact this,
}, 
{
intro hpq, 
have hq, from and.right hpq,
have this, from hnpq hq,
exact this,  
},
end   


theorem deMorgout 
(P Q : Prop) : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := 
begin
  intro u, 
  intro v, 
  cases v, 
  {show false, from u.left v, },
  {show false, from u.right v, },
end   

theorem deMorgan
(P Q :Prop): ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := 
begin 
sorry
end  


theorem deMorgan_classical 
(P Q : Prop): ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := 
begin 
intro h,  
cases em P with hp hnp ,
{have hnq: ¬ Q, from (assume hq : Q, h (and.intro hp hq)), 
exact or.inr hnq,
},
{sorry}, 
end  



/- 
Prove 
¬ (P ∧ Q) → ¬ P ∨ ¬ Q by replacing the sorry's below by proofs.
-/
section deMorgan_classical
open classical
variables {P Q : Prop} 
lemma step₁ (h₁ : ¬ (P ∧ Q)) (hp : P) : ¬ P ∨ ¬ Q :=
have ¬ Q, from assume hq :Q, h₁ (and.intro hp hq),
show ¬ P ∨ ¬ Q, from or.inr this

lemma step₂ (h₁ : ¬ (P ∧ Q) ) (h₂ : ¬ (¬ P ∨ ¬ Q)) : false :=
have ¬ P, from
  assume : P,
  have ¬ P ∨ ¬ Q, from step₁ h₁ ‹P›,
  show false, from h₂ this,
show false, from h₂ (or.inl this) 

theorem step₃ (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q :=
by_contradiction
  (assume h' : ¬ (¬ P ∨ ¬ Q),
    show false, from step₂ h h')
end deMorgan_classical    




lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  intro h
  intro p
  by_cases q : Q
  exact q
  have np := h q
  contradiction



/- Challenge -/
example (x y z : ℕ) (h : ¬ x * y * z < 0) : 
  (0 ≤ x) ∨ (0 ≤ y) ∨ (0 ≤ z) := 
by 
  sorry   