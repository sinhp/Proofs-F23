/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Logic of Predicates 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2023  
-/


import Mathlib.Tactic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Linarith

import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic

/- # Goals of this lecture: 
1. Parsing quantifiers and reading their scope correctly.
2. Identify startegies for proving a quantified sentence in mathematics based on its logical structure.
3. Do the above using interactive Lean tactics.  
-/


/-! ## Predicates  
__Predicates__ are varying propositions, that is they are propositions which depend on varibale(s) (parameters) from a __domain__ of discourse on which are they are defined. Another name for predicate is __relation__. Depending on the context, we might choose one or the other. 

Suppose we want to express the idea of listing propositions
“2 is even”,
“4 is even”,
“6 is even”, etc.

This way, this is an impossible task to do in finite time. We cannot write infinite sentences in finite time/memory. Note that the information specified above is incomplete, nevertheless we got the idea since we understood the pattern: the next sentence in the list will be 
“8 is even”.

Frege showed us how to do this: 
let `E` be the predicate with the domain `ℕ` of natural numbers and let `Even n` be the proposition “n is even”. 

In Lean, we model predicates by functions into the type `Prop` of propositions. 

A __unary__ predicate `A` on a domain `X`, therefore, is a function `A : X → Prop`. You should think of the proposition `A x` as "property A" is holding of `x`. For instance `Even n` is the proposition that "n is even". 

Here `X` is said to be the __domain of discourse__ of `A` or simply the __domain__ of `A`. Note that `A`, upon taking a variables `x : X`, outputs a proposition `A x`. 
-/


variable (X : Type) (A B : X → Prop) -- predictes `A` and `B` on `X`

/- We can think of `A` and `B` as a _family_ of proposition in the sense that for each `x : X`, we get a proposition `A x`. -/

section 
variable (x y : X)
#check A x -- this is a proposition
#check A x → B y -- this is a proposition
end 


def is_even (n : ℕ) := 
∃ k : ℕ, n = 2 * k 

#check is_even 
#check is_even 0 -- the proposition `∃ k : ℕ, 0 = 2 * k` 
#check is_even 3 -- the proposition `∃ k : ℕ, 3 = 2 * k` 

#check Even -- in Mathlib defined at a more general level, not just for natural numbers. 

def is_odd (n : ℕ) := 
∃ k : ℕ, n = 2 * k + 1

#check is_odd




/-! ## Quantifiers 
__Quantifiers__ turn unary predicates into propositions by quantifying over their domain. -/


/-! ### Universal Quantifier (∀)
What makes first-order predicate logic powerful is that it allows us to make assertions using __quantifiers__. Consider the following statements:

  -  Every natural number is even or odd, but not both.
  -  If some natural number is even, then so is its square.

The words "every" and "some" are encoded into the logic with the symbols `∀` and `∃`, respectively and they come with their own inference rules. The symbol `∀` followed by a variable `x` encodes the phrase "for every x". In other words, it asserts that every value of `x` has the property that follows it. A complete formalization of the first sentence above is given by the formal sentence 

  `∀ n : ℕ, is_even n ∨ is_odd n ∧ ¬ (is_even n ∧ is_odd n)`. 

Similarly, a complete formal sentence of the second sentence above is given by

  `∀ n : ℕ, is_even n → is_even (n^2)`. 

  Once we know `n : ℕ` the following are propositions 
  - is_even (n)
  - is_even (n^2)
  - is_even (n) → is_even (n^2)
  - ∀ n : ℕ, is_even (n) → is_even (n^2)
-/




/-! ### Intro/Elim rules for ∀

The __introduction__ and __elimination__ rules of `∀` are similar to those of `→`. 

We start with the __introduction__ rule: Suppose `A : X → Prop` is a predicate. To prove the proposition `∀ x, A x`, we need to prove that for any given `x : X`, the proposition `A x` holds. This means we first fix an arbitrary element `x` of `X` and then show that `A x` holds. 
In Lean, we use the tactic __intro__ in order to do this. Here's a general pattern of construcing a proof of `∀ x, A x` where `sorry` has to be replaced by a correct proof term depending on `A`. 
-/ 
 

example : 
  ∀ x : X, x = x := 
by
  intro x -- we fix an arbitrary element `x` here. 
  rfl


example :
  ∀ n : ℕ, 0 ≤ n := 
by 
  intro n 
  exact Nat.zero_le n 


/-
The __elimination rule__ of `∀` says that given a predicate `A : X → Prop`, if we know that `∀ x, A x` (i.e. `A` holds for every term of `X`) holds then for any particular `t : X` we have that `A t` holds. In Lean, if we have a proof `h : ∀ x, A x` and a term `t : X` then we simply apply `h` to the term `t` to get a proof `h t : A t`. This is sometimes refered to as __specializing__ the proof `h` to `t`.  
-/

section forall_elim

variable (h : ∀ x, A x)
variable (t : X) -- `X` is the domain of discourse of `A : X → Prop`

-- specialize `h` to `t`
example : A t :=
-- we simply apply `h` to `a`
show A t from h t

end forall_elim


-- an example of two eliminations and one introduction of ∀ 
example : 
  (∀ x, A x) → (∀ x, B x) → (∀ x, A x ∧ B x) :=
by
  intros ha hb -- intros for →  
  intro x -- intro for ∀ 
  constructor 
  · exact ha x -- elim for ∀ x, A x
  · exact hb x --elim for ∀ x, B x


theorem forall_impl : 
  (∀ x : X, A x → B x) → (∀ x, A x) → (∀ x, B x) := 
by 
  intros hab ha  
  intro x
  have h₁ : A x := ha x
  have h₂ : A x → B x := hab x
  exact h₂ h₁ 


  
/-! ## Existential Quantifier (∃)

The __existential quantifier__ in logic encodes the phrase “there exists”. The formal expression `∃ x : ℕ, x ^ 2 = 9` says that there is a natural number whose square equals `9`. 
-/

/-! ### Intro rules for ∃ 

The canonical way to prove an existentially-quantified statement such as 
`∃ x : ℕ, x ^ 2 = 9`
is to exhibit a natural number and show that it has the stated property. The number `3` has the required property, and the `rfl` tactic can prove that it meets the stated property. 

__How to prove an `∃`-statement__: In Lean, in order to prove a statement of the form `∃ x, P x`, we exhibit some `a` using the tactic `use a` and then prove `P a` by other means. Sometimes, this `a` can be an object from the local context or a more complicated expression built from the stuff of the context.

t : X   ht : P (t)
----------------- (intro rule for ∃)
∃ x, P(x)

-/

example : 
  ∃ x : ℕ, x ^ 2 = 9 := 
by 
  use 3 -- we want to prove `∃ x : ℕ, x ^ 2 = 9`. So, we use the intro rule of `∃`. Our candidate is 3.   
  rfl  


example : 
  ∃ x : ℚ, 2 < x ∧ x < 3 :=
by 
  use (7 / 3 : ℚ) 
  norm_num -- what does norm_num do? 


-- term mode proof 
example : 
∃ x : ℚ , 2 < x ∧ x < 3 :=
⟨7 / 3, by norm_num⟩


example :
  is_even 10 := 
by
  unfold is_even
  use 5 


example : 
  ∃ n , is_even n :=
by 
  unfold is_even
  use 4 -- picking `3` would be unwise, since `is_even 3` would be impossible to prove.
  use 2 -- This time we have no choice but to pick `2`.


example {X Y : Type} (f : X → Y) (t : X): 
  ∃ y : Y, ∃ x : X, f x = y := 
by 
  use f t -- we ae trying to prove `∃ y : Y, ∃ x : X, f x = y`, and for this we use the intro rule of existential quantifier. Our candidate for the intro rule is `t`. We now have to prove the property `∃ x : X, f x = y`  about `y := f t`
  use t -- we ae trying to prove `∃ (x : X), f x = f t` and for this we use the intro rule of existential quantifier. Our candidate for the intro rule is `t`. 



/-! ### Elimination rule for ∃ 

we know how to prove an exists statement. But how do we use one? 


              
When __using__ a proof of a statement of the form `∃ x : X, P x`, we can assume having `t : X` such that `P t` is true. If from a general `t` and a proof of `P t` we can prove `R` then we can prove `R` from `∃ x, P x`.

               ----₁ 
               P(t)
               ---
                .
                .
                .
               ---
∃ x, P(x)      R
----------------------₁ ∃-elim  
          R

The corresponding Lean tactic is `cases ... with ...`. 
-/


#check (Nat.succ_pos : ∀ (n : ℕ), 0 < n + 1)
#check (lt_irrefl)

lemma nonzero_of_succ (x : ℕ) : 
  (∃ y : ℕ, y + 1 = x) → (x ≠ 0) :=
by 
  intros h₁ h₂ 
  cases' h₁ with y hy -- the first use of `cases` for the elim rule of ∃
  have hy₁ : 0 < y + 1 := Nat.succ_pos y
  rw [h₂] at hy 
  rw [hy] at hy₁ 
  apply lt_irrefl 0
  assumption
  
 

example : 
  ∃ (y : ℝ), ∀ (x : ℝ), x^2 ≠ y := 
by 
  use -1 
  intro x 
  sorry 



example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := 
by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring  





