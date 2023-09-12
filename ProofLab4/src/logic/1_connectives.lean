
/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Mathlib.Data.Real.Basic


/-!
# Logic of Propositions : New Propositions from the Old
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2023   
-/


--- See  [theorem_proving_in_lean4](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)


variable {P Q R : Prop} -- let `P`, `Q` and `R` be propositions. --  P and Q are accessible throughout the entire file,

/- 
Lean's "check" command tells us 
the type of the object we have constructd. 
-/

#check P 
#check P ∧ Q -- conjunction (and)
#check P → Q -- implication (if ... then ...)
#check P ∨ Q -- disjunction (or)
#check ¬ P -- negation (not the case)


/-
Using simple (aka __atomic__) propositions such as 

S1. “The sun is shining” and 
S2. “It is raining”,  

we can form the __compound__ proposition 

S3. “The sun is shining _and_ It is raining”.

S3 is of the form `S1 ∧ S2`. 

By combining propositin using connectives we construct more complicated propositions from simple propositions. This required us to first unquote the sentences, insert an “and” and then put a quote around the resulting sentence. We call a compound proposition (such as “The sun is shining and It is raining”) a __propositional formula__. 

In this way, we can make new propositions from old propositions using __connectives__ (such as `∧`, `→`, `∨`). For each connective, we specify a __rule__  (the so-called introduction rule) to __introduce__ a proof of the compound proposition using that connective and a rule (the so-called elimination rule) to __use__ or ___eliminate__   such a proof.

In below we shall introduce the connectives `∧`, `∨`, `→`, and `¬`, and give their introduction and elimination rules.  


- `∧` has one introduction rule and two elimination rules.  
- `∨` has two introduction rules, and one elimination rule. 
- `→` has one introduction rule, and one elimination rule. 
- `¬` is defined using `→`: its introduction and elimination rules are similar to those of `→`. 
-/



/-! ### Conjunction (∧) 

Conjunction Introduction: 

    P   Q
   -------- ∧-intro
    P ∧ Q 

The canonical way to construct a proof of `P ∧ Q` is to apply `And.intro` to suitable proofs `hp : p` and `hq : q`


Conjunction Elimination: 

    P ∧ Q
   -------- ∧-elim_left
      P 

    P ∧ Q
   -------- ∧-elim_right
      Q 

 What if `hpq : P ∧ Q` is a hypothesis, and we want to use it. Then by the rules above we decompose `hpq` into `hpq.left : P ` and `hpq.right : Q` to get proofs of `P` and `Q` respectively. 
-/


-- introduction example
example (hp : P) : 
  P ∧ P := 
And.intro hp hp


-- introduction example  
example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
sorry 


-- elimination example 
example (hpq : P ∧ Q) : 
  P := 
hpq.left


-- elimination example 
example (hpq : P ∧ Q) : 
  Q := 
hpq.right


/- 
The following is an example of use of both intro and elim rules: We need the intro rule to construct a proof of `Q ∧ P` and we need elim rule to be able to use `h : P ∧ Q` 
-/

lemma and_symm (h : P ∧ Q) : 
  Q ∧ P := 
And.intro h.right h.left

#check and_symm


example (h : P ∧ Q ∧ R) : 
  Q ∧ R ∧ P := 
And.intro h.right.left (And.intro h.right.right h.left)


-- `h.1` is an abbreviation for `h.left` and `h.2` is an abbreviation for  `h.right`
example (h : P ∧ Q ∧ R) : 
  Q ∧ R ∧ P := 
And.intro h.2.1 (And.intro h.2.2 h.1)


example (h : P ∧ Q ∧ R) : 
  Q ∧ P ∧ R := 
sorry 


example (h : P ∧ Q) : 
  Q ∧ P ∧ Q := 
sorry


/- 
__Tip__: 
If there are no red underlines anywhere then your proof is correct. Sometimes the red underlines are very small, so look closely. You can double check by consulting the horizontal blue status line at the bottom of the screen in VS Code. Next to the symbol “⊗” is a number indicating how many mistakes are in the file, and if there are no mistakes, there will also be a check mark.
-/



/-! ### Implication (→) 

The implication `P → Q` is a new proposition built from `P` and `Q` and we read it as __“if P then Q”__.


You can get the implication arrow, similar to functions, by typing `\to` or `\imp` or `\r`. Mathematicians usually denote the implication by double arrow as `P ⇒ Q` but Lean prefers a single arrow.

Implicaiton __introduction__:

If under the assumption that `P` is true we can derive that `Q` is true, then we know that `P → Q` is true. Note that, in this process, we actually do not know whether P is true or not; all we know is that in case `P` holds, then so does `Q`. To assume `P` first we introduce a hypothetical proof `hp` of `P`, and we use `hp` to construct a proof of `Q`, and thereby show that `Q` holds under the assumption that `P` holds. 

    P
    .
    .
    .
    Q
--------- (→ intro)
  P → Q


Implication __elimination__: 
Application of a proof 
`h : P → Q`
to a proof 
`p : P`  
is achieved by the expression
`h p`  
that is `h` followed by `p`.

This is (like) function application.


  P → Q   P 
------------- (→ elim)
      Q

If `h` and `p` are compound expressions, we put brackets around them to make it clear where each one begins and ends. 
e.g. `h₁ h₂ h₃` is interpreted by Lean as `(h₁ h₂) h₃`.
-/


-- introduction example
lemma id_impl : 
  P → P := 
fun (hp : P) => hp

#check False
#check True
#check True.intro

 
example : 
  False → False := 
fun (hp : False) => hp


example : 
  False → True := 
fun (_ : False) => trivial


-- `→` intro ; `∧` elim ; `∧` intro 
example :
  P ∧ Q → Q ∧ P := 
fun hpq => And.intro hpq.2 hpq.1


-- intro for nested implications 
example : 
  P → Q → P :=
fun hp hq => hp


-- intro example 
example : 
  P → Q → P ∧ Q :=
fun hp hq => And.intro hp hq 


-- elimination example 
example (hpq : P → Q) (hqr : Q → R) (hp : P) : 
  R :=
hqr (hpq hp) -- note the brackets, without them Lean gives an error, since function application is by defauly left binding, i.e. without the brackets Lean interprets `hqr hpq hp` as `(hqr hpq) hp`. 


-- elimination example 
example (hpq : P → Q) (hqr : Q → R) (hp : P) : 
  R :=
hqr $ hpq hp 


example (hpq : P → Q) (hqr : Q → R) (hp : P) : 
  R :=
hp |> hpq |> hqr -- like Haskell pipelining 


-- Modus Ponens : elimination example 
lemma modus_ponens : 
  P → (P → Q) → Q := 
fun hp => fun hpq => hpq hp



-- Depenedent Modus Ponens
lemma dep_modus_ponens: 
  P → (P → P → Q) → Q :=
sorry 


example : 
  P → ¬ (P → ¬ P) := 
sorry 



/-
Transitivity of implications: If we know that  proposition P implies Q and Q implies R then we know that P implies R. 
-/

lemma transitivity_of_implication :
  (P → Q) → (Q → R) → P → R :=
sorry

example : 
  (P → (Q → R)) → (P ∧ Q → R) :=
sorry 


example : 
  (P ∧ Q → R) → P → Q → R := 
sorry   


/- we don't undertand the following proof yet; treat the lemmas as a blackbox.-/
lemma zero_neq_one : 
  (0 = 1) → False := 
fun h => by linarith

-- an example of implication introduction 
example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
fun impossible => False.elim (zero_neq_one impossible)




/-! ### Disjunction (∨) 

- `P ∨ Q` means __"P or Q"__. To prove `P ∨ Q`, we need to choose one of `P` or `Q`, and prove that one. 

If `⊢ P ∨ Q` is our goal, then 

- if we have a proof `hp : P`, then term `Or.inl hp` (short for `Or.intro_left`) proves `P ∨ Q`, i.e. `Or.inl hp : P ∨ Q`. 

- if we have a proof `hq : Q`, then term `Or.inr hq` (short for `Or.intro_right`) proves `P ∨ Q`, i.e. `Or.inr hq : P ∨ Q`. 

      P
   -------- ∨-intro-left 
    P ∨ Q
 


      Q
   -------- ∨-intro-right
     P ∨ Q

The elimination rule for disjunction (`∨`) is slightly more complicated. Let's think about it: suppose we know that `P ∨ Q` is true; of course this does not tell us which is the case: that we `P` is true or whether `Q` is true. All we know is that at least one of them is true. So, if we want to prove some other proposition `R` we should prove that `R` follows from `P` and that `R` follows from `Q`. In other words, it is a proof by cases. 


 P ∨ Q     P        Q
            .        .
            .        .
            .        . 
            R        R
----------------------------
            R

In the expression `Or.elim hpq hpr hqr`, the term `Or.elim` takes three arguments, `hpq : P ∨ Q`, `hpr : P → R` and `hqr : Q → R`, and produces a proof of `R`. 
-/ 
 

-- introduction example 
example (hp : P) : 
  Q ∨ P :=
Or.inr hp


-- introduction example 
example (hp : P) : 
  P ∨ Q ∨ ¬ P :=
Or.inl hp


-- introduction example
example (h : P ∧ Q) : 
  P ∨ Q :=
Or.inl h.left  


-- introduction example
example (h : P ∧ Q) : 
  P ∨ Q :=
Or.inr h.right



-- elimination example 
lemma or_symm (h : P ∨ Q) : Q ∨ P :=
  Or.elim h
    (fun hp : P =>
      show Q ∨ P from Or.inr hp)
    (fun hq : Q =>
      show Q ∨ P from Or.inl hq)


/-- we could have avoided using the command `show ... from ..,` `show` command does nothing more than annotate the type. However, it helps with the readability of the proof, since it shows what we are proving at each stage. -/

example (h : P ∨ Q) : Q ∨ P :=
  Or.elim h (fun hp : P => Or.inr hp) (fun hq : Q => Or.inl hq)




/-! ### Negation  

If we start with a propositon `P`, the negation `¬P` (aka "not P") is _defined_ by the formula `P → False`, which you can think of as saying that `P` implies something impossible (`False`). Therefore, if `¬ P` is the case, then `P` cannot be the case, since if `P` were the case, we would conclude that something false/impossible would be the case. 

The rules for negation are therefore similar to the rules for implication. To prove/introduce `¬P`, assume `P` and derive a contradiction `false` (i.e. construct a proof of proposition `false`).  An example of this is the proof of irrationality of root 2.
To eliminate `¬P`, given a proof of `P` and a proof of `¬ P` we get `false`. 
-/

example (h : P → False) : ¬ P := 
h

-- We are trying to prove that "if P then if not P then false"
example : P → ¬P → False := 
fun hp hnp => hnp hp
  
example : P ∧ ¬ P → False :=
fun hpnp => hpnp.2 hpnp.1


lemma proof_by_contrapositive : (P → Q) → (¬Q → ¬P) := 
fun h hnq hp => hnq (h hp)



/-! ### Biimplication, or otherwise known as If and Only If 
The biimplication ` ↔ ` is a derived connective which is derived form `→` and `∧`. For propositions `P` and `Q`, we write `P ↔ Q` for `(P → Q) ∧ (Q → P)`. Therefore `P ↔ Q = (P → Q) ∧ (Q → P)` by definition. And, as such, we can apply the tactic `split` to introduce a proof of `P ↔ Q` and `cases` to eliminate proofs of `P ↔ Q`.
-/

/-
**Note** The `constructor` tactic applies the unique constructor for conjunction, namely `and.intro`. 
-/



theorem conj_comm : P ∧ Q ↔ Q ∧ P :=
by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩




-- example : 
-- P ∧ Q ∧ R → R ∧ Q ∧ P := 
-- begin 
--     sorry, 
-- end 





-- lemma disj_comm {P Q : Prop} : 
--   P ∨ Q ↔ Q ∨ P :=
-- by  
--     constructor <;> intro h <;> exact kh.2 || h.1
  



--#check disj_comm
--#check disj_comm.mp -- extract the forward direction implication `P ∨ Q → Q ∨ P` from the proof `disj_comm` by using `.mp` notation.  
--#check disj_comm.mpr -- extract the converse implication `Q ∨ P → P ∨ Q` from the proof `disj_comm` by using `.mpr` notation.  



/- https://leanprover.github.io/functional_programming_in_lean/programs-proofs/arrays-termination.html#inequality-/



example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by linarith
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by linarith
