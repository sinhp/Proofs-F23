/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Mathlib.Data.Real.Basic


/-!
# Logic of Propositions: Basics
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2023   
-/


/- # Goals of this lecture: 
1. Understanding the rules of Intuitionistic Propositional Logic (IPC) 
2. Understanding the proposition-as-types paradigm and how Lean takes advanatage of this paradigm 
3. Construcitng term-style proofs of propositions. 
-/


/-! ## Propositions 

- Some types in Lean are __propositions__, i.e. assertions that can be judged to be true or false. A proposition is a type, a proof of proposition is a term of the corresponding type.  

- Every proposition is a type, but not every type is a proposition, e.g. `ℕ`. 

- "(proofs : propositions) :: (terms : types)"

- For instance, `2 + 2 = 5` is a proposition, albeit a false one. Therefore, `2 + 2 = 5` as the type of "identifications" of `2+2` and `5` does not have a term in it. On the other hand `rfl : 2 + 2 = 4` is a term/witness that `2 + 2` and `4` are equal. 

Here are some examples:
-/

section
#check 2 + 2 = 4
#check 2 + 2 = 5 -- Note that the command #check does not check the validity only the type

def flt := ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n 
#check flt
end 


/- 
There is a type `Prop` of all propositions. We introduce a proposition by the typing expression `P : Prop`. 
-/
section 
variable {P Q : Prop} -- let "P and Q be propositions"
#check P 
#check Prop -- this is the type of all propositions. So, we have `P : Prop : Type`. We can think of propositions (such as `P`) as types and proofs of propositions as terms of types. so you can have `rfl : 2 + 2 = 4 : Prop : Type`.
#check P ∧ Q -- the conjunction of `P` and `Q` (and)
#check P ∨ Q -- the disjunction of `P` and `Q` (or)
#check P → Q -- the implication (if `P` then `Q`)
#check P ↔ Q -- biimplication (`P` if and only if `Q`)
end 

/- 
For `P : Prop`, we read `hp : P` as "hp is a proof of P", or we have a hypothesis "P" verified by "hp", or "P is true by virtue of hp". 
-/

section
variable {x y : ℤ} {a : ℕ}

-- Terms of propositions are proofs of propositions.
#check (rfl : 1 = 1) -- `rfl` is a proof of reflexivity of eqaulity, thins like `x = x` 
#check (rfl : 2 + 2 = 4) --rfl refers to "reflexivity", `rfl` works because the "normal" form of `2 + 2` and `4` are syntactically the same. 
#check rfl  
#check @rfl -- this gives a more explicit type of `rfl`
#check ∀ x y : ℤ, x + y = y + x -- says "for all integers x and y, the sum x + y is equal to the sum y + x."

-- #check (rfl : ∀ x y : ℤ, x + y = y + x) -- gives error, why do you think that is?

-- #check (rfl : x + y = y + x) -- syntactically these expressions are not the same. `rfl` works for syntactic equality and definitional equality. While `x + y` and `y + x` are propositionally equal. 

-- #check (rfl : a + 0 = x) -- Lean knows `a` is a natural number because we told it so. Then it infers that the `+` operation is an operation between two natural numbers. Then it infers that `0` has the type  natural number. And then it infers the equality `=` is the equality relation between two natural numbers. And then it expects `x` to be a natural number, but we told Lean `variable x y : ℤ`. So these are not equal for the simple type-checking reasons.


#check (rfl : a + 0 = a) -- a bit weird, what's going on is that Lean knows that it has to use `rfl` to establish syntactic equality, but definitionally `a` is the same as `a + 0`. So it converts the second `a` in to `a + 0` and then used `rfl`. 
#check (add_comm : ∀ x y : ℤ, x + y = y + x) -- here we invoke a lemma. We borrowed it from the Lean library.  

end -- end of section 


/- 
The term `rfl` is the (trivial) proof that any term is equal to itself. Here is a term-style proof of ` 2 = 2 `. Here `2 = 2` is the statement we wanna prove and `rfl` is the proof of it. 
-/

/-
To assert a statement in Lean we use the `example` environment which includes 
- context: the parameters which are used in the statement of the lemma. Think of context as a way of telling to Lean "let x, y, z, and n be natural numbers". A statement only makes sense in an appropriate context. 
- statement we wanna prove 
- the proof of the statement (which comes it two styles: term style and tactic style). 

A general __term style__ form of an `example` is as follows: 

example (context_of_our_assumptions) : 
  statement_of_lemma := 
proof_of_lemma

-/

-- in the example below the context is empty. 
example : 
  2 = 2 := 
rfl 

-- An assertion can have a nonempty __context__: in below the context comprises of four variables of natural numbers `a b c d`. The statement we wanna prove tis that `(a + b) * (c + d) = (a + b) * (c + d)` and the proof is by reflexivity. 
example (a b c d : ℕ) : (a + b) * (c + d) = (a + b) * (c + d) := rfl


-- The term `rfl` proves more than syntactic equalities, it proves the equalities between terms which are __definitionally equal__. 

example : 
  2 + 3 = 5 := 
rfl 


-- `( ( ) ( ) ) ( ( ) ( ) ( ) ) = ( ( ) ( ) ( ) ( ) ( ) )`



/-! ### Falsity

Sometimes we encounter propositions which are always false such as “A bachelor is married”, or "0 = 1". 

In Lean, we denote the false proposition by `False`. The _universal property_ of a __false proposition__ is that any other proposition follows from the false proposition. We can prove any proposition from `false`. This is known as the __principle of explosion__ 🎆 aka ex falso. 
-/

example (P : Prop) (impossible : False) :
  P :=
False.elim impossible

example (P : Prop) (impossible : False) :
  P :=
impossible.rec impossible



/-! ### True

Sometimes we encounter propositions which are always true such as “A bachelor is unmarried”, or "0 = 0". 

In Lean, we denote the always-true proposition by `True`. The proposition `True` has a unique proof, namely `trivial`.  
We can prove any proposition from `false`. This is known as the __principle of explosion__ 🎆 aka ex falso. 
-/

#check trivial

example : 
  True := 
trivial 



/-!
## New Propositions from the Old  
-/


--- See  [theorem_proving_in_lean4](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)


variable {P Q R : Prop} -- let `P`, `Q` and `R` be propositions. --  P and Q are accessible throughout the entire file,

/- 
Lean's "check" command tells us 
the type of the object we have constructd. 
-/

#check P 
-- binary __connectives__ (logical operations)
#check P ∧ Q -- conjunction (and)
#check P ∨ Q -- disjunction (or)
#check P → Q -- implication (if ... then ...)

--unary connective
#check ¬ P -- negation (not the case P)


/-
Using simple (aka __atomic__) propositions such as 

S1. “The sun is shining” and 
S2. “It is raining”,  

we can form the __compound__ proposition 

S3. “The sun is shining _and_ It is raining”.

S3 is of the form `S1 ∧ S2`. 

S4. "If the sun is shining then it raining". 

S4 is of the form `S1 → S2`. 


By combining propositin using connectives we construct more complicated propositions from simple propositions. This required us to first unquote the sentences, insert an “and” and then put a quote around the resulting sentence. We call a compound proposition (such as “The sun is shining and It is raining”) a __propositional formula__. 

In this way, we can make new propositions from old propositions using __connectives__ (such as `∧`, `→`, `∨`). For each connective, we specify a __rule__  (the so-called introduction rule) to __introduce__ a proof of the compound proposition using that connective and a rule (the so-called elimination rule) to __use__ or ___eliminate__   such a proof.

In below we shall introduce the connectives `∧`, `∨`, `→`, and `¬`, and give their introduction and elimination rules.  


- `∧` has one introduction rule and two elimination rules.  
- `∨` has two introduction rules, and one elimination rule. 
- `→` has one introduction rule, and one elimination rule. 
- `¬` is defined using `→`: its introduction and elimination rules are similar to those of `→`. 
-/


/-
Connectives (such as conjunction, disjunction, implication) for propositions are analogues of type constructors (such as cartesian product, direct sum, or function type). 

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
------------- (→ elim, modus ponens)
      Q

If `h` and `p` are compound expressions, we put brackets around them to make it clear where each one begins and ends. 
e.g. `h₁ h₂ h₃` is interpreted by Lean as `(h₁ h₂) h₃`.
-/


example : P → P := 
by 
  intro hp 
  exact hp

example : (P ∧ Q) → P := 
by 
 intro hpq -- let P be true and then show P ∧ Q 
 exact hpq.1


example (h₁ : P → Q) (h₂ : P) : Q := 
by 
  exact h₂.2






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
lemma conj_comm :
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

note that the keyword `by` tells Lean whatever that follows is supposed to be a proof of the proposition we are trying to prove. 


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

`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.

For example, suppose you have the goal `⊢ Q` and you have the hypothesis
`g : P → Q` then `apply h` will construct the path backwards,
moving the goal from  `Q` to  `P`.
-/

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → (P → R) := by
  intros hPQR hPQ hP
  apply hPQR
  { exact hP }
  { apply hPQ
    exact hP }




/-
One of the earliest kind of proofs one encounters in mathematics is proof by calculation. This usually involves a chaing of equalities using lemmas expressing properties of operations on numbers and other structures.   
-/


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

We use the tactic `cases` in order to use a proof of `P ∨ Q` to prove some other proposition. 



  P ∨ Q     P        Q
            .        .
            .        .
            .        . 
            R        R
----------------------------
            R           

A variant of `cases`, the tactic ` cases' ` can be used like `cases h with hp hq` to give customary name to the branches of a disjunction, using `hp` for the first branch and `hq` for the second.  
-/

example (h : P ∨ Q) : Q ∨ P := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq 


example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq


/-!
## More Advanced Tactics   
-/


/- Tactics are instructions and more advanced tactics are series of instructions which automate our manual writing of proofs with simple tactics. In below we shall discuss some more advanced tactics which give us the ability to prove more with writing less, and the proofs will look more compact. -/

------------------------
-- tactic __`assumption`__ 
------------------------
/-
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



--------------------------------
-- __Concataneation of tactics__
--------------------------------

/- Let's make the proof above even more compact using concataneation of tactics with `<;>` : the command 
` tac1 <;> tac2 ` 
runs tactic `tac1` on the main goal and tactic `tac2` on each produced goal, concatenating all goals produced by `tac2`.
-/ 

example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
by
  constructor <;> constructor <;> assumption



  
/-! ### Tactic calc 
One of the earliest kind of proofs one encounters in mathematics is proof by calculation. This usually involves a chaing of equalities using lemmas expressing properties of operations on numbers and other structures.  `calc` (short for calculation) is the tactic for this kind of proofs.

- Using `calc`, in order to prove our goal (`x + 1 = w + 1`) we introduce several __subgoals__ each of which needs a separate proof. The subgoals in the example below are 

1. `x + 1 = y + 1` this is true since `x = y` by virtue of `h₁`. 
2. `y + 1 = z + 2` is true and the proof is `h₂`.
3. `z = w ` is true and the proof is `h₃`.

Then the tactic `calc` takes advanatge of the transitivity of equality to bind all these proofs togehter and prove that `x + 1 = w + 2`. 

See [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html?highlight=calc#calculational-proofs) for the general syntax of `calc`. 
-/

example (x y z w : ℝ) (h₁ : x = y) (h₂ : y + 1 = z + 2) (h₃ : z = w) : x + 1 = w + 2 :=
calc 
  x + 1 = y + 1 := by rw [h₁] -- `x + 1 = y + 1` is the first subgoal. `by` converts tactics to terms which we need to supply as the justification for the subgoal. 
  _    = z + 2 := by exact h₂ -- the second subgoal is that `y + 1 = z + 2` 
  _    = w + 2 := by rw [h₃] -- the third subgoal is that `z + 2 = w + 2` 







