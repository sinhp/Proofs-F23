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


lemma false_elim (P : Prop) (impossible : False) :
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



