/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
Puzzle 1 : what is the result of _evaluating_ the following expressions?
-/



#eval 2 - 1 -- be careful to include the `#` at the beginning of `eval`.
#check 2 - 1



#eval 1 - 2 -- why 0? Lean parse `1` as a natural number, not an integer, and therefore `-` operation is subtraction of natural numbers. The Subtraction of natural number is an operation which takes two natural numbers and output a natural number. The result of `m - n` for n bigger than m is always 0 for natural numbers. 

#eval (1 : ℤ) - 2 -- first we _cast_ 1 to be an integer. 
#eval 1 - (2 : ℤ) 

#eval (1 : ℚ) - (2 : ℤ) 
#check (1 : ℚ) - (2 : ℤ) -- the only type where, by casting, 1 and 2 can be unified, i.e. considered as elements of the same type, is ℚ. Therefor the subtraction is a subtraction of ℚ. 

#check Int.cast -- you can consider an integer as a rational number but also a real number 

#check (-2 : ℚ)
#check (-2 : ℝ)
-- #check (-2 : ℂ)

#check @Int.cast ℚ 
#check @Int.cast ℝ 
-- example : (-2 : ℚ) = @Int.cast ℚ (-2 :) := 
-- by 
--   rfl 

/- Casting hierarchy 

ℕ → ℤ → ℚ → ℝ
-/


#eval 1 / 2
#check 1/2 -- is a natural number. 

#check 5/2 -- 5 = 2 × 2 + 1

#eval (5:ℚ)/2 

#eval 2^5

--#eval 2 ^ (-5 : ℤ)  -- ℤ  are not closed under exponentiation `^` 

#eval 2^7 -- ℕ  are not closed under exponentiation `^`

#eval (2 : ℚ) ^ (-5 : ℤ) 

-- #eval (2 : ℚ) ^ (1 : ℚ)

#check -2

#check 2


/-
There is a tactic for casting which we will learn soon. 
-/


/-
Puzzle 2 : what is the type of the following expressions?
-/


#check 2023

#check [2023]

-- #check {2023}  -- this is a set

-- #check String.append "hello" [" ", "world"]



/-! 
### New Types from the Old 
-/

/- For a type `A` we have a the following new types constructed from `A` -/
variable (A: Type u)

#check List A -- the type of lists of elements of type `A`
#check Set A -- the type of sets of elements of type `A`


variable (B : Type u)

#check A × B 
#check Prod A B 

#check A ⊕ B 
#check Sum A B

#check (-2, 3) 
#check (-2, (3: ℤ))

#check (Sum.inr 2 : ℕ ⊕ ℕ)
#check Sum.inr 2 
#check (Sum.inl (-2) : ℤ ⊕ ℕ) 



/-
`#check <expression>` tells us what kind of thing `<expression>` is.
-/
#check 0 

#check 1 + 1

#check 1 + 1 = 3

/-the type of functions from ℕ to ℤ. We study the type of functions in the next lecture.-/
#check ℕ → ℤ 

#check ℤ → ℕ

#check Bool → ℕ → ℤ

#check (Bool → ℕ) → ℤ

#check ℕ → (Bool → ℕ) → ℤ

#check Prod ℕ Bool 

#check Sum ℕ Bool 

#check Sum



/- Write a term of the following types: -/

/- The type of cartesian product of natural numbers with itself -/
/-  `(a, b) : A × B` where `a : A` and `b : B` -/
def my_term₁ : ℕ × ℕ := (200, 1)

#reduce my_term₁

/- giving more context -/
def my_term_of_prod (A : Type) (B : Type) (a: A) (b : B) : A × B := 
(a,b)

#reduce my_term_of_prod

/-

A : Type    B: Type 
-------------------
    A × B : Type 

ℕ    ℕ     ℕ 
-------------------
  ℕ × ℕ    ℕ 
-------------------  
    (ℕ × ℕ) × ℕ 

The typical terms of the product type. 

a : A       b : B
------------------ 
  (a, b) : A × B 

p : A × B  
---------------- (elimination/projection)
p.1 : A   p.2 : B
-/


def my_pair := (3 , 3.4)
#check my_pair

#check my_pair.1
#eval my_pair.1
#eval my_pair.2


/- ℕ × (Float × List ℕ) -/
def my_triple := (3, 3.4, [1,2,3])

#check my_triple.1
#eval my_triple.1
#check my_triple.2
#check my_triple.2.1

example : my_triple.2.1 = 3.4 := 
by 
 rfl 

/- 
Lean parses A × B × C as A × (B × C) by default. 
In general (A × B) × C ≠  A × (B × C). 
-/

def my_term₂ : ℕ × (ℕ × ℕ) := 
(2023, my_term₁)

#reduce my_term₂


def my_term₂_alt : (ℕ × ℕ) × ℕ :=  
(my_term₁, 2023) 


/- In general two terms belonging to two different types can never be equal. Equality makes sense within a fixed type. -/
-- example : my_term₂ = my_term₂_alt := 
-- by 
--  rfl 

/- unbiased triples. -/

/- sum type -/
def my_term₃ : ℕ ⊕ List ℕ := Sum.inr []
def my_term₃_alt : ℕ ⊕ List ℤ := Sum.inl 2   


#check ℕ ⊕ ℤ 

def inclusion_of_nat : ℕ →  ℕ ⊕ List ℤ := 
fun n => Sum.inr [n] 


#check ℕ ⊕ ℕ 

def my_term₄ : ℕ → ℕ := sorry 

def my_term₅ : ℕ ⊕ ℕ × ℕ  := sorry 

def my_term₆ : ℕ ⊕ ℕ × ℤ  := Sum.inl 0

def my_term₇ : Unit ⊕ ℕ ⊕ ℕ × ℕ  := sorry 

def my_term₈ : Unit ⊕ ℕ ⊕ ℕ × ℕ  := sorry 

def my_term₉ : List ℕ := sorry 

def my_term₁₀ : List ℕ  × ℕ := ([1001, 1002, 1003], 0)


/- We are given a term `t : `. Produce a term of type ℤ, depending on `t`, using a projection of `t`.  -/
section 
variable (t :  ℕ × ℤ × ℝ) 
def t_snd : ℤ := sorry 
end 