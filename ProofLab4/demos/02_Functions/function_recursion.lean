/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 

set_option pp.proofs.withType false


/-! ## Functions out of inductive types 

To define a function on an inductive type, we need to specify the value of the function on each constructor.

For instance we already saw that to define the function `isLectureDay` on the type `Weekday` we need to specify the value of the function on each of the seven constructors of `Weekday`.
-/ 

inductive Weekday where 
  | Monday : Weekday
  | Tuesday : Weekday
  | Wednesday : Weekday
  | Thursday : Weekday
  | Friday : Weekday
  | Saturday : Weekday
  | Sunday : Weekday

#check Weekday

#check Weekday.Monday -- The type of this expression is Weekday
#check Weekday.Sunday 


inductive Weekend where  
  | Saturday 
  | Sunday


#check Weekday.Saturday 
#check Weekend.Saturday 

#check Nat
#check Nat.zero
#check Int.zero

/-Define a function on Weekday which specifies the lecture days -/  

def isLectureDay : Weekday →  Bool 
| Weekday.Tuesday => true
| Weekday.Thursday => true
| _ => false     -- _ means whatever the other days as input 


#check @isLectureDay


#check isLectureDay


/- 
Similarly to define a function `fac` out of `ℕ` we need to specify the value of `fac` at `0` and the value of `f` at `succ n` for a previously defined `n : ℕ`.
-/ 

/-
0 ↦ 0! = 1 
n ↦ (n+1)! = (n+1) * n!   1 2 3  
                          2 1 3 
                          3 1 2
                          1 3 2
                          2 3 1
                          3 2 1
Let's do all the permutations of 1 2 3 4 

                          1 2 3 4
                          1 2 4 3
                          1 4 2 3
                          4 1 2 3

                          2 1 3 4
                          2 1 4 3
                          ....



                          
-/

def fac : ℕ → ℤ 
  | 0 => 1
  | (n + 1) => (n + 1) * fac n

#eval fac 4 -- 24


/-
Puzzle: define a function `fibonacci : ℕ → ℕ` which takes a natural number `n` as input and returns the `n`th Fibonacci number.
-/


#eval 2 - 3

def fibonacci : ℕ → ℕ 
  | 0 => 0
  | (n + 1) => fibonacci (n) + fibonacci (n - 1)


#eval fibonacci (2 - 3)
#eval fibonacci 1




/-! ### The Principle of Induction 
The principle of induction says that we can prove a general statement about the natural numbers by proving that the statement holds of `0` and that whenever it holds of a natural number `n`, it also holds of `n+1` . The line `induction' n with n ih` in the proof below therefore results in two goals: in the first we need to prove `0 < fac 0`, and in the second we have the added assumption `ih : 0 < fac n` and a required to prove `0 < fac (n + 1)`. 

1. 
` ⊢ 0 < fac 0`

2. 
`0 < n  ⊢  0 < fac (n + 1)` 

The phrase `with n ih` serves to name the variable and the assumption for the inductive hypothesis, and you can choose whatever names you want for them.
-/ 

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih




-- The following example provides a crude lower bound for the factorial
-- function.
-- It turns out to be easier to start with a proof by cases,
-- so that the remainder of the proof starts with the case
-- :math:`n = 1`.
-- See if you can complete the argument with a proof by induction.
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  sorry



/-- Lexicographical order on ℕ × ℕ  -/ 
inductive LexNat : ℕ × ℕ → ℕ × ℕ → Prop where
  | left  {a₁} (b₁) {a₂} (b₂) (h : a₁ ≤ a₂) : LexNat (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : b₁ ≤ b₂)         : LexNat (a, b₁)  (a, b₂)


#check LexNat.left


def sum_of_lex_nat (p₁ q₁ p₂ q₂ : ℕ × ℕ) (H₁ : LexNat p q) (H₂ : LexNat p₂ q₂) : LexNat (p₁ + p₂) (q₁ + q₂)  := 




/- 
For instance the following is the definition of the less than or equal to relation on the natural numbers.
-/

--open Nat 


def Nat_le : ℕ → ℕ → Prop    
| 0 , 0   => True
| 0 , (.succ _)   => True
| (.succ _) , 0   => False
| (.succ m) , (.succ n) => Nat_le m n 


--#check Lex


