/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4



/-
`#check <expression>` tells us what kind of thing `<expression>` is.
-/

#check 0 

#check 1 + 1

#check 1 + 1 = 3

#check ℕ → ℤ

#check ℤ → ℕ

#check Bool → ℕ → ℤ

#check (Bool → ℕ) → ℤ

#check ℕ → (Bool → ℕ) → ℤ

#check Prod ℕ Bool 

#check Sum ℕ Bool 

#check Sum



/- Write a term of the following types: -/

def my_term₁ : ℕ × ℕ := sorry 

def my_term₂ : ℕ × ℕ × ℕ := sorry 

def my_term₃ : ℕ ⊕ ℕ := sorry 

def my_term₄ : ℕ → ℕ := sorry 

def my_term₅ : ℕ ⊕ ℕ × ℕ  := sorry 

def my_term₆ : ℕ ⊕ ℕ × ℤ  := sorry 

def my_term₇ : Unit ⊕ ℕ ⊕ ℕ × ℕ  := sorry 

def my_term₈ : Unit ⊕ ℕ ⊕ ℕ × ℕ  := sorry 

def my_term₉ : List ℕ := sorry 



/- We are given a term `t : `. Produce a term of type ℤ, depending on `t`, using a projection of `t`.  -/
section 
variable (t :  ℕ × ℤ × ℝ) 
def t_snd : ℤ := sorry 
end 