import ProofLab4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real 

/-! 
# Homework 1
Homework must be done individually.
-/

#check π  




/-
# Problem 1

Form the following expressions and find/verify their type in Lean using the `#check` command. 

1. The sum of two thirds of three fifths as a rational number
2. The sum of two thirds of three fifths as a real number
3. The circumference of a circle with radius 1.5 
4. The volume of a tetrahedron with side length 2.5 
-/


/-
equilateral triangle is the base of tetrahedron. A tetrahedron is a pyramid with a triangular base and three other faces. All the faces are the same equilateral triangle, and all the edges have the same length. 

The volume of a tetrahedron is given by the formula:
V = (1/12) * √2 * a^3 = (√2/12) * 2 * a^3 = (√2/6) * a^3
where a is the length of the edges of the tetrahedron.
-/

#check 2.5
#check 2.5 ^ 3 / 12 * sqrt 2 -- why is `2.5` considered a real? `2.5` is casted to a real value since the expression above includes a real value `sqrt 2`. And all the operations (such as * and /) are operations on real numbers. 

/-
The expression `2.5 ^ 3 / 12 * sqrt 2` is parsed based on the following binding priorities: 
1. ^ (exp) 
2. / 
3. *
Therefore `2.5 ^ 3 / 12 * sqrt 2 = ((2.5 ^ 3) / 12) * sqrt 2`
-/

example : 2.5 ^ 3 / 12 * sqrt 2 = ((2.5 ^ 3) / 12) * sqrt 2 := rfl -- a term proof; `rfl` here is a term which proves `a = a` for all `a`.

example : 2.5 ^ 3 / 12 * sqrt 2 = ((2.5 ^ 3) / 12) * sqrt 2 := 
by 
  rfl -- a tactic proof; `rfl` is a tactic


#check 2.5

-- example : 2^(1/2) = sqrt 2 := rfl 

#eval 2^(1/2)

-- #check ((2.5: ℝ)^3) / (6 * (2^(1/2)))

#eval 1/2 


#check ((2.5 ^ 3 : ℝ) / (12 : ℝ)) * (sqrt 2 : ℝ)

/- 
# Problem 2 
How Lean parses: In this problem we are going to investigate how Lean binds operators, and what binding priorities are assigned to them.
-/

/-
1. 2 + 3 * 4
2. 3 - 2 + 4 
3. 3 / 2 * 4
4. (-3) ^ 2 * 6
5. (-3) ^ 3 ^ 2
6. (-1: ℚ) / 2 ^ 3 * 5
-/



/- 
# Problem 3
In this exercise you will define some terms of given types in Lean. If possible, provide a term of the specified type. If not, explain why not. 
-/ 

/-
1. `List (Unit ⊕ ℕ)` 
2. `List (ℕ × ℚ)`
3. `List ℕ × ℕ`
4. `List (List ℕ)`
5. `List Empty`
6. `Empty × ℕ`
7. `Bool ⊕ Empty × ℕ`
8. `Empty ⊕ Empty`
-/


/-
5.
-/
#check ([] : List Empty)
#check ([] : List ℕ)


/-
While the type `List ℕ` has infinitely many elements including `[]`, the type `List Empty` has only one element `[]`.
-/


/-
6.
-/


-- def my_term₆ : Empty × ℕ := 
-- (?, 0)


example (magic : Empty × ℕ ) : Empty := magic.1 -- the first projection 

/- Having a term of type Empty is a contradiction. As long as we do our mathematics correctly (Lean checked) we are never going to produce/construct a term of type `Empty`. -/
example (t : Empty ) : 0 = 1 := 
sorry 
