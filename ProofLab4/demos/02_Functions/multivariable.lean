
/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 

set_option pp.proofs.withType false

open Real -- opening namespace. 


/-! ### Multivariable Functions (Functions of Many Arguments)  
So far our functions take a single argument as their input, but the functions of many arguments are abound. A function of many arguments can depend on __two or more arguments__ as inputs. Most physical laws can be expressed as functions of many arguments: for instance the pressure (P) of an ideal gas is a function of its temperature (T) and volume (V). And, kinetic energy of a particle is a function of its mass and velocity.
-/



/-
puzzle: guess the type of `kinetic_energy`
-/
#check kinetic_energy 

#reduce dom (kinetic_energy)
#reduce cod (kinetic_energy)

/- 
Suppose `f` is a multivariable function  which assigns to elements 
`a : A` and `b : B` an element `f a b : C`. 

This is represented in Lean by `f : A → B → C`. Lean parses the type as `A → (B → C)`.  This means for every `a : A`, we get a function `f a : B → C`. If we further feed an input `b : B` to the function `f a : B → C` then we obtain an element `f a b : C`.  
-/ 


/-
Since we have the operation of cartesian product on types we can in fact build from  `f` a single variable function from the cartesian product `A × B` to `C`. 

This insight is originally due to the logician and mathematician Frege then later discovered by Schönfinkel, but and again a century later by Haskell Curry.  
-/


#check uncurry

#check @Nat.add

--#eval Nat.add (2,3) -- this does not work

#check Nat.add 2 -- This is a function which takes a natural number and adds `2` to it. 

#eval (Nat.add 2) 3 -- The function `Nat.add 2` applied to the term `3 : ℕ`.  

#check uncurry Nat.add 


--#eval Nat.add (2,3)



/-
puzzle: guess the type of `kinetic_energy`
-/
#check @kinetic_energy

#reduce dom (kinetic_energy)
#reduce cod (kinetic_energy)


def my_kinetic :=  uncurry @kinetic_energy

#check @my_kinetic



/- 
Counting the lattice points in the first quadrant of the plane.
Given the lattice point `(m,n)`, there are exactly `m + n + 1` points whose sum of coordinates is equal to `m + n`.


10
6 11
3 7 12
1 4 8 13
0 2 5 9 14

Fix `k = m + n`. Then the number of lattice points with sum of coordinates equal to k is k + 1. Consider the triangle with vertices `(0,0)`, `(k,0)`, and `(0,k)`. There are  `(k+1)^2 - (k+1)/2 = k * (k+1)/2` points the come before `(0,k+1)` in our counting. So the point `(0, k)` will be at the position `k * (k+1)/2` and the point `(m,n)` where `m + n = k` will be at the position `k * (k+1)/2 + m = (m + n) * (m + n + 1)/2 + m`.  

-/

def cantor_function := 
fun (m : ℕ) (n : ℕ) => (m + n) * (m + n + 1)/2 + m


#check cantor_function 0 

#eval cantor_function 0 0 --0

#eval cantor_function 0 1 --1 
#eval cantor_function 1 0 --2

#eval cantor_function 0 2 --3
#eval cantor_function 1 1 --4
#eval cantor_function 2 0 --5

#eval cantor_function 0 3 --6
#eval cantor_function 1 2 --7
#eval cantor_function 2 1 --8 
#eval cantor_function 3 0 --9 

#eval cantor_function 4 0 --10

#check uncurry cantor_function 

#eval uncurry cantor_function (1,1)


#check curry

#check @curry

#check curry (uncurry cantor_function)

#eval curry (uncurry cantor_function) 1 1



/-
Consider the multivariable function `rational_sum_of_squares : ℚ → ℚ → ℚ` defined by `g x y  = x^2 + y^2`.
-/


#check rational_sum_of_squares 


-- def rational_sum_of_squares_alt (p : ℚ × ℚ) := 
-- sorry 

#eval rational_sum_of_squares (3/5) (4/5)

#check uncurry rational_sum_of_squares

#eval uncurry rational_sum_of_squares (3/5, 4/5)


#check curry fst

#eval curry fst 1 2


/- Define a function `distance_rat : ℚ → ℚ → ℚ` which takes two rational numbers `x : ℚ ` and `y : ℚ ` as inputs and returns as output the standard Euclidean distance `| x - y |` between them. 
-/ 

-- def distance_rat (x y : ℚ) := 
-- sorry


--#check distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should be a rational number
--#eval distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should evaluate to 1
--#eval distance_rat (1/3) (1/2)


example : curry (uncurry f) = f := 
by 
  ext 
  rfl


example : uncurry (curry f) = f := 
by 
  ext 
  rfl 









