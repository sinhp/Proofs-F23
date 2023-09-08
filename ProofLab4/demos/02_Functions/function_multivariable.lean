
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

This is represented in Lean by `f : A → B → C`. Lean parses the type as `A → (B → C)`.  This means for every `a : A`, we get a function `f a : B → C`. If we further feed an input `b : B` to the function `f a : B → C` then we obtain an element `f a b : C`. s  
-/ 




/-
Since we have the operation of cartesian product on sets we can in fact construct from  `f` a single variable function from the cartesian `A × B` to `C`. 

This insight is originally due to the logician and mathematician Frege then later discovered by Schönfinkel, but and again a century later by Haskell Curry.  
-/


#check uncurry

#check uncurry Nat.add 

-- #check uncurry (X := X) (Y:= Y) (Z:= Z)



#check Nat.add 
#check @Nat.add

#check Nat.add 2 -- This is a function which takes a natural number and adds `2` to it. 

#eval Nat.add 2 3 

--#eval Nat.add (2,3)

#check kinetic_energy 

/-
puzzle: guess the type of `kinetic_energy`
-/
#check kinetic_energy

#reduce dom (kinetic_energy)
#reduce cod (kinetic_energy)



def uncurry : (X → Y → Z) → (X × Y → Z) := 
fun f =>  (fun p => f p.1 p.2)
#check uncurry


#check uncurry Nat.add 

-- #check uncurry (X := X) (Y:= Y) (Z:= Z)



#check Nat.add 
#check @Nat.add

#check Nat.add 2 -- This is a function which takes a natural number and adds `2` to it. 

#eval Nat.add 2 3 

--#eval Nat.add (2,3)






def cantor_function := 
fun (m : ℕ) (n : ℕ) => (m + n) * (m + n + 1)/2 + m

#check cantor_function 0 
-- #eval cantor_function 0 

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

def  cantor_function_uncurried := uncurry cantor_function 

#eval cantor_function_uncurried (1,1)




/-- Conversely -/
def curry : (X × Y → Z) → (X → (Y → Z)) :=
 fun f => fun x =>  fun y => f (x , y)

#check curry
#check @curry


-- the type of the uncurried `kinetic_energy` 
#check uncurry kinetic_energy



/-
Consider the multivariable function `rational_sum_of_squares : ℚ → ℚ → ℚ` defined by `g x y  = x^2 + y^2`.
-/


def rational_sum_of_squares (x y : ℚ) := 
x^2 + y^2


-- def rational_sum_of_squares_alt (p : ℚ × ℚ) := 
-- sorry 


#eval rational_sum_of_squares (3/5) (4/5)

#check uncurry rational_sum_of_squares

#eval uncurry rational_sum_of_squares (3/5, 4/5)





/-- for a pair `p`, i.e. a term of type `X × Y` the output of `fst` is the first coordinate of `p` which we access using the first projection `.1`. -/
def fst (p : X × Y) := 
p.1 


/-- for a pair `p`, i.e. a term of type `X × Y` the output of `snd` is the second coordinate of `p` which we access using the second projection `.2`. -/
def snd (p : X × Y) := 
p.2


#check curry fst

#eval curry fst 1 2


/- Define a function `distance_rat : ℚ → ℚ → ℚ` which takes two rational numbers `x : ℚ ` and `y : ℚ ` as inputs and returns as output the standard Euclidean distance `| x - y |` between them. 
-/ 
-- def distance_rat (x y : ℚ) := 
-- sorry


--#check distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should be a rational number
--#eval distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should evaluate to 1
--#eval distance_rat (1/3) (1/2)



/-! ## Functions out of inductive types 

To define a function on an inductive type, we need to specify the value of the function on each constructor.

For instance we already saw that to define the function `isLectureDay` on the type `Weekday` we need to specify the value of the function on each of the seven constructors of `Weekday`.
-/ 

#check isLectureDay


/- 
Similarly to define a function `f` out of `ℕ` we need to specify the value of `f` at `zero` and the value of `f` at `succ n` for `n : ℕ`.
-/ 

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 4 -- 24


/-
Puzzle: define a function `fibonacci : ℕ → ℕ` which takes a natural number `n` as input and returns the `n`th Fibonacci number.
-/



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







/-- Lexicographical order on ℕ × ℕ  -/ 
inductive LexNat : ℕ × ℕ → ℕ × ℕ → Prop where
  | left  {a₁} (b₁) {a₂} (b₂) (h : a₁ ≤ a₂) : LexNat (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : b₁ ≤ b₂)         : LexNat (a, b₁)  (a, b₂)


#check LexNat.left


def sum_of_lex_nat (p₁ q₁ p₂ q₂ : ℕ × ℕ) (H₁ : LexNat p q) (H₂ : LexNat p₂ q₂) : LexNat (p₁ + p₂) (q₁ + q₂)  := sorry 




/- 
For instance the following is the definition of the less than or equal to relation on the natural numbers.
-/

 


def Nat_le : ℕ → ℕ → Prop    
| 0 , 0   => True
| 0 , (.succ _)   => True
| (.succ _) , 0   => False
| (.succ m) , (.succ n) => Nat_le m n 





--#check Lex


/-! ## Composition of Functions -/


def Compose (g : Y → Z) (f : X → Y) (x : X) : Z :=
  g (f x)


/-
We define the operation of __squaring__ a function using `compose`:
-/

def Square (f : X → X) : X → X :=
  Compose f f


/-
A notation for squaring
-/

notation:1000 f "²" => Square f








