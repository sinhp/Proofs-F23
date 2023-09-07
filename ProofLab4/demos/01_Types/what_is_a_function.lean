/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 

open Real -- opening namespace. 



variable {A B C X Y Z U V W : Type} -- "Let A B ... W be types". We are introducing types A ... W right at the start so that we do not have to repeat ourselves for each example/lemma/theorem context declration. 


/-! # Functions -/ 



/-! ## Some Examples -/

#check ℕ 


/- The __first way__ to specify functions -/


/-- Takes a natural number and returns the next/successor one.  -/
def succ := fun (n : ℕ) => n + 1 


def succ_alt := fun n => n + 1

#check @succ  -- `succ : ℕ → ℕ` . `ℕ → ℕ` is the type of all functions from natural numbers to natural numbers. `succ` is a term of `ℕ → ℕ`. In other words, `succ` is a function from natural numbers to natural numbers.   

#check @succ_alt -- the type of variable n is automatically infered as a natural number. 


--#eval succ -- Lean cannot evaluate functions without input.  

#eval succ 0 -- input : 0 , output :1
#eval succ 1000 -- input : 1000 , output :1001


/--
Let `double : ℕ → ℕ` be the function defined by `double (n) = 2 * n`:
-/ 
def double := 
fun (n : ℕ) => 2 * n 
-- we use the symbol `:=` for defining functions in Lean. Whatever follows `:=` is the definition of the function. 

#check double 
#check @double


#eval double 20

#check ℕ × ℕ 
#check A × B


/-
A : Type    B: Type
------------------- (formation rule of function types)
    A → B : Type 


a : A |- f(a) : B 
--------------------- (introduction rule)
fun a => f a : A → B


n : ℕ  ∣- 2 * n : ℕ 
---------------------
fun n => 2 * n : ℕ → ℕ  

-/


#check A → B 


/- Puzzle: define a function `ℕ → ℚ` which takes a natural number and halves it. -/


def half := 
fun (n : ℕ) => ((n : ℚ) /2)

#check @half
#eval half 1


def half_rat := 
fun (n : ℚ) => n/2


#check half_rat
#check @half_rat

#eval half_rat 3/4
#eval half_rat 1

#check half_rat 2
#eval half_rat 2




/- _Test_ your definition with the following inputs. -/

--#eval half 1 -- this should output 1/2
--#eval half 4 -- this should output 2



-- Lean interprets `n` to be an integer (the default way)
def half_neg := fun n => (-n : ℤ)/2  -- this is taking the floor of (-n : ℤ)/2

#check @half_neg

#eval half_neg 1 -- output : -1 


def half_neg_rat := fun n => (-n : ℚ)/2 

#check @half_neg_rat 
#eval half_neg_rat 1


def half_neg_rat_alt := fun (n : ℤ) => (-n : ℚ)/2 

#check @half_neg_rat_alt


--#exit -- to compile until this line 


-- #reduce half_neg_rat_alt -- unknown problem 

#check succ
#reduce succ

#check @Nat.add
#reduce Nat.add


def my_add : ℕ × ℕ → ℕ := 
fun (a, b) => a + b   


def half_neg_alt := 
-- Lean interprets `n` to be a natural number since we told it so. 
fun n : ℕ => (-n : ℤ)/2 


#check half_neg



/- The __domain__ and __codomain__ functions -/
def dom (f : A → B) := A -- `A` is the type of the inputs of `f`
def cod (f : A → B) := B --`B` is the type of the outputs of `f`

#check dom
#check @dom -- `dom` is a term of the type `(A → B) → Type`


/-
A       B 
---------------------------
  A → B    Type 
---------------------------
        (A → B) → Type
-/

/-
ℕ       ℕ 
---------------------------
 succ: ℕ → ℕ     Type 
---------------------------
        dom : (ℕ → ℕ ) → Type
-/



#check dom (succ : ℕ → ℕ)
-- #eval dom (succ : ℕ → ℕ) -- we cannot evaluate types but only terms. 
#reduce dom (succ : ℕ → ℕ)

/- 1/2 : ℚ -/



/- The __second way (non-lambda way) to specify functions__: no `fun` and no `=>` 
-/ 


def double' (n : ℕ) := 
2 * n
#check double'
#reduce double'


def double_alt (n : ℕ) := n + n 
-- syntactically this function is different than `double` and `double'`.
-- #check double_alt 


/- 
Let `square : ℕ → ℕ`  be the function defined by `square (n) = n * n`: 
-/
def square (n : ℕ) := n * n 

#check square
#eval square 3


/- All functions in Lean are __total__ which means they must return an output for each input of the domain. For instance think of taking the square root of a real number. In standard mathematics textbooks, this is only possible if the argument (i.e. what goes under √) is nonnegative. -/

#check sqrt 

noncomputable 
example (n : ℕ): sqrt (square n) = n := 
by 
  refine Iff.mpr sqrt_eq_cases ?_
  left 
  · constructor 
    · norm_cast
    · norm_cast
      positivity
       



/- The __third way__ of definition by __pattern matching__ : specify a function by assigning an output for each possible input.
-/


/- 
The type of weekdays defined _inductively_ as follows. We will talk about inductive types in the future lecture. For now, you can think of them as a way to define new types. The problem below does not emaphsize the inductive nature of this type, but rather focuses on how Lean parses the expressions involving this type.

The first line provides the name of the new type `Weekday`, while the remaining lines each describe a constructor, each corresponding to a day of the week.
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




def switch : Bool → Bool  
| true => false
| false => true


#check switch 
#eval switch false




def nat_of_bool : Bool → ℕ 
| false => 0 
| true => 1 


#check nat_of_bool
--#eval nat_of_bool ff



/- __if ... then ... else ...__ style of definition -/

def bool_of_nat (n : ℕ) := 
if n = 0 then false else true

-- #check bool_of_nat

def isOne (n : Nat) : String := if n = 1 then "yes" else "no"

#check isOne
#eval isOne 0



/- The __absolute value__ function -/
#check (abs : ℚ → ℚ)
#check (abs : ℝ → ℝ)
#check abs (-3 : ℚ)
#eval abs (-3 : ℚ)
#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)




/-! ### Multivariable Functions (Functions of Many Arguments)  
So far our functions take a single argument as their input, but the functions of many arguments are abound. A function of many arguments can depend on __two or more arguments__ as inputs. Most physical laws can be expressed as functions of many arguments: for instance the pressure (P) of an ideal gas is a function of its temperature (T) and volume (V). And, kinetic energy of a particle is a function of its mass and velocity.
-/

def kinetic_energy (m : ℝ) (v : ℝ) := 
(1/2 : ℚ) * m * v * v  


/-
puzzle: guess the type of `kinetic_energy`
-/
#check kinetic_energy

#reduce dom (kinetic_energy)
#reduce cod (kinetic_energy)

/- 
Suppose `f` is a multivariable function  which assigns to elements 
`a : A` and `b : B` an element `f a b : C`. 
Since we have the operation of cartesian product on sets we can in fact construct from  `f` a single variable function from the cartesian `A × B` to `C`. 

This insight is originally due to the logician and mathematician Frege then later discovered by Schönfinkel, but and again a century later by Haskell Curry.  
-/

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
#check @curry X Y Z


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
def distance_rat (x y : ℚ) := 
sorry


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





/- Suppose we have a type `X` and a decision function `d : X → bool`. Define a function `X → ℕ` which takes a `x : X` and returns `0` if `d x = false` and `1` if `d x = true`.     -/

variable {X : Type} {d : X → Bool}

-- def nat_of_bool_decision 





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








