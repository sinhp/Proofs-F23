/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Real.Basic





variable {A B C X Y Z U V W : Type} -- "Let A B ... W be types". We are introducing types A ... W right at the start so that we do not have to repeat ourselves for each example/lemma/theorem context declration. 


/-! # Functions 

- Given types `A` and `B`, we can make a new type `A → B` called the __function type__ of `A` and `B`. The  elements of function types are __functions__.

- The idea of functions: A __function__ `f : A → B` is a program that takes an element `a : A` as an input argument and returns a unique element `f a : B` as output. We also say `f` "assigns" the element `f a` to an element `a`. And sometimes we say `f` "takes" or "maps" `a` to `f a`. We concerive of a function as a total deterministic rule. Each input returns a fully determined ouput according to the assignemnt rule of the function.  

- Domain and codomain: 
In the expression `f : A → B`, the object/type `A` is called the __domain__ (sometimes called __source__) of `f` and the object/type `B` the __codomain__ (sometimes called __tartget__) of `f`. 

- How to __specify__ functions: 
Suppose we have a program/rule which outputs `b : B` for an input `a : A`. Note that `b` might depend on `a`. We represent this program as a function `fun a => b : A → B`. This is the so-called __function abstraction__. 

- How to __use__ functions: 
This is the so-called function __application__ (aka __evaluation__). We'll talk more about this in a minute.
-/


/-! ## Some examples of functions -/

#check ℕ 

/-- Takes a natural number and returns the next/successor one.  -/
def my_succ := fun (n : ℕ) => n +1 



/--
Let `double : ℕ → ℕ` be the function defined by `double (n) = 2 * n`:
-/ 
def double := 
fun n : ℕ => (2 * n) 
-- we use the symbol `:=` for defining functions in Lean. Whatever follows `:=` is the definition of the function. 

#check double 


/-- all functions in Lean are __total__ which means they must return an output for each input from the domain. For instance think of taking the square root of a real number. -/

def half := 
fun n => n/2 

#check half
#check half 1
#eval half 1
#eval half 2


def half_neg := 
-- Lean interprets `n` to be an integer (the default way)
fun n => (-n : ℤ)/2 


def half_neg_alt := 
-- Lean interprets `n` to be a natural number since we told it so. 
fun n : ℕ => (-n : ℤ)/2 


#check half_neg



/-- The __domain__ and __codomain__ functions -/
def dom (f : A → B) := A
def cod (f : A → B) := B




/-
 The __second way (non-lambda way) to specify functions__: Another way to specify the `double` function which avoids the lambda notation is as follows. This is somewhat closer to the way most mathematicians specify their functions. 

This way resembles the way we wrote lemmas/theorems.
-/ 
def double' (n : ℕ) := 
2 * n
#check double'
#reduce double'


def double_alt := 
fun (n : ℕ) => n + n 
-- syntactically this function is different than `double` and `double'`.
-- #check double_alt 



/- 
Let `square : ℕ → ℕ`  be the function defined by `square (n) = n * n`: 
-/
def square (n : ℕ) := 
n * n 
#check square
#eval square 3



-- The __third way__ of definition by __pattern matching__

def switch : Bool → Bool  
| true => false 
| false => true

#check switch 
#eval switch false



-- We can also specify a function by assigning an output for each possible input. 
def nat_of_bool : Bool → ℕ 
| false => 0 
| true => 1 


#check nat_of_bool
--#check nat_of_bool
--#eval nat_of_bool ff



-- __if ... then ... else ...__ style of definition

def bool_of_nat (n : ℕ) := 
if n = 0 then false else true

-- #check bool_of_nat

def isOne (n : Nat) : String := if n = 1 then "yes" else "no"

#check isOne
#eval isOne 0

/- Evaluation can also have side effects, which are generally related to system IO. For example, displaying the string “Hello, world!” is a side effect of the following evaluation:-/
#eval IO.println "Hello, world!"


def self_of_nat (n : ℕ) := n

#check self_of_nat

def int_of_nat : ℕ → ℤ := 
fun n => n

--#check int_of_nat


 
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
kinetic_energy : ℝ → ℝ → ℝ
-/
#check kinetic_energy

#reduce dom (kinetic_energy)
#reduce cod (kinetic_energy)

/- 
Suppose `f` is a multivariable function  which assigns to elements 
`a : A` and `b : B` an element `f a b : C`. 
Since we have the operation of cartesian product on sets we can in fact construct from  `f` a single variable function from the cartesian `A × B` to `C`. 

This insight is often attributed to the mathematician Moses Ilyich Schönfinkel, but it was already in use by Frege. Today it is known as “currying”, a tribute to Haskell Curry who later introduced it in his work independently. 
-/

def uncurry : (X → Y → Z) → (X × Y → Z) := 
fun f =>  (fun p => f p.1 p.2)
#check uncurry
#check @uncurry X Y Z

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

#check rational_sum_of_squares

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









/- CHALLENGE: define a function `distance_rat : ℚ → ℚ → ℚ` which takes two rational numbers `x : ℚ ` and `y : ℚ ` as inputs and returns as output the standard Euclidean distance `| x - y |` between them. 
-/ 
def distance_rat (x y : ℚ) := 
abs (x - y)


#check distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should be a rational number
#eval distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should evaluate to 1
#eval distance_rat (1/3) (1/2)



def Fibonacci : ℕ → ℕ  
  | 0 => 1
  | 1 => 1
  | n + 2 => Fibonacci (n + 1) + Fibonacci n 

#eval Fibonacci 5 -- infoview displays `8`  




/- Suppose we have a type `β` and a decision function `d : β → bool`. Define a function `β → ℕ` which takes a `b : β` and returns `0` if `d b = false` and `1` if `d b = true`.     -/

variable {β : Type} {d : β → Bool}

def nat_of_bool_decision (b : β) : ℕ :=
  match d b with
  | true  => 0
  | false => 1

#check nat_of_bool_decision


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


/-
A function from A to List A which take an elemnt `a : A` and returns the list `[a]` containing `a` as its only element.
-/

def singleton_list (a : A) : List A :=
  [a]

#check singleton_list 
#check singleton_list 1


/-
We define a function which computes the sum of a list of natural numbers.
-/

def sum_list : List ℕ → ℕ 
  | [] => 0
  | (head :: tail) => head + sum_list tail


/-
Let's prove the following property about `singleton_list`: 
-/ 

example : sum_list ∘ singleton_list = id := 
  rfl

/-
Find the sum_list function in Mathlib
-/

#check List


/-
A badly specified function 
-/


-- def loop (n : ℕ) := loop (n + 1)





