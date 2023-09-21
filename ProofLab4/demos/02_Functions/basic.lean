/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofLab4
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 

open Real -- opening namespace. 




/-! # Functions -/ 



/-! ## Some Examples -/

#check ℕ 


/- The __first way__ to specify functions -/


/-- Takes a natural number and returns the next/successor one.  -/
def succ := fun (n : ℕ) => n + 1  -- fun (n : ℕ) => n + 1


def succ_alt := fun n => n + 1

#check @succ  -- `succ : ℕ → ℕ` . `ℕ → ℕ` is the type of all functions from natural numbers to natural numbers. `succ` is a term of `ℕ → ℕ`. In other words, `succ` is a function from natural numbers to natural numbers.   

#check @succ_alt -- the type of variable n is automatically infered as a natural number. 


--#eval succ -- Lean cannot evaluate functions without input.  

#eval succ 0 -- input : 0 , output :1
#eval succ 1000 -- input : 1000 , output :1001



/-
A : Type    B: Type
------------------- (formation rule of function types)
    A → B : Type 


a : A |- f(a) : B 
--------------------- (introduction rule)
fun a => f a : A → B


Example: 
n : ℕ  ∣- 2 * n : ℕ 
---------------------
fun n => 2 * n : ℕ → ℕ  
-/




#check double 
#check @double


#eval double 20




/- Puzzle: define a function `ℕ → ℚ` which takes a natural number and halves it. -/


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



#check half_neg



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

/- `:=` for definition  -/
def succ_alt_alt (n : ℕ) :=  n + 1


#check @succ_alt_alt


#check @double'
#reduce double'


-- syntactically this function is different than `double` and `double'`.
-- #check double_alt 


/- 
Let `square : ℕ → ℕ`  be the function defined by `square (n) = n * n`: 
-/

#check square
#eval square 3


/- All functions in Lean are __total__/__exhaustive__ which means they must return an output for each input of the domain. For instance think of taking the square root of a real number. In standard mathematics textbooks, this is only possible if the argument (i.e. what goes under √) is nonnegative. -/

#check @sqrt  -- the square root function is defined in Mathlib. -- √ x = a means a * a = x. Because a * a = x is nonnegative for all a, the square root function is only defined for nonnegative real numbers. Therefore, it does not make sense to write √ -9. 

-- `x ↦ √ x` has the type of input ℝ≥0  and output ℝ?  √ 2 is not a rational number.

/- exercise: proving in Lean that √ 2  is not a natural number because 1 < √ 2 < 2 -/

/- x= √ 2 then by definition x^2 = 2. It follows that 1 < x otherwise x^2 ≤ 1 which is not true since x^2 = 2.   

√ -1 = i 
-/

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
| _ => false     -- _ means anything else (aka otherwise. sometimes in math textbooks people write o.w.)


#check @isLectureDay
#eval isLectureDay Weekday.Tuesday

-- def switch : Bool → Bool  
-- | true => false
-- | false => true


#check switch 
#eval switch false


-- def nat_of_bool : Bool → ℕ 
-- | false => 0 
-- | true => 1 


#check nat_of_bool
--#eval nat_of_bool ff


/- Suppose we have a type `X` and a decision function `d : X → bool`. Define a function `X → ℕ` which takes a `x : X` and returns `0` if `d x = false` and `1` if `d x = true`.     -/


section 
variable {X : Type} {d : X → Bool}

-- def nat_of_bool_decision 
end 


/- __if ... then ... else ...__ style of definition -/

/- define a function `bool_of_nat : ℕ → bool` which takes a natural number `n` as input and returns `true` if `n` is positive and `false` if `n` is zero. -/
-- def bool_of_nat (n : ℕ) := 
-- if n = 0 then false else true


def bool_of_nat_alt : ℕ → Bool 
| 0 => false
| _ =>  true


/- define a function which takes even numbers to `0` and odd numbers to `1`-/


#check Even 
#check Odd


#check !true

example : !true = false  := by rfl


/- figure it out later -/
def even_odd : ℕ → Bool 
| 0 => true
| 1 => false
| (n + 1) => ¬ even_odd n 


def even_odd_alt (n : ℕ) := 
if (Even n) then true else false


#eval even_odd 1009


-- #check bool_of_nat

-- def isOne (n : Nat) : String := if n = 1 then "yes" else "no"

#check isOne
#eval isOne 0



/- The __absolute value__ function -/
#check (abs : ℚ → ℚ)
#check (abs : ℝ → ℝ)
#check abs (-3 : ℚ)
#eval abs (-3 : ℚ)
#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)





/-
Consider the multivariable function `rational_sum_of_squares : ℚ → ℚ → ℚ` defined by `g x y  = x^2 + y^2`.
-/



-- def rational_sum_of_squares_alt (p : ℚ × ℚ) := 
-- sorry 


#eval rational_sum_of_squares (3/5) (4/5)

#check uncurry rational_sum_of_squares

#eval uncurry rational_sum_of_squares (3/5, 4/5)





/- for a pair `p`, i.e. a term of type `X × Y` the output of `fst` is the first coordinate of `p` which we access using the first projection `.1`. 
-/
#check fst


/- for a pair `p`, i.e. a term of type `X × Y` the output of `snd` is the second coordinate of `p` which we access using the second projection `.2`. 
-/

#check snd


#check curry fst

#eval curry fst 1 2


/- Define a function `distance_rat : ℚ → ℚ → ℚ` which takes two rational numbers `x : ℚ ` and `y : ℚ ` as inputs and returns as output the standard Euclidean distance `| x - y |` between them. 
-/ 
-- def distance_rat (x y : ℚ) := 
-- sorry


--#check distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should be a rational number
--#eval distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should evaluate to 1
--#eval distance_rat (1/3) (1/2)














