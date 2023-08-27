/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Mathlib.Data.Real.Basic

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! This lecture is about the most basic objects we will deal with in the entire course, namely __types__. We will introduce bunch of types and how to construct their elements. 
This lecture is essentially an intro to the programming language aspect of Lean. 
-/

/-! ## Types (Collections) And Terms (Element)


In Lean things are largely organized as __types__ (collections) and __terms__ (elements). __In Lean every expression is typed__.  You can use the `#check` command to print its type.

Some familiar number systems such as __natural numbers (ℕ)__ , __integers (ℤ)__, __rational numbers (ℚ)__, and __real numbers (ℝ)__ are encoded as types in Lean. (Lean's "check" command tells us the type of the object we have constructd). 
-/

#check Nat -- the type of __natural numbers__
#check ℕ -- (ℕ is a special symbol typed by ℕ or \nat )

#check Int -- the type of __integers__ 
#check ℤ -- (ℤ is a special symbol typed by \Z or \int)

#check Rat  -- the type of __rationals__
#check ℚ -- (ℚ is a special symbol typed by \Q or \rat)

#check Real -- the type of __real numbers__
#check ℝ -- (ℝ is a special symbol typed by \R or \real)


/- 
All types, except the __empty__ type, have __terms__ (or elements, or inhabitants). For instance `0 : ℕ`. We read the expression `a : A` as `a is an A`. So `0 : ℕ` says `0 is a natural number`, and `0 : ℤ` says that `0 is an integer`.
-/  

#check Empty -- the empty type  does not have any terms: we cannot find any `a` such that `a : Empty`. 

 

#check Bool -- the type of __booleans__: there are two terms in this type `true` and `false`. 
#check true
#check false 


#check 0 
-- The default type of `0` is `nat` 
-- InfoView displays `0 : ℕ` 
-- Read `0 : ℕ` as saying, "`1` is a natural number."

#check (0 : ℤ) -- We can coerce it to have a different type, such as ℤ, if we wish. 
#check 2
#check (2 : ℝ)

#check (2 : ℤ) + 3 
#check 2 + (3 : ℤ)

#eval 2 + (3 : ℤ) -- We can __evalute__ terms to their simplests form (the so called __canonical__ form). 


#check 1/2 -- since 1 and 2 are natural numbers Lean by default use the division operator between natural numbers. 

#check 1/(2:ℚ) -- we can force Lean to consider the rational numbers division. 

#check (1:ℚ)/2 -- or this way 

def rational_one := (1 : ℚ)

#check rational_one/2

example : 
  rational_one/2 = 1/(2:ℚ) := 
by rfl 


-- `.1` and `.2` are projections from the cartesian space `ℚ × ℚ` to `ℚ` which pick the first and second coordinates. 
#eval (52,4).1
#eval (52,4).2
#eval (52.3676,4.9041).1
#eval ( (52.3676,4.9041).1 : ℚ)



/-! ### New Types from the Old 

In below we shall see some new types constructed from the old ones; we shall also see what the terms of these new types are. 
-/


section 
variable {A B : Type} -- Suppose `A` and `B` are types. We do not know anything about types `A` and `B` except the fact that they are types. We don't even know if they have any terms. 

/- The type of __pairs__: The terms of `A × B` are pairs `(a , b)` where `a : A` and `b : B`. Therefore, if `a : A` and `b : B` then  `(a , b) : A × B`.  -/

#check A × B 

end 



#check ℕ × ℕ 
#check (1 , 2)  -- round brackets for tuples

#check ℕ × ℤ 
#check (1 , (2 : ℤ))
#check ((2 : ℤ) , 1)

#check ((1 : ℝ), (-1 : ℝ))
#check ((1 , -1) : ℝ × ℝ)


#check (1 , (2 , 3))
#check (1 , 2 , 3) 


/-
⊢ ℚ × ℚ
-/
#check ((2.2 : ℚ), (1.7 : ℚ))
/-
⊢ Float × Float
-/
#eval  (2.2, 1.7)

/-
A B : Type
⊢ ℚ × ℚ
-/
#check (1/(3:ℚ), 7/(5:ℚ))

/-
(1 / 3, 7 / 5) : ℚ × ℚ
-/
#check ( (1/3, 7/5) : ℚ × ℚ ) 



#check "hello world"


-- If `A : Type` we can form a new type whose terms are lists of terms of `A`. 
section
variable {A : Type} 
#check List A -- The type of __lists__ of `A`
end 


#check List ℕ 

#check [0,2,5] -- Lean infers the type of the list `[0,2,5]`. How? 
#check [2,0,5] -- this is a different list than the one above

#check ([1, 2, 3] : List ℤ)  

-- #check [(1 : ℕ), (-1 : ℤ) ] -- gives error because the members of a list must have the same type


#check [] -- There is always an empty list, i.e. a list that lists nothing at all. But what is its type? 

#check ([] : List ℕ) 
#check ([] : List ℝ)
-- Think of an empty bookshelf vs an empty bottle of milk, both empty but different beings. 


#check List Empty 
#check ([] : List Empty) -- the empty list of the empty type 


def my_negative_two := (-2 : ℤ) 
#check [my_negative_two] -- the list that has only one member in it and that is `-2 : ℤ`. 


def my_list := ([1, 2, 3] : List ℤ)  

#eval my_list ++ [-1,-2] -- we can add lists by appending the second list to the end of the first one. 

#eval [-1,-2] ++ my_list  -- clearly this is different from `my_list ++ [-1,-2]` so the order of addition matter, but how can we prove this in Lean? 


example : 
  my_list ++ [my_negative_two] = [1,2,3,-2] := 
rfl


#check Array Nat
-- https://leanprover.github.io/lean4/doc/array.html

#check #["hello", "world"] -- Array String



section 
variable {A B : Type}
#check A ⊕ B  -- The __sum__ type of `A` and `B`: write ⊕ using \oplus or \o+

-- Terms of `A ⊕ B` are of the form `Sum.inl a` for some `a : A` or `Sum.inr b` for some `b : B`.   
end 


#check ℕ ⊕ Bool 

variable (s : ℕ ⊕ Bool)

#check (Sum.inl 2 : ℕ ⊕ Bool)

#check Sum.inl 2

#check (Sum.inr false : ℕ ⊕ Bool)



/- Finite Types -/

section 
#check Fin
#check Fin 3 -- this is the type that whose terms are natural numbers less than 3: there are three elements in this type, namely 0, 1, 2.
variable (t : Fin 3)
#check t.1
#check t.2

-- Later we prove that Fin 6 = Fin 2 × Fin 3 --

end 

#check Finset
#check Finset.range



/- type alias -/
abbrev Index := ℕ

theorem foo (a b : ℕ) (H : a < b) : a < 2 * b := 
  by linarith

/-- linarith failed to find a contradiction -/
-- theorem index_check_fail (a b : Index) (H : a < b) : a < 2 * b := 
-- by 
--   linarith 
  

theorem index_check (a b : Index) (H : a < b) : a < 2 * b := 
  by simp[Index] at *; linarith