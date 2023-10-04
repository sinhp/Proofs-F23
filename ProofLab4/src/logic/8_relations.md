/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Int.Basic

import Mathlib.Data.Real.Basic



/- 
A __binary relation__ on a type `X` is a two-variable predicate `R : X → X → Prop`, that is, a proposition `R x y` attached to each pair of elements of `X`.

In mathematics, we often use __infix notation__, writing  `a R b` instead of `R a b`, e.g. `a = b`, `a ≤  b`, etc. Equality an inequality are relations.

* Examples of relations: 

1. The relation on days on the calendar, given by falling on the same day of the week. 
2. The relation on vegetable produce, given by price of x is less than price of y. 
3. The relation on people currently alive on the planet, given by x and y have the same home address. 
4. The relation on people in the world, given by x is a brother of y.
5. The relation on people in the world, given by x is a sister of y.
6. The relation on people in the world, given by person x is influenced by person y.
7. The relation on lines on a 2-dim plane, given by line l and line m are parallel to each other. 
-/ 


-- let `X` be a type, and let `R` be a binary relation on `X`.

variable {R : X → X → Prop}





/- We say that a relation `R : X → Y → Prop`  is functional if it satisfies the following property: 
- If `R x y` and `R x z`, then `y = z`, for every `x y z` of `X`. In other words, if `x` is related to `y` and `x` is related to `z`, then `y` and `z` are the same. Simply put, `x` cannot be related to two different elements. 
- There is at least one element `y` of `X` such that `R x y` for every `x` of `X`. In other words, every element of `X` is related to at least one element of `X`.
-/ 

def fun_rel (R : X → Y → Prop) := 
  (∀ x y z : X, R x y → R x z → y = z) ∧ (∀ x : X, ∃ y : X, R x y)

/-
We show that if a relation is functional, then it is i
-/
