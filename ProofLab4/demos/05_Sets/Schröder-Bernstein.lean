/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofLab4
import Mathlib.Data.Real.Basic -- in this file in Mathlib the real numbers are defined. 
import Mathlib.Data.Real.Sqrt -- this file defines the square root of a real number. 


/-
Schröder-Bernstein theorem: 
If we have injections `f : A → B` and `g : B →A` then `A` and `B` are in bijection which means we have a function `h : A → B` which is a bijective. 

Example: constructing a bijection between the closed interval `[0,1]` and the half-closed interval `[0,1)`. 

If we want to teach Lean about the Schröder-Bernstein theorem we need Lean to understand the following stuff: 

1. Injectivity of functions. 
2. Bijectivity of functions. 
2.1. The left and right inverses of a function

3. To construct `h` we need the notion of image "functor" of a function. 

4. Sets and their union 


For the example 
5. intervals of real numbers. 
-/




















/-! #Toward Schröder-Bernstein Theorem -/


/- We need the following ingredients to state Schröder-Bernstein Theorem and cook up a proof of it

* Injective Functions 
* The left and right inverses of a function
* Sets and their union 
* Image functor of a function 
* 




 -/