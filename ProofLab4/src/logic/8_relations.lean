/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Int.Basic

import Mathlib.Data.Real.Basic



/- 
A __binary relation__ on a type `X` is a two-variable predicate `R : X → X → Prop`, that is, a proposition `R x y` attached to each pair of elements of `X`.

In mathematics, we often use __infix notation__, writing  `a R b` instead of `R a b`, e.g. `a = b`, `a ≤  b`, etc. Equality an inequality are relations.

* Some examples of relations: 

1. The relation on days on the calendar, given by falling on the same day of the week.
`same_day : day → day → Prop` 
2. The relation on vegetable produce, given by price of x is less than price of y. 
`veg_price : veg → veg → Prop`
3. The relation on people currently alive on the planet, given by x and y have the same home address. 
`same_address : person → person → Prop`
4. The relation on people in the world, given by x is a brother of y.
`brother : person → person → Prop`
5. The relation on people in the world, given by x is a sister of y.
`sister : person → person → Prop`
6. The relation on people in the world, given by person x is influenced by person y.
`influenced_by : person → person → Prop`
7. The relation on lines on a 2-dim plane, given by line l and line m are parallel to each other. 
`parallel : line → line → Prop`
8. The relation on lines on a 2-dim plane, given by line l and line m are perpendicular to each other.
`perpendicular : line → line → Prop`
9. The relation on lines on a 2-dim plane, given by line l and line m intersect each other.
`intersect : line → line → Prop`
-/ 



/-
A relation `R` from a type `X` to a type `Y` is a function `X → Y → Prop`: For each `x : X` and `y : Y`, we read the proposition `R x y` as "`x` is related to `y`".

* Examples of relations from `X` to `Y`:

- The Relation of a sequence of rational numbers tending to a real number `x`: 
`tendsto : (ℕ → ℚ) → ℝ → Prop`

- The relation on `ℕ` and `ℤ`, given by `x` is less than or equal to `|y|`.
`le_abs_self : ℕ → ℤ → Prop`

- The relation of a point being incident to a line: 
`incidence : point → line → Prop`
-/


/-
Every function `f : X → Y` induces (i.e. gives rise to) a relation `R : X → Y → Prop` given by `R x y := f x = y`.
-/


def rel_of_fun {X Y : Type} (f : X → Y) : X → Y → Prop := 
  fun x y => f x = y



/- We say that a relation `R : X → Y → Prop`  is functional if it satisfies the following property: 
- If `R x y` and `R x z`, then `y = z`, for every `x y z` of `X`. In other words, if `x` is related to `y` and `x` is related to `z`, then `y` and `z` are the same. Simply put, `x` cannot be related to two different elements. 
- There is at least one element `y` of `X` such that `R x y` for every `x` of `X`. In other words, every element of `X` is related to at least one element of `X`.
-/ 

-- def functional_rel (R : X → Y → Prop) := 
--   (∀ x y z, R x y → R x z → y = z) ∧ (∀ x, ∃ y, R x y)

-- def is_fun_rel (R : X → Y → Prop)  := 
--   (∀ x y z, R x y → R x z → y = z) ∧ (∀ x, ∃ y, R x y)


def is_fun_rel (R : X → Y → Prop)  := 
  (∀ x, ∃ y, R x y)

/-
We show that a relation induced by a function is functional.
-/

-- lemma is_fun_rel_of_fun {X Y : Type} (f : X → Y)  : 
--   is_fun_rel (rel_of_fun f)  :=
-- by 
--   constructor
--   · intro x y z hy hz; simp only [rel_of_fun] at *; rw [← hy, hz]
--   · intro x; use f x; rfl


lemma is_fun_rel_of_fun {X Y : Type} (f : X → Y)  : 
  is_fun_rel (rel_of_fun f)  :=
by 
  intro x; use f x; rfl

/-
We show that if a relation is functional, then it induces a function.
-/

noncomputable
def fun_of_rel {X Y : Type} (R : X → Y → Prop) (h : is_fun_rel R) : X → Y := 
  fun x => Classical.choose (h x)


/-
Classical.choose.{u} {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α
-/
#check Classical.choose
/-
⊢ ∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (Classical.choose h)
-/
#check Classical.choose_spec

lemma fun_of_rel_of_rel_of_fun {X Y : Type} (f : X → Y)  : 
  fun_of_rel (rel_of_fun f) (is_fun_rel_of_fun f) = f :=
by 
  symm
  ext x 
  unfold fun_of_rel
  unfold rel_of_fun
  have h := (is_fun_rel_of_fun f)
  dsimp [rel_of_fun] at h
  exact Classical.choose_spec (h x)
  


namespace FunRel

variable (S : X → Y → Prop) (a : X)


class Weak_Fun_Rel (R : X → Y → Prop) : Prop where 
  (surj : ∀ x, ∃ y, R x y)

#check Weak_Fun_Rel

class Fun_Rel (R : X → Y → Prop)  extends Weak_Fun_Rel R : Prop where
  (inj : ∀ x y z, R x y → R x z → y = z)

#check Fun_Rel
#print Fun_Rel

#check Weak_Fun_Rel.surj 

noncomputable
def fun_of_rel [Weak_Fun_Rel S] : X → Y := 
  fun x => Classical.choose (Weak_Fun_Rel.surj (R := S) x)

#check fun_of_rel -- (S : X → Y → Prop) → [Weak_Fun_Rel S] → (X → Y)

#check rel_of_fun -- (X → Y) → (X → Y → Prop)


instance : Weak_Fun_Rel (rel_of_fun f) where
  surj := by intro x; use f x; rfl




lemma fun_of_rel_of_rel_of_fun {X Y : Type} (f : X → Y)  : 
  fun_of_rel (rel_of_fun f) = f :=
by 
  symm
  ext x 
  unfold fun_of_rel
  unfold rel_of_fun
  apply Classical.choose_spec (p := fun y => f x = y)

-- instance : Weak_Fun_Rel S := 
-- by sorry


-- #check rel_of_fun (fun_of_rel S)

#check Preorder
#print Preorder

universe u
variable (X Y : Type)

set_option trace.Meta.synthInstance true in
instance : Preorder (X → Y → Prop) := inferInstance 



def rel_of_fun_of_fun_of_rel₁ [Weak_Fun_Rel S] : 
  (rel_of_fun (fun_of_rel S)) ≤ S := 
by 
  intro x y hxy
  unfold rel_of_fun at hxy
  unfold fun_of_rel at hxy
  have h := Classical.choose_spec (Weak_Fun_Rel.surj (R := S) x)
  dsimp [rel_of_fun] at h
  rw [hxy] at h
  exact h


def rel_of_fun_of_fun_of_rel₁₂ [Fun_Rel S] : 
  S ≤ (rel_of_fun (fun_of_rel S)) :=
by 
  intro x y hxy
  unfold rel_of_fun
  unfold fun_of_rel
  have h := Classical.choose_spec (Weak_Fun_Rel.surj (R := S) x)
  dsimp [rel_of_fun] at h
  symm
  apply Fun_Rel.inj (R := S) x y (Classical.choose (Weak_Fun_Rel.surj (R := S) x)) hxy h







end FunRel




  #check CanLift