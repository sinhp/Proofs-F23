/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
--import Mathlib.Logic.Equiv.Basic
--import Mathlib.Logic.Equiv.Embedding

#check RightInverse


namespace Function 
/- 
In this file we shall define bijections, and we show that the bijection between sets defines an equivalence relation. 
-/


/-
A functions `f` is a __left inverse__ to a function `g` if `f ∘ g = id`.  
-/
@[simp] 
def left_inv {A B : Type} (f : A → B) (g : B → A)  := f ∘ g = id 

#check left_inv


/-
Example of a left inverse: 
-/

example : left_inv (fun (x : ℤ) => x + 1) (fun (x : ℤ) => x - 1) :=
by 
  simp [left_inv]
  ext x 
  simp [id] 



/-
A functions `g` is a __right inverse__ to a function `f` if `f ∘ g = id`. 
-/
@[simp] 
def right_inv {A B : Type} (g : B → A) (f : A → B) := f ∘ g = id



#check RightInverse
#check LeftInverse



theorem RightInverse.elm (g : Y → X) (f : X → Y) (y : Y) : 
  RightInverse g f →  f (g y) = y := 
by 
  simp[RightInverse]
  intro h
  exact h y
 
example (g : Y → X) (f : X → Y) (hfg : RightInverse g f) (k : Y → X) (hfk : LeftInverse f k) : 
  RightInverse g (f ∘ k ∘ f) :=
by 
  simp [RightInverse]
  intro x 
  dsimp 
  rw [hfg, hfk]


#check LeftInverse.comp

/- 
Give an example of use of `LeftInverse.comp`
-/





/- Complete the proof of the lemma 
`inv_of_left_inv_and_right_inv` in below which says that if a function has both a left inverse and a right inverse, then they are equal. 
-/

#check comp.assoc

lemma inv_of_left_inv_and_right_inv (f : A → B) (g : B → A) (k : A → B) (h₁ : LeftInverse f g) (h₂ : RightInverse k g) : 
k = f :=
-- the statement above says that if `f` is a left inverse of `g` and `k` is a right inverse of `g` then `k = f`. 
by 
  funext x 
  calc 
  k x = (id ∘ k) x := rfl
  _   = ((f ∘ g) ∘ k) x := by simp [h₁ (k x)]
  _   = f ((g ∘ k) x) := by simp 
  _   = f x := by simp [h₂ x]

/- we can invoke `funext` later: -/
example (f : A → B) (g : B → A) (k : A → B) (h₁ : LeftInverse f g) (h₂ : RightInverse k g) : 
k = f :=
by 
  calc 
  k = (id ∘ k) := rfl
  _ = ((f ∘ g) ∘ k) := by congr! ; funext x ; simp [h₁ x]   
  _ = f ∘ (g ∘ k) := by rw [comp.assoc]
  _ = f ∘ id := by funext x ; simp [h₂ x]
  _ = f := by rfl   


/-! Can you redefine `LeftInverse` and `RightInverse` so that we do not need to use `funext`?  -/

def LeftInverse' (f : A → B) (g : B → A) := f ∘ g = id

def RightInverse' (f : A → B) (g : B → A) := g ∘ f = id

lemma inv_of_left_inv_and_right_inv' (f : A → B) (g : B → A) (k : A → B) (h₁ : LeftInverse' f g) (h₂ : RightInverse' k g) :
k = f :=
  by 
    calc 
    k = (id ∘ k) := by rfl
    _ = ((f ∘ g) ∘ k) := by congr! ; rw [h₁]
    _ = f ∘ (g ∘ k) := by rw [comp.assoc]
    _ = f ∘ id := by congr; rw [h₂]
    _ = f := by rfl




/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure equivalence (α : Type) (β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse invFun toFun
  right_inv : RightInverse invFun toFun


#check Equiv

#check ℕ ≃ ℤ  -- the type of equivalence between `ℕ` and `ℤ`. 



/- There is no equivalence between the empty type and the unit type. -/
lemma empty_not_equiv_unit (f : Empty ≃ Unit) : False :=
by 
  cases' f with f_to f_inv h₁ h₂ 
  /- the function `g` construct a term of empty type which is no possible-/
  let impossible_term := f_inv ()
  apply Empty.elim
  exact impossible_term


#check IsEquiv

/- We say two types are __equivalent__ if there is an equivalence between them. -/


def is_equiv (α β : Type) := Nonempty (α ≃ β)

#check is_equiv


/- With the above definition of _equivalent types_ let us prove that the empty type and the unit type are not equivalent! -/

lemma empty_not_equiv_unit' : ¬ is_equiv Empty Unit :=
by 
  intro h
  cases' h with f
  apply empty_not_equiv_unit f  


/- Let's prove that ℕ and ℤ are equivalent types.  -/

lemma nat_equiv_int : is_equiv ℕ ℤ :=
sorry 






/-
`is_equiv` is a binary relation. 
Let's prove that it is an equivalence relation.
-/

/-
Let's prove that `is_equiv` is reflexive.
-/
lemma is_equiv_refl (α : Type) : is_equiv α α :=
by 
  apply Nonempty.intro 
  exact Equiv.refl α


/- Let's prove that if `α` and `β` are equivalent types, then `β` and `α` are equivalent types. -/
lemma is_equiv_symm {α β : Type} : is_equiv α β → is_equiv β α :=
by 
  intro h 
  cases' h with f 
  apply Nonempty.intro 
  exact Equiv.symm f

/-
Let's prove that if `α` and `β` are equivalent types, and `β` and `γ` are equivalent types, then `α` and `γ` are equivalent types.
-/
lemma is_equiv_trans {α β γ : Type} : is_equiv α β → is_equiv β γ → is_equiv α γ :=
by 
  intros h₁ h₂
  cases' h₁ with f
  cases' h₂ with g
  apply Nonempty.intro
  apply Equiv.trans f g

#check is_equiv_symm

#check Equivalence 

/- Let's prove that `is_equiv` is an equivalence relation. -/
lemma is_equiv_equiv : Equivalence is_equiv where
  refl := is_equiv_refl
  symm := is_equiv_symm 
  trans := is_equiv_trans

#check is_equiv_equiv


/-
We know that a type is finite and has exactly one element. Let's construct an elemanet of that type. 
-/

#check Finset 
/- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/


/- We show that evert finite subset is in fact a subset-/
def test_set_of_finset (α : Type) (s : Finset α) : Set α := fun x => x ∈ s




def one_out_fun (α : Type) (h : Fintype α) (h' : Fintype.card α = 1) : α :=
by 
  cases' h with s hs 
  cases' s with s' ndps 
  sorry 


/-
Let's prove that the every finite set with one element is equivalent to the unit type.
-/


-- lemma is_equiv_unit_of_finite_one (α : Type) (h : Fintype α) (h' : Fintype.card α = 1) : is_equiv α Unit :=
-- by 
--   apply Nonempty.intro 
--   refine ⟨ fun _ => (), fun _ => _ , _ , _⟩ 
--   sorry   



/- In below we prove some useful equivalences of types.-/

variable {A B C : Type} 

#check A × B 
#check A ⊕ B 

#check Unit


#check Sum.rec

def two_out_fun :
  ((Unit ⊕ Unit) → A) ≃  A × A where 
  toFun := λ f => ( f $ .inl () , f $ .inr () )
  invFun := fun p => Sum.rec (fun u => p.1) (fun u => p.2) 
  left_inv := by intro f; funext x; dsimp; cases x; rfl; rfl   
  right_inv := fun p => by cases p; rfl


/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrowProdEquivProdArrow (α β γ : Type) : (γ → α × β) ≃ (γ → α) × (γ → β) where
  toFun := fun f => (fun c => (f c).1, fun c => (f c).2)
  invFun := fun p c => (p.1 c, p.2 c)
  left_inv := by simp [LeftInverse]
  right_inv := by simp[RightInverse]; intro p; cases p; rfl    



def prod_coprod_distrib :
  (C × A) ⊕ (C × B) ≃ C × (A ⊕ B) where 
  toFun := Sum.rec (fun p => (p.1, .inl p.2)) (fun p => (p.1, .inr p.2))
  invFun := fun p => match p.2 with 
                     | .inl a => .inl (p.1, a)
                     | .inr b => .inr (p.1, b)
  left_inv := by intro s; cases s; dsimp; rfl; 
  right_inv := by intro t; cases t; dsimp; sorry
    

end Function 



-- def prod_coprod_distrib [has_binary_coproducts C] [cartesian_closed C] (X Y Z : C) :
--   (Z ⨯ X) ⨿ (Z ⨯ Y) ≅ Z ⨯ (X ⨿ Y) :=
-- { hom := coprod.desc (limits.prod.map (𝟙 _) coprod.inl) (limits.prod.map (𝟙 _) coprod.inr),
--   inv := cartesian_closed.uncurry
--     (coprod.desc (cartesian_closed.curry coprod.inl) (cartesian_closed.curry coprod.inr)),
--   hom_inv_id' :=
--   begin
--     apply coprod.hom_ext,
--     rw [coprod.inl_desc_assoc, comp_id, ←uncurry_natural_left, coprod.inl_desc, uncurry_curry],
--     rw [coprod.inr_desc_assoc, comp_id, ←uncurry_natural_left, coprod.inr_desc, uncurry_curry],
--   end,
--   inv_hom_id' :=
--   begin
--     rw [← uncurry_natural_right, ←eq_curry_iff],
--     apply coprod.hom_ext,
--     rw [coprod.inl_desc_assoc, ←curry_natural_right, coprod.inl_desc, ←curry_natural_left, comp_id],
--     rw [coprod.inr_desc_assoc, ←curry_natural_right, coprod.inr_desc, ←curry_natural_left, comp_id],
--   end }


