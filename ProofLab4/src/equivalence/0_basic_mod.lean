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



/- Example: division relation between integers -/


/- 
`divides` is an example of binary relation on `ℤ` built from the existential quantifier (`∃`): the proposition `divides m n` states that the natural number `m` divides natural number `n`. For instance `divides 12 60` and `divides 3 -6` 
-/

@[simp]
def divides (m n : ℤ) := ∃ k : ℤ, n = m * k
#check divides 


lemma self_divide_self_sqr (x : ℤ) 
  : divides x (x^2) :=
by 
 use x 
 exact sq x


theorem divides_mul_right (a b : ℤ) : 
  a ∣ a * b := 
by 
 sorry 

theorem mul_divides_mul {a b c d : ℤ} : 
  a ∣ b → c ∣ d → a * c ∣ b * d := 
by 
  intro hab hcd 
  cases' hab with k hk 
  cases' hcd with l hl
  use l * k 
  simp [hk, hl]
  ring




theorem divides_sum (a b c : ℤ) : 
  a ∣ b → a ∣ c → a ∣ b + c :=  
by    
  intro hab hcd 
  cases' hab with k hk 
  cases' hcd with l hl
  use l + k 
  simp [hk, hl]
  ring


example (a b : ℤ) :
  divides  (a + b) (a^2 + (2 * a + b) * (b + 1) - a) := 
by 
  have : a^2 + (2 * a + b) * (b + 1) - a = (a + b)^2 + (a + b) := by ring
  rw [this]
  apply divides_sum (a + b) ((a + b)^2) (a + b)
  apply self_divide_self_sqr
  rfl 
 



lemma self_divide_self_pow (x : ℤ) (n : ℕ) (h : 0 < n)
  : divides x (x^n) :=
by 
 use x^(n-1)
 sorry 



example : 
  ∀ n : ℤ, divides 2 n ↔ Even n := 
by
  intro n -- we want to prove the ∀ statement `∀ n, divides 2 n ↔ is_even n`
  constructor 
  · dsimp at *; intro ⟨k, hk⟩; use k; rw [hk]; ring;   
  · dsimp [Even]; rintro ⟨r, hr⟩; use r; rw [hr]; ring; 
    


lemma divides_trans (x y z : ℤ) (h₀ : divides x y) (h₁ : divides y z) : 
  divides x z :=
by 
  unfold divides at * 
  obtain ⟨k₀, hk₀⟩ := h₀ 
  obtain ⟨k₁, hk₁⟩ := h₁ 
  use k₀ * k₁
  rw [← mul_assoc, ← hk₀, hk₁]

#check IsSymm
#check symm

example : ¬ (IsSymm ℤ divides) := 
by 
  intro σ 
  have h₁ : divides 1 2 := by use 2; rfl
  have h₂ := σ.symm 1 2 h₁  
  sorry 

#check dvd_antisymm 











/-
If `R` is Reflexive, symmetric and transitive, we say it is an __equivalence relation__. 

We will use the standard notation `x ≈ y` for `R x y` when `R` is an equivalence relation.

* __reflexivity__:  
`R x x`, for every `x` of `X`. 

* __transitivity__: 
If `R x y` and `R y z`, then `R x z`, for every `x y z` of `X`. 

* __symmetry__: 
If `R x y` then `R y x`, for every `x y` of `X`. 


Exercise: decide which of the relations above (1-7) are reflexive, transitive, or symmetric.

In Lean: 
`Reflexive R := ∀ (x : X), R x x`
`symmetric R := ∀ ⦃x y : X⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : X⦄, R x y → R y z → R x z`
`equivalence R := Reflexive R ∧ symmetric R ∧ transitive R`
-/


#reduce Reflexive R -- ∀ (x : X), R x x
#reduce Symmetric R -- ∀ ⦃x y : X⦄, R x y → R y x
#reduce Transitive R -- ∀ ⦃x y z : X⦄, R x y → R y z → R x z


example :
  Equivalence R ↔ Reflexive R ∧ Symmetric R ∧ Transitive R := 
by 
  sorry  



/- Counterexample: as observed above `divides` is transitive and it is also obviously reflexive (why?). But it is not symmetric. Therefore  `divides` is not an equivalence relation. -/


/- In below we prove some general lemmas about reflexive, transitive and symmetric relations. -/

namespace equivalence

lemma refl_ext_left {ρ : Reflexive R} (x y : X) (H : ∀ a : X,  R a x → R a y) : 
  R x y :=
by 
  sorry 

/- Think about what the lemma above says for the relation `divides` -/

lemma refl_ext {ρ : Reflexive R} (x y : X) (H : ∀ a: X,  R x a ↔ R y a) : 
  R x y :=
(H y).mpr (ρ y) 

lemma refl_symm_ext_left {ρ : Reflexive R} {σ : Symmetric R} (x y : X) (H : ∀ a : X,  R x a → R y a) : 
  R x y :=
σ (H x (ρ x))   

theorem eqv_rel_ext {eqv : Equivalence R} (x y : X) (H : ∀ a : X,  R x a → R y a) : R x y :=
by 
  obtain ⟨ρ, σ, τ⟩ := eqv
  sorry

theorem trans_ext {tr : Transitive R} (x y : X) (H : ∃ a : X, R x a ∧ R a y) : R x y := 
by 
  sorry 

end equivalence -- end of namespace





/- From now on we shall use Mathlib's version of `divides` which is defined in a higher levle of generality, not just for integers. For instance suppose we wanted to define the relation of divisibility also on natural numbers. We can analogously define another predicates ` divides' : ℕ → ℕ → Prop`. Clearly, it is not a great idea to have these different unrelated versions of divisibility relation; we want to have a unified treatement. This is what `Dvd` does; it uses the idea of _casting_ and _type classes_ which is one of the more advanced topics we shall cover in the future lectures. 

Mathlib's divisibility relation also has a dedicated symbol `∣`.  

Be careful! The divisibility symbol is not the ordinary bar on your keyboard. Rather, it is a unicode character obtained by typing `\|` in VS Code. 
-/

#check Dvd

example : 4 ∣ 12 := 
by 
  use 3

example : ¬ 4 ∣ 10 := 
by 
  intro h
  cases' h with d hd 
  have h₁ : 5 = 2 * d := sorry 
  have h₂ : 2 ∣ 5 := sorry 
  sorry 


example {a b : ℤ} (n : ℕ) (hab : a ∣ b) : a ∣ b ^ 2 - n * b := by
  obtain ⟨d, hd⟩ := hab -- note the casting of Nat to Int in the goal: the up-arrow in the expression `a ∣ b ^ 2 + ↑n * b` indicates that `n : ℕ` is considered as an integer `↑ n : ℤ`.  
  use d * (a * d - n)
  calc
    b ^ 2 - n * b = (a * d) ^ 2 - n * (a * d) := by rw [hd]
    _ = a * (d * (a * d - n)) := by ring


#check pos_of_mul_pos_right

example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := 
by
  obtain ⟨k, hk⟩ := hab
  have : 1 ≤ k
  · apply pos_of_mul_pos_right (a := a); rw [← hk]; exact hb; linarith
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [this]
    _ = b := by rw [hk]



#check dvd_of_mul_right_dvd 


/-- Two integers are congruent modulo `n`, if their difference is a multiple of `n`. -/
def mod_cong (n a b : ℤ) : Prop := n ∣ a - b 

notation:50  a " ≡ " b " [ZMOD " n "]" => mod_cong n a b

/- type `≡` using `\==`. -/

#check mod_cong 
#check mod_cong 3

example : 2 ≡ 5 [ZMOD 3] := 
by 
  use -1 
  rfl 


/- We now show that the relation of  `mod_cong` is in fact an equivalence relation -/ 

namespace mod_cong_equiv

theorem refl {n : ℤ} : x ≡ x [ZMOD n] := 
by 
  use 0 
  ring 


#check mod_cong_equiv.refl

theorem symm {n : ℤ} (h : x ≡ y [ZMOD n]) : y ≡ x [ZMOD n] := 
by 
  obtain ⟨k, hk⟩ := h  
  use -k 
  apply Iff.mp Int.neg_inj
  simp 
  exact hk 


theorem trans {n : ℤ} (hxy : x ≡ y [ZMOD n])
(hyz : y ≡ z [ZMOD n]) : 
 x ≡ z [ZMOD n] := 
by 
  have : n ∣ (x - y) + (y - z)  := divides_sum _ _ _ hxy hyz 
  simpa using this 


instance trans_mod_cong (n : ℕ) : 
Trans (mod_cong n) (mod_cong n) (mod_cong n) where 
trans h₁ h₂ := trans h₁ h₂

  
#check Trans

end mod_cong_equiv

/-! ### Modular Arithmetic -/

theorem mod_cong.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := 
by
  sorry 

theorem mod_cong.mul {n a b c d : ℤ} (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := 
by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring


theorem mod_cong.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := 
by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring


lemma mod_cong.linear (ha : a ≡ a' [ZMOD n])
    (hb : b ≡ b' [ZMOD n])
    (hc : c ≡ c' [ZMOD n]) :
  (a * b + c ≡ a' * b' + c' [ZMOD n]) :=
by 
  have H
  ·  apply mod_cong.mul ha hb
  apply mod_cong.add H hc


example (ha : a ≡ a' [ZMOD n])
    (hb : b ≡ b' [ZMOD n])
    (hc : c ≡ c' [ZMOD n]) :
  (a * b + c ≡ a' * b' + c' [ZMOD n]) :=
mod_cong.add (mod_cong.mul ha hb) hc





-- example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by  
--   sorry






-- #check gcd

-- example : gcd m n = gcd n m := by
--   apply _root_.dvd_antisymm
--   repeat'
--     apply dvd_gcd
--     apply gcd_dvd_right
--     apply gcd_dvd_left