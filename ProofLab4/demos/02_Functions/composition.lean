/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProofLab4
import Mathlib.Data.Real.Basic


/-! ## Composition of Functions -/



/-
A function can be implemented in different ways, but once it is implemented, we can forget about the details of its implementation and concentrate on how it interacts with other functions. There is an interesting algebra of interactions of functions.


The main way functions interact is via the operation of __composition__. The main idea of composition of functions is to create _compound_ functions from simpler functions which can do more tasks. 


The operation of composition gives us an incredibly powerful tool to focus on these interaction of functions.


Suppose `f : A → B` and `g : B → C` are functions. 
We define a new function `g ∘ f : A → C` by letting

` g ∘ f (x) =  g(f(x))`


The function `g ∘ f` is called the __composition__ of `f` and `g` which we also call "f composed with g" (or "g after f"). Often when there is no risk of confusion mathematicians dispense with `∘` in the notation above and simply write `g f` for the composition of `f` and `g`.
-/


/- 
Let's say we want to define a function which takes two sequences of real numbers and returns their alternate sum.
For instance if `a` is the sequence `0, 1, 2, 3, 4, ...` and `b` is the sequence `1, 1/2, 1/3, 1/4, 1/5,  ...` then ` alternate_sum a b` is the sequence `1, 1/2, 5/3, 7/4, 21/5, ...`.

One way to define this function is to use an `if-then-else` expression. 
-/

def alternate_sum (a b : ℕ → ℝ) : ℕ → ℝ := 
fun n => if n % 2 = 0 then a n + b n else (a n - b n)

/- ... but we can do better using composition of simpler functions. -/


def alternating (a : ℕ → ℝ) : ℕ → ℝ := fun (n : ℕ) => (-1)^n * (a n)

def sum (a b : ℕ → ℝ) : ℕ → ℝ := fun n => (a n + b n)

def alternating_sum (a b : ℕ → ℝ) : ℕ → ℝ  := sum a (alternating b)



/-! ### Composition of functions in Lean -/

def compose (g: Y → Z) (f : X → Y) : X → Z :=  
fun x : X =>  g (f x)


#check Compose -- Mathlib defines a function called `Compose` which is the same as `compose` we defined above.




section 
variable (f₀ : ℕ → ℤ) (g₀ : ℤ → ℚ) (h₀ : ℚ → ℕ )

#check compose g₀ f₀ 
#check g₀ ∘ f₀ -- shorthand notation for `compose g₀ f₀`. 


/-
- Note that we can compose two functions only if the domain of the first one matches with the codomain of the second one. 
-/

/- 
- A shorthand notation for `compose f g` is `f ∘ g`. To get `∘` type "\comp".
- infixr  ` ∘ ` := comp
-/ 

-- #check g₀ ∘ f₀  
#check h₀ ∘ f₀ -- can you understand the error?
#check (h₀ ∘ g₀) ∘ f₀ 
#check h₀ ∘ (g₀ ∘ f₀)
#check (h₀ ∘ g₀) ∘ f₀ 
#check g₀ ∘ (f₀ ∘ h₀) 

/-
*Note*: by default, Lean reads `h₀ ∘ g₀ ∘ f₀` as `(h₀ ∘ g₀) ∘ f₀`, that is the bracketing is from the left to right.  
-/
end 



/-
There is a wonderful yet very simple function which is defined in the same way for every object. This is the so-called __identity function__ of that object. For an object `A`, Lean defines a function `id : A → A` which assigns to an element `a` itself! Therefore, 
`id a = a`. 
-/ 

section 
variable (a : A)
#check id 
#check id a
end 

lemma id_def (a : A) : id a = a := 
by 
  rfl 



#check switch 
#eval switch false
#check switch ∘ switch 
-- #eval (switch ∘ switch) ff


section 
variable (b : Bool )
#check switch b 
#eval switch true
end 






/- 
lemma switch_switch_alt : 
  switch ∘ switch = id := 
begin
  funext b, 
  dsimp,
  refl, -- this does not work since `switch b` depends on the value of `b`, and we have to reason by cases. 
end 



lemma switch_switch : 
  switch ∘ switch = id := 
begin
  funext b, 
  dsimp,
  cases b, -- tactic `cases` branches the proof into two branches, one when `b = ff` and the second branch when `b = tt` 
  {
    refl, 
  }, 
  {
    refl, 
  },
end 




lemma switch_switch_alt_alt : 
  switch ∘ switch = id := 
begin
  funext b, 
  dsimp,
  cases b, 
  repeat {refl},
end 




lemma swap_square_is_id (X Y : Type) : (swap_pair Y X) ∘ (swap_pair X Y)= id := 
begin
ext p, 
repeat {refl}, -- instead of writing refl two times. 
end 




-- function `fun_pair` takes two functions and returns their cartesian product, i.e. a function from the cartesian product of the domains of the input function to the cartesian product of the codomains of the the input functions. 

def fun_pair (f : A → B) (g : X → Y) (p : A × X) : B × Y   := 
(f p.1 , g p.2)



#check fun_pair 
#check fun_pair double switch 
#eval (fun_pair double switch) (2, ff)





#check pairing
#check @pairing 


/-
Therer is a difference between the functions `pairing` and `fun_pair`. 
1. `pairing` takes two functions with the same domain as inputs.  
2. `fun_pair` on the other hand takes any two functions as input. 

However, theorem `fun_pair_is_pairing` below proves that the two functions `pairing` and `fun_pair` are intimately related. 
-/

lemma fun_pair_is_pairing (f : A → X) (g : B → Y) : 
fun_pair (f : A → X) (g : B → Y) =  
pairing (λ c : A × B, f c.1) (λ c : A × B, g c.2) := 
begin
  funext x, 
  refl, 
end 



/- 
Projection `fst` and `pairing` commute. 
-/
lemma fun_of_fst_is_fst_of_fun_pair (X₁ Y₁ X₂ Y₂: Type) (f : X₁ → Y₁) (g : X₂ → Y₂) : fst ∘ (fun_pair f g) = f ∘ fst := 
begin
  ext p, 
  refl, 
end  


def associator (X Y Z : Type) : X × (Y × Z) → (X × Y) × Z := 
λ p, ((p.1, p.2.1), p.2.2)
 
#check associator 

--Challenge: prove pentagon 






/-! ### Propoerties of composition of functions -/


/- 
__unitality of composition__ is a fancy name for saying that the composition of the identity function and any function `f` is the same function `f`. 
-/

/-
For any given function `f : X → Y` we want to prove that `id ∘ f = f`. Therefore in Lean we write 

lemma comp_left_unitality (f : X → Y) : id ∘ f = f  
:= proof 

Now we need to supply the proof. But let's think about `id ∘ f`. For any `x : X`, we have 
`(id ∘ f) x = id (f x) = f x` where these equalities are proved by `rfl`. By `funext` we can conclude that 
`id ∘ f = f`. 
-/

/-
__left unitality of composition__
-/ 

lemma comp_left_unit {X Y : Type} (f : X → Y) : 
  id ∘ f = f := 
begin
funext x,
dsimp,
refl,
end 


/-
__right unitality of composition__
-/ 
lemma comp_right_unit {X Y : Type} (f : X → Y) : 
  f ∘ id = f := 
begin 
funext x, 
dsimp, 
refl, 
end 


/- 
The theorem __associativity of composition__ says in that the order of bracketing in the composition of three functions (with matching domaisn and codomains) does not matter since the two different ways of composition result in the same function, that is 
`(h ∘ g) ∘ f  = h ∘ (g ∘ f)` 
for any three functions `(f : X → Y ) (g : Y → Z) (h : Z → W) `. 
-/

theorem comp_assoc {X Y Z W: Type} (f : X → Y ) (g : Y → Z) (h : Z → W) :   (h ∘ g) ∘ f  = h ∘ (g ∘ f)  := 
begin 
funext x, 
dsimp, 
refl, 
end 



theorem comp_tetrahedral_assoc (f : X → Y ) (g : Y → Z) (h : Z → W) (k : W → V) : k ∘ (h ∘ ( g ∘ f)) = ((k ∘ h) ∘ g) ∘ f 
:= 
begin
  funext x, 
  dsimp, 
  refl, 
end 


theorem comp_tetrahedral_assoc_alt (f : X → Y ) (g : Y → Z) (h : Z → W) (k : W → V) : k ∘ (h ∘ ( g ∘ f)) = ((k ∘ h) ∘ g) ∘ f 
:= 
begin
  calc k ∘ (h ∘ ( g ∘ f)) = (k ∘ h ) ∘ (g ∘ f) : by rw comp_assoc (g ∘ f) h k 
  ... = ((k ∘ h) ∘ g) ∘ f : by rw comp_assoc f g (k ∘ h),   
end 




end PROOFS



/-
We define the operation of __squaring__ a function using `compose`:
-/

def Square (f : X → X) : X → X :=
  Compose f f


/-
A notation for squaring
-/

notation:1000 f "²" => Square f



  