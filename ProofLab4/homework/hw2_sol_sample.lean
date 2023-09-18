import ProofLab4



/-
# Sample Solutions to HW2
-/


/-
## Solutions to Problem 1 
-/

/-
1. Define a sequence `a` of natural numbers where `a n = n^2`.
-/
def a (n : ℕ) : ℕ := n^2

/-
0, 1, 4, 9, ... 

a 0 = 0^2 = 0 
a 1 = 1^2 = 1 
.
.
.
a 9 = 9^2 = 81 
.
.
.
-/

example : a 10 = 100 := rfl




/-
5. Define a sequence `i` of lists of integers where the `0th` term is the list `[0]`, and for nonzero `n` the `nth` term is the list of divisiors of `n`. For instance, the 6th term, i.e. `i 6` is the list `[1, -1, 2, -2,  3, -3, 6, -6]`.
-/

def list_of_div : ℕ → List ℤ := 
sorry -- use recursion to define this 


def i (n : ℕ) : List ℤ  := 
if (n = 0) then [0] else sorry -- "list of integer divisors of natural number n"

/-
one seq of lists : [], [1], [2], [3], ... 
another seq of lists: [-1], [-2], [-3], ... 
yet another lists : [], [0], [1], [1,2], [1,2,3], ... 

The seq i : `[0], [-1,1], [1,-1, 2, -2,], ..., [1, -1, 2, -2,  3, -3, 6, -6], ... ` 
-/





/-
## Solutions to Problem 2 
-/

/-
1. A function `F₁` which takes a sequence of real numbers and returns the first term of the sequence. 
For instance if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₁ a` is `0`.
-/

def F₁ (a : ℕ → ℝ) : ℝ := a 0

def myseq (n : ℕ) : ℝ := n * n + 1

example : F₁ myseq = 1 := by simp [F₁, myseq]




