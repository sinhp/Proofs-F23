import ProofLab4


/-! 
# Homework 2
Homework must be done individually.
-/


/-! 
## Preliminaries About Sequences: 

Follow the link: https://introproofs.github.io/s22/functions/1/#sequences

A __sequence__ in a type `A` is simply a function `a : ℕ → A` . The sequence `a` assigns to every natural number `n : ℕ` an element `a(n) : A`. For instance a sequence of natural numbers is a function `ℕ → ℕ` and a sequence of real numbers is a function `ℕ → ℝ`.
In any case, a sequence specifies an _infinite_ list of natural numbers.

For a squence `a : ℕ → A`, `a 0` is called the _0th term_, element `a 1` is the __first term__, and so on. In general, `a n` is the __nth term__ of the sequence. We call `n` the index of the term `a n : A`.  

A __subsequnce__ `b : ℕ → A` of `a : ℕ → A`  is any infinite selection of some (possibly all) of the terms of `a` in the same order. For instance, if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `b` could be the sequence `2, 3, 5, 7, ...` (but `3, 2, 5, 7, ...` is not a subsequence). Or if `a` is the sequence `π, 2π, 3π, 4π, 5π, 6π, 7π, 8π, 9π, 10π, ...` then `b` could be the sequence `3π, 6π, 9π, 12π, 15π, 16π, 18π, 21π, 24π, 27π, 30π, ...`.

A sequence `a : ℕ → A` is __increasing__ if `a n ≤ a (n+1)` for all `n : ℕ`. A sequence `a : ℕ → A` is __decreasing__ if `a n ≥ a (n+1)` for all `n : ℕ`. A sequence `a : ℕ → A` is __monotone__ if it is either increasing or decreasing.


The __sum__ of a sequence `a : ℕ → ℝ` and a sequence `b : ℕ → ℝ` is the sequence `c : ℕ → ℝ` where `c n = a n + b n`. The _product_ of a sequence `a : ℕ → ℝ` and a sequence `b : ℕ → ℝ` is the sequence `c : ℕ → ℝ` where `c n = a n * b n`. The _difference_ of a sequence `a : ℕ → ℝ` and a sequence `b : ℕ → ℝ` is the sequence `c : ℕ → ℝ` where `c n = a n - b n`. 


The __alternating sum__ of a sequence `a : ℕ → ℝ` and a sequence `b : ℕ → ℝ` is the sequence `c : ℕ → ℝ` where the even-indexed terms of `c` are given by the sum of the even-indexed terms of `a` and `b` and the odd-indexed terms of `c` are given by the difference of the odd-indexed terms of `a` and `b`. For instance, if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` and `b` is the sequence `1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, ...` then the alternating sum of `a` and `b` is the sequence `1, 1/2, 7/3, 11/4, 21/5, 29/6, ...`

The __discrete convolution__ of two sequences `a` and `b` of real numbers is the sequence `c` where `c n` is the sum of `a k * b (n-k)` for `k` from `0` to `n`. More on convolutions: https://en.wikipedia.org/wiki/Convolution
-/  


/-
### Problem 1 (Defining Sequences)

Define the following sequences in Lean:
1. Define a sequence `a` of natural numbers where `a n = n^2`.
2. Define a sequence `b` of real numbers where `b n = 1 / (n+1)`.
3. Define a sequence `c` of real numbers where `c n = 1` when `n` is even and `c n = -1` when `n` is odd.
4. Suppose `d : ℕ → Bool` is a sequence of Booleans. Define a sequence `e` of real numbers where `e n = 1` when `d n = true` and `e n = 0` when `d n = false`.  
-/





/-
### Problem 2 (Transforming Sequences of Real Numbers)

Define the following functions in Lean: 

1. A function `F₁` which takes a sequence of real numbers and returns the first term of the sequence. 
For instance if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₁ a` is `0`.

2. A function `F₂` which takes a sequence of real numbers and returns the sum of the first two terms. 
For instance if `a` is the sequence `1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₂ a` is `3`.

3. A function `F₃` which takes a sequence of real numbers and returns another sequence of real numbers where the nth term is the sum of the first `n` terms of the original sequence. Here the output function needs to be defined by recursion. 
For instance if `a` is the sequence `1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₃ a` is the sequence `1, 3, 6, 10, 15, 21, 28, 36, 45, ...`.


4. A function `F₄` which takes a sequence of real numbers and returns a subsequence of the input sequence with only the even-indexed terms.
For instance if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₄ a` is the sequence `0, 2, 4, 6, 8, ...`.

5. A function `F₅` which takes a sequence of real numbers and returns an increasing sequence. 
For instance if `a` is the sequence `0, 2, 1, 4, 3, 5, 6, 7, 8, 9, ...` then `F₄ a` is the sequence `0, 2, 2, 4, 4, 5, 6, 7, 8, 9, ...`.

6. A function `F₆` which takes two sequences of real numbers and returns their sum. 
For instance if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` and `b` is the sequence `1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, ...` then `F₆ a b` is the sequence `1, 3/2, 5/3, 7/4, 9/5, 11/6, 13/7, 15/8, 17/9, 19/10, ...`.

7. A function `F₇` which takes two sequences of real numbers and returns their alternate sum.
For instance if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` and `b` is the sequence `1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, ...` then `F₇ a b` is the sequence `1, 1/2, 5/3, 7/4, 21/5, 29/6, 85/7, 113/8, 323/9, 433/10, ...`.


8. A function `F₈` which takes a sequence of real numbers and returns a sequence of real numbers where the even-indexed terms are the even-indexed terms of the original sequence and the odd-indexed terms are the negative of the odd-indexed terms of the original sequence. 
For instance, if `a` is the sequence `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ...` then `F₈ a` is the sequence `0, -1, 2, -3, 4, -5, 6, -7, 8, -9, ...`.

9. (**Bonus**) Define a function `F₉` which takes two sequences of real numbers and returns their discrete convolution. Here the output function needs to be defined by recursion. 
-/





/-! 
### Problem 3 (Bonus)
Someone has written the function below without comments. Putting our Sherlock's hat on we are trying to figure out what this function does.

Explain in English what the following function does. 

What are the inputs and outputs and how they are related to each other (the function rule).  

You can also include in your answer some other concepts you have seen before and you think this might have some connections to it in which case you should elaborate on the connection.  
-/

def mystery_fun : ℕ → ℕ → ℕ
| _        ,    0 =>  1
| 0      , (k + 1) => 0
| (n + 1) , (k + 1) => mystery_fun n k + mystery_fun n (k + 1)

#eval mystery_fun 4 0 
#eval mystery_fun 4 1 
#eval mystery_fun 4 2 
#eval mystery_fun 4 3 
#eval mystery_fun 4 4 
#eval mystery_fun 4 5 


