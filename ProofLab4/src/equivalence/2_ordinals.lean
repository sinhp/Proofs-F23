#check Seq

-- Define the type of finite sequences of natural numbers
inductive FinSeq : Type
| nil : FinSeq
| cons : Nat → FinSeq → FinSeq

-- Define the length function on Seq
def len : FinSeq → Nat
| FinSeq.nil => 0
| FinSeq.cons _ s => 1 + len s

def my_fin_seq : FinSeq := FinSeq.cons 3 (FinSeq.cons 2 FinSeq.nil) 

#eval len my_fin_seq




-- Define the lexicographic order on Seq
def lex : FinSeq → FinSeq → Prop
| FinSeq.nil, FinSeq.nil => false
| FinSeq.nil, _ => true
| _, FinSeq.nil => false
| FinSeq.cons n1 s1, FinSeq.cons n2 s2 =>
  if n1 < n2 then True else
  if n1 > n2 then False else
  lex s1 s2


#check lex

#check Acc  


-- A type class for strict orders
class IsStrictOrder (α : Type u) (r : α → α → Prop) extends IsIrrefl α r, IsTrans α r where
  -- Every strict order is asymmetric
  asymm {a b : α} (h₁ : r a b) : ¬ r b a := fun h₂ => irrefl_of h₁ h₂


-- A type class for well-ordered relations
class WellOrder (α : Type u) (r : α → α → Prop) extends IsStrictOrder α r where
  -- Every non-empty subset has a least element
  wf : WellFounded r


-- Define the omega ordinal as the type of well-ordered sequences
def Omega : Type := {s : FinSeq // WellOrder s lex}

-- Give an instance of Omega as the sequence [0, 0, 0, ...]
def omegaInstance : Omega := ⟨Seq.nil, wellOrderNil⟩

-- Prove that the empty sequence is well-ordered by lex
theorem wellOrderNil : WellOrder Seq.nil lex :=
begin
  split,
  { -- Prove that lex is a strict order on Seq.nil
    split,
    { -- Prove that lex is irreflexive on Seq.nil
      intro s,
      cases s with
      | nil => simp [lex]
      | cons n s => simp [lex]
    },
    { -- Prove that lex is transitive on Seq.nil
      intros s1 s2 s3 h12 h23,
      cases s1 with
      | nil =>
        cases s2 with
        | nil => exact h23
        | cons n2 s2 => exact h23
      | cons n1 s1 =>
        cases s2 with
        | nil => cases h12
        | cons n2 s2 =>
          cases s3 with
          | nil => cases h23
          | cons n3 s3 =>
            simp [lex] at h12 h23,
            simp [lex],
            byCases h : n1 < n2,
            { exact h },
            { pushNeg at h,
              cases h with
              | inl h' => rw [h'] at h12 h23,
                exact h23.left
              | inr h' =>
                rw [h'.left] at h12 h23,
                exact ⟨h'.right, trans h12.right h23.right⟩ }
    }
  },
  { -- Prove that every non-empty subset of Seq.nil has a least element by lex
    intro S,
    intro hS,
    have h : S = {Seq.nil} := by {
      apply funext,
      intro x,
      apply propext,
      split,
      { intro hx,
        have hx' := hS hx,
        cases x with
        | nil => simp 
        | cons n x => cases hx'
      },
      { intro hx,
        rw [hx],
        exact ⟨rfl⟩ }
    },
    rw [h],
    use Seq.nil,
    split,
    { simp },
    { intros y hy,
      simp at hy,
      rw [hy],
      simp [lex] }
  }
end

