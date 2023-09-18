import ProofLab4

#check max

#eval max 3 4


--noncomputable 
example : 4 = max (3 : ℝ) 4 := 
by 
  apply le_antisymm
  · apply le_max_right
  · apply max_le 
    · linarith
    · exact le_refl 4 