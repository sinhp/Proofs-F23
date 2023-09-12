/-! ## Composition of Functions -/


def Compose (g : Y → Z) (f : X → Y) (x : X) : Z :=
  g (f x)


/-
We define the operation of __squaring__ a function using `compose`:
-/

def Square (f : X → X) : X → X :=
  Compose f f


/-
A notation for squaring
-/

notation:1000 f "²" => Square f



  