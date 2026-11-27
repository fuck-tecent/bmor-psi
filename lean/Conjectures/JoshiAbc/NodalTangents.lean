import Mathlib

theorem Conjectures.JoshiAbc.NodalTangents :
    ∀ x y : ZMod 5, y^2+x*y=0 ↔ y=0 ∨ y= -x := by
  decide
