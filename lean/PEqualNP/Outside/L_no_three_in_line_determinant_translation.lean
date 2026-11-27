import Mathlib

namespace PEqualNP.Outside

theorem L_no_three_in_line_determinant_translation :
    ∀ (ax ay bx byCoord cx cy tx ty : ℤ),
      ((bx + tx) - (ax + tx)) * ((cy + ty) - (ay + ty)) -
          ((byCoord + ty) - (ay + ty)) * ((cx + tx) - (ax + tx))
        = (bx - ax) * (cy - ay) - (byCoord - ay) * (cx - ax) := by
  intro ax ay bx byCoord cx cy tx ty
  ring

end PEqualNP.Outside
