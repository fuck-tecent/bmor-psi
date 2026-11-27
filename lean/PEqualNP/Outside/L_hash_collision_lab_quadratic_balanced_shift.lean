import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_quadratic_balanced_shift :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b c x y : ZMod p),
      (x + 1, y - 1) ≠ (x, y) ∧
        a * ((x + 1) + (y - 1)) ^ 2 + b * ((x + 1) + (y - 1)) + c
          = a * (x + y) ^ 2 + b * (x + y) + c := by
  intro p hp a b c x y
  constructor
  · intro h
    have h1 : x + 1 = x := congrArg Prod.fst h
    have h2 : (1 : ZMod p) = 0 := by
      have h3 : x + 1 - x = 0 := by rw [h1, sub_self]
      simpa only [add_sub_cancel_left] using h3
    exact one_ne_zero h2
  · have hxy : (x + 1) + (y - 1) = x + y := by ring
    rw [hxy]

end PEqualNP.Outside
