import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_quadratic_swap :
    ∀ (m : ℕ) (a b c x y : ZMod m), x ≠ y →
      (y, x) ≠ (x, y) ∧
        a * (y + x) ^ 2 + b * (y + x) + c =
          a * (x + y) ^ 2 + b * (x + y) + c := by
  intro m a b c x y hxy
  constructor
  · intro h
    exact hxy (congrArg Prod.fst h).symm
  · rw [add_comm y x]

end PEqualNP.Outside
