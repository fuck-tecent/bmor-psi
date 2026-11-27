import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_affine_coordinate_shift :
    ∀ (m : ℕ) (a b c x y : ZMod m), a ≠ 0 ∨ b ≠ 0 → (x + b, y - a) ≠ (x, y) ∧ a * (x + b) + b * (y - a) + c = a * x + b * y + c := by
  intro m a b c x y h
  constructor
  · intro hEq
    have hx : x + b = x := congrArg Prod.fst hEq
    have hy : y - a = y := congrArg Prod.snd hEq
    have hb : b = 0 := by
      have := congrArg (fun t => t - x) hx
      simpa using this
    have ha : a = 0 := by
      have := congrArg (fun t => y - t) hy
      simpa using this
    rcases h with ha0 | hb0
    · exact ha0 ha
    · exact hb0 hb
  · ring
