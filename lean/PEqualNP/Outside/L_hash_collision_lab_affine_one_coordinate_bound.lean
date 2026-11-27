import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_affine_one_coordinate_bound :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b c x y u v : ZMod p), a ≠ 0 → b ≠ 0 →
      a * x + b * y + c = a * u + b * v + c → (x, y) ≠ (u, v) → x ≠ u ∧ y ≠ v := by
  intro p _ a b c x y u v ha hb heq hne
  have key : a * x + b * y = a * u + b * v := add_right_cancel heq
  constructor
  · intro hxu
    apply hne
    have h2 : b * y = b * v := by
      have h1 : a * x + b * y = a * u + b * v := key
      rw [hxu] at h1
      exact add_left_cancel h1
    exact Prod.ext hxu (mul_left_cancel₀ hb h2)
  · intro hyv
    apply hne
    have h2 : a * x = a * u := by
      have h1 : a * x + b * y = a * u + b * v := key
      rw [hyv] at h1
      exact add_right_cancel h1
    exact Prod.ext (mul_left_cancel₀ ha h2) hyv

end PEqualNP.Outside
