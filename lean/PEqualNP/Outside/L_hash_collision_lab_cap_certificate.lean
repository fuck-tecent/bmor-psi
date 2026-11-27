import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cap_certificate :
    ∀ (m B S z : ℤ),
      (∃ x y : ℤ, x ≤ y ∧ y ≤ z ∧ x + y + z = 0 ∧ x ^ 2 + x * y + y ^ 2 = S ∧
        0 ≤ (m + x) ∧ (m + z) ≤ B) ↔
      ((m + z) ≤ B ∧ ∃ d : ℤ, 0 ≤ d ∧ d ≤ 3 * z ∧ z + d ≤ 2 * m ∧
        (2 : ℤ) ∣ (z + d) ∧ d ^ 2 + 3 * z ^ 2 = 4 * S) := by
  intro m B S z
  constructor
  · rintro ⟨x, y, hxy, hyz, hsum, hS, hmx, hmz⟩
    refine ⟨hmz, y - x, by linarith, by linarith, by linarith, ⟨-x, by linarith⟩, ?_⟩
    have hz : z = -(x + y) := by linarith
    subst hz
    nlinarith [hS]
  · rintro ⟨hmz, d, hd0, hd3, hzd, hpar, hsq⟩
    obtain ⟨t, ht⟩ := hpar
    refine ⟨-t, t - z, by linarith, by linarith, by ring, ?_, by linarith, hmz⟩
    have hd : d = 2 * t - z := by linarith
    subst hd
    linarith