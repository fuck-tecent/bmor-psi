import Mathlib

theorem PEqualNP.Outside.L_square_packing_support_axis :
    ∀ A B u v:ℝ, abs u < 1/2 → abs v < 1/2 → 0 < abs A + abs B → abs (A*u+B*v) < (abs A + abs B)/2 := by
  intro A B u v hu hv hAB
  have htri : abs (A*u+B*v) ≤ abs A * abs u + abs B * abs v := by
    calc abs (A*u+B*v) ≤ abs (A*u) + abs (B*v) := abs_add_le _ _
      _ = abs A * abs u + abs B * abs v := by rw [abs_mul, abs_mul]
  have hstrict : abs A * abs u + abs B * abs v < (abs A + abs B)/2 := by
    rcases eq_or_lt_of_le (abs_nonneg A) with hA | hA
    · have hA' : abs A = 0 := hA.symm
      have hBpos : 0 < abs B := by rw [hA'] at hAB; linarith
      have h1 : abs B * abs v < abs B * (1/2) := mul_lt_mul_of_pos_left hv hBpos
      rw [hA']
      nlinarith [h1]
    · have h1 : abs A * abs u < abs A * (1/2) := mul_lt_mul_of_pos_left hu hA
      have h2 : abs B * abs v ≤ abs B * (1/2) := mul_le_mul_of_nonneg_left hv.le (abs_nonneg B)
      nlinarith [h1, h2]
  linarith
