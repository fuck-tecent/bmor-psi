import Mathlib

namespace Conjectures.Goldbach.Rfc11DyadicCmPrimeAnchors_aux

theorem half_le_half_add_two (j : ℕ) : (j : ℝ) / 2 ≤ (((j + 2) / 2 : ℕ) : ℝ) := by
  have h : 2 * ((j + 2) / 2 : ℕ) ≥ j := by omega
  have h' : (2 : ℝ) * (((j + 2) / 2 : ℕ) : ℝ) ≥ (j : ℝ) := by exact_mod_cast h
  linarith

end Conjectures.Goldbach.Rfc11DyadicCmPrimeAnchors_aux

theorem Conjectures.Goldbach.Rfc11DyadicCmPrimeAnchors :
    ∀ j m : ℕ, 61≤j → j≤1049 → m<2^j/2 →
      ((m:ℝ)^(1/4 : ℝ)+1)^2 < (2:ℝ)^((j+2)/2+2 : ℕ) := by
  intro j m hj _ hm
  have hj1 : 1 ≤ j := by omega
  have hm' : m < 2 ^ j := lt_of_lt_of_le hm (Nat.div_le_self (2 ^ j) 2)
  have hmR : (m : ℝ) < (2 : ℝ) ^ (j : ℝ) := by
    have : (m : ℝ) < ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hm'
    simpa [Nat.cast_pow, Real.rpow_natCast] using this
  have hs : (m : ℝ) ^ (1 / 4 : ℝ) < (2 : ℝ) ^ ((j : ℝ) / 4) := by
    have h0 : (m : ℝ) ^ (1 / 4 : ℝ) < ((2 : ℝ) ^ (j : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_lt_rpow (by positivity) hmR (by norm_num : (0:ℝ) < 1/4)
    have hb : ((2 : ℝ) ^ (j : ℝ)) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ ((j : ℝ) / 4) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rwa [hb] at h0
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) / 4) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hstep : (m : ℝ) ^ (1 / 4 : ℝ) + 1 < (2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 4) := by
    linarith
  have hsq : ((m : ℝ) ^ (1 / 4 : ℝ) + 1) ^ 2 < ((2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 4)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < (2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 4) := by positivity
    nlinarith [hstep, hnn, hpos]
  have hpow : ((2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ (2 + (j : ℝ) / 2) := by
    have hx : (0 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) / 4) := by positivity
    have hmul : (2 : ℝ) ^ ((j : ℝ) / 4) * (2 : ℝ) ^ ((j : ℝ) / 4) = (2 : ℝ) ^ ((j : ℝ) / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    calc ((2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 4)) ^ 2
        = 4 * ((2 : ℝ) ^ ((j : ℝ) / 4) * (2 : ℝ) ^ ((j : ℝ) / 4)) := by ring
      _ = 4 * (2 : ℝ) ^ ((j : ℝ) / 2) := by rw [hmul]
      _ = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 2) := by
            have htwo : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_two]
            rw [htwo]
      _ = (2 : ℝ) ^ (2 + (j : ℝ) / 2) := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hexp : 2 + (j : ℝ) / 2 ≤ (((j + 2) / 2 + 2 : ℕ) : ℝ) := by
    have := Conjectures.Goldbach.Rfc11DyadicCmPrimeAnchors_aux.half_le_half_add_two j
    push_cast
    linarith
  have hfinal : (2 : ℝ) ^ (2 + (j : ℝ) / 2) ≤ (2 : ℝ) ^ ((j + 2) / 2 + 2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hlt : ((m : ℝ) ^ (1 / 4 : ℝ) + 1) ^ 2 < (2 : ℝ) ^ (2 + (j : ℝ) / 2) := by
    rw [← hpow]; exact hsq
  exact lt_of_lt_of_le hlt hfinal
