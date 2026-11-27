import Mathlib

theorem PEqualNP.Outside.L_goldbach_rh_zeta_zero_sum :
    RiemannHypothesis → ∀ (Z : Finset ℂ) (a : ℂ → ℂ) (x : ℝ), 0 < x → (∀ s ∈ Z, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) → ‖Finset.sum Z (fun s => a s * (x : ℂ) ^ s)‖ ≤ Real.sqrt x * Finset.sum Z (fun s => ‖a s‖) := by
  intro hRH Z a x hx hZ
  calc
    _ ≤ Finset.sum Z (fun s => ‖a s * (x : ℂ) ^ s‖) := norm_sum_le _ _
    _ = Finset.sum Z (fun s => Real.sqrt x * ‖a s‖) := by
      apply Finset.sum_congr rfl
      intro s hs
      obtain ⟨hpos, hlt, hzero⟩ := hZ s hs
      have hre : s.re = 1 / 2 := by
        apply hRH s hzero
        · rintro ⟨n, hn⟩
          have he : s = (((-2 : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) := by
            push_cast
            exact hn
          rw [he, Complex.ofReal_re] at hpos
          linarith [Nat.cast_nonneg (α := ℝ) n]
        · rintro rfl
          simp at hlt
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx s, hre, ← Real.sqrt_eq_rpow,
        mul_comm]
    _ = _ := (Finset.mul_sum ..).symm
