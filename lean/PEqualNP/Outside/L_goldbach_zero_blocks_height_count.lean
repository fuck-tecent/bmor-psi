import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_height_count :
    ∀ (n : ℕ) (ρ : Fin n → ℂ) (T : ℝ) (M : ℕ), 0<T → n≤M → (∀ i,T≤|(ρ i).im|) → (∑ i,‖(ρ i)⁻¹‖)≤(M:ℝ)/T := by
  intro n ρ T M hT hn him
  have hb : ∀ i, ‖(ρ i)⁻¹‖ ≤ 1/T := by
    intro i
    have hle : T ≤ ‖ρ i‖ := le_trans (him i) (Complex.abs_im_le_norm (ρ i))
    have hpos : (0:ℝ) < ‖ρ i‖ := lt_of_lt_of_le hT hle
    rw [norm_inv, one_div]
    exact (inv_le_inv₀ hpos hT).mpr hle
  calc ∑ i, ‖(ρ i)⁻¹‖ ≤ ∑ _i : Fin n, 1/T := Finset.sum_le_sum (fun i _ => hb i)
    _ = (n:ℝ) * (1/T) := by simp
    _ ≤ (M:ℝ) * (1/T) := by
        have h1 : (n:ℝ) ≤ (M:ℝ) := Nat.cast_le.mpr hn
        have h2 : (0:ℝ) ≤ 1/T := by positivity
        nlinarith
    _ = (M:ℝ)/T := by ring
