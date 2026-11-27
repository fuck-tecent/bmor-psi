import Mathlib

theorem PEqualNP.Outside.L_goldbach_strip_geometry_inverse_square_tail :
    ∀ (S : Finset ℂ) (T : ℝ), 0<T → (∀ z ∈ S,T≤|z.im|) → Finset.sum S (fun z => ‖z⁻¹‖^2) ≤ (S.card:ℝ)/T^2 := by
  intro S T hT him
  have hb : ∀ z ∈ S, ‖z⁻¹‖^2 ≤ 1/T^2 := by
    intro z hzS
    have hle : T ≤ ‖z‖ := le_trans (him z hzS) (Complex.abs_im_le_norm z)
    have hpos : (0:ℝ) < ‖z‖ := lt_of_lt_of_le hT hle
    rw [norm_inv]
    have hsq : (‖z‖⁻¹)^2 = 1/‖z‖^2 := by field_simp
    rw [hsq, one_div, one_div, inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_left₀ (le_of_lt hT) hle 2
  calc ∑ z ∈ S, ‖z⁻¹‖^2 ≤ ∑ _z ∈ S, 1/T^2 := Finset.sum_le_sum hb
    _ = (S.card:ℝ) * (1/T^2) := by simp
    _ = (S.card:ℝ)/T^2 := by ring
