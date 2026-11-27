import Mathlib

private lemma log_one_add_div_lower (n j : ℝ) (hn : 0 < n) (hj : 0 ≤ j) :
    j / (n + j) ≤ Real.log (1 + j / n) := by
  have hpos : 0 < 1 + j / n := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have e : 1 - (1 + j / n)⁻¹ = j / (n + j) := by
    field_simp
    ring
  linarith

private lemma log_one_add_div_upper (n j : ℝ) (hn : 0 < n) (hj : 0 ≤ j) :
    Real.log (1 + j / n) ≤ j / n := by
  have hpos : 0 < 1 + j / n := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

theorem PEqualNP.Outside.L_twin_primes_double_band :
    let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ x n : ℝ, 1000 ≤ x → x ≤ n → 50*n ≤ 51*x → |f x n 2 - 2| < 1/20 := by
  intro f x n hx hxn hn
  show |x * Real.log (1 + 2/n) - 2| < 1/20
  have hn0 : 0 < n := by linarith
  have hlow := log_one_add_div_lower n 2 hn0 zero_le_two
  have hup := log_one_add_div_upper n 2 hn0 zero_le_two
  have hx0 : 0 ≤ x := by linarith
  have h1 : x * (2 / (n + 2)) ≤ x * Real.log (1 + 2/n) := mul_le_mul_of_nonneg_left hlow hx0
  have h2 : 39/20 < x * (2 / (n + 2)) := by
    rw [← mul_div_assoc, lt_div_iff₀ (by linarith)]
    linarith
  have h3 : x * Real.log (1 + 2/n) ≤ x * (2 / n) := mul_le_mul_of_nonneg_left hup hx0
  have h4 : x * (2 / n) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hn0]
    linarith
  rw [abs_sub_lt_iff]
  constructor <;> linarith
