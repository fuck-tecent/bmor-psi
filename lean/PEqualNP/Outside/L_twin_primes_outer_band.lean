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

theorem PEqualNP.Outside.L_twin_primes_outer_band :
    let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ (x n : ℝ) (j : ℕ), 1000 ≤ x → x ≤ n → 50*n ≤ 51*x → 3 ≤ j → 9/4 < f x n j := by
  intro f x n j hx hxn hn hj
  show 9/4 < x * Real.log (1 + (j:ℝ)/n)
  have hn0 : 0 < n := by linarith
  have hj3 : (3:ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ j := by linarith
  have hlow := log_one_add_div_lower n j hn0 hj0
  have hx0 : 0 ≤ x := by linarith
  have h1 : x * ((j:ℝ) / (n + j)) ≤ x * Real.log (1 + (j:ℝ)/n) := mul_le_mul_of_nonneg_left hlow hx0
  have h2 : 9/4 < x * ((j:ℝ) / (n + j)) := by
    rw [← mul_div_assoc, lt_div_iff₀ (by linarith)]
    nlinarith
  linarith
