import Mathlib

private theorem chord_le (a b : ℝ) :
    ‖Complex.exp ((a:ℂ)*Complex.I) - Complex.exp ((b:ℂ)*Complex.I)‖ ≤ |a-b| := by
  have phase : ((a:ℂ)*Complex.I) = Complex.I * ((a-b:ℝ):ℂ) + (b:ℂ)*Complex.I := by
    push_cast
    ring
  rw [phase, Complex.exp_add, ← sub_one_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem Conjectures.Cuts.Task1cc519d520b70065cb7e54f1 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * (2 : ℝ) ^ x3 * x2) * Complex.I); ∀ (x2 : ℕ) (x3 x4 : ℝ), |x3 - x4| ≤ (1 : ℝ) / (2 : ℝ) ^ x2 → ‖x1 x2 x3 - x1 x2 x4‖ ≤ (2 : ℝ) * Real.pi) := by
  intro G L x u hx
  let term (j : ℕ) (v : ℝ) := Complex.exp (((2*Real.pi*(2:ℝ)^j*v:ℝ):ℂ)*Complex.I)
  have localBound (j : ℕ) :
      ‖term j x - term j u‖ ≤ (2:ℝ)^j * (2*Real.pi*|x-u|) := by
    apply (chord_le _ _).trans
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*(2:ℝ)^j)]
    exact le_of_eq (by ring)
  have geometric (n : ℕ) : (∑ j ∈ Finset.range n, (2:ℝ)^j) + 1 = 2^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith
  have hx' : |x-u| * (2:ℝ)^L ≤ 1 := (le_div_iff₀ (by positivity)).mp hx
  change ‖(∑ j ∈ Finset.range L, term j x) - ∑ j ∈ Finset.range L, term j u‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range L, ‖term j x - term j u‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range L, (2:ℝ)^j * (2*Real.pi*|x-u|) :=
      Finset.sum_le_sum fun j _ => localBound j
    _ = (∑ j ∈ Finset.range L, (2:ℝ)^j) * (2*Real.pi*|x-u|) := (Finset.sum_mul ..).symm
    _ ≤ (2:ℝ)^L * (2*Real.pi*|x-u|) :=
      mul_le_mul_of_nonneg_right (by linarith only [geometric L]) (by positivity)
    _ ≤ 2*Real.pi := by
      linarith only [mul_le_mul_of_nonneg_left hx' (by positivity : 0 ≤ 2*Real.pi)]
