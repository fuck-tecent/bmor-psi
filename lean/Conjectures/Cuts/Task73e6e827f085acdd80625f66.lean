import Mathlib

private theorem chord_le (a b : ℝ) :
    ‖Complex.exp ((a:ℂ)*Complex.I) - Complex.exp ((b:ℂ)*Complex.I)‖ ≤ |a-b| := by
  have phase : ((a:ℂ)*Complex.I) = Complex.I * ((a-b:ℝ):ℂ) + (b:ℂ)*Complex.I := by
    push_cast
    ring
  rw [phase, Complex.exp_add, ← sub_one_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem Conjectures.Cuts.Task73e6e827f085acdd80625f66 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * (2 : ℝ) ^ x3 * x2) * Complex.I); have x2 : ℕ → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x4 * x3⌋ / (65536 : ℝ)) * Complex.I); ∀ (x3 : ℕ) (x4 : ℝ), ‖x2 x3 x4 - x1 x3 x4‖ ≤ (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑x3) := by
  intro G T L u
  let frequency (j : ℕ) : ℝ := (2:ℝ)^j*u
  let fine (j : ℕ) : ℝ := 2*Real.pi*frequency j
  let coarse (j : ℕ) : ℝ := 2*Real.pi*(⌊65536*frequency j⌋:ℤ)/65536
  have angle (j : ℕ) : |coarse j - fine j| ≤ 2*Real.pi/65536 := by
    have hlo := Int.floor_le (65536*frequency j)
    have hhi := Int.lt_floor_add_one (65536*frequency j)
    have hp : 0 ≤ 2*Real.pi := by positivity
    have lower := mul_le_mul_of_nonneg_left hlo hp
    have upper := mul_le_mul_of_nonneg_left hhi.le hp
    apply abs_le.mpr
    dsimp only [coarse, fine]
    constructor <;> linarith only [lower, upper, hp]
  let unitPhase (v : ℝ) := Complex.exp ((v:ℂ)*Complex.I)
  have rewriteG : G L u = ∑ j ∈ Finset.range L, unitPhase (fine j) := by
    dsimp only [G, unitPhase, fine, frequency]
    simp only [mul_assoc]
  have rewriteT : T L u = ∑ j ∈ Finset.range L, unitPhase (coarse j) := by
    dsimp only [T, unitPhase, coarse, frequency]
    simp only [mul_assoc]
  rw [rewriteG, rewriteT, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range L, ‖unitPhase (coarse j) - unitPhase (fine j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range L, 2*Real.pi/65536 :=
      Finset.sum_le_sum fun j _ => (chord_le _ _).trans (angle j)
    _ = _ := by simp [mul_comm]
