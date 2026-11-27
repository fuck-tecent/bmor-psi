import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_units_error :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q h : ℕ) (f : ℕ → ℝ) (M e : ℝ), let U := (Finset.range q).filter (fun a => Nat.Coprime a q); (∀ a ∈ U, |f a-M|≤e) → ‖Finset.sum U (fun a => ((f a-M:ℝ):ℂ)*E ((h:ℝ)*(a:ℝ)/(q:ℝ)))‖ ≤ (U.card:ℝ)*e := by
  intro E q h f M e U hb
  have hE : ∀ t : ℝ, ‖E t‖ = 1 := by
    change ∀ t : ℝ, ‖Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ = 1
    intro t
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  calc
    ‖Finset.sum U (fun a => ((f a - M : ℝ) : ℂ) * E ((h : ℝ) * (a : ℝ) / (q : ℝ)))‖
        ≤ Finset.sum U (fun a => ‖((f a - M : ℝ) : ℂ) * E ((h : ℝ) * (a : ℝ) / (q : ℝ))‖) :=
      norm_sum_le U _
    _ ≤ Finset.sum U (fun _ => e) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hb a ha
    _ = (U.card : ℝ) * e := by
      simp only [Finset.sum_const, nsmul_eq_mul]
