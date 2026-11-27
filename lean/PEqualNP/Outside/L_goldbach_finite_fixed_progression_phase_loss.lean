import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_fixed_progression_phase_loss :
    ∀ (N : ℕ) (b : ℕ → ℂ) (θ : ℝ) (E : ℝ), 0 ≤ E → (∀ m ≤ N, ‖∑ k ∈ Finset.range m, b k‖ ≤ E) → ‖∑ k ∈ Finset.range N, b k * Complex.exp (Complex.I*((2*Real.pi*θ*(k:ℝ):ℝ):ℂ))‖ ≤ E*(1+2*Real.pi*N*|θ|) := by
  intro N b θ E hE hB
  set G : ℕ → ℂ := fun k => Complex.exp (Complex.I * (((2*Real.pi*θ*(k:ℝ)) : ℝ) : ℂ)) with hG
  have hGnorm : ∀ k, ‖G k‖ = 1 := by
    intro k
    simp only [hG]
    rw [mul_comm Complex.I (((2*Real.pi*θ*(k:ℝ)) : ℝ) : ℂ), Complex.norm_exp_ofReal_mul_I]
  have hGstep : ∀ i : ℕ, G (i+1) = G i * Complex.exp (Complex.I * (((2*Real.pi*θ) : ℝ) : ℂ)) := by
    intro i
    simp only [hG]
    have h2 : Complex.I * (((2*Real.pi*θ*(((i:ℕ)+1 : ℕ) : ℝ)) : ℝ) : ℂ) = Complex.I * (((2*Real.pi*θ*(i:ℝ)) : ℝ) : ℂ) + Complex.I * (((2*Real.pi*θ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.exp_add]
  have hGdiff : ∀ i : ℕ, ‖G (i+1) - G i‖ ≤ |2*Real.pi*θ| := by
    intro i
    have heq : G (i+1) - G i = G i * (Complex.exp (Complex.I * (((2*Real.pi*θ) : ℝ) : ℂ)) - 1) := by
      rw [hGstep i]
      ring
    rw [heq, norm_mul, hGnorm i, one_mul]
    simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*θ)
  have hterm : ∀ k, b k * Complex.exp (Complex.I*((2*Real.pi*θ*(k:ℝ):ℝ):ℂ)) = b k • G k := by
    intro k
    simp only [hG, smul_eq_mul]
  rw [show (∑ k ∈ Finset.range N, b k * Complex.exp (Complex.I*((2*Real.pi*θ*(k:ℝ):ℝ):ℂ))) = ∑ k ∈ Finset.range N, b k • G k from Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_range_by_parts' (f := b) (g := G) (n := N)]
  have hA : ‖(∑ i ∈ Finset.range N, b i) • G (N - 1)‖ ≤ E := by
    rw [norm_smul, hGnorm, mul_one]
    exact hB N le_rfl
  have hS : ‖∑ i ∈ Finset.range (N - 1), (∑ j ∈ Finset.range (i+1), b j) • (G (i+1) - G i)‖ ≤ ((N - 1 : ℕ) : ℝ) * (E * |2*Real.pi*θ|) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∀ i ∈ Finset.range (N-1), ‖(∑ j ∈ Finset.range (i+1), b j) • (G (i+1) - G i)‖ ≤ E * |2*Real.pi*θ| := by
      intro i hi
      rw [norm_smul]
      have hi' : i + 1 ≤ N := by
        have := Finset.mem_range.mp hi
        omega
      exact mul_le_mul (hB (i+1) hi') (hGdiff i) (norm_nonneg _) hE
    calc ∑ i ∈ Finset.range (N - 1), ‖(∑ j ∈ Finset.range (i+1), b j) • (G (i+1) - G i)‖
        ≤ ∑ i ∈ Finset.range (N - 1), E * |2*Real.pi*θ| := Finset.sum_le_sum hb
      _ = ((N - 1 : ℕ) : ℝ) * (E * |2*Real.pi*θ|) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine le_trans (norm_sub_le _ _) ?_
  have hcast : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
  have hnn : 0 ≤ E * |2*Real.pi*θ| := mul_nonneg hE (abs_nonneg _)
  have hkey : ((N - 1 : ℕ) : ℝ) * (E * |2*Real.pi*θ|) ≤ (N : ℝ) * (E * |2*Real.pi*θ|) :=
    mul_le_mul_of_nonneg_right hcast hnn
  have habs : |2*Real.pi*θ| = 2*Real.pi*|θ| := by
    rw [abs_mul, abs_mul]
    simp [abs_of_pos Real.pi_pos]
  rw [habs] at hkey hS
  nlinarith [hkey, hA, hS]
