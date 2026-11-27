import Mathlib

theorem PEqualNP.Outside.L_goldbach_kernel_decay :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N + 1)) (fun k => E ((k : ℝ) * b))
    ∀ N b, E b ≠ 1 → ‖K N b‖ ≤ 2 / ‖1 - E b‖ := by
  let E : ℝ → ℂ := fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let K : ℕ → ℝ → ℂ := fun N b => Finset.sum (Finset.range (N + 1)) (fun k => E ((k : ℝ) * b))
  change ∀ N b, E b ≠ 1 → ‖K N b‖ ≤ 2 / ‖1 - E b‖
  intro N b hb
  let z : ℂ := E b
  have hbz : z ≠ 1 := hb
  have hnorm : ‖z‖ = 1 := by
    show ‖Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I)‖ = 1
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * b)
  have hpow : ∀ k : ℕ, E ((k : ℝ) * b) = z ^ k := by
    intro k
    induction k with
    | zero => simp [E]
    | succ k ih =>
        change E (((k + 1 : ℕ) : ℝ) * b) = z ^ (k + 1)
        have hstep : E (((k + 1 : ℕ) : ℝ) * b) = E ((k : ℝ) * b) * E b := by
          simp only [E]
          rw [← Complex.exp_add]
          congr 1
          have harg :
              2 * Real.pi * (((k + 1 : ℕ) : ℝ) * b) = 2 * Real.pi * ((k : ℝ) * b) + 2 * Real.pi * b := by
            push_cast
            ring
          rw [harg, Complex.ofReal_add]
          ring
        rw [hstep, ih, pow_succ]
  have hK : K N b = Finset.sum (Finset.range (N + 1)) (fun k => z ^ k) := by
    simp only [K]
    exact Finset.sum_congr rfl (fun k _ => hpow k)
  have hgeom : ∀ n : ℕ, (1 - z) * Finset.sum (Finset.range n) (fun k => z ^ k) = 1 - z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
        ring
  have h1 : ‖(1 : ℂ) - z ^ (N + 1)‖ ≤ 2 := by
    calc ‖(1 : ℂ) - z ^ (N + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (N + 1)‖ := norm_sub_le _ _
      _ = 2 := by
          rw [norm_one, norm_pow, hnorm, one_pow]
          norm_num
  have h2 : ‖(1 - z) * Finset.sum (Finset.range (N + 1)) (fun k => z ^ k)‖ ≤ 2 := by
    rw [hgeom (N + 1)]
    exact h1
  have h3 : ‖(1 : ℂ) - z‖ * ‖Finset.sum (Finset.range (N + 1)) (fun k => z ^ k)‖ ≤ 2 := by
    simpa only [norm_mul] using h2
  have h4 : ‖Finset.sum (Finset.range (N + 1)) (fun k => z ^ k)‖ * ‖(1 : ℂ) - z‖ ≤ 2 := by
    rw [mul_comm]
    exact h3
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    exact (Ne.symm hbz) (sub_eq_zero.mp h)
  have hdpos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr hne
  rw [hK]
  change ‖Finset.sum (Finset.range (N + 1)) (fun k => z ^ k)‖ ≤ 2 / ‖(1 : ℂ) - z‖
  rw [le_div_iff₀ hdpos]
  exact h4
