import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_window_factorization :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let phase := fun (p k n : ℕ) => Complex.exp (((angle p k n : ℝ) : ℂ) * Complex.I); let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; ∀ a x p k : ℕ, coef a x p k = ((∑ n ∈ window x p, phase p k n) * star (∑ r ∈ roots a p, phase p k r)).re / p := by
  intro block roots window angle phase coef a x p k
  change (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p =
    ((∑ n ∈ window x p, phase p k n) * star (∑ r ∈ roots a p, phase p k r)).re / p
  congr 1
  conv_rhs => simp only [star_sum, Finset.sum_mul_sum, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro n hn
  have hangle : angle p k (n : ℝ) - angle p k (r : ℝ) = angle p k ((n : ℝ) - r) := by
    dsimp [angle]
    ring
  rw [show phase p k n * star (phase p k r) =
      Complex.exp (((angle p k (n : ℝ) - angle p k (r : ℝ) : ℝ) : ℂ) * Complex.I) by
        dsimp [phase]
        rw [← Complex.exp_conj, ← Complex.exp_add]
        congr 1
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
        ring, hangle, Complex.exp_ofReal_mul_I_re]
