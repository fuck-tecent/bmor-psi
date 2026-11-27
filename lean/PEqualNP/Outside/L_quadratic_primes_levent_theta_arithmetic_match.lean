import Mathlib

private theorem window_factorization_aux :
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

/- Window factorization adapted from PR #2564 (https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2564), Apache-2.0. -/

theorem PEqualNP.Outside.L_quadratic_primes_levent_theta_arithmetic_match :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let phase := fun (p k n : ℕ) => Complex.exp (((angle p k n : ℝ) : ℂ) * Complex.I); let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; let freqs := fun (p : ℕ) (low : Bool) => (Finset.Ico 1 p).filter (fun k => if low then min k (p-k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p-k)); let part := fun (a x p : ℕ) (low : Bool) => (∑ k ∈ freqs p low, coef a x p k) * Real.log (p : ℝ); let modes := fun (a x : ℕ) (low : Bool) => ∑ p ∈ primes x, part a x p low; ∀ x : ℕ, let u := fun p k : ℕ => ∑ n ∈ window x p, phase p k n; let v := fun p k : ℕ => ∑ r ∈ roots 1 p, phase p k r; modes 1 x false = ∑ p ∈ primes x, (∑ k ∈ freqs p false, (‖u p k+v p k‖^2-‖u p k-v p k‖^2)) / (4*(p : ℝ)) * Real.log (p : ℝ) := by
  intro block roots primes window angle phase coef freqs part modes x u v
  change (∑ p ∈ primes x, (∑ k ∈ freqs p false, coef 1 x p k) * Real.log (p : ℝ)) =
    ∑ p ∈ primes x, (∑ k ∈ freqs p false, (‖u p k+v p k‖^2-‖u p k-v p k‖^2)) / (4*(p : ℝ)) * Real.log (p : ℝ)
  /- Polarization adapted from PR #2554 (https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2554), Apache-2.0. -/
  have hpoint (a b : ℂ) : ‖a+b‖^2-‖a-b‖^2 = 4*(a*star b).re := by
    have hi : RCLike.re (inner ℂ a b) = (a * star b).re := by
      rw [inner_re_symm, RCLike.inner_apply]
      rfl
    rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hi]
    ring
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hc (k : ℕ) : coef 1 x p k = (u p k * star (v p k)).re / p := by
    exact window_factorization_aux 1 x p k
  simp_rw [hc, hpoint]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hpprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  field_simp
