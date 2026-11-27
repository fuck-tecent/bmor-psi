import Mathlib

private theorem paired_cos (p k n r : ℕ) (hk : 0 < k) (hkp : k < p) :
    Real.cos (2 * Real.pi * ((p-k : ℕ) : ℝ) * ((n : ℝ) - r) / p) =
    Real.cos (2 * Real.pi * (k : ℝ) * ((n : ℝ) - r) / p) := by
  let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p
  change Real.cos (angle p (p-k) ((n : ℝ) - r)) = Real.cos (angle p k ((n : ℝ) - r))
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans hk hkp))
  have hcast : ((p - k : ℕ) : ℝ) = (p : ℝ) - k := by exact_mod_cast (Nat.cast_sub hkp.le)
  have heq : angle p (p-k) ((n : ℝ) - r) =
      (((n : ℤ) - (r : ℤ) : ℤ) : ℝ) * (2 * Real.pi) - angle p k ((n : ℝ) - r) := by
    dsimp [angle]
    rw [hcast]
    push_cast
    field_simp
  rw [heq, Real.cos_int_mul_two_pi_sub]

private theorem paired_sum (s t : Finset ℕ) (p k : ℕ) (hk : 0 < k) (hkp : k < p) :
    (∑ r ∈ s, ∑ n ∈ t, Real.cos (2 * Real.pi * ((p-k : ℕ) : ℝ) * ((n : ℝ) - r) / p)) =
      ∑ r ∈ s, ∑ n ∈ t, Real.cos (2 * Real.pi * (k : ℝ) * ((n : ℝ) - r) / p) := by
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro n _
  exact paired_cos p k n r hk hkp

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_quadratic_primes_levent_conjugate_frequency :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; ∀ a x p k : ℕ, 0<k → k<p → coef a x p (p-k) = coef a x p k := by
  intro block roots window angle coef a x p k hk hkp
  exact congrArg (fun z : ℝ => z / p) (paired_sum (roots a p) (window x p) p k hk hkp)
