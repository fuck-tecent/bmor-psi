import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_low_mode_energy :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; let freqs := fun (p : ℕ) (low : Bool) => (Finset.Ico 1 p).filter (fun k => if low then min k (p-k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p-k)); let part := fun (a x p : ℕ) (low : Bool) => (∑ k ∈ freqs p low, coef a x p k) * Real.log (p : ℝ); let modes := fun (a x : ℕ) (low : Bool) => ∑ p ∈ primes x, part a x p low; ∀ x : ℕ, (modes 1 x true)^2 ≤ (∑ p ∈ primes x, Real.log (p : ℝ)) * (∑ p ∈ primes x, (∑ k ∈ freqs p true, coef 1 x p k)^2 * Real.log (p : ℝ)) := by
  intro block roots primes window angle coef freqs part modes x
  change (∑ p ∈ primes x, (∑ k ∈ freqs p true, coef 1 x p k) * Real.log (p : ℝ))^2 ≤
    (∑ p ∈ primes x, Real.log (p : ℝ)) *
      (∑ p ∈ primes x, (∑ k ∈ freqs p true, coef 1 x p k)^2 * Real.log (p : ℝ))
  have hlog : ∀ p ∈ primes x, 0 ≤ Real.log (p : ℝ) := by
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hp'.one_le)
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (primes x) hlog ?_ ?_
  · intro p hp
    exact mul_nonneg (sq_nonneg _) (hlog p hp)
  · intro p hp
    exact le_of_eq (by ring)
