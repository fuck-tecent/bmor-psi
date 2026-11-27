import Mathlib

theorem PEqualNP.Outside.L_goldbach_liouville_multiple_average : let L := fun n : ℕ => if n=0 then (0:ℝ) else (-1:ℝ)^n.primeFactorsList.length; let C := fun n : ℕ => (∑ t ∈ Finset.range n, L t * L (n-t))/(n:ℝ); ∀ (N p : ℕ), 0 < N → Nat.Prime p → p ∣ N → (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N-t))/((N/p:ℕ):ℝ)=C (N/p) := by
  dsimp only
  intro N p hN hp hd
  let L : ℕ → ℝ := fun n => if n=0 then 0 else (-1:ℝ)^n.primeFactorsList.length
  change (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N-t))/((N/p:ℕ):ℝ) = (∑ t ∈ Finset.range (N/p), L t * L (N/p-t))/((N/p:ℕ):ℝ)
  have hmul (k : ℕ) : L (p*k) = -L k := by
    by_cases hk : k = 0
    · simp [L, hk]
    · have hpk : p*k ≠ 0 := mul_ne_zero hp.ne_zero hk
      simp only [L, ite_eq_right hpk, ite_eq_right hk]
      rw [← ArithmeticFunction.cardFactors_apply, ← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_mul hp.ne_zero hk, ArithmeticFunction.cardFactors_apply_prime hp, pow_add]
      simp
  have hNmul : p*(N/p)=N := Nat.mul_div_cancel' hd
  have hp0 : 0 < p := hp.pos
  congr 1
  symm
  apply Finset.sum_bij (fun t _ => p*t)
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by nlinarith [hNmul], dvd_mul_right p t⟩
  · intro t ht u hu h
    exact Nat.eq_of_mul_eq_mul_left hp0 h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨u, rfl⟩ := ht.2
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_range]
    nlinarith [hNmul]
  · intro t ht
    simp only [Finset.mem_range] at ht
    have hsub : N-p*t = p*(N/p-t) := by
      calc
        N-p*t = p*(N/p)-p*t := by rw [hNmul]
        _ = p*(N/p-t) := by rw [Nat.mul_sub_left_distrib]
    rw [hsub, hmul, hmul]
    ring


