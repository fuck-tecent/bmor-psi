import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_quadratic_primes_mass_to_increment :
    let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p:ℝ); let small := fun (x : ℕ) => Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (w n)); let middle := fun (x : ℕ) => Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301)) (w n)); (∀ e : ℝ, 0 < e → ∃ X : ℕ, ∀ x : ℕ, X ≤ x → small x ≤ (1+e)*(x:ℝ)*Real.log (x:ℝ)) → (∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ x : ℕ, B < x ∧ middle x ≤ (1-d)*(x:ℝ)*Real.log (x:ℝ)) → ∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n^2+1 ∧ n^132301 < p^100000 := by
  classical
  intro w small middle hSmall hMiddle B
  obtain ⟨d, hd, hMiddle⟩ := hMiddle
  obtain ⟨X, hSmall⟩ := hSmall (d / 2) (by positivity)
  obtain ⟨x, hx, hMiddleX⟩ := hMiddle (max (max B X) 2)
  have hSmallX := hSmall x (by omega)
  have hxTwo : 2 ≤ x := by omega
  have hxPos : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hxLog : 0 ≤ Real.log (x : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  by_contra hNoLarge
  have hPower (n : ℕ) (hn : n ∈ Finset.Ioc x (2 * x))
      (p : ℕ) (hp : p ∈ (n ^ 2 + 1).primeFactors) : p ^ 100000 ≤ n ^ 132301 := by
    by_contra! hLarge
    have hnLower := (Finset.mem_Ioc.mp hn).1
    have hpFactors := Nat.mem_primeFactors.mp hp
    exact hNoLarge ⟨n, p, by omega, hpFactors.1, hpFactors.2.1, hLarge⟩
  have hTotal : small x + middle x =
      ∑ n ∈ Finset.Ioc x (2 * x), Real.log ((n : ℝ) ^ 2 + 1) := by
    dsimp only [small, middle]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hFilter :
        (n ^ 2 + 1).primeFactors.filter (fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301) =
        (n ^ 2 + 1).primeFactors.filter (fun p => ¬ p ≤ x) := by
      ext p
      simp only [Finset.mem_filter, not_le]
      exact ⟨fun ⟨hp, hxp, _⟩ => ⟨hp, hxp⟩,
        fun ⟨hp, hxp⟩ => ⟨hp, hxp, hPower n hn p hp⟩⟩
    rw [hFilter, Finset.sum_filter_add_sum_filter_not]
    have h := (Real.log_nat_eq_sum_factorization (n ^ 2 + 1)).symm
    simp only [Finsupp.sum, Nat.support_factorization] at h
    push_cast at h
    exact h
  have hLower : 2 * (x : ℝ) * Real.log (x : ℝ) <
      ∑ n ∈ Finset.Ioc x (2 * x), Real.log ((n : ℝ) ^ 2 + 1) := by
    calc
      _ = ∑ _n ∈ Finset.Ioc x (2 * x), 2 * Real.log (x : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, show 2 * x - x = x by omega]
        ring
      _ < _ := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨x + 1, Finset.mem_Ioc.mpr (by omega)⟩
        · intro n hn
          have hxn : (x : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
          have hSquares := mul_pos (sub_pos.mpr hxn)
            (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hxPos)
          calc
            _ = Real.log ((x : ℝ) ^ 2) := by norm_num [Real.log_pow]
            _ < _ := Real.log_lt_log (sq_pos_of_pos hxPos) (by nlinarith only [hSquares])
  have hLoss := mul_nonneg (mul_nonneg hd.le (Nat.cast_nonneg x)) hxLog
  have hBudget : small x + middle x ≤ 2 * (x : ℝ) * Real.log (x : ℝ) := by
    nlinarith only [hSmallX, hMiddleX, hLoss]
  exact (not_lt_of_ge hBudget) (hTotal.symm ▸ hLower)
