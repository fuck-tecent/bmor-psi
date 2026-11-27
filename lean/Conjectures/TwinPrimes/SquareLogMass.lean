import Mathlib

open scoped BigOperators

noncomputable section

/-- PREPUB twin-primes gap `L-twin-primes-square-log-mass`:
the von Mangoldt mass of prime squares up to `Y` is at most `log 4 * √Y`.
Indeed `Λ(p²) = log p`, the sum reindexes to `θ(√Y)`, and Chebyshev bounds `θ(√Y) ≤ log 4 * √Y`. -/
theorem Conjectures.TwinPrimes.SquareLogMass :
    let Λ := ArithmeticFunction.vonMangoldt;
    ∀ Y : ℕ, ((Finset.range (Y+1)).filter
        (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n)^2)).sum (fun n => Λ n)
      ≤ Real.log 4 * Real.sqrt Y := by
  dsimp only
  intro Y
  -- Reindex the prime squares `n = (√n)^2` by their square roots `p = √n`.
  have hbij : (∑ n ∈ (Finset.range (Y+1)).filter
        (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n)^2),
        ArithmeticFunction.vonMangoldt n)
      = ∑ p ∈ (Finset.range (Y.sqrt + 1)).filter (fun p => p.Prime),
          Real.log (p : ℝ) := by
    refine Finset.sum_bij (fun n _ => Nat.sqrt n) ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hnrange, hprime, -⟩ := Finset.mem_filter.mp hn
      have hnY : n ≤ Y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sqrt_le_sqrt hnY)), hprime⟩
    · intro n1 hn1 n2 hn2 he
      obtain ⟨-, -, hsq1⟩ := Finset.mem_filter.mp hn1
      obtain ⟨-, -, hsq2⟩ := Finset.mem_filter.mp hn2
      rw [hsq1, hsq2, he]
    · intro p hp
      obtain ⟨hprange, hpprime⟩ := Finset.mem_filter.mp hp
      have hpY : p ≤ Y.sqrt := Nat.lt_succ_iff.mp (Finset.mem_range.mp hprange)
      have hp2Y : p ^ 2 ≤ Y := by
        calc p ^ 2 = p * p := by ring
          _ ≤ Y.sqrt * Y.sqrt := Nat.mul_self_le_mul_self hpY
          _ = Y.sqrt ^ 2 := by ring
          _ ≤ Y := Nat.sqrt_le' Y
      refine ⟨p ^ 2, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
        · rw [Nat.sqrt_eq']
          exact hpprime
        · rw [Nat.sqrt_eq']
      · rw [Nat.sqrt_eq']
    · intro n hn
      obtain ⟨-, hprime, hsq⟩ := Finset.mem_filter.mp hn
      rw [hsq, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : 2 ≠ 0),
        Nat.sqrt_eq']
      exact ArithmeticFunction.vonMangoldt_apply_prime hprime
  rw [hbij]
  -- The prime sum is `θ(√Y)`, bounded by Chebyshev's estimate.
  have hθ : (∑ p ∈ (Finset.range (Y.sqrt + 1)).filter (fun p => p.Prime),
        Real.log (p : ℝ)) = Chebyshev.theta (Y.sqrt : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log (Y.sqrt)]
    congr 1
  have hmono : Chebyshev.theta (Y.sqrt : ℝ) ≤ Chebyshev.theta (Real.sqrt (Y : ℝ)) := by
    apply Chebyshev.theta_mono
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' Y
  calc (∑ p ∈ (Finset.range (Y.sqrt + 1)).filter (fun p => p.Prime),
        Real.log (p : ℝ))
      = Chebyshev.theta (Y.sqrt : ℝ) := hθ
    _ ≤ Chebyshev.theta (Real.sqrt (Y : ℝ)) := hmono
    _ ≤ Real.log 4 * Real.sqrt (Y : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg (Y : ℝ))
