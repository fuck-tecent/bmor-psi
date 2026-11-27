import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_coset_nonunit_bias :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ n q r : ℕ, 0<q → r<q → ¬r.Coprime q → A n q r ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
  dsimp only
  intro n q r hq _hr hnonunit
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hresidue : p % q = r := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hdiv : p ∣ q := by
      by_contra hnot
      have hcoprime := hprime.coprime_iff_not_dvd.mpr hnot
      apply hnonunit
      change Nat.gcd r q = 1
      rw [← hresidue, ← Nat.gcd_rec, Nat.gcd_comm q p]
      exact hcoprime
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hq.ne'⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
