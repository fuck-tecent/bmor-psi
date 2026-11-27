import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_window_units :
    ∀ (n : ℕ) (w : ℕ → ℝ), (∀ k, ¬Nat.Prime k → w k=0) → 0 < (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ k.Coprime n), w k*w (n-k)) → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n ∧ n≤3*p ∧ 3*p≤2*n ∧ p.Coprime n := by
  intro n w hsupport hpos
  obtain ⟨p, hp, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨hrange, hlo, hhi, hcop⟩ := Finset.mem_filter.mp hp
  have hle : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hrange)
  have prime_of_weight {k : ℕ} (hk : w k ≠ 0) : k.Prime := by
    by_contra h
    exact hk (hsupport k h)
  obtain ⟨hpw, hqw⟩ := mul_ne_zero_iff.mp hterm
  exact ⟨p, n - p, prime_of_weight hpw, prime_of_weight hqw, Nat.add_sub_of_le hle, hlo, hhi, hcop⟩
