import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_large_factor_cofactor :
    ∀ n p : ℕ, 1≤n → p.Prime → p ∣ n^2+1 → n<p → ∃ m : ℕ, 0 < m ∧ m≤n ∧ n^2+1=p*m ∧ (Nat.Prime (n^2+1) ↔ m=1) := by
  intro n p hn hp hdvd hnp
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < n^2+1 := by positivity
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  have hmle : m ≤ n := by
    by_contra hc
    have hmge : n+1 ≤ m := by omega
    have hpge : n+1 ≤ p := by omega
    have hge : (n+1)*(n+1) ≤ p*m := Nat.mul_le_mul hpge hmge
    have hsq : n^2 + 1 < (n+1)*(n+1) := by nlinarith
    omega
  refine ⟨m, hmpos, hmle, hm, ?_⟩
  constructor
  · intro hprime
    rcases hprime.eq_one_or_self_of_dvd p ⟨m, hm⟩ with h1 | h1
    · exact absurd h1 hp.ne_one
    · have h : p*1 = p*m := by
        calc p*1 = p := mul_one p
          _ = n^2+1 := h1
          _ = p*m := hm
      exact (Nat.eq_of_mul_eq_mul_left hp.pos h).symm
  · intro hm1
    rw [hm1, mul_one] at hm
    rw [hm]
    exact hp
