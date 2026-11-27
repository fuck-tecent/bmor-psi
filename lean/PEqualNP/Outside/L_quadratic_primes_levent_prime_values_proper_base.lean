import Mathlib

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_proper_base :
    let block := fun x : ℕ => Finset.Ioc x (2*x);
    ∀ x n : ℕ, n ∈ block x → ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0 → ¬ (n^2+1).Prime → ∃ p k : ℕ, p.Prime ∧ Odd k ∧ 3≤k ∧ n^2+1=p^k ∧ p^3≤(2*x)^2+1 := by
  intro block x n hn hΛ hnp
  obtain ⟨hx, hn2⟩ := Finset.mem_Ioc.1 hn
  have hn1 : 1 ≤ n := by omega
  have hprimepow : IsPrimePow (n^2+1) := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ
  obtain ⟨p, k, hp, hk0, hpk⟩ := hprimepow
  have hp' : Nat.Prime p := Nat.prime_iff.2 hp
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [pow_one] at hpk
    exact hnp (hpk.symm ▸ hp')
  have hnotEven : ¬ Even k := by
    rintro ⟨j, rfl⟩
    have hsq : n^2+1 = (p^j)^2 := by
      rw [← hpk, pow_add, pow_two]
    have h1 : n^2 < (p^j)^2 := by rw [← hsq]; omega
    have hkey : n^2+1 < (n+1)^2 := by
      have h : (n+1)^2 = n^2 + 2*n + 1 := by ring
      rw [h]; omega
    have h2 : (p^j)^2 < (n+1)^2 := by rw [← hsq]; exact hkey
    have h3 : n < p^j := by
      rcases lt_or_ge n (p^j) with h | h
      · exact h
      · have hlt : (p^j)^2 ≤ n^2 := Nat.pow_le_pow_left h 2
        omega
    have h4 : p^j < n+1 := by
      rcases lt_or_ge (p^j) (n+1) with h | h
      · exact h
      · have hlt : (n+1)^2 ≤ (p^j)^2 := Nat.pow_le_pow_left h 2
        omega
    omega
  have hkodd : Odd k := by
    rcases Nat.even_or_odd k with h | h
    · exact absurd h hnotEven
    · exact h
  have hk2 : 2 ≤ k := by omega
  have hkne2 : k ≠ 2 := by
    rintro rfl
    exact hnotEven (by decide)
  have hk3 : 3 ≤ k := by omega
  have hle1 : p^3 ≤ p^k := Nat.pow_le_pow_right hp'.pos hk3
  have hle2 : p^k ≤ (2*x)^2+1 := by
    rw [hpk]
    exact Nat.add_le_add_right (Nat.pow_le_pow_left hn2 2) 1
  exact ⟨p, k, hp', hkodd, hk3, hpk.symm, hle1.trans hle2⟩
