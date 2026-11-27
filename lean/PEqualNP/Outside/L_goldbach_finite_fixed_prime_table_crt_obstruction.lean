import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_fixed_prime_table_crt_obstruction : ∀ (P : Finset ℕ) (A : ℕ), (∀ p ∈ P, Nat.Prime p) → ∃ n : ℕ, A < n ∧ Even n ∧ ∀ p ∈ P, p < n ∧ ¬ Nat.Prime (n-p) := by
  intro P A hP
  classical
  set C := ∏ p ∈ P, p with hC
  have hCpos : 0 < C := by
    rw [hC]
    exact Finset.prod_pos (fun p hp => (hP p hp).pos)
  refine ⟨2 * (C * (A + 2)), ?_, ⟨C * (A + 2), by ring⟩, ?_⟩
  · have h1 : A + 2 ≤ C * (A + 2) := Nat.le_mul_of_pos_left (A + 2) hCpos
    omega
  · intro p hp
    have hpp : Nat.Prime p := hP p hp
    have hppos : 0 < p := hpp.pos
    have hpdvdC : p ∣ C := by
      rw [hC]
      exact Finset.dvd_prod_of_mem (fun p => p) hp
    have hpn : p ∣ 2 * (C * (A + 2)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpdvdC (A + 2)) 2
    set k := 2 * (C * (A + 2)) / p with hk
    have hn_eq : 2 * (C * (A + 2)) = p * k := by
      rw [hk]
      exact (Nat.mul_div_cancel' hpn).symm
    have hA2 : 2 ≤ A + 2 := by omega
    have hk4 : 4 ≤ k := by
      rw [hk, Nat.le_div_iff_mul_le hppos]
      have hpC : p ≤ C := Nat.le_of_dvd hCpos hpdvdC
      have hCA : C * 2 ≤ C * (A + 2) := Nat.mul_le_mul_left C hA2
      calc 4 * p ≤ 4 * C := Nat.mul_le_mul_left 4 hpC
        _ = 2 * (C * 2) := by ring
        _ ≤ 2 * (C * (A + 2)) := Nat.mul_le_mul_left 2 hCA
    have hnp : 2 * (C * (A + 2)) - p = p * (k - 1) := by
      calc 2 * (C * (A + 2)) - p = p * k - p * 1 := by rw [hn_eq, Nat.mul_one]
        _ = p * (k - 1) := (Nat.mul_sub_left_distrib p k 1).symm
    refine ⟨?_, ?_⟩
    · rw [hn_eq]
      have h1 : 1 < k := by omega
      have h2 := Nat.mul_lt_mul_of_pos_left h1 hppos
      simpa using h2
    · rw [hnp]
      intro hprime
      have hdvd : p ∣ p * (k - 1) := dvd_mul_right p (k - 1)
      have hcase := hprime.eq_one_or_self_of_dvd p hdvd
      have hlt : p < p * (k - 1) := by
        have h1 : 1 < k - 1 := by omega
        have h2 := Nat.mul_lt_mul_of_pos_left h1 hppos
        simpa using h2
      rcases hcase with h | h
      · exact hpp.ne_one h
      · exact absurd h (ne_of_lt hlt)