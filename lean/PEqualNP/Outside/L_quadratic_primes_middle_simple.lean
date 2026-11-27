import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_middle_simple :
    ∀ p n:ℕ,Nat.Prime p → p∣n^2+1 → n^2+1<p^2 → (n^2+1).factorization p=1 := by
  intro p n hp hdvd hlt
  have hNpos : 0 < n^2+1 := by positivity
  obtain ⟨m, hm⟩ := hdvd
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : 0 < p := by omega
  have hpne : p ≠ 0 := by omega
  have hlt' : n^2+1 < p * p := by simpa only [pow_two] using hlt
  have hm_lt : m < p := (Nat.mul_lt_mul_left hppos).mp (by rw [← hm]; exact hlt')
  have hmne : m ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hm
    omega
  have hpm : ¬ p ∣ m := by
    intro h
    obtain ⟨k, hk⟩ := h
    have hdvd2 : p^2 ∣ n^2+1 := by
      rw [hm, hk]
      exact ⟨k, by ring⟩
    have hle : p^2 ≤ n^2+1 := Nat.le_of_dvd hNpos hdvd2
    omega
  have hmul : (p * m).factorization = p.factorization + m.factorization :=
    Nat.factorization_mul hpne hmne
  rw [hm, hmul]
  have h1 : p.factorization p = 1 := hp.factorization_self
  have h2 : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpm
  simp [h1, h2]
