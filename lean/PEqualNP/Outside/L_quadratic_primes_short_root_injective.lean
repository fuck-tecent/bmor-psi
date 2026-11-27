import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_short_root_injective :
    ∀ p x m n:ℕ,m∈Finset.Ico x (x+p) → n∈Finset.Ico x (x+p) → m % p = n % p → m=n := by
  intro p x m n hm hn hmod
  rw [Finset.mem_Ico] at hm hn
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨hn1, hn2⟩ := hn
  rcases le_total m n with hle | hle
  · have hk : n - m < p := by omega
    have hdvd : p ∣ n - m := (Nat.modEq_iff_dvd' hle).mp hmod
    have h0 : n - m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hk
    omega
  · have hk : m - n < p := by omega
    have hdvd : p ∣ m - n := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have h0 : m - n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hk
    omega
