import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_large_factor_unique :
    ∀ n p q:ℕ, Nat.Prime p → Nat.Prime q → p∣n^2+1 → q∣n^2+1 → n^2+1<p^2 → n^2+1<q^2 → p=q := by
  intro n p q hp hq hpdiv hqdiv hmp hmq
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hpq : p * q ∣ n ^ 2 + 1 := hcop.mul_dvd_of_dvd_of_dvd hpdiv hqdiv
  have hpos : 0 < n ^ 2 + 1 := by positivity
  have hle : p * q ≤ n ^ 2 + 1 := Nat.le_of_dvd hpos hpq
  have hqlt : q < p := by
    apply lt_of_mul_lt_mul_left _ (le_of_lt hp.pos)
    nlinarith [hle, hmp]
  have hle2 : q * p ≤ n ^ 2 + 1 := by rw [mul_comm]; exact hle
  have hplt : p < q := by
    apply lt_of_mul_lt_mul_left _ (le_of_lt hq.pos)
    nlinarith [hle2, hmq]
  linarith
