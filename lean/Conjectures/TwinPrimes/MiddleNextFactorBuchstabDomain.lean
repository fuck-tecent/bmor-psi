import Mathlib

/-- Middle-band Buchstab cofactor range: once repetitions of the first factor `r` have
been removed, the next least prime factor `ℓ` of `s` still exceeds `r`, its cofactor `m`
is at least `ℓ`, and `ℓ` is the least prime factor of `m` as well; moreover the
middle-band size condition `r^3 < p + 2` follows.  Adapted from
`Conjectures.TwinPrimes.RoughWindowFactorShapes`. -/
theorem Conjectures.TwinPrimes.MiddleNextFactorBuchstabDomain :
    ∀ p r s : ℕ, p.Prime → r.Prime → 1<s → p+2=r*s → r<s.minFac → (¬ Nat.Prime s) →
      ∃ ℓ m : ℕ, ℓ.Prime ∧ r<ℓ ∧ ℓ ≤ m ∧ ℓ ≤ Nat.minFac m ∧ s = ℓ * m ∧ r^3<p+2 := by
  intro p r s _hp hr hs1 hprs hlt hsnp
  have hℓ : (s.minFac).Prime := Nat.minFac_prime (by omega)
  have hℓdvd : s.minFac ∣ s := Nat.minFac_dvd s
  have hpos : 0 < s := by omega
  have hℓle : s.minFac ≤ s / s.minFac := Nat.minFac_le_div hpos hsnp
  have hmul : s.minFac * (s / s.minFac) = s := Nat.mul_div_cancel' hℓdvd
  have hm2 : 2 ≤ s / s.minFac := by
    have := hℓ.two_le
    omega
  have hmdvd : s / s.minFac ∣ s := ⟨s.minFac, hmul.symm.trans (mul_comm _ _)⟩
  have hmfp : (s / s.minFac).minFac.Prime := Nat.minFac_prime (by omega)
  have hmfdvd : (s / s.minFac).minFac ∣ s :=
    dvd_trans (Nat.minFac_dvd _) hmdvd
  have hmfle : s.minFac ≤ (s / s.minFac).minFac :=
    Nat.minFac_le_of_dvd hmfp.two_le hmfdvd
  have hr2 : 2 ≤ r := hr.two_le
  have hℓr : r < s.minFac := hlt
  have hmgt : r < s / s.minFac := lt_of_lt_of_le hℓr hℓle
  have hsgt : r * r < s := by
    have h1 : r + 1 ≤ s.minFac := by omega
    have h2 : r + 1 ≤ s / s.minFac := by omega
    calc r * r < (r + 1) * (r + 1) := by nlinarith
      _ ≤ s.minFac * (s / s.minFac) := Nat.mul_le_mul h1 h2
      _ = s := hmul
  have hr3 : r ^ 3 < p + 2 := by
    have hposr : 0 < r := by omega
    have : r * r * r < r * s := by nlinarith
    rw [hprs]
    simpa [pow_succ, pow_two] using this
  exact ⟨s.minFac, s / s.minFac, hℓ, hℓr, hℓle, hmfle, hmul.symm, hr3⟩
