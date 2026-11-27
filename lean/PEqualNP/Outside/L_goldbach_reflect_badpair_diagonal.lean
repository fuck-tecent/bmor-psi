import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflect_badpair_diagonal :
    ∀ p q : ℕ, p.Prime → q.Prime → ¬ Nat.Coprime p (p+q) → p=q := by
  intro p q hp hq h
  have hsum : p ∣ p + q := by
    by_contra hnot
    exact h (hp.coprime_iff_not_dvd.mpr hnot)
  have hdvd : p ∣ q := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hsum
  exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd
