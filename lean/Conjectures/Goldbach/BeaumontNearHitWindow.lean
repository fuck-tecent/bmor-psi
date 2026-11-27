import Mathlib

theorem Conjectures.Goldbach.BeaumontNearHitWindow :
    ∀ (n p q r : ℕ) (k : ℤ), 0 < n → 2*r < n → r < p+q → p+q+r < 2*n → |(p:ℤ)+(q:ℤ)-k*(n:ℤ)| ≤ (r:ℤ) → |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ (r:ℤ) := by
  intro n p q r k hn hr hlo hhi h
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  have hlo' : (r : ℤ) < (p : ℤ) + q := by exact_mod_cast hlo
  have hhi' : (p : ℤ) + q + r < 2 * (n : ℤ) := by exact_mod_cast hhi
  have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
  have hk : k = 1 := by
    by_contra bad
    rcases (show k ≤ 0 ∨ 2 ≤ k by omega) with hk | hk
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hk hn'.le]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) hn'.le]
  subst k
  simpa using And.intro h₁ h₂ |> abs_le.mpr
