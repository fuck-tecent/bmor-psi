import Mathlib

theorem Conjectures.QuadraticPrimes.DisjointFirstHitPrimeExtraction :
    ∀ (R H U E P : ℕ → ℝ) (a b ε : ℝ), 0<ε → a+b+ε<1 → (∀ x, R x ≤ H x + U x + E x + P x) → (∀ x, H x ≤ a*R x) → (∀ x, E x ≤ ε*R x) → ∀ x, U x ≤ b*R x → (1-a-b-ε)*R x ≤ P x := by
  intro R H U E P a b ε _hε _hmargin hR hH hE x hU
  have hRx := hR x
  have hHx := hH x
  have hEx := hE x
  nlinarith
