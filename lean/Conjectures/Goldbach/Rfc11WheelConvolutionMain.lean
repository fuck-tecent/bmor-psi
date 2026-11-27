import Mathlib

/-!
# Wheel convolution main step (route `finite-rfc-third`, S01)

For every even target `n`, at least `15` of the reflected residue classes modulo
`210 = 2 * 3 * 5 * 7` are allowed: `r` coprime to `210` and `n - r` coprime to `210`.

The count only depends on `n` modulo `210`, so the statement is reduced to the
`210` residue classes, where the bound is checked by kernel reduction.  The
minimum `15 = 1 * 1 * 3 * 5` is attained exactly when `gcd(n, 105) = 1`, which
is the CRT count `(2-1) * (3-2) * (5-2) * (7-2)`.
-/

namespace Conjectures.Goldbach.Rfc11WheelConvolutionMain_aux

/-- The number of allowed reflected residue classes modulo `210` for the target `n`. -/
def card (n : ℕ) : ℕ :=
  ((Finset.range 210).filter
    (fun r => Nat.Coprime r 210 ∧ Nat.Coprime ((n + 210 - r) % 210) 210)).card

/-- The count is periodic in the target with period `210`. -/
theorem card_mod (n : ℕ) : card n = card (n % 210) := by
  unfold card
  congr 1
  apply Finset.filter_congr
  intro r hr
  rw [Finset.mem_range] at hr
  have key : (n + 210 - r) % 210 = (n % 210 + 210 - r) % 210 := by omega
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← key]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [key]; exact h2⟩

-- The finite residue check: every even class modulo `210` has at least `15` allowed
-- reflected classes.
set_option maxRecDepth 100000 in
theorem card_ge_fifteen_of_even : ∀ k < 210, 2 ∣ k → 15 ≤ card k := by decide

end Conjectures.Goldbach.Rfc11WheelConvolutionMain_aux

theorem Conjectures.Goldbach.Rfc11WheelConvolutionMain :
    ∀ n : ℕ, 2∣n → 15 ≤ ((Finset.range 210).filter (fun r => Nat.Coprime r 210 ∧ Nat.Coprime ((n+210-r)%210) 210)).card := by
  intro n hn
  have hcard : ((Finset.range 210).filter
      (fun r => Nat.Coprime r 210 ∧ Nat.Coprime ((n + 210 - r) % 210) 210)).card = Conjectures.Goldbach.Rfc11WheelConvolutionMain_aux.card n := rfl
  rw [hcard, Conjectures.Goldbach.Rfc11WheelConvolutionMain_aux.card_mod]
  refine Conjectures.Goldbach.Rfc11WheelConvolutionMain_aux.card_ge_fifteen_of_even (n % 210) (Nat.mod_lt n (by norm_num)) ?_
  have hdiv : n % 210 + 210 * (n / 210) = n := Nat.mod_add_div n 210
  have h2 : 2 ∣ 210 * (n / 210) := ⟨105 * (n / 210), by ring⟩
  have h3 : n % 210 = n - 210 * (n / 210) := by omega
  rw [h3]
  exact Nat.dvd_sub hn h2
