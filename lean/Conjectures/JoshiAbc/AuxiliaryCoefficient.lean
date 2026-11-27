import Mathlib

/-!
# JA-0062: a uniform size for the auxiliary prime

For every positive real tolerance we pick one prime `l`, at least `7`, whose rational weight
`4 * l / ((l - 3) * (l + 1))` is at most that tolerance.  The primes are unbounded, and the
weight decays like `4 / (l - 3)`, so it suffices to take a prime above the ceiling of `4 / ε`
shifted by `7`; then `ε * (l - 3) ≥ 4` and `l ≥ 7` give the estimate.
-/

theorem Conjectures.JoshiAbc.AuxiliaryCoefficient :
    ∀ ε : ℝ, 0 < ε → ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)) ≤ ε := by
  intro ε hε
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (⌈4/ε⌉₊ + 7)
  have hl7 : 7 ≤ l := by omega
  refine ⟨l, hlp, hl7, ?_⟩
  have hceil : (4:ℝ)/ε ≤ ((⌈4/ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil ((4:ℝ)/ε)
  have hcast : ((⌈4/ε⌉₊ + 7 : ℕ) : ℝ) ≤ (l : ℝ) := Nat.cast_le.mpr hl
  push_cast at hcast
  have hx : (7:ℝ) ≤ (l : ℝ) := by exact_mod_cast hl7
  have hx3 : (4:ℝ)/ε ≤ (l : ℝ) - 3 := by linarith
  have key : 4 ≤ ((l : ℝ) - 3) * ε := (div_le_iff₀ hε).mp hx3
  have hden : 0 < ((l : ℝ) - 3) * ((l : ℝ) + 1) := by nlinarith
  rw [div_le_iff₀ hden]
  calc 4 * (l : ℝ) ≤ 4 * ((l : ℝ) + 1) := by linarith
    _ ≤ (((l : ℝ) - 3) * ε) * ((l : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right key (by linarith)
    _ = ε * (((l : ℝ) - 3) * ((l : ℝ) + 1)) := by ring
