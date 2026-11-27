import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0

The conversion of exponential terms to powers adapts 26day's proof in Goldbach PR #455,
commit c46a616a409fd17d43cef0900bd35c5bf8fedf1a. The even-half-period lemma below
is new in this certificate.
-/

open scoped BigOperators

/-- Translation by an even half-period preserves the unit residues and negates their powers. -/
private theorem sum_unit_powers_even_half {d : ℕ} (hd : d ≠ 0) (heven : 2 ∣ d)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * d)) :
    (∑ b ∈ (Finset.range (2 * d)).filter (fun b => b.Coprime (2 * d)), ζ ^ b) = 0 := by
  have hhalf : ζ ^ d = -1 := by
    have hsquare : (ζ ^ d) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm d 2]
      exact hζ.pow_eq_one
    exact (sq_eq_one_iff.mp hsquare).resolve_left (hζ.pow_ne_one_of_pos_of_lt hd (by omega))
  have hreduce (b : ℕ) : b.Coprime (2 * d) ↔ b.Coprime d := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨And.right, fun hb => ⟨Nat.Coprime.of_dvd_right heven hb, hb⟩⟩
  have hcop (b : ℕ) : (d + b).Coprime (2 * d) ↔ b.Coprime (2 * d) :=
    (hreduce (d + b)).trans (Nat.coprime_self_add_left.trans (hreduce b).symm)
  let term (b : ℕ) : ℂ := if b.Coprime (2 * d) then ζ ^ b else 0
  have hshift (b : ℕ) : term (d + b) = -term b := by
    dsimp only [term]
    by_cases hb : b.Coprime (2 * d)
    · rw [ite_eq_left ((hcop b).mpr hb), ite_eq_left hb, pow_add, hhalf, neg_one_mul]
    · rw [ite_eq_right (mt (hcop b).mp hb), ite_eq_right hb, neg_zero]
  rw [Finset.sum_filter]
  change (∑ b ∈ Finset.range (2 * d), term b) = 0
  rw [two_mul, Finset.sum_range_add]
  simp_rw [hshift]
  simp

theorem PEqualNP.Outside.L_goldbach_cert_144 :
    ∀ a:ℕ, Nat.Coprime a 144 → (∑ b ∈ (Finset.range 144).filter (fun b => Nat.Coprime b 144), Complex.exp (((2*Real.pi*(a:ℝ)*b/144:ℝ):ℂ)*Complex.I))/(48:ℂ)=(0:ℂ)/48 := by
  intro a ha
  let t : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 144)
  let ζ := Complex.exp t
  have hζ : IsPrimitiveRoot ζ 144 := by
    simpa [ζ, t] using Complex.isPrimitiveRoot_exp_of_coprime a 144 (by decide) ha
  have hterm (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 144 : ℝ) : ℂ) * Complex.I) = ζ ^ b := by
    change _ = Complex.exp t ^ b
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    dsimp [t]
    ring
  simp_rw [hterm]
  exact congrArg (fun x : ℂ => x / 48)
    (sum_unit_powers_even_half (d := 72) (by decide) (by decide) hζ)
