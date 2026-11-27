import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_104 :
    ∀ a:ℕ, Nat.Coprime a 104 → (∑ b ∈ (Finset.range 104).filter (fun b => Nat.Coprime b 104), Complex.exp (((2*Real.pi*(a:ℝ)*b/104:ℝ):ℂ)*Complex.I))/(48:ℂ)=(0:ℂ)/48 := by
  intro a ha
  have odd_a : Odd a :=
    Nat.coprime_two_right.mp (ha.of_dvd_right (by decide : 2 ∣ 104))

  -- Since 2 already divides 52, doubling 52 introduces no new prime divisor.
  have reduce (b : ℕ) : Nat.Coprime b 104 ↔ Nat.Coprime b 52 := by
    rw [show 104 = 2 * 52 by decide, Nat.coprime_mul_iff_right]
    exact ⟨And.right, fun h => ⟨h.of_dvd_right (by decide : 2 ∣ 52), h⟩⟩
  have units (b : ℕ) : Nat.Coprime (52 + b) 104 ↔ Nat.Coprime b 104 := by
    rw [reduce, reduce, Nat.add_comm 52 b, Nat.coprime_add_self_left]

  let phase (b : ℕ) := Complex.exp (((2 * Real.pi * (a : ℝ) * b / 104 : ℝ) : ℂ) * Complex.I)
  have shift (b : ℕ) : phase (52 + b) = -phase b := by
    unfold phase
    have angle :
        ((2 * Real.pi * (a : ℝ) * (52 + b : ℕ) / 104 : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * (a : ℝ) * b / 104 : ℝ) : ℂ) * Complex.I +
          (a : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [angle, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, odd_a.neg_one_pow]
    simp

  let term (b : ℕ) := if Nat.Coprime b 104 then phase b else 0
  have term_shift (b : ℕ) : term (52 + b) = -term b := by
    simp only [term, units, shift]
    split <;> simp
  rw [Finset.sum_filter]
  change (∑ b ∈ Finset.range (52 + 52), term b) / 48 = 0 / 48
  rw [Finset.sum_range_add]
  simp only [term_shift, Finset.sum_neg_distrib, add_neg_cancel]
