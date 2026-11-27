import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_153 :
    ∀ a:ℕ, Nat.Coprime a 153 → (∑ b ∈ (Finset.range 153).filter (fun b => Nat.Coprime b 153), Complex.exp (((2*Real.pi*(a:ℝ)*b/153:ℝ):ℂ)*Complex.I))/(96:ℂ)=(0:ℂ)/96 := by
  intro a ha
  let phase (b : ℕ) : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) * b / 153 : ℝ) : ℂ) * Complex.I)
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 3))
  have hroot : IsPrimitiveRoot ζ 3 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 3 (by decide) (ha.of_dvd_right (by decide))
  have hcycle : 1 + ζ + ζ * ζ = 0 := by
    have hmul : (1 + ζ + ζ * ζ) * (ζ - 1) = 0 := by
      calc
        _ = ζ ^ 3 - 1 := by ring
        _ = 0 := by rw [hroot.pow_eq_one, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr (hroot.ne_one (by decide)))

  -- The unit condition depends only on the factors of 51, and repeats every 51 terms.
  have hreduce (b : ℕ) : Nat.Coprime b 153 ↔ Nat.Coprime b 51 := by
    rw [show (153 : ℕ) = 3 * 51 by decide, Nat.coprime_mul_iff_right]
    exact ⟨And.right, fun h => ⟨h.of_dvd_right (by decide), h⟩⟩
  let g (b : ℕ) : ℂ := if Nat.Coprime b 153 then phase b else 0
  have hstep (b : ℕ) : g (51 + b) = ζ * g b := by
    have hcop : Nat.Coprime (51 + b) 153 ↔ Nat.Coprime b 153 := by
      rw [hreduce, hreduce, Nat.add_comm 51 b]
      simpa only [mul_one] using Nat.coprime_add_mul_left_left b 51 1
    have hphase : phase (51 + b) = ζ * phase b := by
      dsimp [phase, ζ]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [g, hcop, hphase]
    split_ifs <;> simp

  let s : ℂ := ∑ b ∈ Finset.range 51, g b
  have hblock₁ : (∑ b ∈ Finset.range 51, g (51 + b)) = ζ * s := by
    simp only [s, hstep, Finset.mul_sum]
  have hblock₂ : (∑ b ∈ Finset.range 51, g (102 + b)) = ζ * (ζ * s) := by
    simp only [s, show (102 : ℕ) = 51 + 51 by decide, add_assoc, hstep, Finset.mul_sum]
  have hsum : (∑ b ∈ Finset.range 153, g b) = 0 := by
    calc
      _ = (s + ζ * s) + ζ * (ζ * s) := by
        rw [show (153 : ℕ) = 102 + 51 by decide, Finset.sum_range_add, hblock₂,
          show (102 : ℕ) = 51 + 51 by decide, Finset.sum_range_add, hblock₁]
      _ = (1 + ζ + ζ * ζ) * s := by ring
      _ = 0 := by rw [hcycle, zero_mul]
  rw [Finset.sum_filter]
  change (∑ b ∈ Finset.range 153, g b) / (96 : ℂ) = _
  rw [hsum]
