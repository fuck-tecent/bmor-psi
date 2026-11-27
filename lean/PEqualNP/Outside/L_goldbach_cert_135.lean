import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_135 :
    ∀ a:ℕ, Nat.Coprime a 135 → (∑ b ∈ (Finset.range 135).filter (fun b => Nat.Coprime b 135), Complex.exp (((2*Real.pi*(a:ℝ)*b/135:ℝ):ℂ)*Complex.I))/(72:ℂ)=(0:ℂ)/72 := by
  intro a ha
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 135))
  have hζ : IsPrimitiveRoot ζ 135 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp_of_coprime a 135 (by decide) ha
  have h₃ : IsPrimitiveRoot (ζ ^ 45) 3 := hζ.pow_of_dvd (by decide) (by decide)
  have geom : 1 + ζ ^ 45 + (ζ ^ 45) ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
      using h₃.geom_sum_eq_zero (by decide)
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 135 : ℝ) : ℂ) * Complex.I) = ζ ^ b := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    ring
  have unit_iff (b : ℕ) : Nat.Coprime b 135 ↔ ¬ 3 ∣ b ∧ ¬ 5 ∣ b := by
    rw [Nat.coprime_comm, show 135 = 3 * 3 * 3 * 5 by decide]
    simp only [Nat.coprime_mul_iff_left, (by decide : Nat.Prime 3).coprime_iff_not_dvd,
      (by decide : Nat.Prime 5).coprime_iff_not_dvd, and_self]
  let f (b : ℕ) : ℂ := if Nat.Coprime b 135 then ζ ^ b else 0
  have shift (b : ℕ) : f (45 + b) = ζ ^ 45 * f b := by
    have hu : Nat.Coprime (45 + b) 135 ↔ Nat.Coprime b 135 := by
      rw [unit_iff, unit_iff]
      omega
    by_cases hb : Nat.Coprime b 135
    · simp only [f, ite_eq_left hb, ite_eq_left (hu.2 hb), pow_add]
    · simp only [f, ite_eq_right hb, ite_eq_right (fun h => hb (hu.1 h)), mul_zero]
  have cancel : (∑ b ∈ Finset.range 135, f b) = 0 := by
    change (∑ b ∈ Finset.range ((45 + 45) + 45), f b) = 0
    rw [Finset.sum_range_add, Finset.sum_range_add f 45 45,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    rw [Nat.add_assoc, shift (45 + b), shift b]
    linear_combination (f b) * geom
  simp_rw [phase]
  rw [Finset.sum_filter]
  exact congrArg (fun z : ℂ => z / 72) cancel
