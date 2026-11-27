import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_109 :
    ∀ a:ℕ, Nat.Coprime a 109 → (∑ b ∈ (Finset.range 109).filter (fun b => Nat.Coprime b 109), Complex.exp (((2*Real.pi*(a:ℝ)*b/109:ℝ):ℂ)*Complex.I))/(108:ℂ)=(-1:ℂ)/108 := by
  intro a ha
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 109))
  have hζ : IsPrimitiveRoot ζ 109 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp_of_coprime a 109 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 109 : ℝ) : ℂ) * Complex.I) = ζ ^ b := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have units : (Finset.range 109).filter (fun b => Nat.Coprime b 109) =
      (Finset.range 109).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 109)]
    omega
  simp_rw [phase]
  rw [units, Finset.sum_erase_eq_sub (Finset.mem_range.mpr (by decide : 0 < 109)),
    hζ.geom_sum_eq_zero (by decide : 1 < 109)]
  simp
