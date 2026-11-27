import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_113 :
    ∀ a:ℕ, Nat.Coprime a 113 → (∑ b ∈ (Finset.range 113).filter (fun b => Nat.Coprime b 113), Complex.exp (((2*Real.pi*(a:ℝ)*b/113:ℝ):ℂ)*Complex.I))/(112:ℂ)=(-1:ℂ)/112 := by
  intro a ha
  let z := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 113))
  have primitive : IsPrimitiveRoot z 113 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 113 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 113 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    unfold z
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have prime : Nat.Prime 113 := by decide
  have units : (Finset.range 113).filter (fun b => Nat.Coprime b 113) =
      (Finset.range 113).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    by_cases hb : b < 113
    · simp only [hb, true_and, and_true]
      rw [Nat.coprime_comm, prime.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero,
        Nat.mod_eq_of_lt hb]
    · simp [hb]

  have split := Finset.sum_erase_add (Finset.range 113) (fun b => z ^ b)
    (by decide : 0 ∈ Finset.range 113)
  rw [pow_zero, primitive.geom_sum_eq_zero (by decide)] at split
  simp only [phase, units, eq_neg_iff_add_eq_zero.mpr split]
