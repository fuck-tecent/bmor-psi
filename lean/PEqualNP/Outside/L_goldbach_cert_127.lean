import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_127 :
    ∀ a:ℕ, Nat.Coprime a 127 → (∑ b ∈ (Finset.range 127).filter (fun b => Nat.Coprime b 127), Complex.exp (((2*Real.pi*(a:ℝ)*b/127:ℝ):ℂ)*Complex.I))/(126:ℂ)=(-1:ℂ)/126 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 127)
  have hroot : IsPrimitiveRoot (Complex.exp θ) 127 := by
    simpa [θ] using Complex.isPrimitiveRoot_exp_of_coprime a 127 (by decide) ha
  have hphase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 127 : ℝ) : ℂ) * Complex.I) =
        Complex.exp θ ^ b := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    dsimp [θ]
    ring
  have hunits : (Finset.range 127).filter (fun b => Nat.Coprime b 127) =
      (Finset.range 127).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    rw [Nat.coprime_comm, (by decide : Nat.Prime 127).coprime_iff_not_dvd]
    omega
  have hsum := Finset.sum_erase_add (Finset.range 127) (fun b => Complex.exp θ ^ b)
      (by simp : 0 ∈ Finset.range 127)
  simp only [pow_zero, hroot.geom_sum_eq_zero (by decide)] at hsum
  simp_rw [hphase]
  rw [hunits, eq_neg_of_add_eq_zero_left hsum]
