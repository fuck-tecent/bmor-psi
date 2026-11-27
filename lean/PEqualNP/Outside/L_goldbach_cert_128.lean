import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_128 :
    ∀ a:ℕ, Nat.Coprime a 128 → (∑ b ∈ (Finset.range 128).filter (fun b => Nat.Coprime b 128), Complex.exp (((2*Real.pi*(a:ℝ)*b/128:ℝ):ℂ)*Complex.I))/(64:ℂ)=(0:ℂ)/64 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 128)
  have hroot : IsPrimitiveRoot (Complex.exp θ) 128 := by
    simpa [θ] using Complex.isPrimitiveRoot_exp_of_coprime a 128 (by decide) ha
  have hhalf : Complex.exp θ ^ 64 = -1 := by
    exact (IsPrimitiveRoot.pow (by decide) hroot (show 128 = 64 * 2 by decide)).eq_neg_one_of_two_right
  have hphase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 128 : ℝ) : ℂ) * Complex.I) =
        Complex.exp θ ^ b := by
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring
  have hshift (b : ℕ) : Nat.Coprime (64 + b) 128 ↔ Nat.Coprime b 128 := by
    change Nat.Coprime (64 + b) (2 ^ 7) ↔ Nat.Coprime b (2 ^ 7)
    simp only [Nat.coprime_pow_right_iff (by decide : 0 < 7), Nat.coprime_two_right,
      Nat.odd_iff]
    omega
  apply congrArg (fun z : ℂ => z / 64)
  simp_rw [hphase]
  rw [Finset.sum_filter, show 128 = 64 + 64 by decide, Finset.sum_range_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  change (if Nat.Coprime b 128 then Complex.exp θ ^ b else 0) +
    (if Nat.Coprime (64 + b) 128 then Complex.exp θ ^ (64 + b) else 0) = 0
  rw [if_congr (hshift b) rfl rfl, pow_add, hhalf]
  split_ifs <;> simp_all only [neg_one_mul, add_neg_cancel, add_zero]
