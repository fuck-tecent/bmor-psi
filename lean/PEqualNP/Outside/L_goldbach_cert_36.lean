import Mathlib

private theorem units_mod_36 : (Finset.range 36).filter (fun b => Nat.Coprime b 36) =
    {1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35} := by decide

private theorem half_turn (z : ℂ) (hz : IsPrimitiveRoot z 36) : z ^ 18 + 1 = 0 := by
  have hne : z ^ 18 ≠ 1 := by
    intro he
    have : (18 : ℕ) = 0 := hz.pow_inj (by decide : 18 < 36) (by decide : 0 < 36)
      (he.trans (pow_zero z).symm)
    omega
  have h : (z ^ 18 - 1) * (z ^ 18 + 1) = 0 := by
    linear_combination hz.pow_eq_one
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

private theorem sum_units (z : ℂ) (hz : IsPrimitiveRoot z 36) :
    (∑ b ∈ (Finset.range 36).filter (fun b => Nat.Coprime b 36), z ^ b) = 0 := by
  rw [units_mod_36]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  -- Each unit below 18 pairs with its translate by 18.
  calc
    _ = (z ^ 18 + 1) * (z + z ^ 5 + z ^ 7 + z ^ 11 + z ^ 13 + z ^ 17) := by ring
    _ = 0 := by rw [half_turn z hz, zero_mul]

theorem PEqualNP.Outside.L_goldbach_cert_36 :
    ∀ a:ℕ, Nat.Coprime a 36 → (∑ b ∈ (Finset.range 36).filter (fun b => Nat.Coprime b 36), Complex.exp (((2*Real.pi*(a:ℝ)*b/36:ℝ):ℂ)*Complex.I))/(12:ℂ)=(0:ℂ)/12 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 36)
  have hz : IsPrimitiveRoot (Complex.exp θ) 36 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 36 (by decide) ha
  apply congrArg (fun s : ℂ => s / 12)
  calc
    _ = ∑ b ∈ (Finset.range 36).filter (fun b => Nat.Coprime b 36), (Complex.exp θ) ^ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = 0 := sum_units _ hz
