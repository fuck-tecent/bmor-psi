import Mathlib

private theorem sum_multiples (z : ℂ) (d m : ℕ) (hd : 0 < d) :
    (∑ b ∈ Finset.range (d * m), if d ∣ b then z ^ b else 0) =
      ∑ j ∈ Finset.range m, (z ^ d) ^ j := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => d * j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Nat.mul_lt_mul_left hd).mpr (Finset.mem_range.mp hj)), ⟨j, rfl⟩⟩
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hd hij
  · intro b hb
    obtain ⟨hbound, ⟨j, rfl⟩⟩ := Finset.mem_filter.mp hb
    exact ⟨j, Finset.mem_range.mpr ((Nat.mul_lt_mul_left hd).mp (Finset.mem_range.mp hbound)), rfl⟩
  · intro j _
    exact (pow_mul z d j).symm

private theorem unit_weight (z : ℂ) (b : ℕ) :
    (if Nat.Coprime b 65 then z ^ b else 0) = z ^ b - (if 5 ∣ b then z ^ b else 0) -
      (if 13 ∣ b then z ^ b else 0) + (if 65 ∣ b then z ^ b else 0) := by
  have hunit : Nat.Coprime b 65 ↔ ¬ 5 ∣ b ∧ ¬ 13 ∣ b := by
    rw [show 65 = 5 * 13 by decide, Nat.coprime_mul_iff_right,
      (Nat.coprime_comm : b.Coprime 5 ↔ _), (Nat.coprime_comm : b.Coprime 13 ↔ _),
      (by decide : Nat.Prime 5).coprime_iff_not_dvd,
      (by decide : Nat.Prime 13).coprime_iff_not_dvd]
  have hboth : 65 ∣ b ↔ 5 ∣ b ∧ 13 ∣ b := by
    exact ⟨fun h => ⟨dvd_trans (by decide : 5 ∣ 65) h, dvd_trans (by decide : 13 ∣ 65) h⟩,
      fun ⟨h₅, h₁₃⟩ => (by decide : Nat.Coprime 5 13).mul_dvd_of_dvd_of_dvd h₅ h₁₃⟩
  by_cases h₅ : 5 ∣ b <;> by_cases h₁₃ : 13 ∣ b <;> simp [hunit, hboth, h₅, h₁₃]

private theorem sum_units_65 (z : ℂ) (hz : IsPrimitiveRoot z 65) :
    (∑ b ∈ (Finset.range 65).filter (fun b => Nat.Coprime b 65), z ^ b) = 1 := by
  have h₅ : IsPrimitiveRoot (z ^ 5) 13 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  have h₁₃ : IsPrimitiveRoot (z ^ 13) 5 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  -- Inclusion-exclusion leaves the contribution of the unique multiple of 65.
  simp_rw [Finset.sum_filter, unit_weight]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_multiples z 5 13 (by decide), sum_multiples z 13 5 (by decide),
    sum_multiples z 65 1 (by decide), hz.geom_sum_eq_zero (by decide),
    h₅.geom_sum_eq_zero (by decide), h₁₃.geom_sum_eq_zero (by decide)]
  simp

theorem PEqualNP.Outside.L_goldbach_cert_65 :
    ∀ a:ℕ, Nat.Coprime a 65 → (∑ b ∈ (Finset.range 65).filter (fun b => Nat.Coprime b 65), Complex.exp (((2*Real.pi*(a:ℝ)*b/65:ℝ):ℂ)*Complex.I))/(48:ℂ)=(1:ℂ)/48 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 65)
  have hz : IsPrimitiveRoot (Complex.exp θ) 65 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 65 (by decide) ha
  apply congrArg (fun s : ℂ => s / 48)
  calc
    _ = ∑ b ∈ (Finset.range 65).filter (fun b => Nat.Coprime b 65), (Complex.exp θ) ^ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = 1 := sum_units_65 _ hz
