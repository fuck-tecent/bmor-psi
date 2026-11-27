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
    (if Nat.Coprime b 77 then z ^ b else 0) = z ^ b - (if 7 ∣ b then z ^ b else 0) -
      (if 11 ∣ b then z ^ b else 0) + (if 77 ∣ b then z ^ b else 0) := by
  have hunit : Nat.Coprime b 77 ↔ ¬ 7 ∣ b ∧ ¬ 11 ∣ b := by
    rw [show 77 = 7 * 11 by decide, Nat.coprime_mul_iff_right,
      (Nat.coprime_comm : b.Coprime 7 ↔ _), (Nat.coprime_comm : b.Coprime 11 ↔ _),
      (by decide : Nat.Prime 7).coprime_iff_not_dvd,
      (by decide : Nat.Prime 11).coprime_iff_not_dvd]
  have hboth : 77 ∣ b ↔ 7 ∣ b ∧ 11 ∣ b := by
    exact ⟨fun h => ⟨dvd_trans (by decide : 7 ∣ 77) h, dvd_trans (by decide : 11 ∣ 77) h⟩,
      fun ⟨h₇, h₁₁⟩ => (by decide : Nat.Coprime 7 11).mul_dvd_of_dvd_of_dvd h₇ h₁₁⟩
  by_cases h₇ : 7 ∣ b <;> by_cases h₁₁ : 11 ∣ b <;> simp [hunit, hboth, h₇, h₁₁]

private theorem sum_units_77 (z : ℂ) (hz : IsPrimitiveRoot z 77) :
    (∑ b ∈ (Finset.range 77).filter (fun b => Nat.Coprime b 77), z ^ b) = 1 := by
  have h₇ : IsPrimitiveRoot (z ^ 7) 11 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  have h₁₁ : IsPrimitiveRoot (z ^ 11) 7 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  -- Inclusion-exclusion leaves the contribution of the unique multiple of 77.
  simp_rw [Finset.sum_filter, unit_weight]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_multiples z 7 11 (by decide), sum_multiples z 11 7 (by decide),
    sum_multiples z 77 1 (by decide), hz.geom_sum_eq_zero (by decide),
    h₇.geom_sum_eq_zero (by decide), h₁₁.geom_sum_eq_zero (by decide)]
  simp

theorem PEqualNP.Outside.L_goldbach_cert_77 :
    ∀ a:ℕ, Nat.Coprime a 77 → (∑ b ∈ (Finset.range 77).filter (fun b => Nat.Coprime b 77), Complex.exp (((2*Real.pi*(a:ℝ)*b/77:ℝ):ℂ)*Complex.I))/(60:ℂ)=(1:ℂ)/60 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 77)
  have hz : IsPrimitiveRoot (Complex.exp θ) 77 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 77 (by decide) ha
  apply congrArg (fun s : ℂ => s / 60)
  calc
    _ = ∑ b ∈ (Finset.range 77).filter (fun b => Nat.Coprime b 77), (Complex.exp θ) ^ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = 1 := sum_units_77 _ hz
