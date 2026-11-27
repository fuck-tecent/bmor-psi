import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_114 :
    ∀ a:ℕ, Nat.Coprime a 114 → (∑ b ∈ (Finset.range 114).filter (fun b => Nat.Coprime b 114), Complex.exp (((2*Real.pi*(a:ℝ)*b/114:ℝ):ℂ)*Complex.I))/(36:ℂ)=(-1:ℂ)/36 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 114)
  let z := Complex.exp θ
  have hroot : IsPrimitiveRoot z 114 := by
    simpa [z, θ] using Complex.isPrimitiveRoot_exp_of_coprime a 114 (by decide) ha
  have hphase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 114 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring
  have multiples (p q : ℕ) (hp : 0 < p) :
      (∑ b ∈ Finset.range (p * q), if p ∣ b then z ^ b else 0) =
        ∑ k ∈ Finset.range q, (z ^ p) ^ k := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij' (p * ·) (· / p)
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        ((Nat.mul_lt_mul_left hp).mpr (Finset.mem_range.mp hk)), Nat.dvd_mul_right p k⟩
    · intro b hb
      apply Finset.mem_range.mpr ∘ (Nat.div_lt_iff_lt_mul hp).mpr
      simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    · exact fun k _ => Nat.mul_div_cancel_left k hp
    · exact fun b hb => Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
    · exact fun k _ => (pow_mul z p k).symm
  have units (b : ℕ) : b.Coprime 114 ↔ ¬ 2 ∣ b ∧ ¬ 3 ∣ b ∧ ¬ 19 ∣ b := by
    change b.Coprime (2 * 3 * 19) ↔ _
    simp only [Nat.coprime_mul_iff_right,
      (@Nat.coprime_comm b 2),
      (@Nat.coprime_comm b 3),
      (@Nat.coprime_comm b 19),
      (by decide : Nat.Prime 2).coprime_iff_not_dvd,
      (by decide : Nat.Prime 3).coprime_iff_not_dvd,
      (by decide : Nat.Prime 19).coprime_iff_not_dvd,
      and_assoc]
  have dvd6 (b : ℕ) : 6 ∣ b ↔ 2 ∣ b ∧ 3 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 2 ∣ 6) h, dvd_trans (by decide : 3 ∣ 6) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h k⟩
  have dvd38 (b : ℕ) : 38 ∣ b ↔ 2 ∣ b ∧ 19 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 2 ∣ 38) h, dvd_trans (by decide : 19 ∣ 38) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 2 19).mul_dvd_of_dvd_of_dvd h k⟩
  have dvd57 (b : ℕ) : 57 ∣ b ↔ 3 ∣ b ∧ 19 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 3 ∣ 57) h, dvd_trans (by decide : 19 ∣ 57) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 3 19).mul_dvd_of_dvd_of_dvd h k⟩
  have dvd114 (b : ℕ) : 114 ∣ b ↔ 6 ∣ b ∧ 19 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 6 ∣ 114) h, dvd_trans (by decide : 19 ∣ 114) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 6 19).mul_dvd_of_dvd_of_dvd h k⟩
  have inclusion (b : ℕ) : (if b.Coprime 114 then z ^ b else 0) =
      z ^ b -
        (if 2 ∣ b then z ^ b else 0) -
        (if 3 ∣ b then z ^ b else 0) -
        (if 19 ∣ b then z ^ b else 0) +
        (if 6 ∣ b then z ^ b else 0) +
        (if 38 ∣ b then z ^ b else 0) +
        (if 57 ∣ b then z ^ b else 0) -
        (if 114 ∣ b then z ^ b else 0) := by
    simp only [units, dvd114, dvd57, dvd38, dvd6]
    by_cases h2 : 2 ∣ b <;> by_cases h3 : 3 ∣ b <;> by_cases h19 : 19 ∣ b <;> simp [h2, h3, h19]
  have sum2 : (∑ b ∈ Finset.range 114, if 2 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 2 57 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 114) hroot (by decide : 114 = 2 * 57)).geom_sum_eq_zero (by decide)
  have sum3 : (∑ b ∈ Finset.range 114, if 3 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 3 38 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 114) hroot (by decide : 114 = 3 * 38)).geom_sum_eq_zero (by decide)
  have sum19 : (∑ b ∈ Finset.range 114, if 19 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 19 6 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 114) hroot (by decide : 114 = 19 * 6)).geom_sum_eq_zero (by decide)
  have sum6 : (∑ b ∈ Finset.range 114, if 6 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 6 19 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 114) hroot (by decide : 114 = 6 * 19)).geom_sum_eq_zero (by decide)
  have sum38 : (∑ b ∈ Finset.range 114, if 38 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 38 3 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 114) hroot (by decide : 114 = 38 * 3)).geom_sum_eq_zero (by decide)
  have sum57 : (∑ b ∈ Finset.range 114, if 57 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 57 2 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 114) hroot (by decide : 114 = 57 * 2)).geom_sum_eq_zero (by decide)
  have sum114 : (∑ b ∈ Finset.range 114, if 114 ∣ b then z ^ b else 0) = 1 := by
    rw [multiples 114 1 (by decide)]
    simp
  apply congrArg (fun s : ℂ => s / 36)
  simp_rw [hphase]
  rw [Finset.sum_filter]
  simp_rw [inclusion]
  norm_num only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hroot.geom_sum_eq_zero (by decide), sum2, sum3, sum19, sum6, sum38, sum57, sum114]
