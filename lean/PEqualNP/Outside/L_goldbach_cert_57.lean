import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_57 :
    ∀ a:ℕ, Nat.Coprime a 57 → (∑ b ∈ (Finset.range 57).filter (fun b => Nat.Coprime b 57), Complex.exp (((2*Real.pi*(a:ℝ)*b/57:ℝ):ℂ)*Complex.I))/(36:ℂ)=(1:ℂ)/36 := by
  intro a ha
  let phase (b : ℕ) : ℂ :=
    Complex.exp (((2 * Real.pi * (a : ℝ) * b / 57 : ℝ) : ℂ) * Complex.I)

  -- Index the multiples of d by the k integers from 0 to k - 1.
  have sum_multiples (d k : ℕ) (hd : 0 < d) (hdk : d * k = 57) :
      (∑ b ∈ (Finset.range 57).filter (fun b => d ∣ b), phase b) =
        ∑ j ∈ Finset.range k, phase (d * j) := by
    symm
    refine Finset.sum_bij (fun j _ => d * j) ?_ ?_ ?_ ?_
    · intro j hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨j, rfl⟩⟩
      rw [← hdk]
      exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hj) hd
    · intro j _ l _ hjl
      exact Nat.eq_of_mul_eq_mul_left hd hjl
    · intro b hb
      obtain ⟨j, rfl⟩ := (Finset.mem_filter.mp hb).2
      have hj := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      rw [← hdk] at hj
      exact ⟨j, Finset.mem_range.mpr (lt_of_mul_lt_mul_left hj (Nat.zero_le d)), rfl⟩
    · intros
      rfl

  have sum_zero (d k : ℕ) (hd : 0 < d) (hk : 1 < k) (hdk : d * k = 57) :
      (∑ b ∈ (Finset.range 57).filter (fun b => d ∣ b), phase b) = 0 := by
    have hk₀ : k ≠ 0 := by omega
    have hcop : a.Coprime k := ha.of_dvd_right ⟨d, hdk.symm.trans (Nat.mul_comm d k)⟩
    let z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / k))
    have hroot : IsPrimitiveRoot z k := Complex.isPrimitiveRoot_exp_of_coprime a k hk₀ hcop
    have hscale : (d : ℂ) * (k : ℂ) = 57 := by exact_mod_cast hdk
    have hdℂ : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hkℂ : (k : ℂ) ≠ 0 := by exact_mod_cast hk₀
    have hphase (j : ℕ) : phase (d * j) = z ^ j := by
      dsimp only [phase, z]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      rw [← hscale]
      field_simp
    rw [sum_multiples d k hd hdk]
    simp_rw [hphase]
    exact hroot.geom_sum_eq_zero hk

  have hall : (∑ b ∈ Finset.range 57, phase b) = 0 := by
    simpa only [one_dvd, Finset.filter_true] using sum_zero 1 57 (by decide) (by decide) (by decide)
  have hthree := sum_zero 3 19 (by decide) (by decide) (by decide)
  have hnineteen := sum_zero 19 3 (by decide) (by decide) (by decide)
  have hintersection : (∑ b ∈ (Finset.range 57).filter (fun b => 57 ∣ b), phase b) = 1 := by
    rw [sum_multiples 57 1 (by decide) (by decide)]
    simp [phase]

  -- Inclusion-exclusion removes multiples of the two prime factors.
  have hpoint (b : ℕ) :
      (if Nat.Coprime b 57 then phase b else 0) =
        phase b - (if 3 ∣ b then phase b else 0) - (if 19 ∣ b then phase b else 0) +
          (if 57 ∣ b then phase b else 0) := by
    have hcop : Nat.Coprime b 57 ↔ ¬3 ∣ b ∧ ¬19 ∣ b := by
      rw [show (57 : ℕ) = 3 * 19 by decide, Nat.coprime_mul_iff_right]
      exact and_congr
        (Nat.coprime_comm.trans ((by decide : Nat.Prime 3).coprime_iff_not_dvd))
        (Nat.coprime_comm.trans ((by decide : Nat.Prime 19).coprime_iff_not_dvd))
    have hboth : 57 ∣ b ↔ 3 ∣ b ∧ 19 ∣ b := by
      refine ⟨fun h => ⟨dvd_trans (by decide : 3 ∣ 57) h, dvd_trans (by decide : 19 ∣ 57) h⟩, ?_⟩
      rintro ⟨h₃, h₁₉⟩
      exact (by decide : Nat.Coprime 3 19).mul_dvd_of_dvd_of_dvd h₃ h₁₉
    by_cases h₃ : 3 ∣ b <;> by_cases h₁₉ : 19 ∣ b <;> simp [hcop, hboth, h₃, h₁₉]

  have hsum : (∑ b ∈ (Finset.range 57).filter (fun b => Nat.Coprime b 57), phase b) = 1 := by
    rw [Finset.sum_filter]
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_filter,
      hall, hthree, hnineteen, hintersection, sub_zero, zero_add]
  change (∑ b ∈ (Finset.range 57).filter (fun b => Nat.Coprime b 57), phase b) / (36 : ℂ) = _
  rw [hsum]
