import Mathlib

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_goldbach_cert_108 :
    ∀ a : ℕ, Nat.Coprime a 108 →
      (∑ b ∈ (Finset.range 108).filter (fun b => Nat.Coprime b 108),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 108 : ℝ) : ℂ) * Complex.I)) /
        (36 : ℂ) = (0 : ℂ) / 36 := by
  intro a ha
  have hodd : ¬ 2 ∣ a := by
    intro h
    exact (by decide : ¬ (2 : ℕ) ∣ 1) (ha.gcd_eq_one ▸ Nat.dvd_gcd h (by decide))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  let t : ℂ := (2 * Real.pi * (a : ℝ) / 108 : ℝ) * Complex.I
  let z := Complex.exp t
  have halfPhase : z ^ 54 = -1 := by
    change Complex.exp t ^ 54 = -1
    rw [← Complex.exp_nat_mul]
    have ht : (54 : ℂ) * t =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      dsimp [t]
      rw [hk]
      push_cast
      ring
    change Complex.exp ((54 : ℂ) * t) = -1
    rw [ht, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]
  have hpow (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 108 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    refine (congrArg Complex.exp ?_).trans (Complex.exp_nat_mul t b)
    dsimp [t]
    push_cast
    ring
  simp_rw [hpow]
  let flip (b : ℕ) := if b < 54 then b + 54 else b - 54
  have hpres : ∀ b : Fin 108, Nat.Coprime b.val 108 →
      flip b.val < 108 ∧ Nat.Coprime (flip b.val) 108 := by decide
  have hsum : ∑ b ∈ (Finset.range 108).filter (fun b => Nat.Coprime b 108), z ^ b = 0 := by
    apply Finset.sum_involution (fun b _ => flip b)
    · intro b hb
      by_cases hl : b < 54
      · simp [flip, hl, pow_add, halfPhase]
      · have he : b = (b - 54) + 54 := by omega
        calc
          z ^ b + z ^ flip b = z ^ ((b - 54) + 54) + z ^ (b - 54) := by
            simpa only [flip, if_neg hl] using congrArg (fun v : ℂ => v + z ^ (b - 54)) (congrArg (fun m : ℕ => z ^ m) he)
          _ = 0 := by simp [pow_add, halfPhase]
    · intro b _ _
      dsimp [flip]
      split <;> omega
    · intro b hb
      have hp := Finset.mem_filter.mp hb
      have h := hpres ⟨b, Finset.mem_range.mp hp.1⟩ hp.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2⟩
    · intro b hb
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      dsimp [flip]
      split <;> split <;> omega
  rw [hsum]
