import Mathlib

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_goldbach_cert_136 :
    ∀ a : ℕ, Nat.Coprime a 136 →
      (∑ b ∈ (Finset.range 136).filter (fun b => Nat.Coprime b 136),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 136 : ℝ) : ℂ) * Complex.I)) /
        (64 : ℂ) = (0 : ℂ) / 64 := by
  intro a ha
  have hodd : ¬ 2 ∣ a := by
    intro h
    exact (by decide : ¬ (2 : ℕ) ∣ 1) (ha.gcd_eq_one ▸ Nat.dvd_gcd h (by decide))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  let t : ℂ := (2 * Real.pi * (a : ℝ) / 136 : ℝ) * Complex.I
  let z := Complex.exp t
  have halfPhase : z ^ 68 = -1 := by
    change Complex.exp t ^ 68 = -1
    rw [← Complex.exp_nat_mul]
    have ht : (68 : ℂ) * t =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      dsimp [t]
      rw [hk]
      push_cast
      ring
    change Complex.exp ((68 : ℂ) * t) = -1
    rw [ht, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]
  have hpow (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 136 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    refine (congrArg Complex.exp ?_).trans (Complex.exp_nat_mul t b)
    dsimp [t]
    push_cast
    ring
  simp_rw [hpow]
  let flip (b : ℕ) := if b < 68 then b + 68 else b - 68
  have hpres : ∀ b : Fin 136, Nat.Coprime b.val 136 →
      flip b.val < 136 ∧ Nat.Coprime (flip b.val) 136 := by decide
  have hsum : ∑ b ∈ (Finset.range 136).filter (fun b => Nat.Coprime b 136), z ^ b = 0 := by
    apply Finset.sum_involution (fun b _ => flip b)
    · intro b hb
      by_cases hl : b < 68
      · simp [flip, hl, pow_add, halfPhase]
      · have he : b = (b - 68) + 68 := by omega
        calc
          z ^ b + z ^ flip b = z ^ ((b - 68) + 68) + z ^ (b - 68) := by
            simpa only [flip, if_neg hl] using congrArg (fun v : ℂ => v + z ^ (b - 68)) (congrArg (fun m : ℕ => z ^ m) he)
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
