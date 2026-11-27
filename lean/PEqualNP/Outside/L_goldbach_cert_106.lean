import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Expanding the coprimality indicator by Möbius inversion leaves a single
    divisor sum, since the root has full order. -/
private theorem sumPrimitivePowers {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : IsPrimitiveRoot z q) :
    (∑ b ∈ (range q).filter (fun b => b.Coprime q), z ^ b) = (μ q : ℂ) := by
  have indicator (b : ℕ) : (if b.Coprime q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ b then (μ d : ℂ) else 0 := by
    have common : q.divisors.filter (· ∣ b) = (b.gcd q).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      exact ⟨fun ⟨⟨hdq, _⟩, hdb⟩ => ⟨⟨hdb, hdq⟩, (Nat.gcd_pos_of_pos_right b hq).ne'⟩,
        fun ⟨⟨hdb, hdq⟩, _⟩ => ⟨⟨hdq, hq.ne'⟩, hdb⟩⟩
    rw [← sum_filter, common, ← Int.cast_sum]
    have h : (∑ d ∈ (b.gcd q).divisors, μ d) = if b.gcd q = 1 then 1 else 0 := by
      rw [← coe_zeta_mul_apply, coe_zeta_mul_moebius, ArithmeticFunction.one_apply]
    rw [h]
    split_ifs <;> simp_all [Nat.Coprime]
  have expand (b : ℕ) : (if b.Coprime q then z ^ b else 0) =
      ∑ d ∈ q.divisors, (μ d : ℂ) * (if d ∣ b then z ^ b else 0) := by
    calc
      _ = (if b.Coprime q then (1 : ℂ) else 0) * z ^ b := by split_ifs <;> simp
      _ = _ := by
        rw [indicator, sum_mul]
        apply sum_congr rfl
        intro d _
        split_ifs <;> simp
  have multiples (d k : ℕ) (hd : 0 < d) :
      (∑ b ∈ range (d * k), if d ∣ b then z ^ b else 0) =
        ∑ j ∈ range k, (z ^ d) ^ j := by
    rw [← sum_filter]
    symm
    apply sum_nbij' (d * ·) (· / d)
    · intro j hj
      exact mem_filter.mpr ⟨mem_range.mpr ((Nat.mul_lt_mul_left hd).mpr (mem_range.mp hj)),
        Nat.dvd_mul_right d j⟩
    · intro b hb
      apply mem_range.mpr ∘ (Nat.div_lt_iff_lt_mul hd).mpr
      simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hb).1
    · exact fun j _ => Nat.mul_div_cancel_left j hd
    · exact fun b hb => Nat.mul_div_cancel' (mem_filter.mp hb).2
    · exact fun j _ => (pow_mul z d j).symm
  rw [sum_filter]
  simp_rw [expand]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [sum_eq_single q]
  · rw [show (∑ b ∈ range q, if q ∣ b then z ^ b else 0) = 1 by
          simpa using multiples q 1 hq, mul_one]
  · intro d hd hne
    have hdpos := Nat.pos_of_mem_divisors hd
    have hfac := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
    have root := IsPrimitiveRoot.pow hq hz hfac
    have two : 1 < q / d := by
      by_contra! h
      interval_cases k : q / d <;> simp_all
    have hs := multiples d (q / d) hdpos
    rw [← hfac, root.geom_sum_eq_zero two] at hs
    rw [hs, mul_zero]
  · simp [hq.ne']

theorem PEqualNP.Outside.L_goldbach_cert_106 :
    ∀ a:ℕ, Nat.Coprime a 106 → (∑ b ∈ (Finset.range 106).filter (fun b => Nat.Coprime b 106), Complex.exp (((2*Real.pi*(a:ℝ)*b/106:ℝ):ℂ)*Complex.I))/(52:ℂ)=(1:ℂ)/52 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 106)
  have hz : IsPrimitiveRoot (Complex.exp θ) 106 := by
    simpa [θ] using Complex.isPrimitiveRoot_exp_of_coprime a 106 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 106 : ℝ) : ℂ) * Complex.I) =
        Complex.exp θ ^ b := by
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring
  have hm : μ 106 = 1 := by
    rw [show 106 = 2 * (53) by decide,
      isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime (2) (53)),
      moebius_apply_prime (by decide : Nat.Prime 2),
      moebius_apply_prime (by decide : Nat.Prime 53)]
    norm_num
  simp_rw [phase]
  rw [sumPrimitivePowers (by decide) hz, hm]
  norm_num
