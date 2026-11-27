import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient

private lemma gc_fiber (q d : ℕ) (hd : d ∣ q) (hq : 0 < q) (ζ : ℂ) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.gcd b q = d), ζ ^ b =
      ∑ c ∈ (Finset.range (q / d)).filter (fun c => Nat.Coprime c (q / d)), (ζ ^ d) ^ c := by
  obtain ⟨m, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hdm : d * m / d = m := Nat.mul_div_cancel_left m hd0
  rw [hdm]
  symm
  refine Finset.sum_bij (fun c _ => d * c) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
    refine ⟨Nat.mul_lt_mul_of_pos_left hc.1 hd0, ?_⟩
    rw [Nat.gcd_mul_left, hc.2.gcd_eq_one, mul_one]
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hd0 h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    have hdb : d ∣ b := by
      rw [← hb.2]; exact Nat.gcd_dvd_left _ _
    obtain ⟨c, rfl⟩ := hdb
    refine ⟨c, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_of_mul_lt_mul_left hb.1, ?_⟩
    have := hb.2
    rw [Nat.gcd_mul_left] at this
    have h2 : d * Nat.gcd c m = d * 1 := by rw [this, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hd0 h2
  · intro c _
    rw [pow_mul]

private lemma gc_decomp (q : ℕ) (hq : 0 < q) (ζ : ℂ) :
    ∑ b ∈ Finset.range q, ζ ^ b =
      ∑ d ∈ q.divisors, ∑ c ∈ (Finset.range (q / d)).filter (fun c => Nat.Coprime c (q / d)),
        (ζ ^ d) ^ c := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun b => Nat.gcd b q) (t := q.divisors)]
  · refine Finset.sum_congr rfl ?_
    intro d hd
    exact gc_fiber q d (Nat.dvd_of_mem_divisors hd) hq ζ
  · intro b _
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_right _ _, hq.ne'⟩

private lemma gc_mu_sum (q : ℕ) (hq : 0 < q) :
    ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) =
      if q = 1 then 1 else 0 := by
  rw [Nat.sum_div_divisors q (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f q)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  have h2 : ((∑ d ∈ q.divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) =
      (((1 : ArithmeticFunction ℤ) q : ℤ) : ℂ) := by rw [h]
  push_cast at h2
  rw [h2, ArithmeticFunction.one_apply]
  split_ifs <;> simp

private lemma gc_main : ∀ q : ℕ, 0 < q → ∀ ζ : ℂ, IsPrimitiveRoot ζ q →
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ζ ^ b =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq ζ hζ
  have hdec := gc_decomp q hq ζ
  have hl : ∑ b ∈ Finset.range q, ζ ^ b = if q = 1 then 1 else 0 := by
    by_cases h1 : q = 1
    · subst h1; simp
    · rw [if_neg h1]
      exact hζ.geom_sum_eq_zero (by omega)
  have h1mem : 1 ∈ q.divisors := by simp [Nat.mem_divisors, hq.ne']
  rw [← Finset.add_sum_erase _ _ h1mem] at hdec
  have hrest : ∑ d ∈ q.divisors.erase 1,
      ∑ c ∈ (Finset.range (q / d)).filter (fun c => Nat.Coprime c (q / d)), (ζ ^ d) ^ c =
      ∑ d ∈ q.divisors.erase 1, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [Finset.mem_erase, Nat.mem_divisors] at hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.2.1 hq
    have hdq : d ∣ q := hd.2.1
    have hlt : q / d < q := Nat.div_lt_self hq (by
      rcases Nat.lt_or_ge 1 d with h | h
      · exact h
      · exact absurd (by omega) hd.1)
    have hpos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
    exact ih (q / d) hlt hpos _ (hζ.pow_of_dvd hd0.ne' hdq)
  have hmu := gc_mu_sum q hq
  rw [← Finset.add_sum_erase _ _ h1mem] at hmu
  rw [hrest] at hdec
  simp only [Nat.div_one, pow_one] at hdec hmu
  rw [hl] at hdec
  have := hdec.symm.trans hmu.symm
  have := add_right_cancel (this.symm.trans rfl |>.symm.trans rfl)
  simpa using this

theorem PEqualNP.Outside.L_goldbach_cert_166 :
    ∀ a:ℕ, Nat.Coprime a 166 → (∑ b ∈ (Finset.range 166).filter (fun b => Nat.Coprime b 166), Complex.exp (((2*Real.pi*(a:ℝ)*b/166:ℝ):ℂ)*Complex.I))/(82:ℂ)=(1:ℂ)/82 := by
  intro a ha
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) / (166 : ℕ)))) 166 := by
    have := Complex.isPrimitiveRoot_exp_of_coprime a 166 (by norm_num) ha
    exact this
  have hmain := gc_main 166 (by norm_num) _ hprim
  have hmu : ((ArithmeticFunction.moebius 166 : ℤ) : ℂ) = 1 := by
    have : ArithmeticFunction.moebius 166 = 1 := by
      rw [show (166 : ℕ) = 2 * 83 from by norm_num,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num : Nat.Coprime 2 83),
        ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
        ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 83)]
      norm_num
    rw [this]; simp
  rw [hmu] at hmain
  have hsum : ∑ b ∈ (Finset.range 166).filter (fun b => Nat.Coprime b 166),
      Complex.exp (((2*Real.pi*(a:ℝ)*b/166:ℝ):ℂ)*Complex.I) =
      ∑ b ∈ (Finset.range 166).filter (fun b => Nat.Coprime b 166),
        (Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) / (166 : ℕ)))) ^ b := by
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [← Complex.exp_nat_mul]
    apply congrArg
    push_cast
    ring
  rw [hsum, hmain]
