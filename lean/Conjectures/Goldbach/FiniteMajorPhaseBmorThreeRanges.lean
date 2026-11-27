import Mathlib

/-!
# PREPUB goldbach gap: `L-goldbach-finite-major-phase-bmor-three-ranges`

Conditional: from the BMOR small-modulus von Mangoldt estimate in arithmetic
progressions (`hbmor`), derive the Abel-summed exponential bound used in the finite
major-arc phase analysis.  The Abel sum is split into three ranges
(`k < 8·10^9`, `8·10^9 ≤ k < 6·10^14`, `k ≥ 6·10^14`) with logarithm bounds
`30`, `22`, `34`; the endpoint uses `log n ≥ 42` (from `n ≥ 4·10^18`).
-/

open scoped BigOperators
open Finset

namespace GoldbachBmorThreeRanges

/-- The exponential `E(x) = exp(2π i x)`. -/
noncomputable abbrev E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The weighted AP sum `ap q a m = Σ_{k≤m, k≡a mod q} Λ(k)`. -/
noncomputable def ap (q a m : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k

/-- The AP error `Bfun q a m = ap q a m − m/φ(q)`. -/
noncomputable def Bfun (q a m : ℕ) : ℝ := ap q a m - (m : ℝ) / (Nat.totient q : ℝ)

/-! ## §1 The exponential: product rule, unit modulus, difference bound -/

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_norm (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  rw [show ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I
      = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) by ring]
  exact Complex.norm_exp_I_mul_ofReal _

lemma E_step (k : ℕ) (β : ℝ) : E (((k + 1 : ℕ) : ℝ) * β) = E ((k : ℝ) * β) * E β := by
  rw [show (((k + 1 : ℕ) : ℝ) * β) = (k : ℝ) * β + β by push_cast; ring, E_add]

/-- `‖E(β) − 1‖ ≤ 2π|β|`. -/
lemma E_sub_one_le (β : ℝ) : ‖E β - 1‖ ≤ 2 * Real.pi * |β| := by
  have harg : E β = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    unfold E
    congr 1
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hsin : Real.sin ((2 * Real.pi * β) / 2) = Real.sin (Real.pi * β) := by
    congr 1
    ring
  rw [hsin, Real.norm_eq_abs, abs_mul, abs_two]
  have hle : |Real.sin (Real.pi * β)| ≤ |Real.pi * β| := Real.abs_sin_le_abs
  have hpi : |Real.pi * β| = Real.pi * |β| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos, hle, hpi, abs_nonneg β]

/-- **Summation by parts (Abel)** for the range sum, differencing the second factor. -/
lemma abel_range (b z : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), b k * z k)
      = (∑ k ∈ Finset.range (n + 1), b k) * z n
        - ∑ k ∈ Finset.range n,
            ((∑ j ∈ Finset.range (k + 1), b j) * (z (k + 1) - z k)) := by
  simpa only [smul_eq_mul, Nat.add_sub_cancel] using
    (Finset.sum_range_by_parts' (f := b) (g := z) (n := n + 1))

/-- Numerical exponential/log bounds for the three-range split. -/
theorem log_bounds :
    (22 : ℝ) ≤ Real.log 8000000000 ∧ Real.log 8000000000 ≤ (30 : ℝ) ∧
    (34 : ℝ) ≤ Real.log 600000000000000 ∧
    (42 : ℝ) ≤ Real.log 4000000000000000000 := by
  have hexp1lt : Real.exp 1 < (2.72 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hexp1gt : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h22 : (22 : ℝ) ≤ Real.log 8000000000 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp (22 : ℝ) = (Real.exp 1) ^ 22 := by
          rw [show (22:ℝ) = (22:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
      _ ≤ (2.72 : ℝ) ^ 22 :=
          le_of_lt (pow_lt_pow_left₀ hexp1lt (Real.exp_pos 1).le (by norm_num))
      _ ≤ 8000000000 := by norm_num
  have h30 : Real.log 8000000000 ≤ (30 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (8000000000 : ℝ) ≤ (2.7 : ℝ) ^ 30 := by norm_num
      _ ≤ (Real.exp 1) ^ 30 :=
          le_of_lt (pow_lt_pow_left₀ hexp1gt (by norm_num) (by norm_num))
      _ = Real.exp (30 : ℝ) := by
          rw [show (30:ℝ) = (30:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
  have h34 : (34 : ℝ) ≤ Real.log 600000000000000 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp (34 : ℝ) = (Real.exp 1) ^ 34 := by
          rw [show (34:ℝ) = (34:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
      _ ≤ (2.72 : ℝ) ^ 34 :=
          le_of_lt (pow_lt_pow_left₀ hexp1lt (Real.exp_pos 1).le (by norm_num))
      _ ≤ 600000000000000 := by norm_num
  have h42 : (42 : ℝ) ≤ Real.log 4000000000000000000 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp (42 : ℝ) = (Real.exp 1) ^ 42 := by
          rw [show (42:ℝ) = (42:ℕ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
      _ ≤ (2.72 : ℝ) ^ 42 :=
          le_of_lt (pow_lt_pow_left₀ hexp1lt (Real.exp_pos 1).le (by norm_num))
      _ ≤ 4000000000000000000 := by norm_num
  exact ⟨h22, h30, h34, h42⟩

end GoldbachBmorThreeRanges


set_option maxHeartbeats 4000000 in
theorem Conjectures.Goldbach.FiniteMajorPhaseBmorThreeRanges :
    (∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ m → |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (m:ℝ)/Nat.totient q| ≤ (m:ℝ)/(840*Real.log (m:ℝ))) → let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q a n : ℕ) (β : ℝ), 3≤q → q≤105 → a<q → Nat.Coprime a q → 4000000000000000000≤n → |β|≤105/(n:ℝ) → ‖∑ k ∈ Finset.Icc 1 n, (((if k %q=a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤ (n:ℝ)*(1/(10^9:ℝ)+1/(840*42)) + Real.pi * |β| * (n:ℝ)^2/(840*34) := by
  intro hbmor
  dsimp only
  intro q a n β hq3 hq105 ha hcop hn hβ
  have hq_pos : 0 < q := by omega
  have hphi_pos_nat : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
  have ha_mod : a % q = a := Nat.mod_eq_of_lt ha
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0] at hcop
      have := (Nat.coprime_zero_left q).mp hcop
      omega
    · exact hpos
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast hphi_pos_nat
  have hphi_ge1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast hphi_pos_nat
  have hnR : (4000000000000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn2 : (16000000000000000000000000000000000000 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [hnR, sq_nonneg ((n : ℝ) - 4000000000000000000)]
  -- abbreviations
  set z : ℕ → ℂ := fun k => Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I) with hz
  set b : ℕ → ℂ := (fun k =>
    (((if k = 0 then (0 : ℝ)
      else ((if k % q = a then ArithmeticFunction.vonMangoldt k else 0)
        - 1 / (Nat.totient q : ℝ)) : ℝ) : ℂ))) with hb
  have hzE : ∀ k, z k = GoldbachBmorThreeRanges.E ((k : ℝ) * β) := fun k => rfl
  have hznorm1 : ∀ k, ‖z k‖ = 1 := fun k => by rw [hzE]; exact GoldbachBmorThreeRanges.E_norm _
  have hzstep : ∀ k, z (k + 1) - z k = z k * (GoldbachBmorThreeRanges.E β - 1) := by
    intro k
    have h1 : z (k + 1) = z k * GoldbachBmorThreeRanges.E β := by
      rw [hzE, hzE]
      have harg : (((k + 1 : ℕ) : ℝ) * β) = (k : ℝ) * β + β := by push_cast; ring
      rw [harg, GoldbachBmorThreeRanges.E_add]
    rw [h1]; ring
  have hznorm_le : ∀ k, ‖z (k + 1) - z k‖ ≤ 2 * Real.pi * |β| := by
    intro k
    rw [hzstep k, norm_mul, hznorm1 k, one_mul]
    exact GoldbachBmorThreeRanges.E_sub_one_le β
  -- the sums of `b` over initial segments are the AP errors
  have hpartial : ∀ k, (∑ j ∈ Finset.range (k + 1), b j) =
      ((GoldbachBmorThreeRanges.Bfun q a k : ℝ) : ℂ) := by
    intro k
    rw [hb, ← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_range_succ']
    have hR0 : ((if (0 : ℕ) = 0 then (0 : ℝ)
        else ((if (0 : ℕ) % q = a then ArithmeticFunction.vonMangoldt 0 else 0)
          - 1 / (Nat.totient q : ℝ))) : ℝ) = 0 := by simp
    rw [hR0, add_zero]
    have hstep : (∑ j ∈ Finset.range k,
          (if j + 1 = 0 then (0 : ℝ)
            else ((if (j + 1) % q = a then ArithmeticFunction.vonMangoldt (j + 1) else 0)
              - 1 / (Nat.totient q : ℝ))))
        = ∑ j ∈ Finset.range k,
          (((if (j + 1) % q = a then ArithmeticFunction.vonMangoldt (j + 1) else 0)
              - 1 / (Nat.totient q : ℝ))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [if_neg (by omega)]
    rw [hstep, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [GoldbachBmorThreeRanges.Bfun, GoldbachBmorThreeRanges.ap, Finset.sum_filter]
    have hfg : (∑ j ∈ Finset.range k,
          (if (j + 1) % q = a then ArithmeticFunction.vonMangoldt (j + 1) else 0))
        = ∑ m ∈ Finset.range (k + 1),
          (if m % q = a % q then ArithmeticFunction.vonMangoldt m else 0) := by
      rw [Finset.sum_range_succ']
      have h0 : (if (0 : ℕ) % q = a % q then ArithmeticFunction.vonMangoldt 0 else 0) = 0 := by
        rw [Nat.zero_mod]
        have hne : (0 : ℕ) ≠ a % q := by omega
        simp [hne]
      rw [h0, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [ha_mod]
    rw [hfg, Finset.card_range]
    ring
  -- crude bound below 8e9
  have hΛ30 : ∀ m, m < 8000000000 → ArithmeticFunction.vonMangoldt m ≤ 30 := by
    intro m hm
    have h1 : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have h2 : Real.log (m : ℝ) ≤ Real.log 8000000000 := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (by positivity) (by exact_mod_cast (by omega : m ≤ 8000000000))
    have h3 : Real.log 8000000000 ≤ 30 := GoldbachBmorThreeRanges.log_bounds.2.1
    linarith
  have hcrude : ∀ k < 8000000000,
      ‖(∑ j ∈ Finset.range (k + 1), b j)‖ ≤ 32 * ((k : ℝ) + 1) := by
    intro k hk
    rw [hpartial, Complex.norm_real, Real.norm_eq_abs]
    rw [GoldbachBmorThreeRanges.Bfun, GoldbachBmorThreeRanges.ap]
    have hkR : (k : ℝ) + 1 ≤ (8000000000 : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ 8000000000)
    have hsumΛ : (∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
        ArithmeticFunction.vonMangoldt m) ≤ 30 * ((k : ℝ) + 1) := by
      calc (∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
              ArithmeticFunction.vonMangoldt m)
          ≤ ∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q), (30 : ℝ) :=
            Finset.sum_le_sum (fun m hm => by
              rw [Finset.mem_filter, Finset.mem_range] at hm
              exact hΛ30 m (by omega))
        _ = (((Finset.range (k + 1)).filter (fun m => m % q = a % q)).card : ℝ) * 30 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 30 * ((k : ℝ) + 1) := by
            have hc : (((Finset.range (k + 1)).filter (fun m => m % q = a % q)).card : ℝ)
                ≤ (k : ℝ) + 1 := by
              have := Finset.card_filter_le (Finset.range (k + 1)) (fun m => m % q = a % q)
              rw [Finset.card_range] at this
              exact_mod_cast this
            calc (((Finset.range (k + 1)).filter (fun m => m % q = a % q)).card : ℝ) * 30
                ≤ ((k : ℝ) + 1) * 30 := mul_le_mul_of_nonneg_right hc (by norm_num)
              _ = 30 * ((k : ℝ) + 1) := by ring
    have hkφ : (k : ℝ) / (Nat.totient q : ℝ) ≤ (k : ℝ) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have h1 : (k : ℝ) / (Nat.totient q : ℝ) ≤ (k : ℝ) / 1 :=
        div_le_div_of_nonneg_left hk0 (by norm_num) hphi_ge1
      simpa using h1
    have hsumΛ0 : (0 : ℝ) ≤ ∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
        ArithmeticFunction.vonMangoldt m :=
      Finset.sum_nonneg (fun m _ => ArithmeticFunction.vonMangoldt_nonneg)
    calc |(∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
            ArithmeticFunction.vonMangoldt m) - (k : ℝ) / (Nat.totient q : ℝ)|
        ≤ |(∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
            ArithmeticFunction.vonMangoldt m)| + |(k : ℝ) / (Nat.totient q : ℝ)| :=
          by
            simpa using abs_sub_le (∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
              ArithmeticFunction.vonMangoldt m) 0 ((k : ℝ) / (Nat.totient q : ℝ))
      _ = (∑ m ∈ (Finset.range (k + 1)).filter (fun m => m % q = a % q),
            ArithmeticFunction.vonMangoldt m) + (k : ℝ) / (Nat.totient q : ℝ) := by
          rw [abs_of_nonneg hsumΛ0,
            abs_of_nonneg (div_nonneg (by positivity) (le_of_lt hphi_pos))]
      _ ≤ 30 * ((k : ℝ) + 1) + (k : ℝ) := by linarith
      _ ≤ 32 * ((k : ℝ) + 1) := by
          nlinarith
  -- hbmor bounds
  have hBMmid : ∀ k, 8000000000 ≤ k → k < 600000000000000 →
      ‖(∑ j ∈ Finset.range (k + 1), b j)‖ ≤ (k : ℝ) / 18480 := by
    intro k hk1 hk2
    rw [hpartial, Complex.norm_real, Real.norm_eq_abs]
    have hb0 := hbmor q a k hq3 hq105 ha hcop hk1
    have hlog22 : (22 : ℝ) ≤ Real.log (k : ℝ) := by
      have h1 : (22 : ℝ) ≤ Real.log 8000000000 := GoldbachBmorThreeRanges.log_bounds.1
      have h2 : Real.log 8000000000 ≤ Real.log (k : ℝ) := by
        apply Real.log_le_log (by norm_num); exact_mod_cast hk1
      linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    calc |GoldbachBmorThreeRanges.Bfun q a k|
        ≤ (k : ℝ) / (840 * Real.log (k : ℝ)) := hb0
      _ ≤ (k : ℝ) / 18480 := by
          apply div_le_div_of_nonneg_left hk0 (by norm_num)
          nlinarith
  have hBMlate : ∀ k, 600000000000000 ≤ k →
      ‖(∑ j ∈ Finset.range (k + 1), b j)‖ ≤ (k : ℝ) / 28560 := by
    intro k hk1
    rw [hpartial, Complex.norm_real, Real.norm_eq_abs]
    have hb0 := hbmor q a k hq3 hq105 ha hcop
      (le_trans (by norm_num : (8000000000 : ℕ) ≤ 600000000000000) hk1)
    have hlog34 : (34 : ℝ) ≤ Real.log (k : ℝ) := by
      have h1 : (34 : ℝ) ≤ Real.log 600000000000000 := GoldbachBmorThreeRanges.log_bounds.2.2.1
      have h2 : Real.log 600000000000000 ≤ Real.log (k : ℝ) := by
        apply Real.log_le_log (by norm_num); exact_mod_cast hk1
      linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    calc |GoldbachBmorThreeRanges.Bfun q a k|
        ≤ (k : ℝ) / (840 * Real.log (k : ℝ)) := hb0
      _ ≤ (k : ℝ) / 28560 := by
          apply div_le_div_of_nonneg_left hk0 (by norm_num)
          nlinarith
  have hBMend : ‖(∑ j ∈ Finset.range (n + 1), b j)‖ ≤ (n : ℝ) / (840 * 42) := by
    rw [hpartial, Complex.norm_real, Real.norm_eq_abs]
    have hn8 : 8000000000 ≤ n := le_trans (by norm_num : (8000000000 : ℕ) ≤ 4000000000000000000) hn
    have hb0 := hbmor q a n hq3 hq105 ha hcop hn8
    have hlog42 : (42 : ℝ) ≤ Real.log (n : ℝ) := by
      have h1 : (42 : ℝ) ≤ Real.log 4000000000000000000 := GoldbachBmorThreeRanges.log_bounds.2.2.2
      have h2 : Real.log 4000000000000000000 ≤ Real.log (n : ℝ) := by
        apply Real.log_le_log (by norm_num); exact_mod_cast hn
      linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    calc |GoldbachBmorThreeRanges.Bfun q a n|
        ≤ (n : ℝ) / (840 * Real.log (n : ℝ)) := hb0
      _ ≤ (n : ℝ) / (840 * 42) := by
          apply div_le_div_of_nonneg_left hn0 (by norm_num)
          nlinarith
  -- summation by parts
  have habel := GoldbachBmorThreeRanges.abel_range b z n
  have hSrep : (∑ k ∈ Finset.Icc 1 n,
        (((if k % q = a then ArithmeticFunction.vonMangoldt k else 0)
          - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * z k)
      = ∑ k ∈ Finset.range (n + 1), b k * z k := by
    have hIcc : Finset.Icc 1 n = (Finset.range (n + 1)).filter (fun k => 1 ≤ k) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
    rw [hIcc, Finset.sum_filter, hb]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    · have hk1 : 1 ≤ k := by omega
      simp [hk1, hk0]
  -- Abel sum bound, split in three ranges
  have hpart_nonneg : ∀ k, (0 : ℝ) ≤ ‖(∑ j ∈ Finset.range (k + 1), b j)‖ :=
    fun k => norm_nonneg _
  have hβnn : (0 : ℝ) ≤ 2 * Real.pi * |β| := by positivity
  have hsum3 : (∑ k ∈ Finset.range n,
        ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
      ≤ 32 * ((8000000000 : ℝ)) ^ 2 + ((600000000000000 : ℝ)) ^ 2 / 18480
        + (n : ℝ) ^ 2 / 57120 := by
    have hsplit1 := Finset.sum_filter_add_sum_filter_not (s := Finset.range n)
      (p := fun k => k < 8000000000) (f := fun k => ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.range n).filter (fun k => ¬ k < 8000000000))
      (p := fun k => k < 600000000000000)
      (f := fun k => ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
    have hS1 : (∑ k ∈ (Finset.range n).filter (fun k => k < 8000000000),
        ‖(∑ j ∈ Finset.range (k + 1), b j)‖) ≤ 32 * ((8000000000 : ℝ)) ^ 2 := by
      have h1 : (∑ k ∈ (Finset.range n).filter (fun k => k < 8000000000),
          ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
          ≤ ∑ k ∈ (Finset.range n).filter (fun k => k < 8000000000),
              (32 * ((8000000000 : ℝ))) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_filter] at hk
        have hc := hcrude k hk.2
        have hk1 : (k : ℝ) + 1 ≤ (8000000000 : ℝ) := by
          exact_mod_cast (by omega : k + 1 ≤ 8000000000)
        nlinarith
      have h2 : (∑ k ∈ (Finset.range n).filter (fun k => k < 8000000000),
            (32 * ((8000000000 : ℝ))))
          = (((Finset.range n).filter (fun k => k < 8000000000)).card : ℝ)
              * (32 * ((8000000000 : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hc : (((Finset.range n).filter (fun k => k < 8000000000)).card : ℝ)
          ≤ (8000000000 : ℝ) := by
        have hle : ((Finset.range n).filter (fun k => k < 8000000000)).card ≤ 8000000000 := by
          have hsub : (Finset.range n).filter (fun k => k < 8000000000)
              ⊆ Finset.range 8000000000 := by
            intro k hk
            rw [Finset.mem_filter, Finset.mem_range] at hk
            exact Finset.mem_range.mpr hk.2
          calc ((Finset.range n).filter (fun k => k < 8000000000)).card
              ≤ (Finset.range 8000000000).card := Finset.card_le_card hsub
            _ = 8000000000 := Finset.card_range _
        exact_mod_cast hle
      rw [h2] at h1
      nlinarith
    have hS2 : (∑ k ∈ (Finset.range n).filter
          (fun k => ¬ k < 8000000000 ∧ k < 600000000000000),
        ‖(∑ j ∈ Finset.range (k + 1), b j)‖) ≤ ((600000000000000 : ℝ)) ^ 2 / 18480 := by
      have h1 : (∑ k ∈ (Finset.range n).filter
            (fun k => ¬ k < 8000000000 ∧ k < 600000000000000),
          ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
          ≤ ∑ k ∈ (Finset.range n).filter
              (fun k => ¬ k < 8000000000 ∧ k < 600000000000000),
              ((600000000000000 : ℝ) / 18480) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkbot : 8000000000 ≤ k := by omega
        have hktop : k < 600000000000000 := hk.2.2
        have hc := hBMmid k hkbot hktop
        have hkR : (k : ℝ) ≤ (600000000000000 : ℝ) := by
          exact_mod_cast (by omega : k ≤ 600000000000000)
        nlinarith
      have h2 : (∑ k ∈ (Finset.range n).filter
            (fun k => ¬ k < 8000000000 ∧ k < 600000000000000),
            ((600000000000000 : ℝ) / 18480))
          = (((Finset.range n).filter
              (fun k => ¬ k < 8000000000 ∧ k < 600000000000000)).card : ℝ)
              * ((600000000000000 : ℝ) / 18480) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hc : (((Finset.range n).filter
          (fun k => ¬ k < 8000000000 ∧ k < 600000000000000)).card : ℝ)
          ≤ (600000000000000 : ℝ) := by
        have hle : ((Finset.range n).filter
            (fun k => ¬ k < 8000000000 ∧ k < 600000000000000)).card ≤ 600000000000000 := by
          have hsub : (Finset.range n).filter
              (fun k => ¬ k < 8000000000 ∧ k < 600000000000000)
              ⊆ Finset.range 600000000000000 := by
            intro k hk
            rw [Finset.mem_filter, Finset.mem_range] at hk
            exact Finset.mem_range.mpr hk.2.2
          calc ((Finset.range n).filter
              (fun k => ¬ k < 8000000000 ∧ k < 600000000000000)).card
              ≤ (Finset.range 600000000000000).card := Finset.card_le_card hsub
            _ = 600000000000000 := Finset.card_range _
        exact_mod_cast hle
      rw [h2] at h1
      nlinarith
    have hS3 : (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
        ‖(∑ j ∈ Finset.range (k + 1), b j)‖) ≤ (n : ℝ) ^ 2 / 57120 := by
      have h1 : (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
          ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
          ≤ ∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
              ((k : ℝ) / 28560) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkbot : 600000000000000 ≤ k := by omega
        exact hBMlate k hkbot
      have h2 : (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
            ((k : ℝ) / 28560))
          ≤ (∑ k ∈ Finset.range n, (k : ℝ)) / 28560 := by
        calc (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
              ((k : ℝ) / 28560))
            = (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
                (k : ℝ)) / 28560 := by rw [Finset.sum_div]
          _ ≤ (∑ k ∈ Finset.range n, (k : ℝ)) / 28560 := by
              apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 28560)
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (by
                  intro k hk
                  exact (Finset.mem_filter.mp hk).1)
                (by intro k _ _; exact_mod_cast Nat.zero_le k)
      have h3 : (∑ k ∈ Finset.range n, (k : ℝ)) ≤ (n : ℝ) ^ 2 / 2 := by
        have hnat := Finset.sum_range_id n
        have hcast : ((∑ k ∈ Finset.range n, k : ℕ) : ℝ) = ∑ k ∈ Finset.range n, (k : ℝ) :=
          Nat.cast_sum _ _
        rw [← hcast, hnat]
        have hdiv : ((n * (n - 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
          have h1 : ((n * (n - 1) / 2 : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) / 2 :=
            Nat.cast_div_le
          have hcastn : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
          linarith
        have hle2 : (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (n : ℝ) ^ 2 / 2 := by
          nlinarith [hn_pos]
        linarith
      calc (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
              ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
          ≤ ∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
              ((k : ℝ) / 28560) := h1
        _ ≤ (∑ k ∈ Finset.range n, (k : ℝ)) / 28560 := h2
        _ ≤ ((n : ℝ) ^ 2 / 2) / 28560 := by
            apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 28560)
            exact h3
        _ = (n : ℝ) ^ 2 / 57120 := by ring
    -- combine the two splits
    have hsecond : (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 8000000000),
          ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
        = (∑ k ∈ (Finset.range n).filter
              (fun k => ¬ k < 8000000000 ∧ k < 600000000000000),
            ‖(∑ j ∈ Finset.range (k + 1), b j)‖)
          + (∑ k ∈ (Finset.range n).filter (fun k => ¬ k < 600000000000000),
            ‖(∑ j ∈ Finset.range (k + 1), b j)‖) := by
      have e1 : ((Finset.range n).filter (fun k => ¬ k < 8000000000)).filter
            (fun k => k < 600000000000000)
          = (Finset.range n).filter (fun k => ¬ k < 8000000000 ∧ k < 600000000000000) := by
        rw [Finset.filter_filter]
      have e2 : ((Finset.range n).filter (fun k => ¬ k < 8000000000)).filter
            (fun k => ¬ k < 600000000000000)
          = (Finset.range n).filter (fun k => ¬ k < 600000000000000) := by
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro k _
        constructor
        · rintro ⟨-, h3⟩; exact h3
        · intro h3; exact ⟨by omega, h3⟩
      rw [← e1, ← e2]
      exact hsplit2.symm
    rw [← hsplit1, hsecond]
    linarith [hS1, hS2, hS3]
  -- the Abel remainder is bounded
  have hT_bound : ‖(∑ k ∈ Finset.range n,
        ((∑ j ∈ Finset.range (k + 1), b j) * (z (k + 1) - z k)))‖
      ≤ 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
          + ((600000000000000 : ℝ)) ^ 2 / 18480 + (n : ℝ) ^ 2 / 57120) := by
    calc ‖(∑ k ∈ Finset.range n,
            ((∑ j ∈ Finset.range (k + 1), b j) * (z (k + 1) - z k)))‖
        ≤ ∑ k ∈ Finset.range n,
            ‖((∑ j ∈ Finset.range (k + 1), b j) * (z (k + 1) - z k))‖ :=
          norm_sum_le _ _
      _ = ∑ k ∈ Finset.range n,
            ‖(∑ j ∈ Finset.range (k + 1), b j)‖ * ‖z (k + 1) - z k‖ := by
          apply Finset.sum_congr rfl
          intro k _; exact norm_mul _ _
      _ ≤ ∑ k ∈ Finset.range n,
            ‖(∑ j ∈ Finset.range (k + 1), b j)‖ * (2 * Real.pi * |β|) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hznorm_le k) (hpart_nonneg k)
      _ = (∑ k ∈ Finset.range n, ‖(∑ j ∈ Finset.range (k + 1), b j)‖) * (2 * Real.pi * |β|) := by
          rw [Finset.sum_mul]
      _ ≤ (32 * ((8000000000 : ℝ)) ^ 2 + ((600000000000000 : ℝ)) ^ 2 / 18480
            + (n : ℝ) ^ 2 / 57120) * (2 * Real.pi * |β|) := by
          exact mul_le_mul_of_nonneg_right hsum3 hβnn
      _ = 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
            + ((600000000000000 : ℝ)) ^ 2 / 18480 + (n : ℝ) ^ 2 / 57120) := by ring
  -- numerical domination of the early/middle ranges
  have hE1M : 32 * ((8000000000 : ℝ)) ^ 2 + ((600000000000000 : ℝ)) ^ 2 / 18480
      ≤ 19500000000000000000000000 := by norm_num
  have hnum1 : 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
        + ((600000000000000 : ℝ)) ^ 2 / 18480) ≤ (n : ℝ) / 10 ^ 9 := by
    have h1 : 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
          + ((600000000000000 : ℝ)) ^ 2 / 18480)
        ≤ 2 * Real.pi * (105 / (n : ℝ)) * 19500000000000000000000000 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hβ (by positivity)) hE1M
      · linarith
      · positivity
    have h2 : 2 * Real.pi * (105 / (n : ℝ)) * 19500000000000000000000000
        ≤ (n : ℝ) / 10 ^ 9 := by
      have hn0 : 0 < (n : ℝ) := hn_pos
      rw [show 2 * Real.pi * (105 / (n : ℝ)) * 19500000000000000000000000
          = (2 * Real.pi * 105 * 19500000000000000000000000) / (n : ℝ) by ring]
      rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 10 ^ 9)]
      -- 2π·105·1.95e25 ≤ n·(n/1e9)  i.e. multiply both sides by 1e9
      have hpi : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
      have hkey : 2 * Real.pi * 105 * 19500000000000000000000000 * 10 ^ 9
          ≤ (16000000000000000000000000000000000000 : ℝ) := by
        nlinarith [hpi]
      nlinarith [hn2, hkey]
    linarith
  have hnum2 : 2 * Real.pi * |β| * ((n : ℝ) ^ 2 / 57120)
      = Real.pi * |β| * (n : ℝ) ^ 2 / (840 * 34) := by
    rw [show (57120 : ℝ) = 2 * 28560 by norm_num]
    rw [show (840 : ℝ) * 34 = 28560 by norm_num]
    field_simp <;> ring
  -- final assembly
  have hmain : ‖(∑ k ∈ Finset.range (n + 1), b k * z k)‖
      ≤ (n : ℝ) / (840 * 42) + (n : ℝ) / 10 ^ 9
        + Real.pi * |β| * (n : ℝ) ^ 2 / (840 * 34) := by
    have h1 : ‖(∑ k ∈ Finset.range (n + 1), b k * z k)‖
        ≤ ‖(∑ j ∈ Finset.range (n + 1), b j) * z n‖
          + ‖(∑ k ∈ Finset.range n,
              ((∑ j ∈ Finset.range (k + 1), b j) * (z (k + 1) - z k)))‖ := by
      rw [habel]
      exact norm_sub_le _ _
    have h2 : ‖(∑ j ∈ Finset.range (n + 1), b j) * z n‖ ≤ (n : ℝ) / (840 * 42) := by
      rw [norm_mul, hznorm1 n, mul_one]
      exact hBMend
    have h3 : ‖(∑ k ∈ Finset.range n,
          ((∑ j ∈ Finset.range (k + 1), b j) * (z (k + 1) - z k)))‖
        ≤ 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
            + ((600000000000000 : ℝ)) ^ 2 / 18480)
          + 2 * Real.pi * |β| * ((n : ℝ) ^ 2 / 57120) := by
      calc _ ≤ 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
            + ((600000000000000 : ℝ)) ^ 2 / 18480 + (n : ℝ) ^ 2 / 57120) := hT_bound
        _ = 2 * Real.pi * |β| * (32 * ((8000000000 : ℝ)) ^ 2
            + ((600000000000000 : ℝ)) ^ 2 / 18480)
          + 2 * Real.pi * |β| * ((n : ℝ) ^ 2 / 57120) := by ring
    linarith [h1, h2, h3, hnum1, hnum2]
  calc ‖(∑ k ∈ Finset.Icc 1 n,
        (((if k % q = a then ArithmeticFunction.vonMangoldt k else 0)
          - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * z k)‖
      = ‖(∑ k ∈ Finset.range (n + 1), b k * z k)‖ := by rw [hSrep]
    _ ≤ (n : ℝ) * (1 / (10 ^ 9 : ℝ) + 1 / (840 * 42))
          + Real.pi * |β| * (n : ℝ) ^ 2 / (840 * 34) := by
        have h : (n : ℝ) * (1 / (10 ^ 9 : ℝ) + 1 / (840 * 42))
            = (n : ℝ) / 10 ^ 9 + (n : ℝ) / (840 * 42) := by ring
        rw [h]
        linarith [hmain]
