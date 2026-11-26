import rational
import vaughan

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction zeta Moebius

namespace PEqualNP.Outside.Vaughan

noncomputable section

/-- Type-I bound for the second Vaughan term.  After the divisor
reindexing, the inner sum over `l` is a log-weighted exponential sum with
frequency `d * t`, so the weighted Abel bound gives the reciprocal-sine
estimate below. -/
theorem norm_expSum_low_mu_mul_log_le (n U : ℕ) (t : ℝ)
    (hsin : ∀ d ∈ Finset.Icc 1 U,
      Real.sin (Real.pi * ((d : ℝ) * t)) ≠ 0) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      ∑ d ∈ Finset.Icc 1 U,
        2 * Real.log (n : ℝ) / |Real.sin (Real.pi * ((d : ℝ) * t))| := by
  rw [expSum_low_mu_mul_log_eq]
  refine (norm_type1_bilinear_log_le n U
    (fun d => (μ : ArithmeticFunction ℝ) d) t hsin).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  have hs : 0 < |Real.sin (Real.pi * ((d : ℝ) * t))| := abs_pos.mpr (hsin d hd)
  have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
    have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
      ArithmeticFunction.abs_moebius_le_one
    have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast h
    simpa using h'
  have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hpos)
        (by exact_mod_cast Nat.div_le_self n d)
  calc
    |(μ : ArithmeticFunction ℝ) d| *
        (2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))|)
        ≤ 1 * (2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))|) := by
      apply mul_le_mul_of_nonneg_right hμ
      exact div_nonneg
        (mul_nonneg (by norm_num) (Real.log_natCast_nonneg (n / d)))
        (abs_nonneg _)
    _ = 2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))| := one_mul _
    _ ≤ 2 * Real.log (n : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))| := by
      rw [div_le_div_iff_of_pos_right hs]
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- Conditional major-arc form: if all the frequencies `d * t` stay at
distance `1/q` from the integers (in the sine sense), then the second Vaughan
term is at most `2 U q log n`. -/
theorem norm_expSum_low_mu_mul_log_le_of_sine_separation (n U q : ℕ) (t : ℝ)
    (hq : 0 < q)
    (hsin : ∀ d ∈ Finset.Icc 1 U,
      (1:ℝ)/(q:ℝ) ≤ |Real.sin (Real.pi * ((d:ℝ) * t))|) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := hqR.ne'
  refine (norm_expSum_low_mu_mul_log_le n U t ?_).trans ?_
  · intro d hd
    have hpos : (0:ℝ) < |Real.sin (Real.pi * ((d:ℝ) * t))| :=
      lt_of_lt_of_le (one_div_pos.mpr hqR) (hsin d hd)
    exact abs_pos.mp hpos
  · have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
    calc
      ∑ d ∈ Finset.Icc 1 U, 2 * Real.log (n:ℝ) /
          |Real.sin (Real.pi * ((d:ℝ) * t))|
          ≤ ∑ _d ∈ Finset.Icc 1 U, 2 * Real.log (n:ℝ) / (1/(q:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hlog)
          (one_div_pos.mpr hqR) (hsin d hd)
      _ = 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        have hcard : U + 1 - 1 = U := by omega
        rw [hcard, nsmul_eq_mul]
        field_simp

/-- Unconditional major-arc Type-I bound: for `t = a/q + β` with
`gcd(a,q) = 1`, `U < q` and `|β| <= 1/(16 q U)`, the second Vaughan term is
bounded by `2 U q log n`. -/
theorem norm_expSum_low_mu_mul_log_le_majorArc (n q U a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUq : U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
        ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
  exact norm_expSum_low_mu_mul_log_le_of_sine_separation n U q
    ((a:ℝ)/(q:ℝ) + β) hq
    (abs_sin_pi_mul_majorArc_ge q U a β hq hcop hU1 hUq hβ)

/- Major-arc estimate for the third Vaughan term: when `q > U^2` and the
perturbation is below `1/(16 q U^2)`, every product `d * e` stays below `q`,
so the inner geometric sums contribute a factor `q` each. -/
set_option maxHeartbeats 1000000 in
theorem norm_expSum_low_mu_lowLambda_zeta_le_majorArc (n q U a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUq : U * U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
  rw [expSum_low_mu_lowLambda_zeta_eq n U ((a:ℝ)/(q:ℝ) + β)]
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := hqR.ne'
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hsine : ∀ k ∈ Finset.Icc 1 (U * U),
      (1:ℝ)/(q:ℝ) ≤ |Real.sin (Real.pi * ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| :=
    abs_sin_pi_mul_majorArc_ge q (U * U) a β hq hcop
      (Nat.mul_pos (by omega : 0 < U) (by omega : 0 < U)) hUq hβ
  calc
    ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
        ≤ ∑ d ∈ Finset.Icc 1 (min U n), ‖((μ : ArithmeticFunction ℝ) d : ℂ) *
            ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
      norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 (min U n), |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ d ∈ Finset.Icc 1 (min U n), |(μ : ArithmeticFunction ℝ) d| *
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            |(Λ : ArithmeticFunction ℝ) e| *
              ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := by
      apply Finset.sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
            ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
                ‖((Λ : ArithmeticFunction ℝ) e : ℂ) *
                  ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                    E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
          norm_sum_le _ _
        _ = ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              |(Λ : ArithmeticFunction ℝ) e| *
                ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := by
          apply Finset.sum_congr rfl
          intro e _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
      obtain ⟨he1, he2⟩ := Finset.mem_Icc.mp he
      have hdU : d ≤ U := by omega
      have heU : e ≤ U := by omega
      have hen : e ≤ n := by
        have h : e ≤ n / d := le_trans he2 (min_le_right _ _)
        have := Nat.div_le_self n d
        omega
      have hμd : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
        have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
          ArithmeticFunction.abs_moebius_le_one
        have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast h
        simpa using h'
      have hΛe : |(Λ : ArithmeticFunction ℝ) e| ≤ Real.log (n:ℝ) := by
        rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hepos : 0 < e := by omega
        exact (ArithmeticFunction.vonMangoldt_le_log).trans
          (Real.log_le_log (by exact_mod_cast hepos) (by exact_mod_cast hen))
      have hk_mem : d * e ∈ Finset.Icc 1 (U * U) :=
        Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) (by omega), Nat.mul_le_mul hdU heU⟩
      have hsin_ge := hsine (d * e) hk_mem
      have hsin_ne : Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
          ((a:ℝ)/(q:ℝ) + β))) ≠ 0 :=
        abs_pos.mp (lt_of_lt_of_le (one_div_pos.mpr hqR) hsin_ge)
      have hphase : (∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))) =
          ∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E ((m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))) := by
        apply Finset.sum_congr rfl
        intro m _
        have harg : ((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β) =
            (m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
          push_cast
          ring
        rw [harg]
      rw [hphase]
      have hinner : ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E ((m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))‖ ≤ 2 * (q:ℝ) := by
        refine (norm_geometric_sum_Icc_le_two (n / (d * e))
          (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) hsin_ne).trans ?_
        have hs' : (1:ℝ) ≤ |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
            ((a:ℝ)/(q:ℝ) + β)))| * (q:ℝ) := (div_le_iff₀ hqR).mp hsin_ge
        have hspos : 0 < |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
            ((a:ℝ)/(q:ℝ) + β)))| := lt_of_lt_of_le (one_div_pos.mpr hqR) hsin_ge
        have hunit : (1:ℝ) / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
            ((a:ℝ)/(q:ℝ) + β)))| ≤ (q:ℝ) := by
          rw [div_le_iff₀ hspos]
          simpa [mul_comm] using hs'
        calc
          (2:ℝ) / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β)))| =
              2 * (1 / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
                ((a:ℝ)/(q:ℝ) + β)))|) := by ring
          _ ≤ 2 * (q:ℝ) := mul_le_mul_of_nonneg_left hunit (by norm_num)
      calc
        |(μ : ArithmeticFunction ℝ) d| *
            (|(Λ : ArithmeticFunction ℝ) e| *
              ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E ((m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))‖)
            ≤ 1 * (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
          refine mul_le_mul hμd ?_ ?_ (by norm_num)
          · exact mul_le_mul hΛe hinner (norm_nonneg _) hlog
          · exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
        _ = Real.log (n:ℝ) * (2 * (q:ℝ)) := one_mul _
    _ ≤ ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 U,
          (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1, by
          have := (Finset.mem_Icc.mp he).2
          omega⟩
      · intro e _ _
        exact mul_nonneg hlog (by positivity)
    _ = ∑ d ∈ Finset.Icc 1 (min U n),
          (U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_const, Nat.card_Icc]
      have hcard : U + 1 - 1 = U := by omega
      rw [hcard, nsmul_eq_mul]
    _ = ((min U n : ℕ) : ℝ) * ((U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ)))) := by
      rw [Finset.sum_const, Nat.card_Icc]
      have hcard : min U n + 1 - 1 = min U n := by omega
      rw [hcard, nsmul_eq_mul]
    _ ≤ 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
      have hmin : ((min U n : ℕ) : ℝ) ≤ (U:ℝ) := by exact_mod_cast min_le_left U n
      have hC : 0 ≤ Real.log (n:ℝ) * (2 * (q:ℝ)) :=
        mul_nonneg hlog (by positivity)
      have hUC : 0 ≤ (U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ))) :=
        mul_nonneg (by positivity) hC
      calc
        ((min U n : ℕ) : ℝ) * ((U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ))))
            ≤ (U:ℝ) * ((U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ)))) :=
          mul_le_mul_of_nonneg_right hmin hUC
        _ = 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring

/- Milestone: on a major arc with `q > U^2`, the entire Type-I part of the
Vaughan decomposition is bounded by `6 U^2 q log n`.  Only the Type-II
bilinear term is left. -/
set_option maxHeartbeats 1000000 in
theorem norm_expSum_vaughan_typeI_le_majorArc (n q U a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U) (hUq : U * U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hU1R : (1:ℝ) ≤ (U:ℝ) := by exact_mod_cast hU1
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hcast : ((U * U : ℕ) : ℝ) = (U:ℝ) * (U:ℝ) := by push_cast; ring
  have hβ2 : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ)) := by
    have hUU : (U:ℝ) ≤ (U:ℝ) * (U:ℝ) := by nlinarith
    have hdenpos : (0:ℝ) < 16 * (q:ℝ) * (U:ℝ) := by positivity
    have hdenle : 16 * (q:ℝ) * (U:ℝ) ≤ 16 * (q:ℝ) * ((U:ℝ)*(U:ℝ)) := by
      nlinarith
    rw [hcast] at hβ
    exact hβ.trans (one_div_le_one_div_of_le hdenpos hdenle)
  have hUqU : U < q := by
    have hUle : U ≤ U * U := Nat.le_mul_of_pos_right U (by omega)
    exact lt_of_le_of_lt hUle hUq
  have hdecomp : expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
      expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) =
      expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) := by
    rw [expSum_vaughan n U]
    ring
  rw [hdecomp]
  have h1 := norm_expSum_low_vonMangoldt_le n U hn hUn ((a:ℝ)/(q:ℝ) + β)
  have h2 := norm_expSum_low_mu_mul_log_le_majorArc n q U a β hq hcop hU1 hUqU hβ2
  have h3 := norm_expSum_low_mu_lowLambda_zeta_le_majorArc n q U a β hq hcop hU1 hUq hβ
  calc
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
            expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
              ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ :=
      norm_sub_le _ _
    _ ≤ (‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
            ((a:ℝ)/(q:ℝ) + β)‖) +
        ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((U:ℝ) + 1) * Real.log (n:ℝ) + 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ)) +
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
      apply add_le_add
      · exact add_le_add h1 h2
      · exact h3
    _ ≤ 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
      have hQ1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
      have hUU : (U:ℝ) ≤ (U:ℝ) * (U:ℝ) := by nlinarith
      have hA1 : ((U:ℝ) + 1) * Real.log (n:ℝ) ≤
          2 * (U:ℝ) * Real.log (n:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        linarith
      have hA2 : 2 * (U:ℝ) * Real.log (n:ℝ) ≤
          2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) := by
        calc
          2 * (U:ℝ) * Real.log (n:ℝ) =
              2 * Real.log (n:ℝ) * (U:ℝ) := by ring
          _ ≤ 2 * Real.log (n:ℝ) * ((U:ℝ) * (U:ℝ)) :=
            mul_le_mul_of_nonneg_left hUU (by positivity)
          _ = 2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) := by ring
      have hA3 : 2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) ≤
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
        calc
          2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) =
              (2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ)) * 1 := by ring
          _ ≤ (2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ)) * (q:ℝ) :=
            mul_le_mul_of_nonneg_left hQ1 (by positivity)
          _ = 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring
      have hB : 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) ≤
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
        calc
          2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) =
              (2 * (q:ℝ) * Real.log (n:ℝ)) * (U:ℝ) := by ring
          _ ≤ (2 * (q:ℝ) * Real.log (n:ℝ)) * ((U:ℝ) * (U:ℝ)) :=
            mul_le_mul_of_nonneg_left hUU (by positivity)
          _ = 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring
      calc
        ((U:ℝ) + 1) * Real.log (n:ℝ) + 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) +
            2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ)
            ≤ 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
                2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
              2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
          apply add_le_add
          · exact add_le_add (hA1.trans (hA2.trans hA3)) hB
          · exact le_rfl
        _ = 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring

/- Cauchy–Schwarz reduction of the Type-II term: the squared Type-II sum is
controlled by the energy of the inner `(e, m)` sums.  This is exactly the
quantity to which the large sieve is applied. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((Finset.Icc (U + 1) n).card : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) n,
          ‖∑ e ∈ Finset.Icc (U + 1) (n / d),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖ ^ 2 := by
  classical
  rw [expSum_high_mu_zeta_highLambda_eq n U t]
  let s : Finset ℕ := Finset.Icc (U + 1) n
  let B : ℕ → ℂ := fun d =>
    ∑ e ∈ Finset.Icc (U + 1) (n / d),
      ((Λ : ArithmeticFunction ℝ) e : ℂ) *
        ∑ m ∈ Finset.Icc 1 (n / (d * e)),
          E (((d * e * m : ℕ) : ℝ) * t)
  change ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
    (s.card : ℝ) * ∑ d ∈ s, ‖B d‖ ^ 2
  have h1 : ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ≤
      ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ := norm_sum_le _ _
  have h2 : (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 ≤
      (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℕ => (1:ℝ))
      (fun d => ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖)
    simpa using this
  have h3 : ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
      ∑ d ∈ s, ‖B d‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro d _
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have hμ2 : |(μ : ArithmeticFunction ℝ) d| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg ((μ : ArithmeticFunction ℝ) d), hμ]
    nlinarith [sq_nonneg ‖B d‖]
  have hnorm : 0 ≤ ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ :=
    norm_nonneg _
  calc
    ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2
        ≤ (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 :=
      pow_le_pow_left₀ hnorm h1 2
    _ ≤ (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := h2
    _ ≤ (s.card : ℝ) * ∑ d ∈ s, ‖B d‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

end

end PEqualNP.Outside.Vaughan
