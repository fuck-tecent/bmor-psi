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

/-- The inner `(e, m)` sum of the Type-II term at a fixed outer `d`. -/
noncomputable def typeIIInner (n U : ℕ) (t : ℝ) (d : ℕ) : ℂ :=
  ∑ e ∈ Finset.Icc (U + 1) (n / d), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
    ∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  dsimp only [E]
  simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

/-- Shifting all phases by a common unit does not change the sum's norm. -/
lemma norm_sum_shift {M : ℕ} (c : Fin M → ℂ) (θ shift : ℝ) :
    ‖∑ n : Fin M, c n * E ((n : ℝ) * θ + shift)‖ =
      ‖∑ n : Fin M, c n * E ((n : ℝ) * θ)‖ := by
  have h : (∑ n : Fin M, c n * E ((n : ℝ) * θ + shift))
      = (∑ n : Fin M, c n * E ((n : ℝ) * θ)) * E shift := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [E_add]
    ring
  rw [h, norm_mul, norm_E, mul_one]

/-- Split a multiple of `B` into `K` consecutive blocks of length `B`. -/
lemma sum_range_mul_eq_sum_blocks (f : ℕ → ℝ) (B K : ℕ) :
    ∑ i ∈ Finset.range (K * B), f i =
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range B, f (k * B + i) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Split a range into full blocks of length `B` plus a remainder. -/
lemma sum_range_eq_blocks_add_rem (f : ℕ → ℝ) (B M : ℕ) :
    ∑ i ∈ Finset.range M, f i =
      ∑ k ∈ Finset.range (M / B), ∑ i ∈ Finset.range B, f (k * B + i) +
        ∑ i ∈ Finset.range (M % B), f ((M / B) * B + i) := by
  conv_lhs => rw [← Nat.div_add_mod M B]
  rw [Finset.sum_range_add]
  have h1 : (∑ x ∈ Finset.range (B * (M / B)), f x) =
      ∑ k ∈ Finset.range (M / B), ∑ i ∈ Finset.range B, f (k * B + i) := by
    rw [Nat.mul_comm B (M / B), sum_range_mul_eq_sum_blocks]
  rw [h1]
  congr 1
  rw [Nat.mul_comm B (M / B)]

/-- Shift an `Icc` sum to a `range` sum. -/
lemma sum_Icc_eq_sum_range_shift {α : Type*} [AddCommMonoid α]
    (A M : ℕ) (f : ℕ → α) (hAM : A ≤ M) :
    ∑ d ∈ Finset.Icc A M, f d = ∑ x ∈ Finset.range (M + 1 - A), f (A + x) := by
  have hIcc : Finset.Icc A M = Finset.Ico A (M + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]

/-- Short-block energy with an arbitrary offset `jB` in the inner variable. -/
lemma majorArc_block_energy_offset (q D B d0 jB : ℕ) (a : ℕ) (β : ℝ)
    (c : ℕ → ℂ) (hq : 0 < q) (hcop : Nat.Coprime a q) (hDq : D < q)
    (hβ : |β| ≤ 1 / (2 * (q:ℝ) * (D:ℝ))) :
    ∑ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1),
        (if n.val < B then c (jB + n.val) else 0) *
          E (((jB + n.val : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2
      ≤ (B + 1 + 2 * (q:ℝ)) *
          ∑ n : Fin (B + 1),
            ‖(if n.val < B then c (jB + n.val) else 0)‖ ^ 2 := by
  let c' : Fin (B + 1) → ℂ := fun n => if n.val < B then c (jB + n.val) else 0
  have h := majorArc_block_energy q D d0 B a β c' hq hcop hDq hβ
  have hshift : ∀ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1), c' n * E (((jB + n.val : ℕ) : ℝ) *
          (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖
      = ‖∑ n : Fin (B + 1), c' n * E ((n.val : ℝ) *
          (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ := by
    intro d
    have harg : ∀ n : Fin (B + 1),
        ((jB + n.val : ℕ) : ℝ) * (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) =
          (n.val : ℝ) * (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) +
            (jB : ℝ) * (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) := by
      intro n
      push_cast
      ring
    simp_rw [harg]
    exact norm_sum_shift c' _ _
  have hLHS : (∑ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1), c' n * E (((jB + n.val : ℕ) : ℝ) *
        (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2)
      = ∑ d : Fin (D + 1),
          ‖∑ n : Fin (B + 1), c' n * E ((n.val : ℝ) *
            (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro d _
    rw [hshift d]
  change (∑ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1), c' n * E (((jB + n.val : ℕ) : ℝ) *
        (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2) ≤
    (B + 1 + 2 * (q:ℝ)) * ∑ n : Fin (B + 1), ‖c' n‖ ^ 2
  rw [hLHS]
  exact h

/-- Coefficient of a dyadic `(e, m)` box after collapsing to `l = e * m`. -/
noncomputable def typeIIBoxCoeff (E0 M0 l : ℕ) : ℂ :=
  ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
      (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
    ((Λ : ArithmeticFunction ℝ) e : ℂ)

lemma box_e_m_reindex (d E0 M0 : ℕ) (hE0 : 0 < E0) (hM0 : 0 < M0) (t : ℝ) :
    (∑ e ∈ Finset.Icc E0 (2 * E0 - 1),
        ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E (((d * e * m : ℕ) : ℝ) * t)) =
      ∑ l ∈ Finset.Icc (E0 * M0) (4 * E0 * M0 - 1),
        (∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
            (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          ((Λ : ArithmeticFunction ℝ) e : ℂ)) *
          E (((d * l : ℕ) : ℝ) * t) := by
  classical
  have hL : (∑ e ∈ Finset.Icc E0 (2 * E0 - 1),
        ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E (((d * e * m : ℕ) : ℝ) * t)) =
      ∑ p ∈ (Finset.Icc E0 (2 * E0 - 1)).sigma
          (fun e => Finset.Icc M0 (2 * M0 - 1)),
        ((Λ : ArithmeticFunction ℝ) p.1 : ℂ) *
          E (((d * p.1 * p.2 : ℕ) : ℝ) * t) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_sigma'
      (s := Finset.Icc E0 (2 * E0 - 1))
      (t := fun e => Finset.Icc M0 (2 * M0 - 1))
      (f := fun e m => ((Λ : ArithmeticFunction ℝ) e : ℂ) *
        E (((d * e * m : ℕ) : ℝ) * t))
  have hR : (∑ l ∈ Finset.Icc (E0 * M0) (4 * E0 * M0 - 1),
        (∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
            (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          ((Λ : ArithmeticFunction ℝ) e : ℂ)) *
          E (((d * l : ℕ) : ℝ) * t)) =
      ∑ q ∈ (Finset.Icc (E0 * M0) (4 * E0 * M0 - 1)).sigma
          (fun l => (Finset.Icc E0 (2 * E0 - 1)).filter
            (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1)),
        ((Λ : ArithmeticFunction ℝ) q.2 : ℂ) *
          E (((d * q.1 : ℕ) : ℝ) * t) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_sigma'
      (s := Finset.Icc (E0 * M0) (4 * E0 * M0 - 1))
      (t := fun l => (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1))
      (f := fun l e => ((Λ : ArithmeticFunction ℝ) e : ℂ) *
        E (((d * l : ℕ) : ℝ) * t))
  rw [hL, hR]
  refine Finset.sum_bij
    (fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpe, hpm⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpe1, hpe2⟩ := Finset.mem_Icc.mp hpe
    obtain ⟨hpm1, hpm2⟩ := Finset.mem_Icc.mp hpm
    have hppos : 0 < p.1 := by omega
    have hlpos : 0 < p.1 * p.2 := Nat.mul_pos hppos (by omega)
    have hllow : E0 * M0 ≤ p.1 * p.2 := Nat.mul_le_mul hpe1 hpm1
    have hlhigh : p.1 * p.2 ≤ 4 * E0 * M0 - 1 := by
      have h1 : p.1 ≤ 2 * E0 - 1 := hpe2
      have h2 : p.2 ≤ 2 * M0 - 1 := hpm2
      have h3 : p.1 * p.2 ≤ (2 * E0 - 1) * (2 * M0 - 1) := Nat.mul_le_mul h1 h2
      have h4 : (2 * E0 - 1) * (2 * M0 - 1) ≤ 4 * E0 * M0 - 1 := by
        have hlt : (2 * E0 - 1) * (2 * M0 - 1) < 4 * E0 * M0 := by
          have hElt : 2 * E0 - 1 < 2 * E0 := by omega
          have hMpos : 0 < 2 * M0 - 1 := by omega
          calc
            (2 * E0 - 1) * (2 * M0 - 1) < (2 * E0) * (2 * M0 - 1) :=
              Nat.mul_lt_mul_of_pos_right hElt hMpos
            _ ≤ (2 * E0) * (2 * M0) := Nat.mul_le_mul_left _ (by omega)
            _ = 4 * E0 * M0 := by ring
        omega
      omega
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hllow, hlhigh⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨hpe, ?_, ?_, ?_⟩
    · exact dvd_mul_right p.1 p.2
    · rw [Nat.mul_div_right p.2 hppos]
      exact hpm1
    · rw [Nat.mul_div_right p.2 hppos]
      exact hpm2
  · intro p hp p' hp' heq
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨hprod, he⟩ := heq
    have he' : p.1 = p'.1 := eq_of_heq he
    have hp1pos : 0 < p.1 := by
      have := (Finset.mem_sigma.mp hp).1
      have := (Finset.mem_Icc.mp this).1
      omega
    have hm : p.2 = p'.2 := by
      apply Nat.mul_left_cancel hp1pos
      calc p.1 * p.2 = p'.1 * p'.2 := hprod
        _ = p.1 * p'.2 := by rw [he']
    exact Sigma.ext he' (heq_of_eq hm)
  · intro q hq
    obtain ⟨hql, hqe⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hql1, hql2⟩ := Finset.mem_Icc.mp hql
    obtain ⟨hqe1, hqe2⟩ := Finset.mem_filter.mp hqe
    obtain ⟨hqedvd, hqm1, hqm2⟩ := hqe2
    have hqepos : 0 < q.2 := by
      have := (Finset.mem_Icc.mp hqe1).1
      omega
    have hq1pos : 0 < q.1 := by
      have hE0M0 : 0 < E0 * M0 := Nat.mul_pos hE0 hM0
      omega
    have hmpos : 0 < q.1 / q.2 := Nat.div_pos (Nat.le_of_dvd hq1pos hqedvd) hqepos
    have hmmem : q.1 / q.2 ∈ Finset.Icc M0 (2 * M0 - 1) :=
      Finset.mem_Icc.mpr ⟨hqm1, hqm2⟩
    refine ⟨⟨q.2, q.1 / q.2⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨hqe1, hmmem⟩
    · show (⟨q.2 * (q.1 / q.2), q.2⟩ : Σ _ : ℕ, ℕ) = q
      rw [Nat.mul_div_cancel' hqedvd]
  · intro p hp
    obtain ⟨-, hpm⟩ := Finset.mem_sigma.mp hp
    show ((Λ : ArithmeticFunction ℝ) p.1 : ℂ) *
        E (((d * p.1 * p.2 : ℕ) : ℝ) * t) =
      ((Λ : ArithmeticFunction ℝ) p.1 : ℂ) *
        E (((d * (p.1 * p.2) : ℕ) : ℝ) * t)
    have h : d * p.1 * p.2 = d * (p.1 * p.2) := by ring
    rw [h]


lemma norm_typeIIBoxCoeff_le (n E0 M0 l : ℕ) (hl0 : 0 < l) (hl : l ≤ n) :
    ‖typeIIBoxCoeff E0 M0 l‖ ≤ Real.log (n : ℝ) := by
  classical
  have hnonneg : 0 ≤ ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
      (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
        (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_nonneg (fun e _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsub : (Finset.Icc E0 (2 * E0 - 1)).filter
      (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1) ⊆ l.divisors := by
    intro e he
    obtain ⟨-, hedvd, -⟩ := Finset.mem_filter.mp he
    exact Nat.mem_divisors.mpr ⟨hedvd, Nat.ne_of_gt hl0⟩
  have hle : ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          (Λ : ArithmeticFunction ℝ) e ≤
      ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hfull : ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e = Real.log (l : ℝ) :=
    ArithmeticFunction.vonMangoldt_sum
  have hlog : Real.log (l : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hl0) (by exact_mod_cast hl)
  have hnorm : ‖typeIIBoxCoeff E0 M0 l‖ =
      ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          (Λ : ArithmeticFunction ℝ) e := by
    unfold typeIIBoxCoeff
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  calc
    ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          (Λ : ArithmeticFunction ℝ) e
        ≤ ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e := hle
    _ = Real.log (l : ℝ) := hfull
    _ ≤ Real.log (n : ℝ) := hlog

lemma sum_normSq_typeIIBoxCoeff_interval_le (n E0 M0 s B : ℕ)
    (hs : 0 < s) (hBn : s + B - 1 ≤ n) :
    ∑ l ∈ Finset.Icc s (s + B - 1), ‖typeIIBoxCoeff E0 M0 l‖ ^ 2 ≤
      (B : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  calc
    ∑ l ∈ Finset.Icc s (s + B - 1), ‖typeIIBoxCoeff E0 M0 l‖ ^ 2
        ≤ ∑ _l ∈ Finset.Icc s (s + B - 1), (Real.log (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have hls : s ≤ l := (Finset.mem_Icc.mp hl).1
      have hln : l ≤ n := by
        have := (Finset.mem_Icc.mp hl).2
        omega
      have h := norm_typeIIBoxCoeff_le n E0 M0 l (by omega) hln
      nlinarith [norm_nonneg (typeIIBoxCoeff E0 M0 l), h]
    _ = ((Finset.Icc s (s + B - 1)).card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : (Finset.Icc s (s + B - 1)).card ≤ B := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast hcard

/-- Core fixed-interval block energy: coefficients bounded by `log n` on the
interval `[s, s+B-1]` give energy at most `(B+1+2q) * B * (log n)^2`. -/
lemma majorArc_coeff_interval_energy (n q D d0 s B : ℕ) (a : ℕ) (β : ℝ)
    (c : ℕ → ℂ) (hq : 0 < q) (hcop : Nat.Coprime a q) (hDq : D < q)
    (hβ : |β| ≤ 1 / (2 * (q:ℝ) * (D:ℝ)))
    (hcoeff : ∀ l, s ≤ l → l ≤ s + B - 1 → ‖c l‖ ≤ Real.log (n : ℝ)) :
    ∑ d : Fin (D + 1),
      ‖∑ j : Fin (B + 1), (if j.val < B then c (s + j.val) else 0) *
          E (((s + j.val : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2
      ≤ ((B : ℝ) + 1 + 2 * (q : ℝ)) *
          (((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
  have h := majorArc_block_energy_offset q D B d0 s a β c hq hcop hDq hβ
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcoeff_sum : (∑ j : Fin (B + 1),
      ‖(if j.val < B then c (s + j.val) else 0)‖ ^ 2) ≤
      (((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
    calc
      ∑ j : Fin (B + 1), ‖(if j.val < B then c (s + j.val) else 0)‖ ^ 2
          ≤ ∑ _n : Fin (B + 1), (Real.log (n : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j.val < B
        · rw [if_pos hj]
          have hsl : s ≤ s + j.val := by omega
          have hsu : s + j.val ≤ s + B - 1 := by omega
          have hc := hcoeff (s + j.val) hsl hsu
          nlinarith [norm_nonneg (c (s + j.val)), hc]
        · rw [if_neg hj]
          have := sq_nonneg (Real.log (n : ℝ))
          simpa using this
      _ = ((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  exact hcoeff_sum

/-- A dyadic box with `8 D E M ≤ n` is fully inside the Type-II region:
every `d < 2D`, `e < 2E`, `m < 2M` satisfies `d * e * m ≤ n`. -/
lemma box_product_le_of_dyadic (n D E M : ℕ) (h : 8 * D * E * M ≤ n) :
    ∀ d e m : ℕ, D ≤ d → d < 2 * D → E ≤ e → e < 2 * E →
      M ≤ m → m < 2 * M → d * e * m ≤ n := by
  intro d e m hd1 hd2 he1 he2 hm1 hm2
  have hd : d ≤ 2 * D := by omega
  have he : e ≤ 2 * E := by omega
  have hm : m ≤ 2 * M := by omega
  have hde : d * e ≤ (2 * D) * (2 * E) := Nat.mul_le_mul hd he
  have hdem : d * e * m ≤ ((2 * D) * (2 * E)) * (2 * M) :=
    Nat.mul_le_mul hde hm
  have hval : ((2 * D) * (2 * E)) * (2 * M) = 8 * D * E * M := by ring
  rw [hval] at hdem
  exact hdem.trans h

/-- Major-arc energy for a fixed dyadic `(e,m)` box. -/
theorem majorArc_box_energy (n q D d0 E0 M0 : ℕ) (a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hDq : D < q)
    (hβ : |β| ≤ 1 / (2 * (q:ℝ) * (D:ℝ)))
    (hE0 : 0 < E0) (hM0 : 0 < M0) (hboxn : 4 * E0 * M0 - 1 ≤ n) :
    ∑ d : Fin (D + 1),
      ‖∑ e ∈ Finset.Icc E0 (2 * E0 - 1), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E ((((d0 + d.val : ℕ) * e * m : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β))‖ ^ 2
      ≤ (((3 * E0 * M0 : ℕ) : ℝ) + 1 + 2 * (q : ℝ)) *
          ((((3 * E0 * M0 : ℕ) : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
  classical
  let s : ℕ := E0 * M0
  let B : ℕ := 3 * E0 * M0
  have hBpos : 0 < B := by
    dsimp only [B]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hE0) hM0
  have hsum_s : s + B - 1 = 4 * E0 * M0 - 1 := by
    dsimp only [s, B]
    have h4 : E0 * M0 + 3 * E0 * M0 = 4 * E0 * M0 := by ring
    rw [h4]
  have hterm : ∀ d : Fin (D + 1),
      ‖∑ e ∈ Finset.Icc E0 (2 * E0 - 1), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E ((((d0 + d.val : ℕ) * e * m : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β))‖
      = ‖∑ j : Fin (B + 1),
          (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
            E (((s + j.val : ℕ) : ℝ) *
              (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ := by
    intro d
    rw [box_e_m_reindex (d0 + d.val) E0 M0 hE0 hM0 ((a:ℝ)/(q:ℝ) + β)]
    let f : ℕ → ℂ := fun l => typeIIBoxCoeff E0 M0 l *
      E ((((d0 + d.val : ℕ) * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))
    change ‖∑ l ∈ Finset.Icc (E0 * M0) (4 * E0 * M0 - 1), f l‖ =
      ‖∑ j : Fin (B + 1),
          (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
            E (((s + j.val : ℕ) : ℝ) *
              (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖
    rw [← hsum_s]
    rw [sum_Icc_eq_sum_range_shift s (s + B - 1) f (by omega)]
    have hfin : (∑ j : Fin (B + 1),
        (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
          E (((s + j.val : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β))))
        = ∑ x ∈ Finset.range B, typeIIBoxCoeff E0 M0 (s + x) *
          E ((((d0 + d.val : ℕ) * (s + x) : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
      rw [Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ => (if k < B then typeIIBoxCoeff E0 M0 (s + k) else 0) *
          E (((s + k : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β))))
        (n := B + 1)]
      rw [Finset.sum_range_succ]
      simp only [Nat.lt_irrefl, if_false, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      have hxB : x < B := Finset.mem_range.mp hx
      rw [if_pos hxB]
      congr 1
      push_cast
      ring
    rw [hfin]
    have hlen : s + B - 1 + 1 - s = B := by omega
    rw [hlen]
  calc
    ∑ d : Fin (D + 1),
        ‖∑ e ∈ Finset.Icc E0 (2 * E0 - 1), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E ((((d0 + d.val : ℕ) * e * m : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β))‖ ^ 2
        = ∑ d : Fin (D + 1),
            ‖∑ j : Fin (B + 1),
              (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
                E (((s + j.val : ℕ) : ℝ) *
                  (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hterm d]
    _ ≤ ((B : ℝ) + 1 + 2 * (q : ℝ)) *
          (((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
      apply majorArc_coeff_interval_energy n q D d0 s B a β
        (typeIIBoxCoeff E0 M0) hq hcop hDq hβ
      intro l hsl hlu
      have hl0 : 0 < l := by
        have : 0 < s := by
          dsimp only [s]
          exact Nat.mul_pos hE0 hM0
        omega
      have hln : l ≤ n := by
        have : l ≤ 4 * E0 * M0 - 1 := by
          calc l ≤ s + B - 1 := hlu
            _ = 4 * E0 * M0 - 1 := hsum_s
        omega
      exact norm_typeIIBoxCoeff_le n E0 M0 l hl0 hln
    _ = (((3 * E0 * M0 : ℕ) : ℝ) + 1 + 2 * (q : ℝ)) *
          ((((3 * E0 * M0 : ℕ) : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
      dsimp only [B]

/-- The truncated divisor convolution `c_U(l) = ∑_{e | l, e > U} Λ(e)`. -/
noncomputable def typeIICoeff (U l : ℕ) : ℂ :=
  ∑ e ∈ l.divisors.filter (fun e => U < e), ((Λ : ArithmeticFunction ℝ) e : ℂ)

/-- Collapsed Fourier form of the Type-II inner sum. -/
noncomputable def typeIIFourier (n U : ℕ) (t : ℝ) (d : ℕ) : ℂ :=
  ∑ l ∈ Finset.Icc 1 (n / d), typeIICoeff U l * E (((d * l : ℕ) : ℝ) * t)

lemma norm_typeIICoeff_le (n U l : ℕ) (hl : l ≤ n) :
    ‖typeIICoeff U l‖ ≤ Real.log (n : ℝ) := by
  classical
  have hnonneg : 0 ≤ ∑ e ∈ l.divisors.filter (fun e => U < e),
      (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_nonneg (fun e _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsub : l.divisors.filter (fun e => U < e) ⊆ l.divisors :=
    Finset.filter_subset _ _
  have hle : ∑ e ∈ l.divisors.filter (fun e => U < e),
        (Λ : ArithmeticFunction ℝ) e ≤
      ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hfull : ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e = Real.log (l : ℝ) :=
    ArithmeticFunction.vonMangoldt_sum
  have hlog : Real.log (l : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst l
      simpa using Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hl)
  have hnorm : ‖typeIICoeff U l‖ =
      ∑ e ∈ l.divisors.filter (fun e => U < e), (Λ : ArithmeticFunction ℝ) e := by
    unfold typeIICoeff
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  calc
    ∑ e ∈ l.divisors.filter (fun e => U < e), (Λ : ArithmeticFunction ℝ) e
        ≤ ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e := hle
    _ = Real.log (l : ℝ) := hfull
    _ ≤ Real.log (n : ℝ) := hlog

lemma sum_normSq_typeIICoeff_le (n U : ℕ) (s : Finset ℕ)
    (hs : ∀ l ∈ s, l ≤ n) :
    ∑ l ∈ s, ‖typeIICoeff U l‖ ^ 2 ≤ (s.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  calc
    ∑ l ∈ s, ‖typeIICoeff U l‖ ^ 2 ≤ ∑ l ∈ s, (Real.log (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have h := norm_typeIICoeff_le n U l (hs l hl)
      nlinarith [norm_nonneg (typeIICoeff U l), h]
    _ = (s.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]

lemma typeIIInner_eq_typeIIFourier (n U d : ℕ) (hd : 0 < d) (t : ℝ) :
    typeIIInner n U t d = typeIIFourier n U t d := by
  unfold typeIIInner typeIIFourier typeIICoeff
  rw [inner_high_sum_collapse n d U hd t]

/-- Support-truncated Cauchy–Schwarz: if `B` vanishes above `n/(U+1)`, then
the squared weighted sum only sees `d ≤ n/(U+1)`. -/
lemma norm_sum_mu_mul_sq_le_of_support (n U : ℕ) (B : ℕ → ℂ)
    (hsupp : ∀ d, n / (U + 1) < d → B d = 0) :
    ‖∑ d ∈ Finset.Icc (U + 1) n, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
      ((n / (U + 1) : ℕ) : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)), ‖B d‖ ^ 2 := by
  classical
  let s : Finset ℕ := Finset.Icc (U + 1) (n / (U + 1))
  have hsub : s ⊆ Finset.Icc (U + 1) n := by
    intro d hd
    simp only [s, Finset.mem_Icc] at hd ⊢
    have hdivle : n / (U + 1) ≤ n := Nat.div_le_self n (U + 1)
    omega
  have hzero : ∀ d ∈ Finset.Icc (U + 1) n, d ∉ s →
      ((μ : ArithmeticFunction ℝ) d : ℂ) * B d = 0 := by
    intro d hd hds
    have hd1 : U + 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hds' : d ∉ Finset.Icc (U + 1) (n / (U + 1)) := by
      simpa only [s] using hds
    have hdgt : n / (U + 1) < d := by
      by_contra h
      exact hds' (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)
    rw [hsupp d hdgt, mul_zero]
  have hsum : (∑ d ∈ Finset.Icc (U + 1) n,
      ((μ : ArithmeticFunction ℝ) d : ℂ) * B d)
      = ∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d :=
    (Finset.sum_subset hsub hzero).symm
  rw [hsum]
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
  have hcard : (s.card : ℝ) ≤ ((n / (U + 1) : ℕ) : ℝ) := by
    have hcard_nat : s.card ≤ n / (U + 1) := by
      simp only [s]
      rw [Nat.card_Icc]
      rw [Nat.sub_le_iff_le_add]
      omega
    exact_mod_cast hcard_nat
  have hnorm : 0 ≤ ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ :=
    norm_nonneg _
  calc
    ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2
        ≤ (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 :=
      pow_le_pow_left₀ hnorm h1 2
    _ ≤ (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := h2
    _ ≤ ((n / (U + 1) : ℕ) : ℝ) *
          ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((n / (U + 1) : ℕ) : ℝ) * ∑ d ∈ s, ‖B d‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Refined Type-II Cauchy–Schwarz: the energy only runs over
`d ≤ n/(U+1)`, which removes a spurious factor `U` from the earlier bound. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le_range (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((n / (U + 1) : ℕ) : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)), ‖typeIIInner n U t d‖ ^ 2 := by
  rw [expSum_high_mu_zeta_highLambda_eq n U t]
  apply norm_sum_mu_mul_sq_le_of_support n U (typeIIInner n U t)
  intro d hd
  dsimp only [typeIIInner]
  have hnd : n / d < U + 1 := by
    have hdpos : 0 < d := by
      have hnn : 0 ≤ n / (U + 1) := Nat.zero_le _
      omega
    rw [Nat.div_lt_iff_lt_mul hdpos]
    have h1 : n < d * (U + 1) :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < U + 1)).mp hd
    simpa [Nat.mul_comm] using h1
  rw [Finset.Icc_eq_empty (by omega)]
  simp

/-- Refined Type-II energy with the collapsed divisor-convolution inner sum. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le_range' (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((n / (U + 1) : ℕ) : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)), ‖typeIIFourier n U t d‖ ^ 2 := by
  refine (norm_expSum_high_mu_zeta_highLambda_sq_le_range n U t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  rw [typeIIInner_eq_typeIIFourier n U d hdpos t]

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

/-- Squared-energy form of the collapsed Type-II term: the inner sums are now
single Fourier transforms of the truncated divisor convolution. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le' (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((Finset.Icc (U + 1) n).card : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) n,
          ‖∑ l ∈ Finset.Icc 1 (n / d),
            (∑ e ∈ l.divisors.filter (fun e => U < e),
              ((Λ : ArithmeticFunction ℝ) e : ℂ)) *
              E (((d * l : ℕ) : ℝ) * t)‖ ^ 2 := by
  refine (norm_expSum_high_mu_zeta_highLambda_sq_le n U t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  rw [inner_high_sum_collapse n d U hdpos t]

end

end PEqualNP.Outside.Vaughan
