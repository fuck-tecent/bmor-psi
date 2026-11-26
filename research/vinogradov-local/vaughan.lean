import Mathlib

/-! Vaughan's identity, adapted locally from the accepted Goldbach proof
`L_goldbach_frontier_vaughan_type1_elimination` (PR #2430, Apache-2.0).
This local file isolates the finite identity before any analytic estimate. -/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction zeta Moebius

namespace PEqualNP.Outside.Vaughan

noncomputable section

noncomputable def low (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ U then f m else 0, by simp⟩

noncomputable def high (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if U < m then f m else 0, by simp⟩

private theorem low_add_high (U : ℕ) (f : ArithmeticFunction ℝ) :
    low U f + high U f = f := by
  ext m
  change (if m ≤ U then f m else 0) + (if U < m then f m else 0) = f m
  by_cases h : m ≤ U
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

theorem vaughan_identity (U : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      low U Λ + low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
        low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ) +
        high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ := by
  have hμ : (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
      (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [low_add_high, coe_moebius_mul_coe_zeta]
  have hlog : (ζ : ArithmeticFunction ℝ) * (low U Λ + high U Λ) =
      ArithmeticFunction.log := by
    rw [low_add_high, zeta_mul_vonMangoldt]
  calc
    _ = low U Λ + high U Λ := (low_add_high U Λ).symm
    _ = low U Λ + (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
        (ζ : ArithmeticFunction ℝ) * high U Λ := by rw [hμ, one_mul]
    _ = _ := by rw [← hlog]; ring

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def expSum (n : ℕ) (f : ArithmeticFunction ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (f k : ℂ) * E ((k : ℝ) * t)

lemma expSum_add (n : ℕ) (f g : ArithmeticFunction ℝ) (t : ℝ) :
    expSum n (f + g) t = expSum n f t + expSum n g t := by
  unfold expSum
  simp only [ArithmeticFunction.add_apply, Complex.ofReal_add, add_mul]
  rw [Finset.sum_add_distrib]

lemma expSum_sub (n : ℕ) (f g : ArithmeticFunction ℝ) (t : ℝ) :
    expSum n (f - g) t = expSum n f t - expSum n g t := by
  unfold expSum
  simp only [sub_apply, Complex.ofReal_sub, sub_mul]
  rw [Finset.sum_sub_distrib]

theorem expSum_vaughan (n U : ℕ) (t : ℝ) :
    expSum n Λ t =
      expSum n (low U Λ) t +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ)) t +
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) t := by
  have h : expSum n Λ t =
      expSum n (low U Λ + low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
        low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ) +
        high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) t := by
    conv_lhs => rw [vaughan_identity U]
  rw [h]
  rw [expSum_add, expSum_sub, expSum_add]


lemma norm_expSum_le_of_support (n U : ℕ) (f : ArithmeticFunction ℝ) (C t : ℝ)
    (hC : 0 ≤ C) (hsupp : ∀ k : ℕ, U < k → f k = 0)
    (hbound : ∀ k : ℕ, k ≤ U → |f k| ≤ C) :
    ‖expSum n f t‖ ≤ (U + 1 : ℝ) * C := by
  classical
  unfold expSum
  let F : ℕ → ℂ := fun k => (f k : ℂ) * E ((k : ℝ) * t)
  have hsum : (∑ k ∈ Finset.range (n + 1), (f k : ℂ) * E ((k : ℝ) * t)) =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ U), F k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k ≤ U
    · simp [F, h]
    · have hk : U < k := lt_of_not_ge h
      simp [F, h, hsupp k hk]
  rw [hsum]
  have hsubset : (Finset.range (n + 1)).filter (fun k => k ≤ U) ⊆ Finset.range (U + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  calc
    ‖∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ U), F k‖
        ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ U), ‖F k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ U), C := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.mem_filter] at hk
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hEk : ‖E ((k : ℝ) * t)‖ = 1 := by
        dsimp only [E]
        simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((k : ℝ) * t))
      rw [hEk, mul_one]
      exact hbound k hk.2
    _ ≤ ∑ _k ∈ Finset.range (U + 1), C := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k _ _
      exact hC
    _ = (U + 1 : ℝ) * C := by simp


lemma norm_expSum_low_le (n U : ℕ) (f : ArithmeticFunction ℝ) (C t : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ k : ℕ, k ≤ U → |f k| ≤ C) :
    ‖expSum n (low U f) t‖ ≤ (U + 1 : ℝ) * C := by
  apply norm_expSum_le_of_support n U (low U f) C t hC
  · intro k hk
    simp [low, not_le_of_gt hk]
  · intro k hk
    simpa [low, hk] using hbound k hk


lemma norm_expSum_low_vonMangoldt_le (n U : ℕ) (hn : 1 ≤ n) (hUn : U ≤ n) (t : ℝ) :
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) t‖ ≤
      (U + 1 : ℝ) * Real.log (n : ℝ) := by
  apply norm_expSum_low_le n U (Λ : ArithmeticFunction ℝ) (Real.log (n : ℝ)) t
  · exact Real.log_natCast_nonneg n
  · intro k hk
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    by_cases hk0 : k = 0
    · simp [hk0, Real.log_natCast_nonneg n]
    · have hk_n : k ≤ n := hk.trans hUn
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hlog : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hk_n)
      exact ArithmeticFunction.vonMangoldt_le_log.trans hlog


lemma norm_expSum_le_sum_abs (n : ℕ) (f : ArithmeticFunction ℝ) (t : ℝ) :
    ‖expSum n f t‖ ≤ ∑ k ∈ Finset.range (n + 1), |f k| := by
  unfold expSum
  calc
    ‖∑ k ∈ Finset.range (n + 1), (f k : ℂ) * E ((k : ℝ) * t)‖
        ≤ ∑ k ∈ Finset.range (n + 1), ‖(f k : ℂ) * E ((k : ℝ) * t)‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), |f k| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hEk : ‖E ((k : ℝ) * t)‖ = 1 := by
        dsimp only [E]
        simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((k : ℝ) * t))
      rw [hEk, mul_one]


lemma low_mu_mul_log_apply (U k : ℕ) :
    (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) k =
      ∑ x ∈ k.divisorsAntidiagonal.filter (fun x => x.1 ≤ U),
        (μ : ArithmeticFunction ℝ) x.1 * ArithmeticFunction.log x.2 := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x.1 ≤ U <;> simp [low, h]

/-- Reindex the second Vaughan term as the classical Type-I bilinear sum
`sum_{d <= U} mu(d) sum_{l <= n/d} log(l) e(d l t)`. -/
theorem expSum_low_mu_mul_log_eq (n U : ℕ) (t : ℝ) :
    expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t =
      ∑ d ∈ Finset.Icc 1 U,
        ((μ : ArithmeticFunction ℝ) d : ℂ) *
          ∑ l ∈ Finset.Icc 1 (n / d),
            (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t) := by
  classical
  unfold expSum
  have h1 : ∀ k ∈ Finset.range (n + 1),
      (((low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) k : ℝ) : ℂ) *
          E ((k : ℝ) * t) =
        ∑ x ∈ k.divisorsAntidiagonal.filter (fun x => x.1 ≤ U),
          ((μ : ArithmeticFunction ℝ) x.1 : ℂ) * (ArithmeticFunction.log x.2 : ℂ) *
            E ((k : ℝ) * t) := by
    intro k _
    rw [low_mu_mul_log_apply]
    push_cast
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_sigma']
  have h2 : (∑ d ∈ Finset.Icc 1 U, ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)) =
      ∑ d ∈ Finset.Icc 1 U, ∑ l ∈ Finset.Icc 1 (n / d),
        ((μ : ArithmeticFunction ℝ) d : ℂ) *
          ((ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  rw [h2]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => (⟨p.2.1, p.2.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpk, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpx', hple⟩ := Finset.mem_filter.mp hpx
    obtain ⟨hprod, hkne⟩ := Nat.mem_divisorsAntidiagonal.mp hpx'
    have hp1pos : 0 < p.2.1 := by
      rcases Nat.eq_zero_or_pos p.2.1 with h0 | hpos
      · exfalso
        rw [h0, zero_mul] at hprod
        exact hkne hprod.symm
      · exact hpos
    have hp2pos : 0 < p.2.2 := by
      rcases Nat.eq_zero_or_pos p.2.2 with h0 | hpos
      · exfalso
        rw [h0, mul_zero] at hprod
        exact hkne hprod.symm
      · exact hpos
    have hpkn : p.1 ≤ n := by
      have := Finset.mem_range.mp hpk
      omega
    have hdiv : p.2.2 ≤ n / p.2.1 := by
      rw [Nat.le_div_iff_mul_le hp1pos]
      calc
        p.2.2 * p.2.1 = p.1 := by rw [Nat.mul_comm, hprod]
        _ ≤ n := hpkn
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨by omega, hple⟩, ⟨by omega, hdiv⟩⟩
  · intro p hp p' hp' heq
    obtain ⟨-, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpx', -⟩ := Finset.mem_filter.mp hpx
    obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hpx'
    obtain ⟨-, hpx₁⟩ := Finset.mem_sigma.mp hp'
    obtain ⟨hpx₂, -⟩ := Finset.mem_filter.mp hpx₁
    obtain ⟨hprod', -⟩ := Nat.mem_divisorsAntidiagonal.mp hpx₂
    have hx1 : p.2.1 = p'.2.1 :=
      congrArg (fun z : Σ _ : ℕ, ℕ => z.1) heq
    have hx2 : p.2.2 = p'.2.2 :=
      congrArg (fun z : Σ _ : ℕ, ℕ => z.2) heq
    have hx : p.2 = p'.2 := Prod.ext hx1 hx2
    refine Sigma.ext ?_ (heq_of_eq hx)
    rw [← hprod, ← hprod', hx1, hx2]
  · intro q hq
    obtain ⟨hqd, hql⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hq1, hqU⟩ := Finset.mem_Icc.mp hqd
    obtain ⟨hql1, hqln⟩ := Finset.mem_Icc.mp hql
    refine ⟨⟨q.1 * q.2, (q.1, q.2)⟩, ?_, ?_⟩
    · have hmul : q.1 * q.2 ≤ n := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le (by omega : 0 < q.1)).mp hqln
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · rw [Finset.mem_range]
        show q.1 * q.2 < n + 1
        omega
      · refine Finset.mem_filter.mpr ⟨?_, hqU⟩
        exact Nat.mem_divisorsAntidiagonal.mpr
          ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
    · rfl
  · intro p hp
    obtain ⟨-, hpx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpx', -⟩ := Finset.mem_filter.mp hpx
    obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hpx'
    show ((μ : ArithmeticFunction ℝ) p.2.1 : ℂ) * (ArithmeticFunction.log p.2.2 : ℂ) *
        E ((p.1 : ℝ) * t) =
      ((μ : ArithmeticFunction ℝ) p.2.1 : ℂ) *
        ((ArithmeticFunction.log p.2.2 : ℂ) * E (((p.2.1 * p.2.2 : ℕ) : ℝ) * t))
    rw [← hprod]
    ring


lemma mul_zeta_mul_apply (f g : ArithmeticFunction ℝ) (k : ℕ) :
    (f * (ζ : ArithmeticFunction ℝ) * g) k =
      ∑ p ∈ k.divisorsAntidiagonal,
        ∑ q ∈ p.1.divisorsAntidiagonal, f q.1 * g p.2 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    ← Nat.sum_divisorsAntidiagonal (fun i _ => f i)]
  rw [Finset.sum_mul]

/- Reindex `sum_{k <= n} (f * zeta * g)(k) e(k t)` as a triple sum over
`d * e * m <= n`.  Both the third Type-I term and the Type-II term of the
Vaughan decomposition have this shape. -/
set_option maxHeartbeats 1000000 in
theorem expSum_mul_zeta_eq (n : ℕ) (f g : ArithmeticFunction ℝ) (t : ℝ) :
    expSum n (f * (ζ : ArithmeticFunction ℝ) * g) t =
      ∑ d ∈ Finset.Icc 1 n,
        (f d : ℂ) *
          ∑ e ∈ Finset.Icc 1 (n / d),
            (g e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t) := by
  classical
  unfold expSum
  have h1 : ∀ k ∈ Finset.range (n + 1),
      (((f * (ζ : ArithmeticFunction ℝ) * g) k : ℝ) : ℂ) * E ((k : ℝ) * t) =
        ∑ p ∈ k.divisorsAntidiagonal,
          ∑ q ∈ p.1.divisorsAntidiagonal,
            (f q.1 : ℂ) * (g p.2 : ℂ) * E ((k : ℝ) * t) := by
    intro k _
    rw [mul_zeta_mul_apply]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_sigma']
  rw [Finset.sum_sigma']
  have h2 : (∑ d ∈ Finset.Icc 1 n, (f d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (n / d), (g e : ℂ) *
          ∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E (((d * e * m : ℕ) : ℝ) * t)) =
      ∑ d ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Icc 1 (n / d),
        ∑ m ∈ Finset.Icc 1 (n / (d * e)),
          (f d : ℂ) * ((g e : ℂ) * E (((d * e * m : ℕ) : ℝ) * t)) := by
    simp only [Finset.mul_sum]
  rw [h2]
  rw [Finset.sum_sigma']
  rw [Finset.sum_sigma']
  refine Finset.sum_bij
    (fun X _ => (⟨⟨X.2.1, X.1.2.2⟩, X.2.2⟩ : Σ _ : (Σ _ : ℕ, ℕ), ℕ)) ?_ ?_ ?_ ?_
  · intro X hX
    obtain ⟨hX1, hX2⟩ := Finset.mem_sigma.mp hX
    obtain ⟨hk_range, hp_mem⟩ := Finset.mem_sigma.mp hX1
    obtain ⟨hpk, hkne⟩ := Nat.mem_divisorsAntidiagonal.mp hp_mem
    obtain ⟨hqp, hpne⟩ := Nat.mem_divisorsAntidiagonal.mp hX2
    have hp1pos : 0 < X.1.2.1 := by
      rcases Nat.eq_zero_or_pos X.1.2.1 with h0 | hpos
      · exfalso
        rw [h0, zero_mul] at hpk
        exact hkne hpk.symm
      · exact hpos
    have hp2pos : 0 < X.1.2.2 := by
      rcases Nat.eq_zero_or_pos X.1.2.2 with h0 | hpos
      · exfalso
        rw [h0, mul_zero] at hpk
        exact hkne hpk.symm
      · exact hpos
    have hq1pos : 0 < X.2.1 := by
      rcases Nat.eq_zero_or_pos X.2.1 with h0 | hpos
      · exfalso
        rw [h0, zero_mul] at hqp
        exact hpne hqp.symm
      · exact hpos
    have hq2pos : 0 < X.2.2 := by
      rcases Nat.eq_zero_or_pos X.2.2 with h0 | hpos
      · exfalso
        rw [h0, mul_zero] at hqp
        exact hpne hqp.symm
      · exact hpos
    have hkn : X.1.1 ≤ n := by
      have := Finset.mem_range.mp hk_range
      omega
    have hq1n : X.2.1 ≤ n := by
      have hle1 : X.2.1 ≤ X.1.2.1 := by
        calc X.2.1 ≤ X.2.1 * X.2.2 := Nat.le_mul_of_pos_right X.2.1 hq2pos
          _ = X.1.2.1 := hqp
      have hle2 : X.1.2.1 ≤ X.1.1 := by
        calc X.1.2.1 ≤ X.1.2.1 * X.1.2.2 := Nat.le_mul_of_pos_right X.1.2.1 hp2pos
          _ = X.1.1 := hpk
      omega
    have hed : X.1.2.2 ≤ n / X.2.1 := by
      rw [Nat.le_div_iff_mul_le hq1pos]
      calc X.1.2.2 * X.2.1 ≤ X.1.2.2 * (X.2.1 * X.2.2) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right X.2.1 hq2pos)
        _ = X.1.2.1 * X.1.2.2 := by rw [hqp]; ring
        _ = X.1.1 := hpk
        _ ≤ n := hkn
    have hmd : X.2.2 ≤ n / (X.2.1 * X.1.2.2) := by
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos hq1pos hp2pos)]
      calc X.2.2 * (X.2.1 * X.1.2.2) = (X.2.1 * X.2.2) * X.1.2.2 := by ring
        _ = X.1.2.1 * X.1.2.2 := by rw [hqp]
        _ = X.1.1 := hpk
        _ ≤ n := hkn
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨hq1pos, hq1n⟩
      · exact Finset.mem_Icc.mpr ⟨hp2pos, hed⟩
    · exact Finset.mem_Icc.mpr ⟨hq2pos, hmd⟩
  · intro X hX X' hX' heq
    obtain ⟨hX1, hX2⟩ := Finset.mem_sigma.mp hX
    obtain ⟨-, hp_mem⟩ := Finset.mem_sigma.mp hX1
    obtain ⟨hpk, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp_mem
    obtain ⟨hqp, -⟩ := Nat.mem_divisorsAntidiagonal.mp hX2
    obtain ⟨hX1', hX2'⟩ := Finset.mem_sigma.mp hX'
    obtain ⟨-, hp_mem'⟩ := Finset.mem_sigma.mp hX1'
    obtain ⟨hpk', -⟩ := Nat.mem_divisorsAntidiagonal.mp hp_mem'
    obtain ⟨hqp', -⟩ := Nat.mem_divisorsAntidiagonal.mp hX2'
    have hq1 : X.2.1 = X'.2.1 :=
      congrArg (fun z : Σ _ : (Σ _ : ℕ, ℕ), ℕ => z.1.1) heq
    have he : X.1.2.2 = X'.1.2.2 :=
      congrArg (fun z : Σ _ : (Σ _ : ℕ, ℕ), ℕ => z.1.2) heq
    have hq2 : X.2.2 = X'.2.2 :=
      congrArg (fun z : Σ _ : (Σ _ : ℕ, ℕ), ℕ => z.2) heq
    have hp1 : X.1.2.1 = X'.1.2.1 := by
      rw [← hqp, ← hqp', hq1, hq2]
    have hp : X.1.2 = X'.1.2 := Prod.ext hp1 he
    have hk : X.1.1 = X'.1.1 := by
      rw [← hpk, ← hpk', hp]
    have hXinner : X.1 = X'.1 := Sigma.ext hk (heq_of_eq hp)
    have hXq : X.2 = X'.2 := Prod.ext hq1 hq2
    exact Sigma.ext hXinner (heq_of_eq hXq)
  · intro Y hY
    obtain ⟨hYi, hYm⟩ := Finset.mem_sigma.mp hY
    obtain ⟨hYd, hYe⟩ := Finset.mem_sigma.mp hYi
    obtain ⟨hd1, hdn⟩ := Finset.mem_Icc.mp hYd
    obtain ⟨he1, hen⟩ := Finset.mem_Icc.mp hYe
    obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hYm
    refine ⟨⟨⟨Y.1.1 * Y.1.2 * Y.2, (Y.1.1 * Y.2, Y.1.2)⟩,
      (Y.1.1, Y.2)⟩, ?_, ?_⟩
    · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
        · rw [Finset.mem_range]
          show Y.1.1 * Y.1.2 * Y.2 < n + 1
          have h1 : Y.1.2 * Y.1.1 ≤ n :=
            (Nat.le_div_iff_mul_le (by omega : 0 < Y.1.1)).mp hen
          have h2 : Y.2 * (Y.1.1 * Y.1.2) ≤ n :=
            (Nat.le_div_iff_mul_le
              (Nat.mul_pos (by omega : 0 < Y.1.1) (by omega : 0 < Y.1.2))).mp hmn
          have hk : Y.1.1 * Y.1.2 * Y.2 = Y.2 * (Y.1.1 * Y.1.2) := by ring
          omega
        · refine Nat.mem_divisorsAntidiagonal.mpr ⟨?_, ?_⟩
          · show (Y.1.1 * Y.2) * Y.1.2 = Y.1.1 * Y.1.2 * Y.2
            ring
          · exact Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega)
      · refine Nat.mem_divisorsAntidiagonal.mpr ⟨?_, ?_⟩
        · show Y.1.1 * Y.2 = Y.1.1 * Y.2
          rfl
        · exact Nat.mul_ne_zero (by omega) (by omega)
    · rfl
  · intro X hX
    obtain ⟨hX1, hX2⟩ := Finset.mem_sigma.mp hX
    obtain ⟨-, hp_mem⟩ := Finset.mem_sigma.mp hX1
    obtain ⟨hpk, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp_mem
    obtain ⟨hqp, -⟩ := Nat.mem_divisorsAntidiagonal.mp hX2
    show (f X.2.1 : ℂ) * (g X.1.2.2 : ℂ) * E ((X.1.1 : ℝ) * t) =
      (f X.2.1 : ℂ) * ((g X.1.2.2 : ℂ) *
        E (((X.2.1 * X.1.2.2 * X.2.2 : ℕ) : ℝ) * t))
    have hk : X.1.1 = X.2.1 * X.1.2.2 * X.2.2 := by
      rw [← hpk, ← hqp]
      ring
    rw [hk]
    ring


/-- Restrict a sum over `Icc 1 N` to `Icc 1 (min U N)` when `f` vanishes above `U`. -/
lemma sum_Icc_eq_sum_Icc_min_of_eq_zero {f : ℕ → ℝ} {g : ℕ → ℂ} {U N : ℕ}
    (hf : ∀ k, U < k → f k = 0) :
    ∑ k ∈ Finset.Icc 1 N, (f k : ℂ) * g k =
      ∑ k ∈ Finset.Icc 1 (min U N), (f k : ℂ) * g k := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk hks
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk2 : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hks' : ¬ (k ≤ min U N) := by
      intro h
      exact hks (Finset.mem_Icc.mpr ⟨hk1, h⟩)
    have hmin : min U N ≤ U := min_le_left _ _
    have hkU : U < k := by omega
    rw [hf k hkU]
    simp

/-- Restrict a sum over `Icc 1 N` to `Icc (U+1) N` when `f` vanishes up to `U`. -/
lemma sum_Icc_eq_sum_Icc_succ_of_eq_zero {f : ℕ → ℝ} {g : ℕ → ℂ} {U N : ℕ}
    (hf : ∀ k, k ≤ U → f k = 0) :
    ∑ k ∈ Finset.Icc 1 N, (f k : ℂ) * g k =
      ∑ k ∈ Finset.Icc (U + 1) N, (f k : ℂ) * g k := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk hks
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk2 : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hks' : ¬ (U + 1 ≤ k) := by
      intro h
      exact hks (Finset.mem_Icc.mpr ⟨h, hk2⟩)
    have hkU : k ≤ U := by omega
    rw [hf k hkU]
    simp

/-- Third Vaughan term reindexed as a double Type-I sum over `d, e <= U`,
each with an inner geometric sum in `m`. -/
theorem expSum_low_mu_lowLambda_zeta_eq (n U : ℕ) (t : ℝ) :
    expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) t =
      ∑ d ∈ Finset.Icc 1 (min U n),
        ((μ : ArithmeticFunction ℝ) d : ℂ) *
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t) := by
  have hζ : (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) =
      (low U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        low U (Λ : ArithmeticFunction ℝ)) := by
    ring
  rw [hζ, expSum_mul_zeta_eq n (low U (μ : ArithmeticFunction ℝ))
    (low U (Λ : ArithmeticFunction ℝ)) t]
  rw [sum_Icc_eq_sum_Icc_min_of_eq_zero (U := U) (N := n) (f := low U (μ : ArithmeticFunction ℝ))
    (g := fun d => ∑ e ∈ Finset.Icc 1 (n / d), (low U (Λ : ArithmeticFunction ℝ) e : ℂ) *
      ∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t))
    (fun k hk => by simp [low, not_le_of_gt hk])]
  apply Finset.sum_congr rfl
  intro d hd
  have hdU : d ≤ U := by
    have := (Finset.mem_Icc.mp hd).2
    omega
  rw [show low U (μ : ArithmeticFunction ℝ) d = (μ : ArithmeticFunction ℝ) d by
    simp [low, hdU]]
  congr 1
  rw [sum_Icc_eq_sum_Icc_min_of_eq_zero (U := U) (N := n / d) (f := low U (Λ : ArithmeticFunction ℝ))
    (g := fun e => ∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t))
    (fun k hk => by simp [low, not_le_of_gt hk])]
  apply Finset.sum_congr rfl
  intro e he
  have heU : e ≤ U := by
    have := (Finset.mem_Icc.mp he).2
    omega
  rw [show low U (Λ : ArithmeticFunction ℝ) e = (Λ : ArithmeticFunction ℝ) e by
    simp [low, heU]]

/-- Type-II Vaughan term reindexed as a bilinear sum over `d, e > U`, each
with an inner geometric sum in `m`. -/
theorem expSum_high_mu_zeta_highLambda_eq (n U : ℕ) (t : ℝ) :
    expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t =
      ∑ d ∈ Finset.Icc (U + 1) n,
        ((μ : ArithmeticFunction ℝ) d : ℂ) *
          ∑ e ∈ Finset.Icc (U + 1) (n / d),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t) := by
  rw [expSum_mul_zeta_eq n (high U (μ : ArithmeticFunction ℝ))
    (high U (Λ : ArithmeticFunction ℝ)) t]
  rw [sum_Icc_eq_sum_Icc_succ_of_eq_zero (U := U) (N := n)
    (f := high U (μ : ArithmeticFunction ℝ))
    (g := fun d => ∑ e ∈ Finset.Icc 1 (n / d), (high U (Λ : ArithmeticFunction ℝ) e : ℂ) *
      ∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t))
    (fun k hk => by simp [high, not_lt_of_ge hk])]
  apply Finset.sum_congr rfl
  intro d hd
  have hdU : U < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  rw [show high U (μ : ArithmeticFunction ℝ) d = (μ : ArithmeticFunction ℝ) d by
    simp [high, hdU]]
  congr 1
  rw [sum_Icc_eq_sum_Icc_succ_of_eq_zero (U := U) (N := n / d)
    (f := high U (Λ : ArithmeticFunction ℝ))
    (g := fun e => ∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t))
    (fun k hk => by simp [high, not_lt_of_ge hk])]
  apply Finset.sum_congr rfl
  intro e he
  have heU : U < e := by
    have := (Finset.mem_Icc.mp he).1
    omega
  rw [show high U (Λ : ArithmeticFunction ℝ) e = (Λ : ArithmeticFunction ℝ) e by
    simp [high, heU]]

end

end PEqualNP.Outside.Vaughan
