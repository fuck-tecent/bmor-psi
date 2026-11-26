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

end

end PEqualNP.Outside.Vaughan
