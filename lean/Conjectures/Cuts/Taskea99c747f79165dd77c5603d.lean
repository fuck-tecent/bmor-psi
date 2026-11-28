import Mathlib

namespace Conjectures.Cuts.Taskea99c747f79165dd77c5603d_aux

lemma one_le_rad (n : ℕ) : (1 : ℕ) ≤ n.primeFactors.prod id :=
  Finset.one_le_prod (fun _p hp => Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp))

lemma log_rad_nonneg (a b : ℕ) :
    (0 : ℝ) ≤ Real.log (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) := by
  refine Real.log_nonneg ?_
  have h := one_le_rad (a * b * (a + b))
  exact_mod_cast h

end Conjectures.Cuts.Taskea99c747f79165dd77c5603d_aux

theorem Conjectures.Cuts.Taskea99c747f79165dd77c5603d :
    ∀ (x1 : ℝ), (1 : ℝ) < x1 → ∀ (x3 : ℕ), ∃ (x4 : ℝ), ∀ (x5 x6 : ℕ), (0 : ℕ) < x5 → (0 : ℕ) < x6 → x5.Coprime x6 → x5 + x6 < x3 ∨ x5 = x6 ∨ x5 + x6 ≤ (x5 * x6 * (x5 + x6)).primeFactors.prod id → Real.log (↑x5 + ↑x6) ≤ x1 * Real.log ↑((x5 * x6 * (x5 + x6)).primeFactors.prod id) + x4 := by
  intro x1 hx1 x3
  refine ⟨Real.log (x3 : ℝ), ?_⟩
  intro x5 x6 h5 h6 hcop h
  have hlogN : (0 : ℝ) ≤ Real.log (x3 : ℝ) := Real.log_natCast_nonneg x3
  have hrad : (0 : ℝ) ≤
      Real.log (((x5 * x6 * (x5 + x6)).primeFactors.prod id : ℕ) : ℝ) :=
    Conjectures.Cuts.Taskea99c747f79165dd77c5603d_aux.log_rad_nonneg x5 x6
  have hx1pos : (0 : ℝ) < x1 := by linarith
  have hsum : (0 : ℝ) < (x5 : ℝ) + (x6 : ℝ) := by positivity
  rcases h with hlt | heq | hle
  · have hlt' : (x5 : ℝ) + (x6 : ℝ) < (x3 : ℝ) := by exact_mod_cast hlt
    have hlog : Real.log ((x5 : ℝ) + (x6 : ℝ)) ≤ Real.log (x3 : ℝ) :=
      Real.log_le_log hsum hlt'.le
    nlinarith
  · subst heq
    have hgcd : Nat.gcd x5 x5 = 1 := hcop.gcd_eq_one
    rw [Nat.gcd_self] at hgcd
    have h1 : x5 = 1 := hgcd
    subst h1
    have htwo : ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) = 2 := by norm_num
    have hrad2 : (((1 * 1 * (1 + 1)).primeFactors.prod id : ℕ) : ℝ) = 2 := by norm_num
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hmul : Real.log 2 ≤ x1 * Real.log 2 := by
      have := mul_le_mul_of_nonneg_right hx1.le hlog2
      linarith
    rw [hrad2, htwo]
    linarith
  · have hle' : (x5 : ℝ) + (x6 : ℝ) ≤
        (((x5 * x6 * (x5 + x6)).primeFactors.prod id : ℕ) : ℝ) := by exact_mod_cast hle
    have hpos : (0 : ℝ) < (((x5 * x6 * (x5 + x6)).primeFactors.prod id : ℕ) : ℝ) := by
      have := Conjectures.Cuts.Taskea99c747f79165dd77c5603d_aux.one_le_rad (x5 * x6 * (x5 + x6))
      exact_mod_cast this
    have hlog : Real.log ((x5 : ℝ) + (x6 : ℝ)) ≤
        Real.log (((x5 * x6 * (x5 + x6)).primeFactors.prod id : ℕ) : ℝ) :=
      Real.log_le_log hsum hle'
    nlinarith
