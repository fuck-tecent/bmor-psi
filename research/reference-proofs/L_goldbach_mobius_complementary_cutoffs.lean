import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction

namespace GoldbachMobiusParity

/-- The cutoff is expressed in logarithmic coordinates. -/
noncomputable def truncated (t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) * max (t - Real.log d) 0

private theorem sum_mu_zero {n : ℕ} (hn : 1 < n) :
    ∑ d ∈ n.divisors, (μ d : ℝ) = 0 := by
  have h : ∑ d ∈ n.divisors, μ d = 0 := by
    rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta]
    simp [Nat.ne_of_gt hn]
  exact_mod_cast h

private theorem complementary_mu {n d : ℕ} (hs : Squarefree n) (hd : d ∣ n) :
    (μ n : ℝ) * (μ (n/d) : ℝ) = (μ d : ℝ) := by
  have heq : d * (n/d) = n := Nat.mul_div_cancel' hd
  have hsf : Squarefree (d * (n/d)) := by rw [heq]; exact hs
  have hc : Nat.Coprime d (n/d) :=
    Nat.coprime_iff_isRelPrime.mpr (IsRelPrime.of_squarefree_mul hsf)
  have hm : μ n = μ d * μ (n/d) := by
    calc μ n = μ (d * (n/d)) := congrArg _ heq.symm
         _ = _ := isMultiplicative_moebius.map_mul_of_coprime hc
  have hs2 := moebius_sq_eq_one_of_squarefree hsf.of_mul_right
  have h : μ n * μ (n/d) = μ d := by
    rw [hm, mul_assoc, ← sq, hs2, mul_one]
  exact_mod_cast h

private theorem split_log_cutoff {n : ℕ} (hn : 1 < n) (t : ℝ) :
    ArithmeticFunction.vonMangoldt n = truncated t n -
      ∑ d ∈ n.divisors, (μ d : ℝ) * max (Real.log d - t) 0 := by
  rw [truncated, ← Finset.sum_sub_distrib]
  have sum_eq : (∑ d ∈ n.divisors,
      ((μ d : ℝ) * max (t - Real.log d) 0 - μ d * max (Real.log d - t) 0)) =
       ∑ d ∈ n.divisors, ((μ d : ℝ)*t - μ d*Real.log d) := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : Real.log d ≤ t
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
      ring
    · have h' := le_of_not_ge h
      rw [max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h')]
      ring
  rw [sum_eq, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mu_zero hn, zero_mul]
  change ArithmeticFunction.vonMangoldt n =
          0 - ∑ d ∈ n.divisors, (μ d : ℝ) * ArithmeticFunction.log d
  rw [sum_moebius_mul_log_eq]
  ring

/-- The complementary long-divisor sum is the parity factor times another short sum. -/
theorem complementary_cutoffs {n : ℕ} (hn : 1 < n) (hs : Squarefree n) (t : ℝ) :
    ArithmeticFunction.vonMangoldt n =
      truncated t n - (μ n : ℝ) * truncated (Real.log n - t) n := by
  have nz : n ≠ 0 := by omega
  have second : (μ n : ℝ) * truncated (Real.log n - t) n =
      ∑ d ∈ n.divisors, (μ d : ℝ) * max (Real.log d - t) 0 := by
    unfold truncated
    rw [Finset.mul_sum]
    rw [← Nat.sum_div_divisors n (fun j : ℕ =>
      (μ n : ℝ) * ((μ j : ℝ) * max (Real.log n - t - Real.log j) 0))]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have dne : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have dn : (d : ℝ) ≠ 0 := by exact_mod_cast dne
    rw [← mul_assoc, complementary_mu hs hdvd, Nat.cast_div hdvd dn,
        Real.log_div (by exact_mod_cast nz) dn]
    ring_nf
  rw [second]
  exact split_log_cutoff hn t

end GoldbachMobiusParity

theorem PEqualNP.Outside.L_goldbach_mobius_complementary_cutoffs :
    ∀ (n : ℕ) (t : ℝ), 1 < n → Squarefree n → let T := fun x : ℝ => n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * max (x - Real.log (d : ℝ)) 0); ArithmeticFunction.vonMangoldt n = T t - (ArithmeticFunction.moebius n : ℝ) * T (Real.log (n : ℝ) - t) := by
  intro n t hn hs
  exact GoldbachMobiusParity.complementary_cutoffs hn hs t
