import Mathlib

open Finset

namespace PEqualNP.Outside

theorem L_goldbach_sieve_lcm_quadratic :
    ∀ (x : ℕ) (m : ℕ → ℕ) (D : Finset ℕ) (w : ℕ → ℝ), (∑ k ∈ Finset.range x, (∑ d ∈ D.filter (fun d => d∣m k), w d)^2) = ∑ a ∈ D, ∑ b ∈ D, w a*w b*(((Finset.range x).filter (fun k => Nat.lcm a b∣m k)).card : ℝ) := by
  intro x m D w
  classical
  have hterm (k : ℕ) :
      (∑ d ∈ D.filter (fun d => d ∣ m k), w d) ^ 2 =
        ∑ a ∈ D, ∑ b ∈ D, if Nat.lcm a b ∣ m k then w a * w b else 0 := by
    rw [Finset.sum_filter, pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : a ∣ m k <;> by_cases hb : b ∣ m k <;> simp [Nat.lcm_dvd_iff, ha, hb]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end PEqualNP.Outside
