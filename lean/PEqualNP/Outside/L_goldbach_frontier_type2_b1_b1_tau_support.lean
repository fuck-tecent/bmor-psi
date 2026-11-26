import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

theorem L_goldbach_frontier_type2_b1_b1_tau_support :
    (let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊;
     let B₁ := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊;
     let τ₁ := fun (n m : ℕ) =>
       ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a),
         (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d),
             ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
           ArithmeticFunction.vonMangoldt (m / a);
     ∀ n m : ℕ, m ≤ (U n) ^ 2 → τ₁ n m = 0) := by
  dsimp only
  intro n m hm
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finset.mem_filter] at ha
  rcases ha with ⟨ha_div, ha_gt, _ha_le, hma_gt⟩
  exfalso
  have hma_dvd : a ∣ m := Nat.dvd_of_mem_divisors ha_div
  have hprod : a * (m / a) = m := Nat.mul_div_cancel' hma_dvd
  have h1 : (⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊ : ℝ) < (a : ℝ) := by exact_mod_cast ha_gt
  have h2 : (⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊ : ℝ) < (m / a : ℕ) := by exact_mod_cast hma_gt
  have hprodR : (a : ℝ) * (m / a : ℕ) = (m : ℝ) := by exact_mod_cast hprod
  have hmR : (m : ℝ) ≤ ((⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊ : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hm
  nlinarith

end

end PEqualNP.Outside
