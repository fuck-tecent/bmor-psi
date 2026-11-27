import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

open Finset ArithmeticFunction

theorem PEqualNP.Outside.L_goldbach_fixed_ap_theta_reduction :
    (∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), (if k.Prime then ArithmeticFunction.vonMangoldt k else 0)) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/200) → (∀ n : ℕ, 10^16 ≤ n → (∑ k ∈ Finset.range (n+1), (if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)) ≤ (n:ℝ)/200) → (∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/100) := by
  intro hprime hpowers q a n hq hu ha hn hx
  let U := (range (n+1)).filter (fun k => k % q = a % q)
  let P (k : ℕ) : ℝ := if k.Prime then vonMangoldt k else 0
  let H (k : ℕ) : ℝ := if k.Prime then 0 else vonMangoldt k
  have pos (k : ℕ) : 0 ≤ H k := by
    dsimp [H]
    split <;> simp [vonMangoldt_nonneg]
  have splitWeights : (∑ k ∈ U, vonMangoldt k) = (∑ k ∈ U, P k) + ∑ k ∈ U, H k := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by by_cases h : k.Prime <;> simp [P,H,h]
  have bound : (∑ k ∈ U, H k) ≤ (n:ℝ)/200 := by
    apply le_trans _ (hpowers n hn)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun k _ _ => pos k)
  have h₁ : |(∑ k ∈ U, P k) - (n:ℝ)/q.totient| ≤ (n:ℝ)/200 := hprime q a n hq hu ha hn hx
  change |(∑ k ∈ U, vonMangoldt k) - (n:ℝ)/q.totient| ≤ _
  rw [splitWeights, add_sub_right_comm]
  apply (abs_add_le ..).trans
  rw [abs_of_nonneg (sum_nonneg fun k _ => pos k)]
  linarith only [h₁,bound]
