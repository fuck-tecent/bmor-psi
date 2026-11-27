import Mathlib

open Finset

namespace PEqualNP.Outside

private def oddFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (2 < ·)

private noncomputable def singular (n : ℕ) : ℝ :=
  ∏ p ∈ oddFactors n, (1 + 1 / ((p : ℝ) - 2))

private noncomputable def increment (p : ℕ) : ℝ := (1 + 1 / ((p : ℝ) - 2))^2 - 1

private theorem increment_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ increment p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h : 0 ≤ 1 / ((p : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  unfold increment
  nlinarith [sq_nonneg (1 / ((p : ℝ) - 2))]

/-- A telescoping rational product bounds the averaged Euler factors at integers from 5 onwards. -/
private theorem tail_product (N : ℕ) (hN : 4 ≤ N) :
    ∏ p ∈ Icc 5 N, (1 + increment p / (p : ℝ)) ≤ 2 * ((N : ℝ) - 2) / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hI : Icc 5 (k + 1) = insert (k + 1) (Icc 5 k) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, prod_insert (by simp)]
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hinc := increment_nonneg (p := k + 1) (by omega)
    calc
      _ ≤ (1 + increment (k+1) / ((k+1 : ℕ) : ℝ)) * (2 * ((k : ℝ) - 2) / k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by
        simp only [increment, Nat.cast_succ]
        rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring]
        have h0 : (k : ℝ) ≠ 0 := by linarith
        have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
        calc
          _ = 2 * ((k : ℝ) - 1) / (k + 1) - 2 / ((k + 1) * (k - 1 : ℝ)^2) := by
            field_simp [h0, h1, h2]
            ring
          _ ≤ _ := sub_le_self _ (by positivity)

/-- Every odd prime factor of a positive integer at most `M` is 3 or lies in this tail. -/
private def candidates (M : ℕ) : Finset ℕ := insert 3 (Icc 5 (M+4))

private theorem candidates_ge_three {M p : ℕ} (hp : p ∈ candidates M) : 3 ≤ p := by
  rcases mem_insert.mp hp with rfl | hp
  · decide
  · have := (mem_Icc.mp hp).1
    omega

private theorem candidates_product (M : ℕ) :
    ∏ p ∈ candidates M, (1 + increment p / (p : ℝ)) ≤ 4 := by
  have htail := tail_product (M+4) (by omega)
  have hpos : (0 : ℝ) < (M+4 : ℕ) := by positivity
  have hbound : 2 * (((M+4 : ℕ) : ℝ) - 2) / (M+4 : ℕ) ≤ 2 :=
    (div_le_iff₀ hpos).mpr (by linarith)
  rw [candidates, prod_insert (by simp)]
  have hthree : 1 + increment 3 / (3 : ℝ) = 2 := by norm_num [increment]
  change (1 + increment 3 / (3 : ℝ)) * _ ≤ 4
  rw [hthree]
  linarith [htail.trans hbound]

private theorem oddFactors_subset {M n : ℕ} (hn : n ≤ M) : oddFactors n ⊆ candidates M := by
  intro p hp
  obtain ⟨hdiv, hodd⟩ := mem_filter.mp hp
  have hpN := Nat.le_of_mem_primeFactors hdiv
  have hfour : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) (Nat.prime_of_mem_primeFactors hdiv)
  by_cases h : p = 3
  · exact mem_insert.mpr (Or.inl h)
  · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨by omega, by omega⟩))

private def divisorProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

private noncomputable def subsetWeight (t : Finset ℕ) : ℝ := ∏ p ∈ t, increment p

/-- A subset of the odd prime factors contributes only at multiples of its product. -/
private theorem square_le_divisor_sum {n M : ℕ} (hn : n ≤ M) :
    singular n ^ 2 ≤ ∑ t ∈ (candidates M).powerset,
      if divisorProduct t ∣ n then subsetWeight t else 0 := by
  classical
  let A := oddFactors n
  have hdiv (t : Finset ℕ) (ht : t ∈ A.powerset) : divisorProduct t ∣ n := by
    have hsub : t ⊆ n.primeFactors :=
      (mem_powerset.mp ht).trans (filter_subset _ _)
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hsub).trans n.prod_primeFactors_dvd
  calc
    singular n ^ 2 = ∏ p ∈ A, (1 + increment p) := by
      unfold singular
      rw [← Finset.prod_pow]
      apply prod_congr rfl
      intro p _
      dsimp [increment]
      ring
    _ = ∑ t ∈ A.powerset, subsetWeight t := Finset.prod_one_add A
    _ = ∑ t ∈ A.powerset, if divisorProduct t ∣ n then subsetWeight t else 0 := by
      exact sum_congr rfl fun t ht ↦ (ite_eq_left (hdiv t ht)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun t ht ↦ mem_powerset.mpr ((mem_powerset.mp ht).trans (oddFactors_subset hn))
      · intro t ht _
        split_ifs
        · exact prod_nonneg fun p hp ↦ increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
        · exact le_rfl

private theorem multiples_count (M d : ℕ) : ((Icc 1 M).filter (fun n ↦ d ∣ n)).card = M / d := by
  have sets : (Icc 1 M).filter (fun n ↦ d ∣ n) = (range M.succ).filter (fun n ↦ n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [sets, Nat.card_multiples']

/-- Average the expanded factors using the exact count `M / d` of positive multiples. -/
private theorem prefix_square (M : ℕ) : (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ 4*(M : ℝ) := by
  classical
  let P := candidates M
  calc
    (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ ∑ n ∈ Icc 1 M, ∑ t ∈ P.powerset,
        if divisorProduct t ∣ n then subsetWeight t else 0 :=
      sum_le_sum fun n hn ↦ square_le_divisor_sum (mem_Icc.mp hn).2
    _ = ∑ t ∈ P.powerset, ∑ n ∈ Icc 1 M,
        if divisorProduct t ∣ n then subsetWeight t else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ P.powerset, (M : ℝ) * (∏ p ∈ t, increment p / (p : ℝ)) := by
      apply sum_le_sum
      intro t ht
      have hw : 0 ≤ subsetWeight t := prod_nonneg fun p hp ↦
        increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
      rw [← sum_filter, sum_const, multiples_count, nsmul_eq_mul]
      calc
        _ ≤ ((M : ℝ) / (divisorProduct t : ℝ)) * subsetWeight t :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hw
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp only [divisorProduct, Nat.cast_prod, subsetWeight]
          ring
    _ = (M : ℝ) * ∏ p ∈ P, (1 + increment p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 4 * (M : ℝ) := by
      rw [mul_comm (4 : ℝ)]
      exact mul_le_mul_of_nonneg_left (candidates_product M) (Nat.cast_nonneg _)

/-- Doubling changes only the prime factor 2, which is excluded from the local factors. -/
private theorem singular_double (m : ℕ) : singular (2*m) = singular m := by
  by_cases hm : m = 0
  · simp [hm]
  · have hfac : oddFactors (2*m) = oddFactors m := by
      ext p
      by_cases hp : p = 2
      · subst p
        simp [oddFactors]
      · simp [oddFactors, Nat.primeFactors_mul (by decide : 2 ≠ 0) hm, Nat.prime_two.primeFactors, hp]
    unfold singular
    rw [hfac]

theorem L_goldbach_central_factor_square :
    let S := fun n : ℕ => ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2)); let I := fun x : ℕ => (Finset.Icc x (2*x)).filter (fun n => Even n); ∃ K : ℝ, 0<K ∧ ∀ x : ℕ, 1≤x → (∑ n ∈ I x, (S n)^2) ≤ K*(x:ℝ) := by
  change ∃ K : ℝ, 0 < K ∧ ∀ x : ℕ, 1 ≤ x →
    (∑ n ∈ (Icc x (2*x)).filter Even, singular n ^ 2) ≤ K*(x : ℝ)
  refine ⟨4, by norm_num, fun x hx ↦ ?_⟩
  let half (n : ℕ) := n / 2
  have double_half {n : ℕ} (hn : n ∈ (Icc x (2*x)).filter Even) : 2 * half n = n := by
    obtain ⟨a, ha⟩ := (mem_filter.mp hn).2
    dsimp [half]
    omega
  refine le_trans ?_ (prefix_square x)
  apply Finset.sum_le_sum_of_injOn half
  · intro a ha b hb he
    rw [← double_half ha, he, double_half hb]
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    have hinterval := mem_Icc.mp (mem_filter.mp hn).1
    have hdouble := double_half hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn
    exact le_of_eq (congrArg (fun y : ℝ ↦ y^2)
      ((congrArg singular (double_half hn).symm).trans (singular_double _)))
  · exact fun m _ _ ↦ sq_nonneg _

end PEqualNP.Outside
