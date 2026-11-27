import Mathlib

theorem Conjectures.JoshiAbc.RoundingRadical :
    let rad := fun (n : ℕ) => n.primeFactors.prod id; ∀ (a b : ℕ) (S : Finset ℕ) (u : ℕ → ℝ), 0<a → 0<b → S ⊆ (2*a*b*(a+b)).primeFactors → (∀ p ∈ S, 0≤u p ∧ u p≤1) → S.sum (fun p => u p*Real.log p) ≤ Real.log (rad (a*b*(a+b)))+Real.log 2 := by
  dsimp
  intro a b S u ha hb hS hu
  let n : ℕ := a * b * (a + b)
  have hn : n ≠ 0 := by
    dsimp [n]
    positivity
  have htwo_n : 2 * a * b * (a + b) = 2 * n := by
    dsimp [n]
    ring
  have hfac : (2 * n).primeFactors = insert 2 n.primeFactors := by
    rw [Nat.primeFactors_mul (by norm_num) hn,
      Nat.Prime.primeFactors Nat.prime_two]
    simp
  have hSn : S ⊆ (2 * n).primeFactors := by
    simpa [htwo_n] using hS
  have hlogprod : Real.log ((n.primeFactors.prod id : ℕ) : ℝ) =
      n.primeFactors.sum (fun p => Real.log p) := by
    rw [Nat.cast_prod id n.primeFactors]
    rw [Real.log_prod]
    · simp
    · intro p hp
      exact Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero
  calc
    S.sum (fun p => u p * Real.log p) ≤ S.sum (fun p => Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_of_le_one_left (Real.log_natCast_nonneg p) (hu p hp).2
    _ ≤ (2 * n).primeFactors.sum (fun p => Real.log p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSn
      intro p hp hnot
      exact Real.log_natCast_nonneg p
    _ = (insert 2 n.primeFactors).sum (fun p => Real.log p) := by
      rw [hfac]
    _ ≤ Real.log 2 + n.primeFactors.sum (fun p => Real.log p) := by
      by_cases hmem : 2 ∈ n.primeFactors
      · rw [Finset.insert_eq_of_mem hmem]
        exact le_add_of_nonneg_left (Real.log_natCast_nonneg 2)
      · rw [Finset.sum_insert hmem]
        norm_num
    _ = Real.log ((n.primeFactors.prod id : ℕ) : ℝ) + Real.log 2 := by
      rw [hlogprod]
      ring
    _ = Real.log (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) + Real.log 2 := by
      rfl
