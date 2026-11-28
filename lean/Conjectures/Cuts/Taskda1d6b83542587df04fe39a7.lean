import Mathlib

theorem Conjectures.Cuts.Taskda1d6b83542587df04fe39a7 :
    (have x1 : ℕ → ℕ → ℝ := fun (x1 x2 : ℕ) => ↑((x1 ^ (2 : ℕ) + (1 : ℕ)).factorization x2) * Real.log ↑x2; ∀ (x2 : ℕ), (2 : ℕ) ≤ x2 → (2 : ℝ) * ↑x2 * Real.log ↑x2 ≤ ∑ x4 ∈ Finset.Ioc x2 ((2 : ℕ) * x2), ∑ x5 ∈ (x4 ^ (2 : ℕ) + (1 : ℕ)).primeFactors, x1 x4 x5) := by
  classical
  dsimp only
  intro x hx
  let weight (n p : ℕ) : ℝ := ((n^2+1).factorization p : ℝ) * Real.log (p:ℝ)
  have hLog (N : ℕ) (hN : N ≠ 0) :
      Real.log (N:ℝ) = ∑ p ∈ N.primeFactors, (N.factorization p : ℝ) * Real.log (p:ℝ) := by
    have hProd : (N : ℝ) = ∏ p ∈ N.primeFactors, (p:ℝ) ^ N.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization (n:=N) hN
    have hNZ : ∀ p ∈ N.primeFactors, (p:ℝ)^N.factorization p ≠ 0 := by
      intro p hp
      exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
    calc
      Real.log (N:ℝ) = Real.log (∏ p ∈ N.primeFactors, (p:ℝ)^N.factorization p) :=
        congrArg Real.log hProd
      _ = ∑ p ∈ N.primeFactors, Real.log ((p:ℝ)^N.factorization p) := Real.log_prod hNZ
      _ = _ := by simp only [Real.log_pow]
  have hEach (n : ℕ) (hn : n ∈ Finset.Ioc x (2*x)) :
      2 * Real.log (x:ℝ) ≤ ∑ p ∈ (n^2+1).primeFactors, weight n p := by
    have hxn : x ≤ n := (Finset.mem_Ioc.mp hn).1.le
    have hxR : (0:ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hxnR : (x:ℝ) ≤ n := by exact_mod_cast hxn
    calc
      2 * Real.log (x:ℝ) = Real.log ((x:ℝ)^2) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log ((n^2+1 : ℕ):ℝ) := by
        apply Real.log_le_log (by positivity)
        push_cast
        exact (pow_le_pow_left₀ hxR.le hxnR 2).trans (le_add_of_nonneg_right (by norm_num))
      _ = _ := hLog _ (by omega)
  have hCount : (Finset.Ioc x (2*x)).card = x := by rw [Nat.card_Ioc]; omega
  change 2*(x:ℝ)*Real.log (x:ℝ) ≤
    ∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors, weight n p
  calc
    2*(x:ℝ)*Real.log (x:ℝ) = ∑ _n ∈ Finset.Ioc x (2*x), 2 * Real.log (x:ℝ) := by
      rw [Finset.sum_const, hCount, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum hEach
