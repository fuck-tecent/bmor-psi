import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

/-- Apply discrete summation by parts and split its accumulated cost at the given index. -/
theorem PEqualNP.Outside.L_goldbach_finite_phase_abel_two_ranges :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let F := fun (q a n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, (((if k % q=a % q then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); ∀ (q a n t : ℕ) (β : ℝ), 0 < q → t ≤ n → ‖F q a n β‖ ≤ |D q a n| + J q a 0 t β + J q a t n β := by
  dsimp only
  intro q a n t β _ ht
  let E (x : ℝ) := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let w (k : ℕ) : ℝ := if k % q = a % q then ArithmeticFunction.vonMangoldt k else 0
  let d (m : ℕ) : ℝ := (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q),
    ArithmeticFunction.vonMangoldt k) - (m:ℝ)/(Nat.totient q:ℝ)
  let bReal (k : ℕ) : ℝ := w (k+1) - 1 / (Nat.totient q : ℝ)
  let b (k : ℕ) : ℂ := (bReal k : ℂ)
  let phase (k : ℕ) : ℂ := E (((k+1 : ℕ) : ℝ)*β)
  let B : ℝ := 2 * Real.pi * |β|
  have hB : 0 ≤ B := by unfold B; positivity
  have hunit (k : ℕ) : ‖phase k‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hstep (k : ℕ) : phase (k+1) = phase k * E β := by
    dsimp only [phase, E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdiff (k : ℕ) : ‖phase (k+1) - phase k‖ ≤ B := by
    rw [hstep, show phase k * E β - phase k = phase k * (E β - 1) by ring,
      norm_mul, hunit, one_mul]
    have hE : E β = Complex.exp (Complex.I * ((2*Real.pi*β : ℝ) : ℂ)) := by
      dsimp [E]
      rw [mul_comm]
    rw [hE]
    simpa [B, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*β))
  have hPrefixReal (m : ℕ) : (∑ k ∈ Finset.range m, bReal k) = d m := by
    have hzero : w 0 = 0 := by simp [w]
    have hshift := Finset.sum_range_succ' w m
    simp only [hzero, add_zero, zero_add] at hshift
    dsimp only [bReal]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hshift]
    simp only [d, Finset.sum_filter, w]
    ring
  have hPrefix (m : ℕ) : ‖∑ k ∈ Finset.range m, b k‖ = |d m| := by
    change ‖∑ k ∈ Finset.range m, (bReal k : ℂ)‖ = _
    rw [← Complex.ofReal_sum, hPrefixReal, Complex.norm_real, Real.norm_eq_abs]
  have hMain : ‖phase (n-1) • ∑ k ∈ Finset.range n, b k‖ = |d n| := by
    rw [norm_smul, hunit, one_mul, hPrefix]
  have hTerms : (∑ j ∈ Finset.range (n-1), |d (j+1)|) ≤
      ∑ m ∈ Finset.range n, |d m| := by
    have hReindex : (∑ j ∈ Finset.range (n-1), |d (j+1)|) =
        ∑ m ∈ Finset.Ico 1 n, |d m| := by
      refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
      · intro j hj
        have := Finset.mem_range.mp hj
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · intro i _ j _ hij
        omega
      · intro j hj
        have := Finset.mem_Ico.mp hj
        exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro j _
        rfl
    rw [hReindex]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
    · intro m _ _
      exact abs_nonneg (d m)
  have hTail : ‖∑ j ∈ Finset.range (n-1),
      (phase (j+1) - phase j) • ∑ k ∈ Finset.range (j+1), b k‖ ≤
      B * (∑ m ∈ Finset.range n, |d m|) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n-1),
          ‖(phase (j+1) - phase j) • ∑ k ∈ Finset.range (j+1), b k‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n-1), B * |d (j+1)| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, hPrefix]
        exact mul_le_mul_of_nonneg_right (hdiff j) (abs_nonneg _)
      _ = B * (∑ j ∈ Finset.range (n-1), |d (j+1)|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hTerms hB
  have hReindex : (∑ j ∈ Finset.range n, phase j • b j) =
      ∑ k ∈ Finset.Icc 1 n, ((w k - 1/(Nat.totient q:ℝ):ℝ):ℂ) * E ((k:ℝ)*β) := by
    refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      have := Finset.mem_Icc.mp hj
      exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      simp only [phase, b, bReal, smul_eq_mul, mul_comm]
  change ‖∑ k ∈ Finset.Icc 1 n, ((w k - 1/(Nat.totient q:ℝ):ℝ):ℂ) * E ((k:ℝ)*β)‖ ≤
    |d n| + B * (∑ m ∈ Finset.Ico 0 t, |d m|) + B * (∑ m ∈ Finset.Ico t n, |d m|)
  rw [← hReindex, Finset.sum_range_by_parts]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ |d n| + B * (∑ m ∈ Finset.range n, |d m|) := add_le_add hMain.le hTail
    _ = _ := by
      rw [← Finset.range_eq_Ico, ← Finset.sum_range_add_sum_Ico _ ht]
      ring
