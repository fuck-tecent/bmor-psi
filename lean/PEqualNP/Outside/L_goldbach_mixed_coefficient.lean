import Mathlib

open Finset MeasureTheory

private noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- Over one period the zero frequency has integral one and every other
integer frequency has integral zero. -/
private theorem integral_integer_frequency (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm, phase]
  · let a : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha : a ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hm)
        (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
    have hexp (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (a * (t : ℂ)) := by
      unfold phase
      dsimp only [a]
      push_cast
      congr 1
      ring
    have hend : Complex.exp a = 1 := Complex.exp_int_mul_two_pi_mul_I m
    simp_rw [hexp]
    rw [integral_exp_mul_complex ha]
    simp [hm, hend]

/-- The nth Fourier coefficient of the product of two finite exponential sums
is the nth additive convolution of their weights. -/
theorem PEqualNP.Outside.L_goldbach_mixed_coefficient :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t))
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    ∀ n u v, intervalIntegral (fun t => S n u t * S n v t * E (-(n : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = (conv u v n : ℂ) := by
  intro E S conv n u v
  let indices := range (n + 1)
  let frequency (i j : ℕ) : ℤ := (i : ℤ) + j - n
  let term (i j : ℕ) (t : ℝ) : ℂ :=
    ((u i : ℂ) * (v j : ℂ)) * phase ((frequency i j : ℝ) * t)
  have expand (t : ℝ) :
      S n u t * S n v t * E (-(n : ℝ) * t) =
        ∑ i ∈ indices, ∑ j ∈ indices, term i j t := by
    change (∑ i ∈ indices, (u i : ℂ) * phase ((i : ℝ) * t)) *
      (∑ j ∈ indices, (v j : ℂ) * phase ((j : ℝ) * t)) * phase (-(n : ℝ) * t) = _
    rw [sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    have shift : (i : ℝ) * t + (j : ℝ) * t + -(n : ℝ) * t = (frequency i j : ℝ) * t := by
      dsimp [frequency]
      push_cast
      ring
    dsimp only [term]
    rw [← shift, phase_add, phase_add]
    ring
  have hcont (i j : ℕ) : Continuous (term i j) := by
    dsimp [term, phase]
    fun_prop
  have row (i : ℕ) (hi : i ∈ indices) :
      (∫ t in (0 : ℝ)..1, ∑ j ∈ indices, term i j t) = (u i : ℂ) * v (n - i) := by
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hmem : n - i ∈ indices := mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n i))
    have hfreq (j : ℕ) : frequency i j = 0 ↔ j = n - i := by
      dsimp [frequency]
      omega
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable 0 1)]
    simp [term, intervalIntegral.integral_const_mul, integral_integer_frequency, hfreq, mul_ite, hmem]
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i ∈ indices, ∑ j ∈ indices, term i j t := by simp_rw [expand]
    _ = ∑ i ∈ indices, ∫ t in (0 : ℝ)..1, ∑ j ∈ indices, term i j t :=
      intervalIntegral.integral_finsetSum (fun i _ =>
        (continuous_finsetSum indices (fun j _ => hcont i j)).intervalIntegrable 0 1)
    _ = ∑ i ∈ indices, (u i : ℂ) * v (n - i) := sum_congr rfl row
    _ = _ := by simp [conv, indices]
