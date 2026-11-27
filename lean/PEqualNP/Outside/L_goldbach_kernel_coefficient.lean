import Mathlib

theorem PEqualNP.Outside.L_goldbach_kernel_coefficient :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b)); ∀ N s : ℕ, s≤N → intervalIntegral (fun t => (K N t)^2*E (-(s:ℝ)*t)) (0:ℝ) 1 MeasureTheory.volume = ((s+1:ℕ):ℂ) := by
  intro E K N s hs
  let R := Finset.range (N+1)
  let harmonic (z : ℤ) (t : ℝ) :=
    Complex.exp ((z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * t)
  have hcont (z : ℤ) : Continuous (harmonic z) := by
    dsimp [harmonic]
    fun_prop
  have orthogonal (z : ℤ) :
      (∫ t : ℝ in 0..1, harmonic z t) = if z = 0 then (1 : ℂ) else 0 := by
    by_cases hz : z = 0
    · subst z
      simp [harmonic]
    · have hc : (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        exact mul_ne_zero (Int.cast_ne_zero.mpr hz)
          (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero)
      simp [harmonic, integral_exp_mul_complex hc, hz, Complex.exp_int_mul_two_pi_mul_I]
  have expand (t : ℝ) : (K N t)^2 * E (-(s:ℝ)*t) =
      ∑ i ∈ R, ∑ j ∈ R, harmonic ((i:ℤ)+j-s) t := by
    change (∑ i ∈ R, E ((i : ℝ)*t))^2 * E (-(s:ℝ)*t) = _
    rw [pow_two, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [E, harmonic]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have fiber (i : ℕ) :
      (∑ j ∈ R, (if (i:ℤ)+j-s = 0 then (1:ℂ) else 0)) =
        if i ≤ s then 1 else 0 := by
    by_cases hi : i ≤ s
    · have heq (j : ℕ) : (i:ℤ)+j-s = 0 ↔ j = s-i := by omega
      have hmem : s-i ∈ R := Finset.mem_range.mpr (by omega)
      simp [heq, hi, hmem]
    · have hne (j : ℕ) : (i:ℤ)+j-s ≠ 0 := by omega
      simp [hne, hi]
  have hrange : R.filter (fun i => i ≤ s) = Finset.range (s+1) := by
    ext i
    simp only [R, Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∫ t : ℝ in 0..1, ∑ i ∈ R, ∑ j ∈ R, harmonic ((i:ℤ)+j-s) t :=
      intervalIntegral.integral_congr (fun t _ => expand t)
    _ = ∑ i ∈ R, ∑ j ∈ R, ∫ t : ℝ in 0..1, harmonic ((i:ℤ)+j-s) t := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        exact intervalIntegral.integral_finsetSum (fun j _ => (hcont _).intervalIntegrable 0 1)
      · intro i _
        exact (continuous_finsetSum _ (fun j _ => hcont _)).intervalIntegrable 0 1
    _ = ∑ i ∈ R, (if i ≤ s then (1:ℂ) else 0) := by simp_rw [orthogonal, fiber]
    _ = _ := by
      rw [← Finset.sum_filter, hrange]
      simp
