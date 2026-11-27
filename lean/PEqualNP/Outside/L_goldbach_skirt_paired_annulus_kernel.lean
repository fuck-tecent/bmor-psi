import Mathlib

theorem PEqualNP.Outside.L_goldbach_skirt_paired_annulus_kernel :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q : ℕ) (j : ℤ) (h H : ℝ), 0 < q → 0 ≤ h → h ≤ H → let A := (Finset.range q).filter (fun a => Nat.Coprime a q); let T := fun (a : ℕ) (r : ℝ) => intervalIntegral (fun u => E ((j:ℝ)*((a:ℝ)/q+u))) (-r) r MeasureTheory.volume; (∑ a ∈ A, (T a H - T a h)) = (∑ a ∈ A, E ((j:ℝ)*a/q)) * ((if j=0 then 2*(H-h) else (Real.sin (2*Real.pi*j*H)-Real.sin (2*Real.pi*j*h))/(Real.pi*j) : ℝ):ℂ) := by
  intro E q j h H hq hh hhH A T
  have hEadd : ∀ x y : ℝ, E (x + y) = E x * E y := by
    intro x y
    dsimp only [E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsin : ∀ x : ℝ, E x = ((↑(Real.cos (2*Real.pi*x)) : ℂ) + (↑(Real.sin (2*Real.pi*x)) : ℂ) * Complex.I) := by
    intro x
    dsimp only [E]
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hT : ∀ (a : ℕ) (r : ℝ), T a r = E ((j:ℝ)*(a:ℝ)/q) * (∫ u in (-r)..r, E ((j:ℝ)*u)) := by
    intro a r
    have hcongr : T a r = ∫ u in (-r)..r, E ((j:ℝ)*(a:ℝ)/q) * E ((j:ℝ)*u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change E ((j:ℝ)*((a:ℝ)/q+u)) = E ((j:ℝ)*(a:ℝ)/q) * E ((j:ℝ)*u)
      rw [← hEadd]
      congr 1
      ring
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hK : ∀ r : ℝ, (∫ u in (-r)..r, E ((j:ℝ)*u)) = if j = 0 then ((2*r:ℝ):ℂ) else ((Real.sin (2*Real.pi*(j:ℝ)*r)/(Real.pi*(j:ℝ)) : ℝ) : ℂ) := by
    intro r
    by_cases hj : j = 0
    · rw [if_pos hj]
      simp only [hj, Int.cast_zero, zero_mul]
      have h1 : E (0:ℝ) = 1 := by
        dsimp only [E]
        simp
      rw [show (∫ u in (-r)..r, E (0:ℝ)) = ∫ u in (-r)..r, (1:ℂ) from by
        apply intervalIntegral.integral_congr
        intro u hu
        exact h1]
      rw [intervalIntegral.integral_const]
      push_cast
      simp
      ring
    · rw [if_neg hj]
      have hj0 : (j:ℝ) ≠ 0 := by exact_mod_cast hj
      have hpj : 2 * (Real.pi:ℂ) * (j:ℂ) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
        · norm_num
        · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        · exact_mod_cast hj
      have hc : 2 * (Real.pi:ℂ) * (j:ℂ) * Complex.I ≠ 0 := by
        exact mul_ne_zero hpj Complex.I_ne_zero
      have hconv : (∫ u in (-r)..r, E ((j:ℝ)*u)) = ∫ u in (-r)..r, Complex.exp ((2 * (Real.pi:ℂ) * (j:ℂ) * Complex.I) * ↑u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        change E ((j:ℝ)*u) = Complex.exp ((2 * (Real.pi:ℂ) * (j:ℂ) * Complex.I) * ↑u)
        dsimp only [E]
        congr 1
        push_cast
        ring
      rw [hconv, integral_exp_mul_complex hc]
      have hr1 : Complex.exp ((2 * (Real.pi:ℂ) * (j:ℂ) * Complex.I) * ↑r) = E ((j:ℝ)*r) := by
        dsimp only [E]
        congr 1
        push_cast
        ring
      have hr2 : Complex.exp ((2 * (Real.pi:ℂ) * (j:ℂ) * Complex.I) * ↑(-r)) = E ((j:ℝ)*(-r)) := by
        dsimp only [E]
        congr 1
        push_cast
        ring
      rw [hr1, hr2, hsin ((j:ℝ)*r), hsin ((j:ℝ)*(-r))]
      have hargneg : 2*Real.pi*((j:ℝ)*(-r)) = -(2*Real.pi*((j:ℝ)*r)) := by ring
      rw [hargneg, Real.cos_neg, Real.sin_neg]
      push_cast
      field_simp
      ring
  have hKH : (∫ u in (-H)..H, E ((j:ℝ)*u)) - (∫ u in (-h)..h, E ((j:ℝ)*u)) = ((if j = 0 then 2*(H-h) else (Real.sin (2*Real.pi*j*H)-Real.sin (2*Real.pi*j*h))/(Real.pi*j) : ℝ) : ℂ) := by
    rw [hK H, hK h]
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos hj, if_pos hj]
      rw [← Complex.ofReal_sub]
      congr 1
      ring
    · rw [if_neg hj, if_neg hj, if_neg hj]
      rw [← Complex.ofReal_sub]
      congr 1
      have hj0 : (j:ℝ) ≠ 0 := by exact_mod_cast hj
      have hpj2 : Real.pi*(j:ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hj0
      field_simp
  have hterm : ∀ a : ℕ, T a H - T a h = E ((j:ℝ)*(a:ℝ)/q) * ((∫ u in (-H)..H, E ((j:ℝ)*u)) - (∫ u in (-h)..h, E ((j:ℝ)*u))) := by
    intro a
    rw [hT a H, hT a h]
    ring
  calc (∑ a ∈ A, (T a H - T a h)) = (∑ a ∈ A, E ((j:ℝ)*(a:ℝ)/q)) * ((∫ u in (-H)..H, E ((j:ℝ)*u)) - (∫ u in (-h)..h, E ((j:ℝ)*u))) := by
        simp only [hterm]
        rw [Finset.sum_mul]
    _ = (∑ a ∈ A, E ((j:ℝ)*a/q)) * ((if j = 0 then 2*(H-h) else (Real.sin (2*Real.pi*j*H)-Real.sin (2*Real.pi*j*h))/(Real.pi*j) : ℝ) : ℂ) := by
        rw [hKH]
