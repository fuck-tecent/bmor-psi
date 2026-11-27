import Mathlib

theorem PEqualNP.Outside.L_goldbach_fourth_band_rational_resonance :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    ∀ (A B h q a : ℕ), 0 < q → Nat.Coprime a q →
      let z := E ((a:ℝ)*h/q)
      ‖∑ l ∈ Finset.Ioc A B, E ((a:ℝ)*h*l/q)‖ ≤
        if q ∣ h then ((B-A:ℕ):ℝ) else min ((B-A:ℕ):ℝ) (2/‖1-z‖) := by
  dsimp only
  intro A B h q a hq hcop
  set z : ℂ := Complex.exp (((2*Real.pi*((a:ℝ)*h/q):ℝ):ℂ)*Complex.I) with hz_def
  have hz_norm : ‖z‖ = 1 := by
    rw [hz_def]
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((a:ℝ)*h/q))
  have hpow : ∀ l : ℕ,
      Complex.exp (((2*Real.pi*((a:ℝ)*h*l/q):ℝ):ℂ)*Complex.I) = z ^ l := by
    intro l
    have harg : (((2*Real.pi*((a:ℝ)*h*l/q):ℝ):ℂ)*Complex.I)
        = (l:ℂ) * (((2*Real.pi*((a:ℝ)*h/q):ℝ):ℂ)*Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul, ← hz_def]
  have hsum_eq : (∑ l ∈ Finset.Ioc A B,
        Complex.exp (((2*Real.pi*((a:ℝ)*h*l/q):ℝ):ℂ)*Complex.I))
      = ∑ l ∈ Finset.Ioc A B, z ^ l := by
    exact Finset.sum_congr rfl (fun l _ => hpow l)
  rw [hsum_eq]
  rcases le_or_gt B A with hBA | hAB
  · -- empty interval: both sides vanish
    have hsub : B - A = 0 := Nat.sub_eq_zero_of_le hBA
    have hsum0 : (∑ l ∈ Finset.Ioc A B, z ^ l) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [Finset.mem_Ioc] at hl
      omega
    rw [hsub, hsum0]
    simp only [Nat.cast_zero, norm_zero]
    split_ifs with h
    · exact le_refl 0
    · rw [min_eq_left]
      positivity
  · -- nonempty interval: geometric-series bound
    have hIoc_eq : Finset.Ioc A B = Finset.Ico (A+1) (B+1) := by
      ext l
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have htriv : ‖∑ l ∈ Finset.Ioc A B, z ^ l‖ ≤ ((B-A:ℕ):ℝ) := by
      calc ‖∑ l ∈ Finset.Ioc A B, z ^ l‖
          ≤ ∑ l ∈ Finset.Ioc A B, ‖z ^ l‖ := norm_sum_le _ _
        _ = ∑ l ∈ Finset.Ioc A B, (1:ℝ) := by
            apply Finset.sum_congr rfl
            intro l _
            rw [norm_pow, hz_norm, one_pow]
        _ = ((Finset.Ioc A B).card : ℝ) := by simp
        _ = ((B-A:ℕ):ℝ) := by simp
    by_cases hres : q ∣ h
    · rw [if_pos hres]
      exact htriv
    · rw [if_neg hres]
      apply le_min htriv
      have hz_ne : z ≠ 1 := by
        intro hz1
        have harg' : (((2*Real.pi*((a:ℝ)*h/q):ℝ):ℂ)*Complex.I)
            = 2 * (Real.pi:ℂ) * Complex.I * ((a*h:ℕ):ℂ) / (q:ℂ) := by
          push_cast
          ring
        have hdvd : q ∣ a * h := by
          apply (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := a*h) (N := q) hq.ne').mp
          rw [hz_def] at hz1
          rwa [harg'] at hz1
        have hdvd' : q ∣ h * a := by rwa [mul_comm] at hdvd
        exact hres (hcop.symm.dvd_mul_right.mp hdvd')
      have hmul2 : (∑ l ∈ Finset.Ioc A B, z ^ l) * (1 - z) = z ^ (A+1) - z ^ (B+1) := by
        rw [hIoc_eq]
        exact geom_sum_Ico_mul_neg z (m := A+1) (n := B+1) (by omega)
      have hnorm : ‖∑ l ∈ Finset.Ioc A B, z ^ l‖ * ‖1 - z‖ ≤ 2 := by
        calc ‖∑ l ∈ Finset.Ioc A B, z ^ l‖ * ‖1 - z‖
            = ‖(∑ l ∈ Finset.Ioc A B, z ^ l) * (1 - z)‖ := (norm_mul _ _).symm
          _ = ‖z ^ (A+1) - z ^ (B+1)‖ := by rw [hmul2]
          _ ≤ ‖z ^ (A+1)‖ + ‖z ^ (B+1)‖ := norm_sub_le _ _
          _ = 2 := by
              rw [norm_pow, norm_pow, hz_norm, one_pow, one_pow]
              norm_num
      have hpos : 0 < ‖1 - z‖ := by
        rw [norm_pos_iff]
        intro h0
        exact hz_ne (sub_eq_zero.mp h0).symm
      exact (le_div_iff₀ hpos).mpr hnorm
