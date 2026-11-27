import Mathlib

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_quadratic_primes_levent_root_phase_reality :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p;
    let phase := fun (p k n : ℕ) => Complex.exp (((angle p k n : ℝ) : ℂ) * Complex.I);
    ∀ p k : ℕ, 0<p → (∑ r ∈ roots 1 p, phase p k r).im = 0 := by
  dsimp only
  intro p k hp
  have hIm : ∀ s : Finset ℕ,
      (∑ r ∈ s, Complex.exp ((↑(2 * Real.pi * (k:ℝ) * (r:ℝ) / (p:ℝ)) : ℂ) * Complex.I)).im
      = ∑ r ∈ s, Real.sin (2 * Real.pi * (k:ℝ) * (r:ℝ) / (p:ℝ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_im, ih, Complex.exp_ofReal_mul_I_im]
  rw [hIm]
  by_cases hp1 : p = 1
  · subst hp1
    simp
  have hp2 : 2 ≤ p := by omega
  have hp0 : (p:ℝ) ≠ 0 := by
    have : 0 < p := by omega
    positivity
  have hsin : ∀ a : ℕ, a < p → Real.sin (2 * Real.pi * (k:ℝ) * ((p - a : ℕ):ℝ) / (p:ℝ))
      = - Real.sin (2 * Real.pi * (k:ℝ) * (a:ℝ) / (p:ℝ)) := by
    intro a ha
    have hsub : ((p - a : ℕ) : ℝ) = (p:ℝ) - (a:ℝ) := by
      rw [Nat.cast_sub (by omega : a ≤ p)]
    have key : 2 * Real.pi * (k:ℝ) * ((p - a : ℕ):ℝ) / (p:ℝ)
        = -(2 * Real.pi * (k:ℝ) * (a:ℝ) / (p:ℝ)) + (k:ℤ) * (2 * Real.pi) := by
      rw [hsub]
      field_simp
      push_cast
      ring
    rw [key, Real.sin_add_int_mul_two_pi, Real.sin_neg]
  have hmem : ∀ a ∈ (Finset.range p).filter (fun r => p ∣ r^2+1),
      p - a ∈ (Finset.range p).filter (fun r => p ∣ r^2+1) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    have hlt : a < p := Finset.mem_range.1 ha1
    have ha0 : 0 < a := by
      by_contra hcon
      have hz : a = 0 := by omega
      rw [hz] at ha2
      norm_num at ha2
      omega
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    have hcast : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
      rw [Nat.cast_sub (by omega : a ≤ p)]
      simp
    have hroot : ((a : ZMod p)^2 + 1) = 0 := by
      have h1 : ((a^2+1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (a^2+1)).2 ha2
      push_cast at h1
      simpa using h1
    rw [← CharP.cast_eq_zero_iff (ZMod p) p ((p-a)^2+1)]
    push_cast
    rw [hcast, neg_sq]
    simpa using hroot
  have hzero : (∑ r ∈ (Finset.range p).filter (fun r => p ∣ r^2+1),
      Real.sin (2 * Real.pi * (k:ℝ) * (r:ℝ) / (p:ℝ))) = 0 := by
    refine Finset.sum_involution (fun a _ => p - a) ?_ ?_ ?_ ?_
    · intro a ha
      have hlt : a < p := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
      rw [hsin a hlt]
      ring
    · intro a ha hfa hcon
      apply hfa
      have hlt : a < p := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
      have h2a : 2 * a = p := by omega
      have hang : 2 * Real.pi * (k:ℝ) * (a:ℝ) / (p:ℝ) = (k:ℝ) * Real.pi := by
        have ha0 : (a:ℝ) ≠ 0 := by
          have hpos : 0 < a := by omega
          positivity
        rw [← h2a]
        push_cast
        field_simp
      rw [hang, Real.sin_nat_mul_pi]
    · intro a ha
      exact hmem a ha
    · intro a ha
      have hlt : a < p := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
      omega
  exact hzero
