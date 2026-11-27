import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_rational_phase :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let ap := fun (q a N : ℕ) (f : ℕ → ℝ) => Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f;
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t));
    ∀ (N q h : ℕ) (f : ℕ → ℝ), 0 < q → S N f ((h : ℝ) / (q : ℝ)) = Finset.sum (Finset.range q) (fun a => (ap q a N f : ℂ) * E ((h : ℝ) * (a : ℝ) / (q : ℝ))) := by
  change ∀ (N q h : ℕ) (f : ℕ → ℝ), 0 < q →
    Finset.sum (Finset.range (N + 1))
      (fun k => (f k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * ((h : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)) =
    Finset.sum (Finset.range q)
      (fun a => ((Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I))
  intro N q h f hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hmaps : ∀ k ∈ Finset.range (N + 1), k % q ∈ Finset.range q :=
    fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)
  have hphase : ∀ a k : ℕ, k % q = a →
      Complex.exp (((2 * Real.pi * ((k : ℝ) * ((h : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    intro a k hk
    have hnat : k = q * (k / q) + a := by
      rw [← hk]
      exact (Nat.div_add_mod k q).symm
    have hdiv : (k : ℝ) = (q : ℝ) * ((k / q : ℕ) : ℝ) + (a : ℝ) := by
      calc
        (k : ℝ) = ((q * (k / q) + a : ℕ) : ℝ) := congrArg (Nat.cast : ℕ → ℝ) hnat
        _ = (q : ℝ) * ((k / q : ℕ) : ℝ) + (a : ℝ) := by
          rw [Nat.cast_add, Nat.cast_mul]
    have hreal : (k : ℝ) * ((h : ℝ) / (q : ℝ)) =
        (h : ℝ) * (a : ℝ) / (q : ℝ) + (((k / q) * h : ℕ) : ℝ) := by
      apply mul_right_cancel₀ hq0
      rw [hdiv, Nat.cast_mul]
      have h1 : ((q : ℝ) * ((k / q : ℕ) : ℝ) + (a : ℝ)) * ((h : ℝ) / (q : ℝ)) * (q : ℝ) =
          ((q : ℝ) * ((k / q : ℕ) : ℝ) + (a : ℝ)) * (h : ℝ) := by
        rw [mul_assoc, div_mul_cancel₀ _ hq0]
      have h2 : ((h : ℝ) * (a : ℝ) / (q : ℝ) + ((k / q : ℕ) : ℝ) * (h : ℝ)) * (q : ℝ) =
          (h : ℝ) * (a : ℝ) + ((k / q : ℕ) : ℝ) * (h : ℝ) * (q : ℝ) := by
        rw [add_mul, div_mul_cancel₀ _ hq0]
      rw [h1, h2]
      ring
    have hexp :
        (((2 * Real.pi * ((k : ℝ) * ((h : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I) +
          (((k / q) * h : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hreal, mul_add, Complex.ofReal_add, add_mul]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
      ring
    rw [hexp, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  calc
    Finset.sum (Finset.range (N + 1))
        (fun k => (f k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * ((h : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I))
      = Finset.sum (Finset.range q)
          (fun a => Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a))
            (fun k => (f k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * ((h : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I))) :=
        (Finset.sum_fiberwise_of_maps_to (g := fun k => k % q) hmaps
          (fun k => (f k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * ((h : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I))).symm
    _ = Finset.sum (Finset.range q)
          (fun a => Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a))
            (fun k => (f k : ℂ) * Complex.exp (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hphase a k (Finset.mem_filter.mp hk).2]
    _ = Finset.sum (Finset.range q)
          (fun a => (Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) (fun k => (f k : ℂ))) *
            Complex.exp (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (Finset.sum_mul ((Finset.range (N + 1)).filter (fun k => k % q = a)) (fun k => (f k : ℂ))
          (Complex.exp (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I))).symm
    _ = Finset.sum (Finset.range q)
          (fun a => ((Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f : ℝ) : ℂ) *
            Complex.exp (((2 * Real.pi * ((h : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Complex.ofReal_sum]
