import Mathlib

theorem PEqualNP.Outside.L_goldbach_fourier_inversion :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let c := fun (M j k : ℕ) => E ((j : ℝ) * (k : ℝ) / (M : ℝ));
    let F := fun (M : ℕ) (f : ℕ → ℂ) (j : ℕ) => Finset.sum (Finset.range M) (fun k => f k * c M j k);
    ∀ M f k, k < M → Finset.sum (Finset.range M) (fun j => F M f j * star (c M j k)) = (M : ℂ) * f k := by
  change ∀ (M : ℕ) (f : ℕ → ℂ) (k : ℕ), k < M →
    Finset.sum (Finset.range M)
      (fun j =>
        (Finset.sum (Finset.range M)
          (fun l => f l * Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) *
        star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) =
    (M : ℂ) * f k
  intro M f k hk
  have hM_pos : 0 < M := by omega
  have hM_real : (M : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hM_pos)
  have hstar_exp : ∀ x : ℝ,
      star (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (-((x : ℂ) * Complex.I)) := by
    intro x
    change (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (-((x : ℂ) * Complex.I))
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hterm : ∀ l j : ℕ,
      Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
        star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)) =
      (Complex.exp (((2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)) ^ j := by
    intro l j
    rw [hstar_exp, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    have hreal :
        2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) -
          2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) =
        (j : ℝ) * (2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ))) := by
      ring
    calc
      ((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I +
          -(((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) -
            2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) := by
          rw [Complex.ofReal_sub, sub_mul, sub_eq_add_neg]
      _ = (((j : ℝ) * (2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ))) : ℝ) : ℂ) * Complex.I := by
          rw [hreal]
      _ = (j : ℂ) * (((2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) := by
          rw [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  have hdiag :
      Finset.sum (Finset.range M)
        (fun j =>
          Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
            star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) =
      (M : ℂ) := by
    have h1 : ∀ j ∈ Finset.range M,
        Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
          star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)) = 1 := by
      intro j _
      rw [hterm k j, sub_self, zero_div, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_pow]
    calc
      Finset.sum (Finset.range M)
          (fun j =>
            Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
              star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)))
        = Finset.sum (Finset.range M) (fun _ => (1 : ℂ)) := Finset.sum_congr rfl h1
      _ = (M : ℂ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hoff : ∀ l : ℕ, l < M → l ≠ k →
      Finset.sum (Finset.range M)
        (fun j =>
          Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
            star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) = 0 := by
    intro l hl hlk
    set ω : ℂ := Complex.exp (((2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)
    have hsum_eq :
        Finset.sum (Finset.range M)
          (fun j =>
            Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
              star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) =
        Finset.sum (Finset.range M) (fun j => ω ^ j) :=
      Finset.sum_congr rfl fun j _ => hterm l j
    rw [hsum_eq]
    have hω_pow : ω ^ M = 1 := by
      dsimp only [ω]
      rw [← Complex.exp_nat_mul]
      have hexp :
          (M : ℂ) * (((2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) =
          (((l : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        have hreal :
            (M : ℝ) * (2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ))) =
            (((l : ℤ) - (k : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
          rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
          have hcancel : (M : ℝ) * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) = (l : ℝ) - (k : ℝ) := by
            rw [mul_comm, div_mul_cancel₀ _ hM_real]
          calc
            (M : ℝ) * (2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)))
              = (2 * Real.pi) * ((M : ℝ) * (((l : ℝ) - (k : ℝ)) / (M : ℝ))) := by ring
            _ = (2 * Real.pi) * ((l : ℝ) - (k : ℝ)) := by rw [hcancel]
            _ = ((l : ℝ) - (k : ℝ)) * (2 * Real.pi) := by ring
        calc
          (M : ℂ) * (((2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)
            = (((M : ℝ) * (2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ))) : ℝ) : ℂ) * Complex.I := by
              simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
              ring
          _ = (((((l : ℤ) - (k : ℤ) : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
              rw [hreal]
          _ = (((l : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
              simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
              ring
      rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
    have hω_ne : ω ≠ 1 := by
      intro hω1
      dsimp only [ω] at hω1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hω1
      have him :
          2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) = (n : ℝ) * (2 * Real.pi) := by
        have h1 := congrArg Complex.im hn
        have hlhs :
            (((2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) : ℝ) : ℂ) * Complex.I).im =
            2 * Real.pi * (((l : ℝ) - (k : ℝ)) / (M : ℝ)) := by
          rw [Complex.mul_I_im, Complex.ofReal_re]
        have hrhs :
            ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im = (n : ℝ) * (2 * Real.pi) := by
          have hr : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
              (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
            simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
            ring
          rw [hr, Complex.mul_I_im, Complex.ofReal_re]
        rw [hlhs, hrhs] at h1
        exact h1
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
      have hdiv : ((l : ℝ) - (k : ℝ)) / (M : ℝ) = (n : ℝ) := by
        apply mul_left_cancel₀ h2pi
        exact him.trans (mul_comm (n : ℝ) (2 * Real.pi))
      have hmul : (l : ℝ) - (k : ℝ) = (n : ℝ) * (M : ℝ) := by
        have h3 := congrArg (fun x : ℝ => x * (M : ℝ)) hdiv
        rw [div_mul_cancel₀ _ hM_real] at h3
        exact h3
      have hint_real : (((l : ℤ) - (k : ℤ) : ℤ) : ℝ) = ((n * (M : ℤ) : ℤ) : ℝ) := by
        rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
        exact hmul
      have hint : (l : ℤ) - (k : ℤ) = n * (M : ℤ) := Int.cast_inj.mp hint_real
      rcases lt_trichotomy n 0 with hn_neg | rfl | hn_pos
      · have hle : n * (M : ℤ) ≤ -(M : ℤ) := by
          simpa [neg_one_mul] using
            (mul_le_mul_of_nonneg_right (show n ≤ -1 by omega) (show (0 : ℤ) ≤ (M : ℤ) by omega))
        omega
      · rw [zero_mul] at hint
        omega
      · have hge : (M : ℤ) ≤ n * (M : ℤ) := by
          simpa [one_mul] using
            (mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ n by omega) (show (0 : ℤ) ≤ (M : ℤ) by omega))
        omega
    have hgeom : (Finset.sum (Finset.range M) (fun j => ω ^ j)) * (ω - 1) = 0 := by
      rw [geom_sum_mul ω M, hω_pow, sub_self]
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hω_ne)
  calc
    Finset.sum (Finset.range M)
        (fun j =>
          (Finset.sum (Finset.range M)
            (fun l => f l * Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) *
          star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)))
      = Finset.sum (Finset.range M)
          (fun j =>
            Finset.sum (Finset.range M)
              (fun l => f l * (Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
                star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mul_assoc]
    _ = Finset.sum (Finset.range M)
          (fun l =>
            Finset.sum (Finset.range M)
              (fun j => f l * (Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
                star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))))) :=
        Finset.sum_comm
    _ = Finset.sum (Finset.range M)
          (fun l =>
            f l * Finset.sum (Finset.range M)
              (fun j => Complex.exp (((2 * Real.pi * ((j : ℝ) * (l : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
                star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I)))) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        exact (Finset.mul_sum (Finset.range M) _ (f l)).symm
    _ = f k * Finset.sum (Finset.range M)
          (fun j => Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I) *
            star (Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I))) := by
        refine Finset.sum_eq_single k ?_ ?_
        · intro l hl hlk
          rw [hoff l (Finset.mem_range.mp hl) hlk, mul_zero]
        · intro hk'
          exact (hk' (Finset.mem_range.mpr hk)).elim
    _ = f k * (M : ℂ) := by rw [hdiag]
    _ = (M : ℂ) * f k := mul_comm (f k) (M : ℂ)
