import Mathlib

open scoped BigOperators
open MeasureTheory

private noncomputable def osc (z : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((z : ℂ) * (2 * Real.pi * Complex.I)) * x)

private lemma osc_integral (z : ℤ) :
    (∫ x : ℝ in 0..1, osc z x) = if z = 0 then 1 else 0 := by
  by_cases hz : z = 0
  · simp [hz, osc]
  · have hc : (z : ℂ) * (2 * Real.pi * Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hz)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    simp only [osc, integral_exp_mul_complex hc, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, mul_zero, Complex.exp_zero, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div,
      ite_eq_right hz]

private lemma full_coeff (n : ℕ) (w : ℕ → ℝ) :
    (∫ x : ℝ in 0..1,
      (∑ k ∈ Finset.range (n+1), (w k : ℂ) * osc k x)^2 * osc (-(n : ℤ)) x) =
      ((∑ k ∈ Finset.range (n+1), w k * w (n-k) : ℝ) : ℂ) := by
  let A (k l : ℕ) (x : ℝ) := ((w k : ℂ) * w l) * osc ((k : ℤ) + l - n) x
  have hA (k l : ℕ) : Continuous (A k l) := by unfold A osc; fun_prop
  have expand (x : ℝ) :
      (∑ k ∈ Finset.range (n+1), (w k : ℂ) * osc k x)^2 * osc (-(n : ℤ)) x =
      ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1), A k l x := by
    rw [sq, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    simp only [A, osc, Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_natCast]
    have regroup (a b c d e : ℂ) : a * b * (c * d) * e = (a*c)*((b*d)*e) := by ring
    rw [regroup, ← Complex.exp_add, ← Complex.exp_add]
    congr 2; ring
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum _ (fun l _ => hA k l)).intervalIntegrable 0 1)]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hA k l).intervalIntegrable 0 1)]
  simp only [A, intervalIntegral.integral_const_mul, osc_integral]
  rw [Finset.sum_eq_single (n-k)]
  · simp [show (k : ℤ) + (n-k : ℕ) - n = 0 by omega]
  · intro l _ hl
    simp [show (k : ℤ) + l - n ≠ 0 by omega]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem PEqualNP.Outside.L_goldbach_type2_center_wide_subtraction :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ n : ℕ, let f := fun t : ℝ => (S n (τ₃ n) t)^2 * E (-(n:ℝ)*t); Jdeep n (τ₃ n) (τ₃ n) = ((∑ k ∈ Finset.range (n+1), τ₃ n k * τ₃ n (n-k)):ℝ) - intervalIntegral ((wideArcs n).indicator f) (0:ℝ) 1 MeasureTheory.volume := by
  classical
  intro E S Q Q₁ H wideArcs Λ μ U B₂ B₃ τ₃ Jdeep n f
  have aosc (k : ℕ) (x : ℝ) : E ((k : ℝ)*x) = osc k x := by
    dsimp [E, osc]; push_cast; congr 1; ring
  have nosc (x : ℝ) : E (-(n : ℝ)*x) = osc (-(n : ℤ)) x := by
    dsimp [E, osc]; push_cast; congr 1; ring
  have hfull : (∫ x : ℝ in 0..1, f x) =
      ((∑ k ∈ Finset.range (n+1), τ₃ n k * τ₃ n (n-k) : ℝ) : ℂ) := by
    simpa only [f, S, aosc, nosc] using full_coeff n (τ₃ n)
  have hcont : Continuous f := by dsimp [f, S, E]; fun_prop
  have hmeas : MeasurableSet (wideArcs n) := by
    simp only [wideArcs, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro a
    by_cases h : 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q
    · rcases h with ⟨h₁, h₂, h₃, h₄⟩
      convert (isClosed_le (f := fun t : ℝ => |t-(a:ℝ)/(q:ℝ)|)
        (g := fun _ : ℝ => (H n:ℝ)/((q:ℝ)*(n:ℝ))) (by fun_prop) continuous_const).measurableSet using 1
      ext x
      exact ⟨fun hx => hx.2.2.2.2, fun hx => ⟨h₁, h₂, h₃, h₄, hx⟩⟩
    · convert MeasurableSet.empty (α := ℝ) using 1
      ext x
      exact iff_of_false (fun hx => h ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩) (fun hx => hx)
  change (∫ t : ℝ in 0..1, (wideArcs n)ᶜ.indicator _ t) = _
  simp only [← sq]
  rw [← hfull]
  change (∫ t : ℝ in 0..1, (wideArcs n)ᶜ.indicator f t) = _
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [integral_indicator hmeas.compl, integral_indicator hmeas]
  exact setIntegral_compl hmeas ((hcont.intervalIntegrable 0 1).1)
