import Mathlib
import Conjectures.Goldbach.Type2MovingDiagonalMoment

open Finset DyadicMixedB4Fourier

theorem Conjectures.Cuts.Task4258c8db4b0e59f69cc4fa33 : (∀ (x1 : ℕ → ℤ) (x2 : Finset ℕ),   have x3 : ℝ → ℂ := fun (x3 : ℝ) => ∑ x4 ∈ x2, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(x1 x4) * ↑x3);   have x4 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x4 : Fin (4 : ℕ)) => x2;   have x5 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x5 : Fin (4 : ℕ) → ℕ) => ∑ x6 : Fin (4 : ℕ), x1 (x5 x6);   ∫ (x6 : ℝ) in (0 : ℝ)..(1 : ℝ), ‖x3 x6‖ ^ (8 : ℕ) = ↑{x6 ∈ x4.product x4 | x5 x6.1 = x5 x6.2}.card) := by
  classical
  intro f A S Q F
  have eqMode (k : ℤ) (t : ℝ) : Complex.exp (2 * (Real.pi:ℂ) * Complex.I * k * t) = mode k t := by
    unfold mode frequency
    congr 1
    ring
  have fourth (t : ℝ) : S t ^ 4 = ∑ x ∈ Q, mode (F x) t := by
    dsimp only [S]
    rw [sum_pow']
    apply sum_congr rfl
    intro x _
    unfold mode frequency
    rw [← Complex.exp_sum]
    congr 1
    dsimp [F]
    push_cast
    simp only [mul_sum,sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  let P := Q ×ˢ Q
  let delta (p : (Fin 4 → ℕ) × (Fin 4 → ℕ)) := F p.1 - F p.2
  have point (t : ℝ) : ((‖S t‖^8 : ℝ):ℂ) = ∑ p ∈ P, mode (delta p) t := by
    rw [show ‖S t‖^8 = ‖S t^4‖^2 by rw [norm_pow]; ring,
      Complex.ofReal_pow, ← Complex.mul_conj', fourth]
    change (∑ x ∈ Q, mode (F x) t) * star (∑ x ∈ Q, mode (F x) t) = _
    rw [star_sum, sum_mul_sum, Finset.sum_product]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => mode_mul_conj _ _ _
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    _ = ∫ t in (0:ℝ)..1, ∑ p ∈ P, mode (delta p) t := intervalIntegral.integral_congr fun t _ => point t
    _ = ∑ p ∈ P, ∫ t in (0:ℝ)..1, mode (delta p) t :=
      intervalIntegral.integral_finsetSum fun p _ => (continuous_mode _).intervalIntegrable _ _
    _ = _ := by
      simp only [mode_integral,delta,sub_eq_zero,←sum_filter,sum_const,nsmul_eq_mul,mul_one]
      norm_cast
