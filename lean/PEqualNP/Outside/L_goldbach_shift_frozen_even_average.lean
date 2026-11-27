import Mathlib

open scoped BigOperators
open MeasureTheory Set

namespace PEqualNP.Outside

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_continuous : Continuous phase := by
  unfold phase
  fun_prop

private lemma shifted_average (A : Set ℝ) (hA : MeasurableSet A)
    (F : ℝ → ℂ) (hF : Continuous F) (n H : ℕ) :
    (∑ j ∈ Finset.range H, intervalIntegral (fun t => A.indicator
      (fun u => F u * phase (-((n+2*j : ℕ) : ℝ)*u)) t) (0:ℝ) 1 volume) / (H : ℂ) =
    intervalIntegral (fun t => A.indicator (fun u =>
      F u * phase (-(n:ℝ)*u) * ((∑ j ∈ Finset.range H, phase (-2*(j:ℝ)*u))/(H:ℂ))) t)
      (0:ℝ) 1 volume := by
  have hint (j : ℕ) : IntervalIntegrable (fun t => A.indicator
      (fun u => F u * phase (-((n+2*j : ℕ) : ℝ)*u)) t) volume 0 1 := by
    apply intervalIntegrable_iff.mpr
    have hc : Continuous (fun u : ℝ => F u * phase (-((n+2*j : ℕ) : ℝ)*u)) := by
      exact hF.mul (phase_continuous.comp (by fun_prop))
    exact hc.intervalIntegrable 0 1 |>.def' |>.indicator hA
  rw [← intervalIntegral.integral_finsetSum (fun j _ => hint j)]
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  by_cases htA : t ∈ A
  · simp only [Set.indicator_of_mem htA]
    rw [← mul_div_assoc, Finset.mul_sum]
    apply congrArg (fun z : ℂ => z / (H : ℂ))
    apply Finset.sum_congr rfl
    intro j hj
    have hid : -((n + 2*j : ℕ) : ℝ)*t = -(n:ℝ)*t + (-2*(j:ℝ)*t) := by push_cast; ring
    rw [hid, phase_add]
    ring
  · simp [Set.indicator_of_notMem htA]

theorem L_goldbach_shift_frozen_even_average :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ n H : ℕ, Even n → 0 < H → 2*(H-1) ≤ n → (∑ j ∈ Finset.range H, deepCoeff n (n+2*j))/(H:ℂ) = intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => f n u * ((∑ j ∈ Finset.range H, E (-2*(j:ℝ)*u))/(H:ℂ))) t) (0:ℝ) 1 MeasureTheory.volume := by
  dsimp only
  intro n H heven hH hbound
  let A : Set ℝ := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ∧
    a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤
      ((256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))}
  have hA : MeasurableSet A := by
    change MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ∧
      a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤
      ((256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))}
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro a
    simp only [← and_assoc]
    apply measurableSet_setOf.mpr
    apply Measurable.and measurable_const
    apply measurableSet_setOf.mp
    exact (isClosed_le (show Continuous (fun t : ℝ => |t - (a:ℝ)/(q:ℝ)|) by fun_prop) continuous_const).measurableSet
  have hF : Continuous (fun t : ℝ => (∑ k ∈ Finset.range (n+1),
      ((if Nat.Prime k then Real.log (k:ℝ) else 0 : ℝ) : ℂ) * phase ((k:ℝ)*t))^2) := by
    apply Continuous.pow
    apply continuous_finsetSum
    intro k hk
    exact continuous_const.mul (phase_continuous.comp (by fun_prop))
  exact shifted_average Aᶜ hA.compl _ hF n H

end PEqualNP.Outside
