import Mathlib

open Finset

private theorem sum_prefix_reciprocal_endpoint (f : ℕ → ℝ) :
    ∀ N : ℕ, 2 ≤ N →
      (∑ t ∈ Ico 2 N, (∑ n ∈ range (t - 1), f n) / ((t : ℝ) * (t + 1))) =
        ∑ n ∈ range (N - 1), f n * ((n + 2 : ℝ)⁻¹ - (N : ℝ)⁻¹) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    norm_num [Finset.sum_range_succ]
  | succ N hN ih =>
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have hNextPos : 0 < (N : ℝ) + 1 := by positivity
    have hRecip : (N : ℝ)⁻¹ - ((N + 1 : ℕ) : ℝ)⁻¹ =
        (1 : ℝ) / ((N : ℝ) * (N + 1)) := by
      push_cast
      field_simp [hNpos.ne', hNextPos.ne']
      ring
    have hLength : N + 1 - 1 = (N - 1) + 1 := by omega
    have hTop : ((N - 1 : ℕ) : ℝ) + 2 = ((N + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      push_cast
      ring
    rw [Finset.sum_Ico_succ_top hN, hLength, Finset.sum_range_succ, hTop]
    simp only [sub_self, mul_zero, add_zero]
    rw [ih, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [show f n / ((N : ℝ) * (N + 1)) =
      f n * ((N : ℝ)⁻¹ - ((N + 1 : ℕ) : ℝ)⁻¹) by rw [hRecip]; ring]
    ring

theorem Conjectures.TwinPrimes.JumpAbelEndpointIdentity :
    ∀ N : ℕ, 2≤N → (∑ t ∈ Finset.Ico 2 N, (∑ n ∈ Finset.range (t-1), ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))/((t:ℝ)*(t+1))) = ∑ n ∈ Finset.range (N-1), ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) * ((n+2:ℝ)⁻¹-(N:ℝ)⁻¹) :=
  sum_prefix_reciprocal_endpoint (fun n =>
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))

