import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflection_energy_identity :
    ∀ (n : ℕ) (w : ℕ → ℝ),
      2 * (Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p))) =
        2 * Finset.sum (Finset.range (n + 1)) (fun p => (w p) ^ 2) -
          Finset.sum (Finset.range (n + 1)) (fun p => (w p - w (n - p)) ^ 2) := by
  intro n w
  let S : ℝ := Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p))
  let A : ℝ := Finset.sum (Finset.range (n + 1)) (fun p => (w p) ^ 2)
  let B : ℝ := Finset.sum (Finset.range (n + 1)) (fun p => (w (n - p)) ^ 2)
  have hB : B = A := by
    dsimp [B, A]
    rw [← Finset.sum_range_reflect (fun p => (w p) ^ 2) (n + 1)]
    simp [Nat.add_sub_cancel]
  have hdiff : Finset.sum (Finset.range (n + 1)) (fun p => (w p - w (n - p)) ^ 2) =
      A - 2 * S + B := by
    calc
      Finset.sum (Finset.range (n + 1)) (fun p => (w p - w (n - p)) ^ 2) =
          Finset.sum (Finset.range (n + 1))
            (fun p => (w p) ^ 2 - 2 * (w p * w (n - p)) + (w (n - p)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = A - 2 * S + B := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [A, S, B]
        rw [← Finset.mul_sum]
  rw [show (∑ p ∈ Finset.range (n + 1), w p * w (n - p)) = S by rfl]
  rw [show (∑ p ∈ Finset.range (n + 1), (w p) ^ 2) = A by rfl]
  rw [hdiff, hB]
  ring
