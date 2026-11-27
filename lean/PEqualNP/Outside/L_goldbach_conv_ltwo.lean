import Mathlib

theorem PEqualNP.Outside.L_goldbach_conv_ltwo :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    ∀ (u v : ℕ → ℝ) (n : ℕ),
      (conv u v n) ^ 2 ≤
        Finset.sum (Finset.range (n + 1)) (fun p => (u p) ^ 2) *
          Finset.sum (Finset.range (n + 1)) (fun p => (v p) ^ 2) := by
  dsimp only
  intro u v n
  have reflected :
      Finset.sum (Finset.range (n + 1)) (fun k => v (n - k) ^ 2) =
        Finset.sum (Finset.range (n + 1)) (fun k => v k ^ 2) := by
    simpa only [Nat.add_sub_cancel] using
      (Finset.sum_range_reflect (fun k => v k ^ 2) (n + 1))
  simpa only [reflected] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) u (fun k => v (n - k)))
