import Mathlib

theorem PEqualNP.Outside.L_goldbach_conv_weight_replacement :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k));
    ∀ (u v : ℕ → ℝ) (n : ℕ), conv u u n - conv v v n =
      conv (fun k => u k - v k) u n + conv v (fun k => u k - v k) n := by
  dsimp only
  intro u v n
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring
