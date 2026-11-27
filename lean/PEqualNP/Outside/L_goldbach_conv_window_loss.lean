import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic

theorem PEqualNP.Outside.L_goldbach_conv_window_loss :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); ∀ (u v : ℕ → ℝ) (n : ℕ) (A : Finset ℕ), (∀ k, 0≤u k ∧ 0≤v k) → let T := Finset.range (n+1); conv u v n - Finset.sum (T ∩ A) (fun k => u k*v (n-k)) = Finset.sum (T \ A) (fun k => u k*v (n-k)) := by
  dsimp only
  intro u v n A _
  have partition := Finset.sum_inter_add_sum_sdiff (Finset.range (n + 1)) A
    (fun k => u k * v (n - k))
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using partition.symm)
