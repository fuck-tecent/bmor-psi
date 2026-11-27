import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_prod_deviation :
    ∀ (n : ℕ) (z : Fin n → ℂ), ‖(∏ i,(1+z i))-1‖ ≤ (∏ i,(1+‖z i‖))-1 := by
  intro n
  induction n with
  | zero =>
    intro z
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero, sub_self, sub_self, norm_zero]
  | succ m ih =>
    intro z
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hih := ih (fun i => z (Fin.castSucc i))
    have hP0 : 0 ≤ (∏ i : Fin m, (1 + ‖z (Fin.castSucc i)‖)) - 1 :=
      (norm_nonneg _).trans hih
    have hlast : ‖(1 : ℂ) + z (Fin.last m)‖ ≤ 1 + ‖z (Fin.last m)‖ := by
      have h := norm_add_le (1 : ℂ) (z (Fin.last m))
      rw [norm_one] at h
      exact h
    have hmul :
        ‖(∏ i : Fin m, (1 + z (Fin.castSucc i))) - 1‖ * ‖(1 : ℂ) + z (Fin.last m)‖ ≤
          ((∏ i : Fin m, (1 + ‖z (Fin.castSucc i)‖)) - 1) * (1 + ‖z (Fin.last m)‖) :=
      mul_le_mul hih hlast (norm_nonneg _) hP0
    have hid :
        (∏ i : Fin m, (1 + z (Fin.castSucc i))) * (1 + z (Fin.last m)) - 1 =
          ((∏ i : Fin m, (1 + z (Fin.castSucc i))) - 1) * (1 + z (Fin.last m)) + z (Fin.last m) := by
      ring
    calc
      ‖(∏ i : Fin m, (1 + z (Fin.castSucc i))) * (1 + z (Fin.last m)) - 1‖
          = ‖((∏ i : Fin m, (1 + z (Fin.castSucc i))) - 1) * (1 + z (Fin.last m)) + z (Fin.last m)‖ := by
        rw [hid]
      _ ≤ ‖((∏ i : Fin m, (1 + z (Fin.castSucc i))) - 1) * (1 + z (Fin.last m))‖ + ‖z (Fin.last m)‖ :=
        norm_add_le _ _
      _ = ‖(∏ i : Fin m, (1 + z (Fin.castSucc i))) - 1‖ * ‖(1 : ℂ) + z (Fin.last m)‖ + ‖z (Fin.last m)‖ := by
        rw [norm_mul]
      _ ≤ ((∏ i : Fin m, (1 + ‖z (Fin.castSucc i)‖)) - 1) * (1 + ‖z (Fin.last m)‖) + ‖z (Fin.last m)‖ := by
        exact add_le_add hmul le_rfl
      _ = (∏ i : Fin m, (1 + ‖z (Fin.castSucc i)‖)) * (1 + ‖z (Fin.last m)‖) - 1 := by
        ring
