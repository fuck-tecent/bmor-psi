import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_first_moment :
    ∀ (I F : Finset ℕ) (e : ℕ → ℝ) (b : ℝ), F ⊆ I →
      (∀ n ∈ F, b ≤ |e n|) → (F.card : ℝ) * b ≤ Finset.sum I (fun n => |e n|) := by
  intro I F e b hFI hb
  calc
    (F.card : ℝ) * b = F.sum (fun _ => b) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ F.sum (fun n => |e n|) := Finset.sum_le_sum hb
    _ ≤ I.sum (fun n => |e n|) :=
      Finset.sum_le_sum_of_subset_of_nonneg hFI (fun n _ _ => abs_nonneg (e n))
