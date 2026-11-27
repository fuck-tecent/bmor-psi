import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_fourth_moment :
    ∀ (I F : Finset ℕ) (e : ℕ → ℝ) (b : ℝ),
      F ⊆ I → 0 ≤ b → (∀ n ∈ F, b ≤ |e n|) →
      (F.card : ℝ) * b ^ 4 ≤ Finset.sum I (fun n => (e n) ^ 4) := by
  intro I F e b hFI hb hlarge
  have hterm : ∀ n ∈ F, b ^ 4 ≤ (e n) ^ 4 := by
    intro n hn
    have he : 0 ≤ (e n) ^ 4 := by positivity
    calc
      b ^ 4 ≤ |e n| ^ 4 := pow_le_pow_left₀ hb (hlarge n hn) 4
      _ = (e n) ^ 4 := by rw [← abs_pow, abs_of_nonneg he]
  calc
    (F.card : ℝ) * b ^ 4 = Finset.sum F (fun _ => b ^ 4) := by
      simp [nsmul_eq_mul]
    _ ≤ Finset.sum F (fun n => (e n) ^ 4) := Finset.sum_le_sum hterm
    _ ≤ Finset.sum I (fun n => (e n) ^ 4) :=
      Finset.sum_le_sum_of_subset_of_nonneg hFI (fun n _ _ => by positivity)
