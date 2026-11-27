import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_size :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ m:ℕ, (S (3*m)).card=m-1 := by
  intro S m
  have window : S (3 * m) = Finset.Ioo m (2 * m) := by
    ext k
    simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  rw [window, Nat.card_Ioo]
  omega
