import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_parity :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n:ℕ, Odd n → Even (S n).card := by
  intro S n hn
  have window : S n = Finset.Ioo (n / 3) (n - n / 3) := by
    ext k
    simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  rw [window, Nat.card_Ioo]
  obtain ⟨m, hm⟩ := hn
  exact ⟨m - n / 3, by omega⟩
