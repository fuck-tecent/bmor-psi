import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_mirror :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n k:ℕ,k∈S n → n-k∈S n := by
  dsimp only
  intro n k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  omega
