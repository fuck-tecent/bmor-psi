import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_sieve_square_majorant :
    ∀ (P m : ℕ) (D : Finset ℕ) (weights : ℕ → ℝ), 1∈D → weights 1=1 → (∀ d ∈ D, d∣P) → (if m.Coprime P then (1:ℝ) else 0) ≤ (∑ d ∈ D.filter (fun d => d∣m), weights d)^2 := by
  intro P m D weights hone hweight hdiv
  split_ifs with hcop
  · have hfilter : D.filter (fun d => d ∣ m) = {1} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hmem, hdm⟩
        exact Nat.eq_one_of_dvd_coprimes hcop hdm (hdiv d hmem)
      · rintro rfl
        exact ⟨hone, one_dvd m⟩
    simp [hfilter, hweight]
  · exact sq_nonneg _

end PEqualNP.Outside
