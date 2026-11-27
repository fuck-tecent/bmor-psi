import Mathlib

/-- The legal starts for stride `(25, 4)` form a product of two ranges. -/
theorem PEqualNP.Outside.L_no_three_in_line_cert_25_4 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+50<n ∧ z.2+8<n)).card=(n-50)*(n-8) := by
  intro n
  have h : ((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + 50 < n ∧ z.2 + 8 < n) =
      (Finset.range (n - 50)).product (Finset.range (n - 8)) := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨_, hx, hy⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · intro hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
      have hx' := Finset.mem_range.mp hx
      have hy' := Finset.mem_range.mp hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
          by omega, by omega⟩
  rw [h]
  calc
    ((Finset.range (n - 50)).product (Finset.range (n - 8))).card =
        (Finset.range (n - 50)).card * (Finset.range (n - 8)).card :=
      Finset.card_product _ _
    _ = (n - 50) * (n - 8) := by simp only [Finset.card_range]
