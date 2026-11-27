import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_25_2 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+50<n ∧ z.2+4<n)).card=(n-50)*(n-4) := by
  intro n
  have starts :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 50 < n ∧ z.2 + 4 < n) =
        (Finset.range (n - 50)).product (Finset.range (n - 4)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp
