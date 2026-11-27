import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_18_13 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+36<n ∧ z.2+26<n)).card=(n-36)*(n-26) := by
  intro n
  have starts :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 36 < n ∧ z.2 + 26 < n) =
        (Finset.range (n - 36)).product (Finset.range (n - 26)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp
