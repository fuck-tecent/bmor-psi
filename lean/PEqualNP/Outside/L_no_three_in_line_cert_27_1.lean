import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_27_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+54<n ∧ z.2+2<n)).card=(n-54)*(n-2) := by
  intro n
  have starts :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 54 < n ∧ z.2 + 2 < n) =
        (Finset.range (n - 54)).product (Finset.range (n - 2)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp
