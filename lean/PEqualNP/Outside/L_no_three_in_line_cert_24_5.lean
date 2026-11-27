import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_24_5 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+48<n ∧ z.2+10<n)).card=(n-48)*(n-10) := by
  intro n
  have starts :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 48 < n ∧ z.2 + 10 < n) =
        (Finset.range (n - 48)).product (Finset.range (n - 10)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp
