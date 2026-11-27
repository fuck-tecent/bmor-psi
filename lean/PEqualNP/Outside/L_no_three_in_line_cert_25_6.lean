import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_25_6 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+50<n ∧ z.2+12<n)).card=(n-50)*(n-12) := by
  intro n
  have starts :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 50 < n ∧ z.2 + 12 < n) =
        (Finset.range (n - 50)).product (Finset.range (n - 12)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts, Finset.product_eq_sprod, Finset.card_product, Finset.card_range, Finset.card_range]
