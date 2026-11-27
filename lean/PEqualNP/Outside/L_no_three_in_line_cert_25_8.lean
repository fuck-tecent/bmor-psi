import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_25_8 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+50<n ∧ z.2+16<n)).card=(n-50)*(n-16) := by
  intro n
  have h : ((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + 50 < n ∧ z.2 + 16 < n) =
      (Finset.range (n - 50)).product (Finset.range (n - 16)) := by
    ext z
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
