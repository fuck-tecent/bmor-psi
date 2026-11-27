import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_17_12 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+24<n)).card=(n-34)*(n-24) := by
  intro n
  have h : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+24<n)) = (Finset.range (n-34)) ×ˢ (Finset.range (n-24)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
