import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_4_3 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+8<n ∧ z.2+6<n)).card=(n-8)*(n-6) := by
  intro n
  have h : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+8<n ∧ z.2+6<n)) = (Finset.range (n-8)) ×ˢ (Finset.range (n-6)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
