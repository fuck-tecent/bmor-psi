import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_5_3 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+10<n ∧ z.2+6<n)).card=(n-10)*(n-6) := by
  intro n
  have h : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+10<n ∧ z.2+6<n)) = (Finset.range (n-10)) ×ˢ (Finset.range (n-6)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
