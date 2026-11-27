import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_20_1 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+40<n ∧ z.2+2<n)).card=(n-40)*(n-2) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+40<n ∧ z.2+2<n))
      = (Finset.range (n-40)) ×ˢ (Finset.range (n-2)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
