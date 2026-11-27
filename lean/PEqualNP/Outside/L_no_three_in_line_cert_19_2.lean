import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_2 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+4<n)).card=(n-38)*(n-4) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+38<n ∧ z.2+4<n))
      = (Finset.range (n-38)) ×ˢ (Finset.range (n-4)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
