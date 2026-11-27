import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_16_3 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+32<n ∧ z.2+6<n)).card=(n-32)*(n-6) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+32<n ∧ z.2+6<n))
      = (Finset.range (n-32)) ×ˢ (Finset.range (n-6)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
