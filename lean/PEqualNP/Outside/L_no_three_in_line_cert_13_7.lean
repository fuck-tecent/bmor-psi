import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_13_7 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 26 < n ∧ z.2 + 14 < n)).card
        = (n - 26) * (n - 14) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 26 < n ∧ z.2 + 14 < n)).card = (n - 26) * (n - 14)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 26 < n ∧ z.2 + 14 < n)
        = (Finset.range (n - 26)) ×ˢ (Finset.range (n - 14)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
