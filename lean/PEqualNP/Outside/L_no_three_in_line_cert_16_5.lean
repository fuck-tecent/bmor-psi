import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_16_5 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 32 < n ∧ z.2 + 10 < n)).card
        = (n - 32) * (n - 10) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 32 < n ∧ z.2 + 10 < n)).card = (n - 32) * (n - 10)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 32 < n ∧ z.2 + 10 < n)
        = (Finset.range (n - 32)) ×ˢ (Finset.range (n - 10)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
