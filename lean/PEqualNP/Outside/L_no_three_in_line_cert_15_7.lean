import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_15_7 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 30 < n ∧ z.2 + 14 < n)).card
        = (n - 30) * (n - 14) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 30 < n ∧ z.2 + 14 < n)).card = (n - 30) * (n - 14)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 30 < n ∧ z.2 + 14 < n)
        = (Finset.range (n - 30)) ×ˢ (Finset.range (n - 14)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
