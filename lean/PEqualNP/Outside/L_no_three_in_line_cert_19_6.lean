import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_6 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 38 < n ∧ z.2 + 12 < n)).card
        = (n - 38) * (n - 12) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 38 < n ∧ z.2 + 12 < n)).card = (n - 38) * (n - 12)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 38 < n ∧ z.2 + 12 < n)
        = (Finset.range (n - 38)) ×ˢ (Finset.range (n - 12)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
