import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_8 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 38 < n ∧ z.2 + 16 < n)).card
        = (n - 38) * (n - 16) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 38 < n ∧ z.2 + 16 < n)).card = (n - 38) * (n - 16)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 38 < n ∧ z.2 + 16 < n)
        = (Finset.range (n - 38)) ×ˢ (Finset.range (n - 16)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
