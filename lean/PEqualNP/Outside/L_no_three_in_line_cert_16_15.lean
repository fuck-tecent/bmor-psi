import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_16_15 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+32<n ∧ z.2+30<n)).card=(n-32)*(n-30) := by
  intro n
  change ((Finset.range n ×ˢ Finset.range n).filter _).card = _
  have starts :
      (Finset.range n ×ˢ Finset.range n).filter
          (fun z => z.1 + 32 < n ∧ z.2 + 30 < n) =
        Finset.range (n - 32) ×ˢ Finset.range (n - 30) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp only [Finset.card_product, Finset.card_range]
