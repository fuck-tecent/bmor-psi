import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_24_7 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+48<n ∧ z.2+14<n)).card=(n-48)*(n-14) := by
  intro n
  change ((Finset.range n ×ˢ Finset.range n).filter _).card = _
  have starts :
      (Finset.range n ×ˢ Finset.range n).filter
          (fun z => z.1 + 48 < n ∧ z.2 + 14 < n) =
        Finset.range (n - 48) ×ˢ Finset.range (n - 14) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp only [Finset.card_product, Finset.card_range]
