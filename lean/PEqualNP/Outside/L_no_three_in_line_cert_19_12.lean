import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_12 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+24<n)).card=(n-38)*(n-24) := by
  intro n
  change ((Finset.range n ×ˢ Finset.range n).filter _).card = _
  have starts :
      (Finset.range n ×ˢ Finset.range n).filter
          (fun z => z.1 + 38 < n ∧ z.2 + 24 < n) =
        Finset.range (n - 38) ×ˢ Finset.range (n - 24) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp only [Finset.card_product, Finset.card_range]
