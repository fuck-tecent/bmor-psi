import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_21_10 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+42<n ∧ z.2+20<n)).card=(n-42)*(n-20) := by
  intro n
  change ((Finset.range n ×ˢ Finset.range n).filter _).card = _
  have starts :
      (Finset.range n ×ˢ Finset.range n).filter
          (fun z => z.1 + 42 < n ∧ z.2 + 20 < n) =
        Finset.range (n - 42) ×ˢ Finset.range (n - 20) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp only [Finset.card_product, Finset.card_range]
