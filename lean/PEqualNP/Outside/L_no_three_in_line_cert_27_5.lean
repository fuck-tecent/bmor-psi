import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_27_5 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+54<n ∧ z.2+10<n)).card=(n-54)*(n-10) := by
  intro n
  change ((Finset.range n ×ˢ Finset.range n).filter _).card = _
  have starts :
      (Finset.range n ×ˢ Finset.range n).filter
          (fun z => z.1 + 54 < n ∧ z.2 + 10 < n) =
        Finset.range (n - 54) ×ˢ Finset.range (n - 10) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp only [Finset.card_product, Finset.card_range]
