import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_15_4 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+30<n ∧ z.2+8<n)).card=(n-30)*(n-8) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+30<n ∧ z.2+8<n))
      = (Finset.range (n-30)) ×ˢ (Finset.range (n-8)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
