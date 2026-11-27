import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_11_3 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+22<n ∧ z.2+6<n)).card=(n-22)*(n-6) := by
  intro n
  have e0 : ((Finset.range n).product (Finset.range n)).filter (fun z => z.1+22<n ∧ z.2+6<n)
      = (Finset.range (n-22)).product (Finset.range (n-6)) := by
    ext z
    simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [e0]
  simp [Finset.card_product]
