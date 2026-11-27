import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_11_9 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+22<n ∧ z.2+18<n)).card=(n-22)*(n-18) := by
  intro n
  have e0 : ((Finset.range n).product (Finset.range n)).filter (fun z => z.1+22<n ∧ z.2+18<n)
      = (Finset.range (n-22)).product (Finset.range (n-18)) := by
    ext z
    simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [e0]
  simp [Finset.card_product]
