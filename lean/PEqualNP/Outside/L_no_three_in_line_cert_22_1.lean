import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_22_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+44<n ∧ z.2+2<n)).card=(n-44)*(n-2) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 44 < n) = Finset.range (n - 44) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 2 < n) = Finset.range (n - 2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+44<n ∧ z.2+2<n))
      = ((Finset.range n).filter (fun x => x+44<n)).product ((Finset.range n).filter (fun x => x+2<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 44)) (Finset.range (n - 2))
