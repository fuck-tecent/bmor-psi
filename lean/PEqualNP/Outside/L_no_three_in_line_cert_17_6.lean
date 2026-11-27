import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_17_6 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+12<n)).card=(n-34)*(n-12) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 34 < n) = Finset.range (n - 34) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 12 < n) = Finset.range (n - 12) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+12<n))
      = ((Finset.range n).filter (fun x => x+34<n)).product ((Finset.range n).filter (fun x => x+12<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 34)) (Finset.range (n - 12))
