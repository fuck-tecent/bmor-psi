import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_4 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+8<n)).card=(n-38)*(n-8) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 38 < n) = Finset.range (n - 38) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 8 < n) = Finset.range (n - 8) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+8<n))
      = ((Finset.range n).filter (fun x => x+38<n)).product ((Finset.range n).filter (fun x => x+8<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 38)) (Finset.range (n - 8))
