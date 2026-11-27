import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_23_2 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+46<n ∧ z.2+4<n)).card=(n-46)*(n-4) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 46 < n) = Finset.range (n - 46) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 4 < n) = Finset.range (n - 4) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+46<n ∧ z.2+4<n))
      = ((Finset.range n).filter (fun x => x+46<n)).product ((Finset.range n).filter (fun x => x+4<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 46)) (Finset.range (n - 4))
