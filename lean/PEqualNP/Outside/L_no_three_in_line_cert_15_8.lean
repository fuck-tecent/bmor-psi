import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_15_8 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+30<n ∧ z.2+16<n)).card=(n-30)*(n-16) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 30 < n) = Finset.range (n - 30) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 16 < n) = Finset.range (n - 16) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+30<n ∧ z.2+16<n))
      = ((Finset.range n).filter (fun x => x+30<n)).product ((Finset.range n).filter (fun x => x+16<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 30)) (Finset.range (n - 16))
