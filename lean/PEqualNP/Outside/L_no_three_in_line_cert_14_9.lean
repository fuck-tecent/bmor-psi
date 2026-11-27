import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_14_9 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+28<n ∧ z.2+18<n)).card=(n-28)*(n-18) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 28 < n) = Finset.range (n - 28) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 18 < n) = Finset.range (n - 18) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+28<n ∧ z.2+18<n))
      = ((Finset.range n).filter (fun x => x+28<n)).product ((Finset.range n).filter (fun x => x+18<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 28)) (Finset.range (n - 18))
