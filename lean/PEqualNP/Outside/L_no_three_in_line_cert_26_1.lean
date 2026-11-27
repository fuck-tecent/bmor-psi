import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_26_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+52<n ∧ z.2+2<n)).card=(n-52)*(n-2) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 52 < n) = Finset.range (n - 52) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 2 < n) = Finset.range (n - 2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+52<n ∧ z.2+2<n))
      = ((Finset.range n).filter (fun x => x+52<n)).product ((Finset.range n).filter (fun x => x+2<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 52)) (Finset.range (n - 2))
