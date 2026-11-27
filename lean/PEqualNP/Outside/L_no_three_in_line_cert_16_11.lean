import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_16_11 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+32<n ∧ z.2+22<n)).card=(n-32)*(n-22) := by
  intro n
  have h1 : (Finset.range n).filter (fun x => x + 32 < n) = Finset.range (n - 32) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : (Finset.range n).filter (fun x => x + 22 < n) = Finset.range (n - 22) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hprod : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+32<n ∧ z.2+22<n))
      = ((Finset.range n).filter (fun x => x+32<n)).product ((Finset.range n).filter (fun x => x+22<n)) := by
    ext z
    simp [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [hprod, h1, h2]
  simpa using Finset.card_product (Finset.range (n - 32)) (Finset.range (n - 22))
