import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_9 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+18<n)).card=(n-38)*(n-18) := by
  intro n
  have starts :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 38 < n ∧ z.2 + 18 < n) =
        (Finset.range (n - 38)).product (Finset.range (n - 18)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp
