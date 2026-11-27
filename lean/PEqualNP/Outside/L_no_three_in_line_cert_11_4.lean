import Mathlib

private theorem countGridStarts (a b : ℕ) :
    ∀ n : ℕ, (((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + a < n ∧ z.2 + b < n)).card = (n - a) * (n - b) := by
  intro n
  have h : ((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + a < n ∧ z.2 + b < n) =
      (Finset.range (n - a)).product (Finset.range (n - b)) := by
    ext z
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    omega
  rw [h]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]

theorem PEqualNP.Outside.L_no_three_in_line_cert_11_4 :
    ∀ n : ℕ, (((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + 22 < n ∧ z.2 + 8 < n)).card = (n - 22) * (n - 8) :=
  countGridStarts 22 8
