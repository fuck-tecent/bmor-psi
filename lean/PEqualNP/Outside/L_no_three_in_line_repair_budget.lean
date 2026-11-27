import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_repair_budget :
    ∀ (T:Finset (Finset (ℕ×ℕ))) (D:Finset (ℕ×ℕ)) (f:Finset (ℕ×ℕ)→ℕ×ℕ), (∀ A∈T,f A∈A ∧ f A∈D) → (∀ p∈D,2≤(T.filter (fun A => f A=p)).card) → 2*D.card≤T.card := by
  intro T D f h1 h2
  calc 2 * D.card = ∑ p ∈ D, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ D, (T.filter (fun A => f A = p)).card := Finset.sum_le_sum (fun p hp => h2 p hp)
    _ = T.card := (Finset.card_eq_sum_card_fiberwise (fun A hA => (h1 A hA).2)).symm
