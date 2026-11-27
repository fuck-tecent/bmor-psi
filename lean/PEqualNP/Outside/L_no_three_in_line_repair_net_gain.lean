import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_repair_net_gain :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∀ a b:ℝ,b<a → (∀ B:ℕ,∃ n>B,∃ U D:Finset (ℕ×ℕ),valid n (U \ D) ∧ (3/2+a)*(n:ℝ)≤U.card ∧ (D.card:ℝ)≤b*n) → ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ S : Finset (ℕ × ℕ), valid n S ∧ (3/2+d)*(n:ℝ) ≤ (S.card:ℝ) := by
  intro valid a b hba h
  refine ⟨a - b, sub_pos.mpr hba, ?_⟩
  intro B
  obtain ⟨n, hn, U, D, hvalid, hU, hD⟩ := h B
  refine ⟨n, hn, U \ D, hvalid, ?_⟩
  have hcard : (U.card : ℝ) ≤ ((U \ D).card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card (s := U) (t := D)
  calc
    (3 / 2 + (a - b)) * (n : ℝ) = (3 / 2 + a) * (n : ℝ) - b * (n : ℝ) := by ring
    _ ≤ (U.card : ℝ) - (D.card : ℝ) := sub_le_sub hU hD
    _ ≤ ((U \ D).card : ℝ) := sub_le_iff_le_add.mpr hcard
