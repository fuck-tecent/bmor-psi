import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_neighbor_odd_support :
    ∀ (n r a b : ℕ), 8 ≤ n → Even n → ¬ Even r → Nat.Prime a → Nat.Prime b → n < a^3 → n < b^3 → a+b ≠ n+r ∧ a+b ≠ n-r := by
  intro n r a b hn hneven hr ha hb hca hcb
  have residue {p : ℕ} (hp : p.Prime) (hc : n < p^3) : p % 2 = 1 := by
    apply hp.eq_two_or_odd.resolve_left
    intro h
    subst p
    norm_num at hc
    omega
  have hpa := residue ha hca
  have hpb := residue hb hcb
  have hpos := ha.pos
  rw [Nat.even_iff] at hneven hr
  constructor
  · omega
  · by_cases hrn : r ≤ n
    · omega
    · rw [Nat.sub_eq_zero_of_le (by omega : n ≤ r)]
      omega
