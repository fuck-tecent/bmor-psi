import Mathlib

namespace PEqualNP.Outside

theorem L_no_three_in_line_grid_upper_bound :
    ∀ (n : ℕ) (S : Finset (ℕ × ℕ)),
      (∀ p ∈ S, p.1 < n ∧ p.2 < n) →
        (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
          ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠
            ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))) →
          S.card ≤ 2 * n := by
  intro n S hgrid hgen
  have hfib : ∀ x ∈ Finset.range n,
      (S.filter (fun q : ℕ × ℕ => q.1 = x)).card ≤ 2 := by
    intro x _
    by_contra hle
    have htwo : 2 < (S.filter (fun q : ℕ × ℕ => q.1 = x)).card := not_le.1 hle
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 htwo
    have haS : a ∈ S := (Finset.mem_filter.1 ha).1
    have hbS : b ∈ S := (Finset.mem_filter.1 hb).1
    have hcS : c ∈ S := (Finset.mem_filter.1 hc).1
    have hax : a.1 = x := (Finset.mem_filter.1 ha).2
    have hbx : b.1 = x := (Finset.mem_filter.1 hb).2
    have hcx : c.1 = x := (Finset.mem_filter.1 hc).2
    have hb1 : b.1 = a.1 := by rw [hbx, hax]
    have hc1 : c.1 = a.1 := by rw [hcx, hax]
    have hval : ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) =
        ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ)) := by
      rw [hb1, hc1]
      simp
    exact hgen a haS b hbS c hcS hab hac hbc hval
  have hmaps : (S : Set (ℕ × ℕ)).MapsTo (fun q : ℕ × ℕ => q.1)
      (↑(Finset.range n) : Set ℕ) := by
    intro p hp
    exact Finset.mem_range.2 (hgrid p hp).1
  have hsum : S.card =
      ∑ x ∈ Finset.range n, (S.filter (fun q : ℕ × ℕ => q.1 = x)).card :=
    Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.range n)
      (f := fun q : ℕ × ℕ => q.1) hmaps
  calc S.card = ∑ x ∈ Finset.range n, (S.filter (fun q : ℕ × ℕ => q.1 = x)).card := hsum
    _ ≤ ∑ x ∈ Finset.range n, 2 := Finset.sum_le_sum hfib
    _ = 2 * n := by
      rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm]

end PEqualNP.Outside
