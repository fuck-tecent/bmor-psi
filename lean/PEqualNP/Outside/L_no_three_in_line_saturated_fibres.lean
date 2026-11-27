import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_saturated_fibres :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ)));
      ∀ (n : ℕ) (S : Finset (ℕ × ℕ)), valid n S → S.card = 2 * n → ∀ i < n, (S.filter (fun z => z.1 = i)).card = 2 ∧ (S.filter (fun z => z.2 = i)).card = 2 := by
  intro valid n S hv hcard i hi
  have hb : ∀ z ∈ S, z.1 < n ∧ z.2 < n := hv.1
  have hdet := hv.2
  -- Every row holds at most two points.
  have hrow : ∀ i, (S.filter (fun z : ℕ × ℕ => z.1 = i)).card ≤ 2 := by
    intro x
    by_contra hlt
    have h3 : 2 < (S.filter (fun z : ℕ × ℕ => z.1 = x)).card := by omega
    obtain ⟨a, ha, b, hb', c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have hbS : b ∈ S := (Finset.mem_filter.mp hb').1
    have hcS : c ∈ S := (Finset.mem_filter.mp hc').1
    have hxa : a.1 = x := (Finset.mem_filter.mp ha).2
    have hxb : b.1 = x := (Finset.mem_filter.mp hb').2
    have hxc : c.1 = x := (Finset.mem_filter.mp hc').2
    exact hdet a haS b hbS c hcS hab hac hbc (by rw [hxa, hxb, hxc]; ring)
  -- Every column holds at most two points.
  have hcol : ∀ i, (S.filter (fun z : ℕ × ℕ => z.2 = i)).card ≤ 2 := by
    intro x
    by_contra hlt
    have h3 : 2 < (S.filter (fun z : ℕ × ℕ => z.2 = x)).card := by omega
    obtain ⟨a, ha, b, hb', c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have hbS : b ∈ S := (Finset.mem_filter.mp hb').1
    have hcS : c ∈ S := (Finset.mem_filter.mp hc').1
    have hya : a.2 = x := (Finset.mem_filter.mp ha).2
    have hyb : b.2 = x := (Finset.mem_filter.mp hb').2
    have hyc : c.2 = x := (Finset.mem_filter.mp hc').2
    exact hdet a haS b hbS c hcS hab hac hbc (by rw [hya, hyb, hyc]; ring)
  -- Split the total over rows (and over columns).
  have hsumRow : S.card = ∑ x ∈ Finset.range n, (S.filter (fun z : ℕ × ℕ => z.1 = x)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1) (t := Finset.range n)
      (fun z hz => Finset.mem_range.mpr (hb z hz).1)
  have hsumCol : S.card = ∑ x ∈ Finset.range n, (S.filter (fun z : ℕ × ℕ => z.2 = x)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.2) (t := Finset.range n)
      (fun z hz => Finset.mem_range.mpr (hb z hz).2)
  have key : ∀ f : ℕ → ℕ, (∀ x, f x ≤ 2) → (∑ x ∈ Finset.range n, f x = 2 * n) →
      ∀ i < n, f i = 2 := by
    intro f hf htot j hj
    have hmem : j ∈ Finset.range n := Finset.mem_range.mpr hj
    have hsumeq : (∑ x ∈ Finset.range n, f x) = (∑ x ∈ (Finset.range n).erase j, f x) + f j :=
      (Finset.sum_erase_add (s := Finset.range n) (f := f) hmem).symm
    have hrest : (∑ x ∈ (Finset.range n).erase j, f x) ≤ 2 * ((Finset.range n).erase j).card := by
      have h := Finset.sum_le_sum (s := (Finset.range n).erase j) (f := f)
        (g := fun _ => 2) (fun x _ => hf x)
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
    have hcard' : ((Finset.range n).erase j).card = n - 1 := by
      rw [Finset.card_erase_of_mem hmem, Finset.card_range]
    have hfj : f j ≤ 2 := hf j
    omega
  constructor
  · exact key (fun x => (S.filter (fun z : ℕ × ℕ => z.1 = x)).card) hrow (by rw [← hsumRow, hcard]) i hi
  · exact key (fun x => (S.filter (fun z : ℕ × ℕ => z.2 = x)).card) hcol (by rw [← hsumCol, hcard]) i hi
