import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_rounding_profile :
    let F := fun n q r : ℕ => (Finset.range (n + 1)).filter (fun k => k % q = r)
    ∀ n q : ℕ, 0 < q →
      let s := (n + 1) % q
      (∑ r ∈ Finset.range q, (((F n q r).card : ℝ) - (n + 1 : ℕ) / (q : ℝ)) ^ 2) =
        (s : ℝ) * ((q : ℝ) - s) / q := by
  intro F n q hq s
  let d := (n + 1) / q
  have hs : s < q := Nat.mod_lt _ hq
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdiv : (↑(n + 1) : ℝ) = (q : ℝ) * d + s := by
    exact_mod_cast (Nat.div_add_mod (n + 1) q).symm
  have hcard (r : ℕ) (hr : r < q) :
      (F n q r).card = d + if r < s then 1 else 0 := by
    simpa only [F, d, s, Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt hr]
      using Nat.count_modEq_card (n + 1) hq r

  -- The first s residue classes contain one additional element.
  let hi : ℝ := ((d : ℝ) + 1 - ↑(n + 1) / (q : ℝ)) ^ 2
  let lo : ℝ := ((d : ℝ) - ↑(n + 1) / (q : ℝ)) ^ 2
  calc
    _ = ∑ r ∈ Finset.range q, (if r < s then hi else lo) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hcard r (Finset.mem_range.mp hr)]
      by_cases h : r < s <;> simp [h, hi, lo]
    _ = (s : ℝ) * hi + ((q - s : ℕ) : ℝ) * lo := by
      conv_lhs => rw [show q = s + (q - s) by omega]
      rw [Finset.sum_range_add]
      congr 1
      · calc
          _ = ∑ _r ∈ Finset.range s, hi := by
            apply Finset.sum_congr rfl
            intro r hr
            exact if_pos (Finset.mem_range.mp hr)
          _ = _ := by simp [nsmul_eq_mul]
      · simp [nsmul_eq_mul]
    _ = _ := by
      dsimp only [hi, lo]
      rw [Nat.cast_sub hs.le, hdiv]
      field_simp [hqr] <;> ring
