import Mathlib

theorem PEqualNP.Outside.L_goldbach_primitive_window_powers :
    let B := fun n p : ℕ => (Finset.Icc 1 (Nat.log 2 n)).filter (fun a => n≤3*p^a ∧ 3*p^a≤2*n); ∀ n p : ℕ, 0<n → p.Prime → (B n p).card ≤ (if p=2 then 2 else 1) := by
  dsimp only
  intro n p _ hp
  let S := (Finset.Icc 1 (Nat.log 2 n)).filter (fun a => n ≤ 3 * p^a ∧ 3 * p^a ≤ 2*n)
  let k : ℕ := if p = 2 then 2 else 1
  change S.card ≤ k
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := S.min'_mem hS
    have hlower : n ≤ 3 * p^m := (Finset.mem_filter.mp hm).2.1
    have hp2 := hp.two_le
    have hgrowth : 3 ≤ p^k := by
      by_cases h : p = 2
      · norm_num [k, h]
      · simpa [k, h] using (show 3 ≤ p by omega)
    have hsub : S ⊆ Finset.Ico m (m+k) := by
      intro a ha
      refine Finset.mem_Ico.mpr ⟨S.min'_le a ha, ?_⟩
      by_contra! hgap
      have hupper := (Finset.mem_filter.mp ha).2.2
      have hpos : 0 < p^m := pow_pos hp.pos _
      have hmul : p^m * 3 ≤ p^a := calc
        p^m * 3 ≤ p^m * p^k := Nat.mul_le_mul_left _ hgrowth
        _ = p^(m+k) := (pow_add p m k).symm
        _ ≤ p^a := pow_le_pow_right₀ (by omega) hgap
      omega
    calc
      S.card ≤ (Finset.Ico m (m+k)).card := Finset.card_le_card hsub
      _ = k := by rw [Nat.card_Ico]; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
