import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.FiniteWeightedSieveRemoveUnit :
    let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); let A := fun (n z : ℕ) => (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n-p))) = ∅); ∀ (n z y : ℕ), 4≤n → (∑ p ∈ A n z, W z y (n-p)) = (∑ p ∈ Finset.filter (fun p => 2≤n-p) (A n z), W z y (n-p)) + (if (n-1).Prime then (2:ℤ) else 0) := by
  intro W A n z y hn
  have hpos : ∀ {p}, p ∈ A n z → 0 < n - p := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hp_le := Finset.mem_range.mp h.1
    by_contra hz
    have he : p = n := by omega
    exact h.2.2.1 (he ▸ dvd_refl p)
  have hq (q : ℕ) (hq : q.Prime) : ¬ q ∣ (1 : ℕ) := by
    intro h
    exact hq.ne_one (Nat.dvd_one.mp h)
  have hq2 (q : ℕ) (hq' : q.Prime) : ¬ q ^ 2 ∣ (1 : ℕ) := by
    intro h
    exact hq q hq' (dvd_trans (by rw [pow_two]; exact dvd_mul_right q q) h)
  have hw : W z y 1 = 2 := by
    let P := (Finset.Ico z y).filter Nat.Prime
    have he₁ : P.filter (fun p => p ∣ (1 : ℕ)) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun p hp =>
        hq p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2 (Finset.mem_filter.mp hp).2
    have he₂ : P.filter (fun p => p ^ 2 ∣ (1 : ℕ)) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun p hp =>
        hq2 p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2 (Finset.mem_filter.mp hp).2
    change (2 : ℤ) - ↑(P.filter (fun p => p ∣ (1 : ℕ))).card -
      ↑(P.filter (fun p => p ^ 2 ∣ (1 : ℕ))).card = 2
    rw [he₁, he₂]
    rfl
  have hsub : n - (n - 1) = 1 := by omega
  have hsmall (p : ℕ) : p ∈ (A n z).filter (fun p => ¬ 2 ≤ n - p) ↔
      p = n - 1 ∧ (n - 1).Prime := by
    constructor
    · intro hp
      obtain ⟨ha, hb⟩ := Finset.mem_filter.mp hp
      have h := hpos ha
      have he : p = n - 1 := by omega
      exact ⟨he, he ▸ (Finset.mem_filter.mp ha).2.1⟩
    · rintro ⟨rfl, hp⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, ?_, ?_⟩, by simp [hsub]⟩
      · intro hd
        have hone : n - 1 ∣ 1 := by
          have hadd : n - 1 + 1 = n := by omega
          exact (Nat.dvd_add_iff_right (dvd_refl (n - 1))).mpr (hadd ▸ hd)
        exact hq (n - 1) hp hone
      · rw [hsub]
        exact Finset.eq_empty_iff_forall_notMem.mpr fun q h =>
          hq q (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp h).2.2
  have hs : (∑ p ∈ (A n z).filter (fun p => ¬ 2 ≤ n - p), W z y (n - p)) =
      (if (n - 1).Prime then (2 : ℤ) else 0) := by
    by_cases hp : (n - 1).Prime
    · have he : (A n z).filter (fun p => ¬ 2 ≤ n - p) = {n - 1} := by
        ext p
        rw [hsmall, Finset.mem_singleton]
        exact and_iff_left hp
      rw [he, Finset.sum_singleton, hsub, hw, ite_eq_left hp]
    · have he : (A n z).filter (fun p => ¬ 2 ≤ n - p) = ∅ := by
        ext p
        rw [hsmall]
        simp [hp]
      rw [he, Finset.sum_empty, ite_eq_right hp]
  rw [← Finset.sum_filter_add_sum_filter_not (A n z) (fun p => 2 ≤ n - p)
    (fun p => W z y (n - p)), hs]
