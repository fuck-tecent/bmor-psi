import Mathlib

open ArithmeticFunction

private theorem windowCard {p : ℕ} (hp : 2 ≤ p) (X : ℝ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (∃ j : ℕ, p^j = k) ∧ X/3 ≤ (k:ℝ) ∧ (k:ℝ) ≤ 2*X/3) :
    s.card ≤ 2 := by
  by_cases h : s.Nonempty
  · let m := s.min' h
    have hm : m ∈ s := s.min'_mem h
    obtain ⟨⟨j, hj⟩, hlo, _⟩ := hs m hm
    have hsub : s ⊆ {m, m*p} := by
      intro k hk
      obtain ⟨⟨e, he⟩, _, hhi⟩ := hs k hk
      have hmk : m ≤ k := s.min'_le k hk
      have hkm : k ≤ 2*m := by
        exact_mod_cast (show (k:ℝ) ≤ 2*(m:ℝ) by linarith)
      by_cases hej : e ≤ j
      · have aux := Nat.pow_le_pow_right (by omega : 0 < p) hej
        rw [he,hj] at aux
        simp [show k = m by omega]
      · have hle : e < j+2 := by
          by_contra! hge
          have aux := Nat.pow_le_pow_right (by omega : 0 < p) hge
          rw [pow_add, hj, he] at aux
          have hpos : 0 < m := hj ▸ pow_pos (by omega) j
          have hsq : 2 < p^2 := by nlinarith [Nat.mul_self_le_mul_self hp]
          have hlt := Nat.mul_lt_mul_of_pos_left hsq hpos
          omega
        have ee : e = j+1 := by omega
        rw [← he, ee, pow_succ, hj]
        simp
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

theorem PEqualNP.Outside.L_goldbach_four_window_bad_base_square :
    ∀ (n : ℕ) (X : ℝ), 2 ≤ n → 0 < X → X ≤ n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k n ∧ X/3 ≤ (k:ℝ) ∧ (k:ℝ) ≤ 2*X/3), (ArithmeticFunction.vonMangoldt k)^2) ≤ 2*(Real.log n)^2 := by
  intro n X hn _ _
  classical
  let S := (Finset.range (n+1)).filter
    (fun k : ℕ => ¬ Nat.Coprime k n ∧ X/3 ≤ (k:ℝ) ∧ (k:ℝ) ≤ 2*X/3)
  let T := S.filter (fun k => IsPrimePow k)
  have hS {k : ℕ} (hk : k ∈ T) :
      (¬ Nat.Coprime k n ∧ X/3 ≤ (k:ℝ) ∧ (k:ℝ) ≤ 2*X/3) ∧ IsPrimePow k := by
    obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hk
    exact ⟨(Finset.mem_filter.mp h1).2, h2⟩
  have maps (k : ℕ) (hk : k ∈ T) : k.minFac ∈ n.divisors := by
    obtain ⟨⟨hnc, _, _⟩, hpp⟩ := hS hk
    have hp := Nat.minFac_prime hpp.ne_one
    have hd : k.minFac ∣ n := by
      by_contra hnd
      have hc := Nat.Coprime.pow_left (k.factorization k.minFac)
        (hp.coprime_iff_not_dvd.mpr hnd)
      rw [hpp.minFac_pow_factorization_eq] at hc
      exact hnc hc
    exact Nat.mem_divisors.mpr ⟨hd,by omega⟩
  have hsum : (∑ k ∈ T, (vonMangoldt k)^2) = ∑ k ∈ S, (vonMangoldt k)^2 := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro k hk hnot
    have hpp : ¬ IsPrimePow k := fun h => hnot (Finset.mem_filter.mpr ⟨hk,h⟩)
    simp [vonMangoldt_eq_zero_iff.mpr hpp]
  change (∑ k ∈ S, (vonMangoldt k)^2) ≤ _
  rw [← hsum, ← Finset.sum_fiberwise_of_maps_to maps]
  calc
    _ ≤ ∑ p ∈ n.divisors, 2 * (vonMangoldt p)^2 := by
      apply Finset.sum_le_sum
      intro p _
      let F := T.filter (fun k => k.minFac = p)
      change (∑ k ∈ F, (vonMangoldt k)^2) ≤ _
      by_cases hF : F.Nonempty
      · obtain ⟨k₀, hk₀⟩ := hF
        obtain ⟨ht₀, heq₀⟩ := Finset.mem_filter.mp hk₀
        have hp : Nat.Prime p := heq₀ ▸ Nat.minFac_prime (hS ht₀).2.ne_one
        have hcard := windowCard hp.two_le X F (by
          intro k hk
          obtain ⟨ht, heq⟩ := Finset.mem_filter.mp hk
          obtain ⟨hw, hpp⟩ := hS ht
          exact ⟨⟨_, heq ▸ hpp.minFac_pow_factorization_eq⟩, hw.2⟩)
        calc
          _ = ∑ _k ∈ F, (vonMangoldt p)^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            obtain ⟨ht, heq⟩ := Finset.mem_filter.mp hk
            rw [vonMangoldt_apply (n := k), ite_eq_left (hS ht).2, heq, vonMangoldt_apply_prime hp]
          _ = (F.card : ℝ) * (vonMangoldt p)^2 := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hF]
    _ ≤ 2 * (Real.log n)^2 := by
      rw [← Finset.mul_sum, ← vonMangoldt_sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => vonMangoldt_nonneg)) (by norm_num)
