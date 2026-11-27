import Mathlib

private lemma mht_tail (L N : ℕ) :
    ∑ k ∈ Finset.range N, (if L ≤ k then 1 / ((k:ℝ) + 1) ^ 2 else 0) ≤
      2 / ((L:ℝ) + 1) - 2 / (((max N L : ℕ) : ℝ) + 1) := by
  induction N with
  | zero =>
    have : ((max 0 L : ℕ) : ℝ) = L := by simp
    rw [this]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases h : L ≤ n
    · rw [if_pos h]
      have e1 : max n L = n := max_eq_left h
      have e2 : max (n + 1) L = n + 1 := max_eq_left (by omega)
      rw [e1] at ih
      rw [e2]
      push_cast
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
      have : 1 / ((n:ℝ) + 1) ^ 2 ≤ 2 / ((n:ℝ) + 1) - 2 / ((n:ℝ) + 1 + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · rw [if_neg h]
      have e1 : max n L = L := max_eq_right (by omega)
      have e2 : max (n + 1) L = L := max_eq_right (by omega)
      rw [e1] at ih
      rw [e2]
      linarith

private lemma mht_tail' (L N : ℕ) :
    ∑ k ∈ Finset.range N, (if L ≤ k then 1 / ((k:ℝ) + 1) ^ 2 else 0) ≤ 2 / ((L:ℝ) + 1) := by
  have := mht_tail L N
  have : 0 ≤ 2 / (((max N L : ℕ) : ℝ) + 1) := by positivity
  linarith

private lemma mht_pt (C t m : ℝ) (L : ℕ) (j : ℤ) (hC : 0 ≤ C) (hm0 : 0 ≤ m)
    (hm : m ≤ C * Real.log (2 + |(Int.floor t : ℝ) + (j:ℝ)|)) (hLj : L ≤ j.natAbs) :
    m / (1 + (j.natAbs : ℝ)) ^ 6 ≤
      C * (Real.log (2 + |t| + (L:ℝ)) + Real.log 2 + 1) / (1 + (L:ℝ)) ^ 4 *
        (1 / ((j.natAbs : ℝ) + 1) ^ 2) := by
  set k := j.natAbs with hk
  have hkL : (L:ℝ) ≤ k := by exact_mod_cast hLj
  have hL0 : (0:ℝ) ≤ L := Nat.cast_nonneg _
  set t' := |t| with ht'
  have ht0 : 0 ≤ t' := abs_nonneg t
  set u := 2 + t' + (L:ℝ) with hu
  have hu2 : 2 ≤ u := by linarith
  have hjk : |(j:ℝ)| = k := by
    rw [hk, Nat.cast_natAbs, Int.cast_abs]
  have hfl1 : (Int.floor t : ℝ) ≤ t := Int.floor_le t
  have hfl2 : t < (Int.floor t : ℝ) + 1 := Int.lt_floor_add_one t
  have habs : |(Int.floor t : ℝ) + (j:ℝ)| ≤ t' + 1 + k := by
    have h1 : |(Int.floor t : ℝ)| ≤ t' + 1 := by
      rw [abs_le]; constructor
      · have := neg_abs_le t; linarith
      · have := le_abs_self t; linarith
    calc |(Int.floor t : ℝ) + (j:ℝ)| ≤ |(Int.floor t : ℝ)| + |(j:ℝ)| := abs_add_le _ _
      _ ≤ t' + 1 + k := by rw [hjk]; linarith
  set B : ℝ := 1 + (L:ℝ) with hB
  have hB1 : 1 ≤ B := by linarith
  set x : ℝ := (k:ℝ) + 1 with hx
  have hxB : B ≤ x := by rw [hB, hx]; linarith
  have hx0 : 0 < x := by linarith
  have hB0 : 0 < B := by linarith
  set y : ℝ := x / B with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hB0]; linarith
  have hv : 2 + |(Int.floor t : ℝ) + (j:ℝ)| ≤ u * (2 * y) := by
    have : 3 + t' + k ≤ u * (2 * y) := by
      rw [hy, ← mul_div_assoc, mul_div_assoc', le_div_iff₀ hB0]
      rw [hu, hB, hx]
      nlinarith
    linarith
  have hpos : 0 < 2 + |(Int.floor t : ℝ) + (j:ℝ)| := by positivity
  have hlog : Real.log (2 + |(Int.floor t : ℝ) + (j:ℝ)|) ≤
      Real.log u + Real.log 2 + y := by
    have h1 := Real.log_le_log hpos hv
    rw [Real.log_mul (by linarith) (by positivity), Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < y)
    linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set a := Real.log u + Real.log 2 with ha
  have ha0 : 0 ≤ a := by linarith
  have hmy : m ≤ C * (a + y) := by
    refine hm.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hay : a + y ≤ (a + 1) * y ^ 4 := by
    have h4 : y ≤ y ^ 4 := by
      calc y = y * 1 := by ring
        _ ≤ y * y ^ 3 := by gcongr; exact one_le_pow₀ hy1
        _ = y ^ 4 := by ring
    have h5 : 1 ≤ y ^ 4 := one_le_pow₀ hy1
    nlinarith
  have e1 : (1 + (k:ℝ)) = x := by rw [hx]; ring
  rw [e1]
  have hx6 : 0 < x ^ 6 := by positivity
  have e2 : y ^ 4 = x ^ 4 / B ^ 4 := by rw [hy, div_pow]
  calc m / x ^ 6 ≤ C * ((a + 1) * y ^ 4) / x ^ 6 := by
        apply div_le_div_of_nonneg_right _ hx6.le
        calc m ≤ C * (a + y) := hmy
          _ ≤ C * ((a + 1) * y ^ 4) := mul_le_mul_of_nonneg_left hay hC
    _ = C * (a + 1) / B ^ 4 * (1 / x ^ 2) := by
        rw [e2]; field_simp
    _ = _ := by rw [ha, hB]

private lemma mht_fin (c : ℝ) (hc : 0 ≤ c) (L : ℕ) (s : Finset ℤ) :
    ∑ j ∈ s, (if L ≤ j.natAbs then c * (1 / ((j.natAbs : ℝ) + 1) ^ 2) else 0) ≤
      4 * c / ((L:ℝ) + 1) := by
  set h : ℕ → ℝ := fun k => if L ≤ k then c * (1 / ((k : ℝ) + 1) ^ 2) else 0 with hh
  have hnn : ∀ k, 0 ≤ h k := by
    intro k; simp only [hh]; split_ifs <;> positivity
  have e : ∑ j ∈ s, (if L ≤ j.natAbs then c * (1 / ((j.natAbs : ℝ) + 1) ^ 2) else 0) =
      ∑ j ∈ s, h j.natAbs := rfl
  rw [e, Finset.sum_comp]
  set N := (s.image Int.natAbs).sup id + 1 with hN
  have hsub : s.image Int.natAbs ⊆ Finset.range N := by
    intro k hk
    rw [Finset.mem_range, hN]
    have := Finset.le_sup (f := id) hk
    simp only [id] at this
    omega
  have hfib : ∀ k ∈ s.image Int.natAbs,
      ((s.filter (fun j => j.natAbs = k)).card • h k) ≤ 2 * h k := by
    intro k _
    have hc2 : (s.filter (fun j => j.natAbs = k)).card ≤ 2 := by
      have hs : s.filter (fun j => j.natAbs = k) ⊆ {(k:ℤ), -(k:ℤ)} := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hs).trans (Finset.card_le_two)
    rw [nsmul_eq_mul]
    have : ((s.filter (fun j => j.natAbs = k)).card : ℝ) ≤ 2 := by exact_mod_cast hc2
    exact mul_le_mul_of_nonneg_right this (hnn k)
  calc ∑ k ∈ s.image Int.natAbs, (s.filter (fun j => j.natAbs = k)).card • h k
      ≤ ∑ k ∈ s.image Int.natAbs, 2 * h k := Finset.sum_le_sum hfib
    _ = 2 * ∑ k ∈ s.image Int.natAbs, h k := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ k ∈ Finset.range N, h k := by
        gcongr

    _ = 2 * c * ∑ k ∈ Finset.range N, (if L ≤ k then 1 / ((k:ℝ) + 1) ^ 2 else 0) := by
        have : ∑ k ∈ Finset.range N, h k =
            c * ∑ k ∈ Finset.range N, (if L ≤ k then 1 / ((k:ℝ) + 1) ^ 2 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [hh]; split_ifs <;> ring
        rw [this, mul_assoc]
    _ ≤ 2 * c * (2 / ((L:ℝ) + 1)) := by
        gcongr
        exact mht_tail' L N
    _ = 4 * c / ((L:ℝ) + 1) := by ring

theorem Conjectures.TwinPrimes.MovingHeightMellinTail :
    ∀ C : ℝ, 0 ≤ C → ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ) (L : ℕ) (m : ℤ → ℝ), (∀ j : ℤ, 0 ≤ m j ∧ m j ≤ C*Real.log (2+|(Int.floor t : ℝ)+(j:ℝ)|)) → (∑' j : ℤ, if L ≤ j.natAbs then m j/(1+(j.natAbs:ℝ))^6 else 0) ≤ K*Real.log (2+|t|+(L:ℝ))/(1+(L:ℝ))^5 := by
  intro C hC
  refine ⟨16 * C, by positivity, ?_⟩
  intro t L m hm
  set u := 2 + |t| + (L:ℝ) with hu
  have hL0 : (0:ℝ) ≤ L := Nat.cast_nonneg _
  have hu2 : 2 ≤ u := by have := abs_nonneg t; linarith
  have hlu : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu2
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set c := C * (Real.log u + Real.log 2 + 1) / (1 + (L:ℝ)) ^ 4 with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 0 ≤ Real.log u := by linarith
    have : 0 ≤ Real.log 2 := by linarith
    positivity
  have hB0 : (0:ℝ) < (L:ℝ) + 1 := by linarith
  have hpt : ∀ j : ℤ, (if L ≤ j.natAbs then m j/(1+(j.natAbs:ℝ))^6 else 0) ≤
      (if L ≤ j.natAbs then c * (1 / ((j.natAbs : ℝ) + 1) ^ 2) else 0) := by
    intro j
    by_cases h : L ≤ j.natAbs
    · rw [if_pos h, if_pos h]
      exact mht_pt C t (m j) L j hC (hm j).1 (hm j).2 h
    · rw [if_neg h, if_neg h]
  have hnn : 0 ≤ fun j : ℤ => (if L ≤ j.natAbs then m j/(1+(j.natAbs:ℝ))^6 else 0) := by
    intro j
    simp only [Pi.zero_apply]
    split_ifs
    · exact div_nonneg (hm j).1 (by positivity)
    · exact le_refl _
  have hfin : ∀ s : Finset ℤ, ∑ j ∈ s, (if L ≤ j.natAbs then m j/(1+(j.natAbs:ℝ))^6 else 0) ≤
      4 * c / ((L:ℝ) + 1) := fun s =>
    (Finset.sum_le_sum (fun j _ => hpt j)).trans (mht_fin c hc0 L s)
  refine (Real.tsum_le_of_sum_le hnn hfin).trans ?_
  have h4 : Real.log u + Real.log 2 + 1 ≤ 4 * Real.log u := by linarith
  have hB : (0:ℝ) < 1 + (L:ℝ) := by linarith
  have e : 4 * c / ((L:ℝ) + 1) = 4 * C * (Real.log u + Real.log 2 + 1) / (1 + (L:ℝ)) ^ 5 := by
    rw [hc]; field_simp; ring
  rw [e]
  have : 4 * C * (Real.log u + Real.log 2 + 1) ≤ 16 * C * Real.log u := by nlinarith
  exact div_le_div_of_nonneg_right this (by positivity)
