import Mathlib

private lemma seven_even_pair (k : ℕ) (u z : ℤ)
    (h : u ^ 2 + 3 * z ^ 2 = 28 * (4 : ℤ) ^ (k + 1)) : Even u ∧ Even z := by
  have h8 : (8 : ℤ) ∣ u ^ 2 + 3 * z ^ 2 := by
    rw [h]
    refine ⟨14 * 4 ^ k, ?_⟩
    rw [pow_succ]
    ring
  have hz : Even z := by
    rcases Int.even_or_odd z with hz | hz
    · exact hz
    · exfalso
      obtain ⟨b, rfl⟩ := hz
      obtain ⟨t, ht⟩ := h8
      obtain ⟨c, hc⟩ := Int.even_mul_succ_self b
      have hb2 : b ^ 2 + b = 2 * c := by nlinarith
      have hu2 : u ^ 2 = 8 * t - 24 * c - 3 := by nlinarith
      rcases Int.even_or_odd u with hu | hu
      · obtain ⟨a, rfl⟩ := hu
        have h4 : 4 * (a ^ 2 - 2 * t + 6 * c) = -3 := by nlinarith
        omega
      · obtain ⟨a, rfl⟩ := hu
        obtain ⟨d, hd⟩ := Int.even_mul_succ_self a
        have ha : a ^ 2 + a = 2 * d := by nlinarith
        have h4 : a ^ 2 + a = 2 * t - 6 * c - 1 := by nlinarith
        omega
  refine ⟨?_, hz⟩
  obtain ⟨z', rfl⟩ := hz
  have h4 : (4 : ℤ) ∣ u ^ 2 := by
    refine ⟨7 * (4 : ℤ) ^ (k + 1) - 3 * z' ^ 2, by nlinarith⟩
  have hsq : Even (u ^ 2) := by
    obtain ⟨w, hw⟩ := h4
    exact ⟨2 * w, by rw [hw]; ring⟩
  exact (Int.even_pow.mp hsq).1

private lemma seven_classify : ∀ (k : ℕ) (u z : ℤ), 0 ≤ u → 0 ≤ z →
    u ^ 2 + 3 * z ^ 2 = 28 * (4 : ℤ) ^ k →
    (u = 5 * (2 : ℤ) ^ k ∧ z = (2 : ℤ) ^ k) ∨
    (u = 4 * (2 : ℤ) ^ k ∧ z = 2 * (2 : ℤ) ^ k) ∨
    (u = (2 : ℤ) ^ k ∧ z = 3 * (2 : ℤ) ^ k) := by
  intro k
  induction k with
  | zero =>
    intro u z hu hz h
    norm_num at h
    have hz3 : z ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have h4 : (4 : ℤ) ≤ z := by omega
      nlinarith [sq_nonneg u]
    have hu5 : u ≤ 5 := by
      by_contra hlt
      push Not at hlt
      have h6 : (6 : ℤ) ≤ u := by omega
      nlinarith [sq_nonneg z]
    interval_cases z <;> interval_cases u <;> norm_num at h
    all_goals norm_num
  | succ k ih =>
    intro u z hu hz h
    obtain ⟨hue, hze⟩ := seven_even_pair k u z h
    rw [even_iff_two_dvd] at hue hze
    obtain ⟨u', rfl⟩ := hue
    obtain ⟨z', rfl⟩ := hze
    have hu' : 0 ≤ u' := by omega
    have hz' : 0 ≤ z' := by omega
    have h' : u' ^ 2 + 3 * z' ^ 2 = 28 * (4 : ℤ) ^ k := by
      have hp : (4 : ℤ) ^ (k + 1) = (4 : ℤ) ^ k * 4 := pow_succ 4 k
      nlinarith
    rcases ih u' z' hu' hz' h' with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      exact ⟨by rw [e1, pow_succ]; ring, by rw [e2, pow_succ]; ring⟩
    · right; left
      exact ⟨by rw [e1, pow_succ]; ring, by rw [e2, pow_succ]; ring⟩
    · right; right
      exact ⟨by rw [e1, pow_succ]; ring, by rw [e2, pow_succ]; ring⟩

theorem PEqualNP.Outside.L_hash_collision_lab_seven_thresholds :
    ∀ (k : ℕ) (z : ℤ), (∃ x y : ℤ, x ≤ y ∧ y ≤ z ∧ x + y + z = 0 ∧ x ^ 2 + x * y + y ^ 2 = 7 * (4 : ℤ) ^ k) ↔ z = 2 * (2 : ℤ) ^ k ∨ z = 3 * (2 : ℤ) ^ k := by
  intro k z
  constructor
  · rintro ⟨x, y, hxy, hyz, hsum, hnorm⟩
    have hz0 : 0 ≤ z := by linarith
    have hu0 : 0 ≤ y - x := by linarith
    have hEq : (y - x) ^ 2 + 3 * z ^ 2 = 28 * (4 : ℤ) ^ k := by
      have hid : 4 * (x ^ 2 + x * y + y ^ 2) = (y - x) ^ 2 + 3 * (x + y) ^ 2 := by ring
      have hs : x + y = -z := by linarith
      have hsq : (x + y) ^ 2 = z ^ 2 := by rw [hs]; ring
      nlinarith [hid, hsq]
    have hle : y - x ≤ 3 * z := by linarith
    rcases seven_classify k (y - x) z hu0 hz0 hEq with ⟨hu5, hz1⟩ | ⟨hu4, hz2⟩ | ⟨hu1, hz3⟩
    · exfalso
      have hpos : 0 < (2 : ℤ) ^ k := pow_pos (by norm_num) k
      nlinarith
    · left
      exact hz2
    · right
      exact hz3
  · rintro (hz | hz)
    · rw [hz]
      refine ⟨-3 * (2 : ℤ) ^ k, (2 : ℤ) ^ k, ?_, ?_, ?_, ?_⟩
      · have hpos : 0 < (2 : ℤ) ^ k := pow_pos (by norm_num) k
        omega
      · have hpos : 0 < (2 : ℤ) ^ k := pow_pos (by norm_num) k
        omega
      · ring
      · have h4 : ((2 : ℤ) ^ k) ^ 2 = (4 : ℤ) ^ k := by
          rw [sq, ← mul_pow]
          norm_num
        nlinarith [h4]
    · rw [hz]
      refine ⟨-2 * (2 : ℤ) ^ k, -(2 : ℤ) ^ k, ?_, ?_, ?_, ?_⟩
      · have hpos : 0 < (2 : ℤ) ^ k := pow_pos (by norm_num) k
        omega
      · have hpos : 0 < (2 : ℤ) ^ k := pow_pos (by norm_num) k
        omega
      · ring
      · have h4 : ((2 : ℤ) ^ k) ^ 2 = (4 : ℤ) ^ k := by
          rw [sq, ← mul_pow]
          norm_num
        nlinarith [h4]
