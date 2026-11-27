import Mathlib

theorem PEqualNP.Outside.L_goldbach_shift_normalized_support :
    ∀ (n : ℕ) (e η : ℝ) (ω : ℕ → ℝ), 0 < n → 0 < e → 0 < η → let W := (Finset.Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0); (∑ m ∈ W, ω m) = 1 → (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((e/2)*(n:ℝ))^2 → 4*(n:ℝ)^(2/3+η) ≤ e^2*(W.card:ℝ) := by
  intro n e η ω hn he hη W hsum hbudget
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcs : (∑ m ∈ W, (1 : ℝ) * ω m) ^ 2 ≤ (∑ m ∈ W, (1 : ℝ) ^ 2) * (∑ m ∈ W, (ω m) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq W (fun _ => (1 : ℝ)) ω
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum, one_pow] at hcs
  have hrpow : (n : ℝ) ^ ((8 : ℝ) / 3 + η) = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3 + η) := by
    rw [← Real.rpow_add hnpos]
    ring_nf
  rw [Real.rpow_two] at hrpow
  have hpos8 : 0 ≤ (n : ℝ) ^ ((8 : ℝ) / 3 + η) := Real.rpow_nonneg hnpos.le _
  have hmul1 : (n : ℝ) ^ ((8 : ℝ) / 3 + η) ≤ (W.card : ℝ) * ((∑ m ∈ W, (ω m) ^ 2) * (n : ℝ) ^ ((8 : ℝ) / 3 + η)) := by
    calc
      (n : ℝ) ^ ((8 : ℝ) / 3 + η) = 1 * (n : ℝ) ^ ((8 : ℝ) / 3 + η) := (one_mul _).symm
      _ ≤ ((W.card : ℝ) * (∑ m ∈ W, (ω m) ^ 2)) * (n : ℝ) ^ ((8 : ℝ) / 3 + η) :=
        mul_le_mul_of_nonneg_right hcs hpos8
      _ = (W.card : ℝ) * ((∑ m ∈ W, (ω m) ^ 2) * (n : ℝ) ^ ((8 : ℝ) / 3 + η)) := mul_assoc _ _ _
  have hcard0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hmul2 : (W.card : ℝ) * ((∑ m ∈ W, (ω m) ^ 2) * (n : ℝ) ^ ((8 : ℝ) / 3 + η)) ≤
      (W.card : ℝ) * ((e / 2 * (n : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hbudget hcard0
  have hcomb : 4 * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((2 : ℝ) / 3 + η)) ≤
      4 * ((W.card : ℝ) * ((e / 2 * (n : ℝ)) ^ 2)) := by
    rw [← hrpow]
    linarith [hmul1.trans hmul2]
  have hn2pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hring : 4 * ((W.card : ℝ) * ((e / 2 * (n : ℝ)) ^ 2)) = (e ^ 2 * (W.card : ℝ)) * (n : ℝ) ^ 2 := by ring
  have hring2 : 4 * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((2 : ℝ) / 3 + η)) = (4 * (n : ℝ) ^ ((2 : ℝ) / 3 + η)) * (n : ℝ) ^ 2 := by ring
  rw [hring, hring2] at hcomb
  exact le_of_mul_le_mul_right hcomb hn2pos
