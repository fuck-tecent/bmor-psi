import Mathlib

open Finset
namespace DyadicWordCount

private def weight (t k : ℕ) : ℕ :=
  (1000*t).choose k * 17^k * 183^(1000*t-k)

private theorem adjacent {t k : ℕ} (hk : k < 1000*t) :
    weight t (k+1) * ((k+1)*183) = weight t k * ((1000*t-k)*17) := by
  have hs : 1000*t-k = (1000*t-(k+1))+1 := by omega
  have he : 183^(1000*t-k) = (183:ℕ)^(1000*t-(k+1))*183 := by
    rw [hs, pow_succ]
  dsimp only [weight]
  rw [he, pow_succ 17]
  calc
    _ = ((1000*t).choose (k+1)*(k+1)) * (17^k*17*183^(1000*t-(k+1))*183) := by ring
    _ = _ := by rw [Nat.choose_succ_right_eq]; ring

private theorem peak (t k : ℕ) (hk : k ≤ 1000*t) : weight t k ≤ weight t (85*t) := by
  have up (a : ℕ) (ha : a < 85*t) : weight t a ≤ weight t (a+1) := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (a+1)*183)).mp
    rw [adjacent (by omega : a < 1000*t)]
    exact Nat.mul_le_mul_left _ (by omega)
  have down (a : ℕ) (ha : 85*t ≤ a) (hB : a < 1000*t) : weight t (a+1) ≤ weight t a := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (a+1)*183)).mp
    rw [adjacent hB]
    exact Nat.mul_le_mul_left _ (by omega)
  by_cases h : k ≤ 85*t
  · have climb (d : ℕ) (hd : k+d ≤ 85*t) : weight t k ≤ weight t (k+d) := by
      induction d with
      | zero => simp
      | succ d ih => exact (ih (by omega)).trans (up (k+d) (by omega))
    simpa [Nat.add_sub_of_le h] using climb (85*t-k) (by omega)
  · have descend (d : ℕ) (hd : 85*t+d ≤ 1000*t) : weight t (85*t+d) ≤ weight t (85*t) := by
      induction d with
      | zero => simp
      | succ d ih => exact (down (85*t+d) (by omega) (by omega)).trans (ih (by omega))
    simpa [Nat.add_sub_of_le (by omega : 85*t ≤ k)] using descend (k-85*t) (by omega)

private theorem mode_bound (t : ℕ) :
    200^(1000*t) ≤ (1000*t+1)*weight t (85*t) := by
  calc
    (200:ℕ)^(1000*t) = (17+183:ℕ)^(1000*t) := rfl
    _ = ∑ k ∈ range (1000*t+1), weight t k := by
      rw [add_pow]
      apply sum_congr rfl
      intro k hk
      simp only [weight, Nat.cast_id]
      ring
    _ ≤ ∑ _k ∈ range (1000*t+1), weight t (85*t) :=
      sum_le_sum fun k hk => peak t k (by simpa using Nat.le_of_lt_succ (mem_range.mp hk))
    _ = _ := by simp

/-- There are at least 2^(419t)/(1000t+1) ways to place exactly 85t transitions. -/
theorem fixed_transition_entropy (t : ℕ) :
    2^(419*t) ≤ (1000*t+1) * (1000*t).choose (85*t) := by
  have cert : (2:ℕ)^419*17^85*183^915 ≤ 200^1000 := by decide +kernel
  have raised := Nat.pow_le_pow_left cert t
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul] at raised
  have hb := mode_bound t
  unfold weight at hb
  have hsub : 1000*t - 85*t = 915*t := by omega
  rw [hsub] at hb
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (17:ℕ)^(85*t)*183^(915*t))).mp
  calc
    _ = 2^(419*t)*17^(85*t)*183^(915*t) := by ring
    _ ≤ _ := raised.trans hb
    _ = _ := by ring

end DyadicWordCount

theorem Conjectures.Cuts.Taskb02f1cb99d942089048bdeec : (∀ (x1 : ℕ), (2 : ℕ) ^ ((419 : ℕ) * x1) ≤ ((1000 : ℕ) * x1 + (1 : ℕ)) * ((1000 : ℕ) * x1).choose ((85 : ℕ) * x1)) :=
  DyadicWordCount.fixed_transition_entropy
