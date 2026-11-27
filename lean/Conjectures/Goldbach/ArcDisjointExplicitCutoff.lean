import Mathlib

private lemma quartic_growth (k : ℕ) (hk : 19 ≤ k) :
    2 * k ^ 4 + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkR : (19 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by linarith
    have hquarticR : ((k : ℝ) + 1) ^ 4 ≤ 2 * (k : ℝ) ^ 4 := by
      have hquot : ((k : ℝ) + 1) / (k : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hkpos]
        linarith
      have hpow : (((k : ℝ) + 1) / (k : ℝ)) ^ 4 ≤ ((11 : ℝ) / 10) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hquot 4
      have htwo : ((11 : ℝ) / 10) ^ 4 ≤ 2 := by norm_num
      have hkey : (((k : ℝ) + 1) ^ 4) / (k : ℝ) ^ 4 ≤ 2 := by
        rw [← div_pow]
        exact hpow.trans htwo
      have hmul := mul_le_mul_of_nonneg_right hkey (pow_nonneg hkpos.le 4)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 4 hkpos.ne')] at hmul
    have hquartic : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
      exact_mod_cast hquarticR
    calc
      2 * (k + 1) ^ 4 + 3 ≤ 4 * k ^ 4 + 3 := by omega
      _ ≤ 2 * (2 * k ^ 4 + 3) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

theorem Conjectures.Goldbach.ArcDisjointExplicitCutoff :
    ∀ n : ℕ, 1000000 ≤ n → 2 * ((Nat.log 2 (n + 2)) ^ 2) ^ 2 < n := by
  intro n hn
  let k := Nat.log 2 (n + 2)
  have hk : 19 ≤ k := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    have hpow : (2 : ℕ) ^ 19 = 524288 := by norm_num
    omega
  have hgrowth : 2 * k ^ 4 + 3 ≤ 2 ^ k := quartic_growth k hk
  have hlogpow : 2 ^ k ≤ n + 2 := by
    exact Nat.pow_log_le_self 2 (by omega)
  have hbudget : 2 * (k ^ 2) ^ 2 + 3 ≤ n + 2 := by
    calc
      2 * (k ^ 2) ^ 2 + 3 = 2 * k ^ 4 + 3 := by ring
      _ ≤ 2 ^ k := hgrowth
      _ ≤ n + 2 := hlogpow
  dsimp [k] at hbudget ⊢
  omega
