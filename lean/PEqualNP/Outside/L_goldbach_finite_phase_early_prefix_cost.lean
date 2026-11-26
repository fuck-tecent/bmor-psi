import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_finite_phase_early_prefix_cost :
    let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); let T : ℕ := 8000000000; ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 4000000000000000000 ≤ n → |β| ≤ 105/((q:ℝ)*n) → J q a 0 T β ≤ (n:ℝ)/10^12 := by

  dsimp only
  intro q a n β hq hqmax ha hcop hn hβ
  let T : ℕ := 8000000000
  let D : ℕ → ℝ := fun m => (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (m:ℝ)/Nat.totient q
  change 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico 0 T, |D m|) ≤ (n:ℝ)/10^12
  have hT : (T:ℝ) ≤ (2:ℝ)^34 := by norm_num [T]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    linarith
  have hlog : Real.log (T:ℝ) ≤ 50 := by
    calc
      _ ≤ Real.log ((2:ℝ)^34) := Real.log_le_log (by norm_num [T]) hT
      _ = (34:ℝ)*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 50 := by linarith
  have hΛ (k : ℕ) (hk : k ≤ T) : ArithmeticFunction.vonMangoldt k ≤ 50 := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · exact ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk)).trans hlog)
  have htot : (1:ℝ) ≤ Nat.totient q := by
    exact_mod_cast (show 1 ≤ Nat.totient q from Nat.totient_pos.mpr (by omega))
  have hD (m : ℕ) (hm : m ∈ Finset.Ico 0 T) : |D m| ≤ 51*(T:ℝ) := by
    have hmt : m < T := (Finset.mem_Ico.mp hm).2
    let s := (Finset.range (m+1)).filter (fun k => k % q=a % q)
    have hs : s.card ≤ T := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using (show m+1 ≤ T by omega))
    have hsum0 : 0 ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hsum : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤ 50*(T:ℝ) := by
      calc
        _ ≤ ∑ k ∈ s, (50:ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkm := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact hΛ k (by omega)
        _ = (s.card:ℝ)*50 := by simp
        _ ≤ _ := by
          have hh : (s.card:ℝ) ≤ T := by exact_mod_cast hs
          linarith
    have hmR : (m:ℝ) ≤ T := by exact_mod_cast hmt.le
    have hdiv0 : 0 ≤ (m:ℝ)/Nat.totient q := by positivity
    have hdiv : (m:ℝ)/Nat.totient q ≤ (T:ℝ) := by
      apply (div_le_iff₀ (by linarith : (0:ℝ)<Nat.totient q)).mpr
      calc
        _ ≤ (T:ℝ) := hmR
        _ = (T:ℝ)*1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htot (by positivity)
    change |(∑ k ∈ s, ArithmeticFunction.vonMangoldt k)-(m:ℝ)/Nat.totient q| ≤ _
    rw [abs_le]
    have hT0 : (0:ℝ) ≤ (T:ℝ) := by positivity
    constructor
    · linarith only [hsum0, hdiv, hT0]
    · calc
        _ ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k := sub_le_self _ hdiv0
        _ ≤ 50*(T:ℝ) := hsum
        _ ≤ 51*(T:ℝ) := mul_le_mul_of_nonneg_right (by norm_num) hT0
  have hS : (∑ m ∈ Finset.Ico 0 T, |D m|) ≤ 51*(T:ℝ)^2 := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico 0 T, 51*(T:ℝ) := Finset.sum_le_sum hD
      _ = _ := by simp [Nat.card_Ico]; ring
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast (show 1≤q by omega)
  have hden : (4000000000000000000:ℝ) ≤ (q:ℝ)*n := by
    calc
      _ ≤ (n:ℝ) := hnR
      _ = 1*(n:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hqR (by positivity)
  have hβ' : |β| ≤ (105:ℝ)/4000000000000000000 :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden)
  have hpi : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  calc
    _ ≤ 8*((105:ℝ)/4000000000000000000)*(51*(T:ℝ)^2) := by
      exact mul_le_mul (mul_le_mul hpi hβ' (abs_nonneg _) (by norm_num))
        hS (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
    _ ≤ (4000000000000000000:ℝ)/10^12 := by norm_num [T]
    _ ≤ _ := div_le_div_of_nonneg_right hnR (by norm_num)
