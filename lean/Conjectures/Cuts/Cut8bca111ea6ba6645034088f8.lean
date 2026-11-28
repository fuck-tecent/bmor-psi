import Mathlib

open Finset

-- child 1 zh: 逐个核验不超过 16384 的正 16 倍数均可写成两个奇素数之和。
-- child 1 en: Check that every positive multiple of 16 through 16384 is a sum of two odd primes.
-- child 2 zh: 对从 16384 起的整数起点证明对数平方窗中的正密度。
-- child 2 en: Prove the logarithm-squared window density for integer starts from 16384 onward.
theorem Conjectures.Cuts.Cut8bca111ea6ba6645034088f8 (finite : (let good := fun n : ℕ => ∃ p q : ℕ, Nat.Prime p ∧ Odd p ∧ Nat.Prime q ∧ Odd q ∧ p + q = n; ∀ j : ℕ, j < 1024 → good (16*(j+1)))) (large : (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 16384 ≤ n → 1 + ⌊c*(Real.log (n : ℝ))^2⌋₊ ≤ ((Finset.Ioc n ⌊(n : ℝ) + 123*(Real.log (n : ℝ))^2⌋₊).filter (fun m => 0 < ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Odd p ∧ Nat.Prime (m-p) ∧ Odd (m-p))).card)).card)) : (let good := fun n : ℕ => ∃ p q : ℕ, Nat.Prime p ∧ Odd p ∧ Nat.Prime q ∧ Odd q ∧ p + q = n; ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → let h := (Real.log x)^2; let W := Finset.Ioc ⌊x⌋₊ ⌊x + 123*h⌋₊; 1 + ⌊c*h⌋₊ ≤ (@Finset.filter ℕ good (Classical.decPred good) W).card) := by
  classical
  intro good
  obtain ⟨δ, hδ, hLarge⟩ := large
  let cap : ℝ := 1 / (2 * (16384 : ℝ)^2)
  let c := min (δ / 4) cap
  have hc : 0 < c := lt_min (by positivity) (by dsimp [cap]; positivity)
  have hcδ : c ≤ δ / 4 := min_le_left _ _
  have hcap : c ≤ cap := min_le_right _ _
  refine ⟨c, hc, ?_⟩
  intro x hx h W
  let n : ℕ := ⌊x⌋₊
  have hxPos : 0 < x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hxPos.le
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn₂ : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hlogX : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  change 1 + ⌊c * (Real.log x)^2⌋₊ ≤
    (@Finset.filter ℕ good (Classical.decPred good) (Ioc n ⌊x + 123*(Real.log x)^2⌋₊)).card
  by_cases hn : 16384 ≤ n
  · have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₂
    have hnPos : (0 : ℝ) < n := by linarith
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hlogMono := Real.log_le_log hnPos hnx
    have hSquare : (n : ℝ) + 1 ≤ (n : ℝ)^2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hlogLimit : Real.log x ≤ 2 * Real.log (n : ℝ) := by
      have hh := Real.log_le_log hxPos (hxn.le.trans hSquare)
      rw [Real.log_pow] at hh
      simpa using hh
    have hsq : (Real.log x)^2 ≤ 4 * (Real.log (n : ℝ))^2 := by
      calc
        _ ≤ (2 * Real.log (n : ℝ))^2 := pow_le_pow_left₀ hlogX hlogLimit 2
        _ = _ := by ring
    have hFloorScore : ⌊c * (Real.log x)^2⌋₊ ≤ ⌊δ * (Real.log (n : ℝ))^2⌋₊ := by
      apply Nat.floor_mono
      calc
        _ ≤ (δ/4) * (4 * (Real.log (n : ℝ))^2) :=
          mul_le_mul hcδ hsq (sq_nonneg _) (by positivity)
        _ = _ := by ring
    have hEdge : ⌊(n : ℝ) + 123 * (Real.log (n : ℝ))^2⌋₊ ≤ ⌊x + 123*(Real.log x)^2⌋₊ := by
      apply Nat.floor_mono
      have hpower := pow_le_pow_left₀ hln hlogMono 2
      linarith only [hnx, hpower]
    refine (Nat.add_le_add_left hFloorScore 1).trans ((hLarge n hn).trans ?_)
    apply card_le_card
    intro k hk
    obtain ⟨hi,hgood⟩ := mem_filter.mp hk
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hi
    obtain ⟨p,hp⟩ := card_pos.mp hgood
    obtain ⟨hpRange,hpPrime,hpOdd,hqPrime,hqOdd⟩ := mem_filter.mp hp
    have hpk : p ≤ k := Nat.le_of_lt_succ (mem_range.mp hpRange)
    have hkGood : good k := ⟨p,k-p,hpPrime,hpOdd,hqPrime,hqOdd,Nat.add_sub_of_le hpk⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlo,hhi.trans hEdge⟩,hkGood⟩
  · have hnSmall : n < 16384 := Nat.lt_of_not_ge hn
    have hxSmall : x < 16384 := hxn.trans_le (by exact_mod_cast (show n + 1 ≤ 16384 by omega))
    have hlogSmall : Real.log x ≤ 16384 :=
      (Real.log_le_sub_one_of_pos hxPos).trans (by linarith)
    have hscore : c * (Real.log x)^2 < 1 := by
      have hs := pow_le_pow_left₀ hlogX hlogSmall 2
      have hs' := mul_le_mul hcap hs (sq_nonneg _) (by dsimp [cap]; positivity)
      dsimp [cap] at hs'
      norm_num at hs'
      linarith only [hs']
    have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
      have hv := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num)
      rw [Real.log_inv] at hv
      norm_num at hv
      linarith
    have hlogHalf := hlog2.trans (Real.log_le_log (by norm_num) hx)
    have hpow := pow_le_pow_left₀ (by norm_num : 0 ≤ (1/2 : ℝ)) hlogHalf 2
    have hwidth : n + 16 ≤ ⌊x + 123*(Real.log x)^2⌋₊ := by
      apply Nat.le_floor
      push_cast
      nlinarith only [hnx,hpow]
    let j := n / 16
    have hj : j < 1024 := by dsimp [j]; omega
    have hlater : n < 16*(j+1) := by dsimp [j]; omega
    have hnear : 16*(j+1) ≤ n+16 := by dsimp [j]; omega
    have hg : good (16*(j+1)) := finite j hj
    rw [Nat.floor_eq_zero.mpr hscore, add_zero]
    apply card_pos.mpr
    exact ⟨16*(j+1),mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlater,hnear.trans hwidth⟩,hg⟩⟩
