import Mathlib

open Filter

-- child 1 zh: 对充分大的 X，区间 [4, 2X] 中没有两素数表示的偶数个数，其四次幂至多为 X³。
-- child 1 en: For sufficiently large X, the fourth power of the number of even Goldbach exceptions in [4, 2X] is at most X cubed.
-- child 2 zh: 对每个 X ≥ 16，倍增区间内至少一个允许的二次幂移位失败的偶目标数，至多为允许指数数目乘以 [4, 2X] 内的偶例外数。
-- child 2 en: For every X ≥ 16, the number of even targets in [X, 2X) with a failed permitted shift is at most the number of permitted exponents times the number of even Goldbach exceptions in [4, 2X].
theorem Conjectures.Cuts.Cutb8b5b2d0c851739233606b73
    (hSparse :
      let G := fun m : ℕ => ((Finset.range (m+1)).filter
        (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
      ∃ Y : ℕ, ∀ X ≥ Y,
        ((Finset.Icc 4 (2*X)).filter (fun m => Even m ∧ G m = 0)).card^4 ≤ X^3)
    (hTransfer :
      let G := fun m : ℕ => ((Finset.range (m+1)).filter
        (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
      ∀ X : ℕ, 16 ≤ X →
        let L := Nat.log 2 X / 2
        let E := (Finset.Ico X (2*X)).filter (fun n =>
          Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card)
        E.card ≤ L * ((Finset.Icc 4 (2*X)).filter (fun m => Even m ∧ G m = 0)).card) :
    (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4) := by
  -- Absorb the logarithmic multiplicity into the gap between the two exponents.
  have eventualLogBound :
      ∃ K : ℕ, ∀ X : ℕ, K ≤ X → (Nat.log 2 X / 2)^20 ≤ X := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc : 0 < (Real.log 2)^20 := pow_pos hlog2 _
    have hs := (isLittleO_log_rpow_rpow_atTop 20 (show 0 < (1 : ℝ) by norm_num)).bound hc
    obtain ⟨Y, hY⟩ := eventually_atTop.mp hs
    refine ⟨max 1 ⌈Y⌉₊, ?_⟩
    intro X hX
    have hX1 : 1 ≤ X := (le_max_left ..).trans hX
    have hX1' : (1:ℝ) ≤ X := by exact_mod_cast hX1
    have hceil : ⌈Y⌉₊ ≤ X := (le_max_right ..).trans hX
    have hYX : Y ≤ X := (Nat.le_ceil Y).trans (by exact_mod_cast hceil)
    have h := hY (X:ℝ) hYX
    have hlogX : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg hX1'
    have hX0 : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
    have hpow : Real.log (X:ℝ)^20 ≤ (Real.log 2)^20 * (X:ℝ) := by
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_one,
        Real.norm_of_nonneg (Real.rpow_nonneg hlogX _), Real.norm_of_nonneg hX0] using h
    have hcast : ((Nat.log 2 X : ℕ) : ℝ) ≤ Real.log (X:ℝ) / Real.log 2 := by
      rw [Real.log_div_log, ← Real.natFloor_logb_natCast 2 X]
      exact Nat.floor_le (Real.logb_nonneg (by norm_num) hX1')
    have hdiv : ((Nat.log 2 X / 2 : ℕ) : ℝ) ≤ (Nat.log 2 X : ℝ) := by
      exact_mod_cast Nat.div_le_self (Nat.log 2 X) 2
    have hfirst := pow_le_pow_left₀ (by positivity) (hdiv.trans hcast) 20
    have hlast : (Real.log (X:ℝ) / Real.log 2)^20 ≤ (X:ℝ) := by
      rw [div_pow]
      apply (div_le_iff₀ hc).mpr
      simpa only [mul_comm] using hpow
    exact_mod_cast hfirst.trans hlast
  have combine {a b L X : ℕ}
      (hcount : a ≤ L*b) (hsparse : b^4 ≤ X^3) (hlog : L^20 ≤ X) : a^5 ≤ X^4 := by
    have h20 : a^20 ≤ X^16 := calc
      a^20 ≤ (L*b)^20 := Nat.pow_le_pow_left hcount 20
      _ = L^20*(b^4)^5 := by ring
      _ ≤ X*(X^3)^5 := Nat.mul_le_mul hlog (Nat.pow_le_pow_left hsparse 5)
      _ = X^16 := by ring
    have h4 : (a^5)^4 ≤ (X^4)^4 := by
      simpa only [← pow_mul, show 5*4 = 20 by decide, show 4*4 = 16 by decide] using h20
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : (4:ℕ) ≠ 0)).mp h4
  rcases hSparse with ⟨Y, hY⟩
  rcases eventualLogBound with ⟨K, hK⟩
  refine ⟨max (max Y K) 16, ?_⟩
  intro X hX
  have hYK : max Y K ≤ X := (le_max_left ..).trans hX
  exact combine (hTransfer X ((le_max_right ..).trans hX))
    (hY X ((le_max_left ..).trans hYK)) (hK X ((le_max_right ..).trans hYK))
