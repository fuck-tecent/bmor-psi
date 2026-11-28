import Mathlib
import Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge

/-!
# Exceptional set of Goldbach counterexamples: from dyadic windows to `[4, X]`

This cut reduces the global counting task to two closed analytic statements: a uniform
positive linear floor for the published major arcs (premise 1) and the four-sevenths
negative-energy bound for the minor arcs (premise 2). The verified bridge module
`Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge` turns those two premises into a
dyadic bound `the bad set on [X, 2X] ≼ X^(4/7+ε)`.  The proof below spreads the whole range
`[4, X]` over the dyadic blocks `[2^j, 2^(j+1)]`, absorbs the geometric series
`∑_j (2^(4/7+ε))^j` and the finitely many small blocks into a single constant, and
finally enlarges that constant by the factor `X^(4/7+ε) ≥ 1`.

-- child 1 zh: 主弧线性下界：存在正常数 c，使所有充分大的偶数 n 的主弧实部至少为 c·n。
-- child 1 en: A positive linear floor for the major arcs: some c > 0 with real part of the major-arc contribution at least c·n for every sufficiently large even n.
-- child 2 zh: 次弧负能量的四七次幂界：固定二进区间上负贡献平方和为 O(X^(18/7+ε))。
-- child 2 en: The four-sevenths negative-energy bound: the squared negative minor-arc contributions on a dyadic interval are O(X^(18/7+ε)).
-/

theorem Conjectures.Cuts.Cutec096e061b7ecac525916ec8
    (h₁ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re)
    (h₂ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-minor n))^2)) ≤ C * (X:ℝ) ^ (18/7 + e)) :
    (let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ C * (X:ℝ) ^ (4/7 + e)) := by
  classical
  intro bad e he
  -- Dyadic input: the verified bridge turns both premises into a bound on `[X, 2X]`.
  obtain ⟨C₁, N₁, hC₁, hbridge⟩ :=
    Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge h₁ h₂ e he
  have hbad : bad = fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := rfl
  -- Rewrap the bridge in terms of the local predicate `bad` (the decidability instances differ).
  have hbr : ∀ Y : ℕ, N₁ ≤ Y →
      ((Finset.Icc Y (2*Y)).filter bad).card ≤ C₁ * (Y:ℝ)^(4/7+e) := by
    intro Y hY
    have h := hbridge Y hY
    rw [Finset.filter_congr_decidable] at h
    exact h
  have hs : (0:ℝ) < 4/7 + e := by positivity
  -- The doubling ratio `q = 2^(4/7+e) > 1` and its geometric series.
  set q : ℝ := (2:ℝ)^(4/7 + e) with hq
  have hq1 : 1 < q := by rw [hq]; exact Real.one_lt_rpow (by norm_num) hs
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hqne : q ≠ 1 := ne_of_gt hq1
  have hqm : 0 < q - 1 := by linarith
  -- Starting index of the dyadic blocks on which the bridge is applicable.
  set j₀ : ℕ := Nat.clog 2 N₁ with hj₀
  have h2j₀ : N₁ ≤ 2^j₀ := by rw [hj₀]; exact Nat.le_pow_clog (by norm_num) N₁
  refine ⟨(j₀:ℝ) * ((2:ℝ)^j₀ + 1) + C₁*q^2/(q-1), max N₁ 4, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ (j₀:ℝ) * ((2:ℝ)^j₀ + 1) := by positivity
    have h2 : (0:ℝ) < C₁*q^2/(q-1) := by positivity
    linarith
  intro X hX
  obtain ⟨hXN, hX4⟩ := max_le_iff.mp hX
  have hX2 : 2 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  -- `L` is the number of doublings needed to cover `[4, X]`.
  set L : ℕ := Nat.clog 2 X with hL
  have hXL : X ≤ 2^L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) X
  have hL1 : 1 ≤ L := by rw [hL]; exact Nat.clog_pos (by norm_num) (by omega)
  have hpred : 2^(L-1) < X := by
    rw [hL]; exact Nat.pow_pred_clog_lt_self 2 (by omega)
  have hpowL : 2^L < 2*X := by
    have hsplit : 2^L = 2^(L-1) * 2 := by
      calc 2^L = 2^((L-1)+1) := by rw [Nat.sub_add_cancel hL1]
        _ = 2^(L-1) * 2 := by rw [pow_succ]
    rw [hsplit]
    calc 2^(L-1) * 2 < X * 2 := Nat.mul_lt_mul_of_pos_right hpred (by norm_num)
      _ = 2 * X := by ring
  -- Dyadic blocks `[2^j, 2^(j+1)]`, restricted to bad `n`.
  set blk : ℕ → Finset ℕ := fun j => (Finset.Icc (2^j) (2^(j+1))).filter bad with hblk
  -- Every bad `4 ≤ n ≤ X` lies in the block indexed by `clog 2 n - 1`.
  have hsub : (Finset.Icc 4 X).filter bad ⊆ (Finset.range (L+1)).biUnion blk := by
    intro n hn
    obtain ⟨hnI, hnb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn4, hnX⟩ := Finset.mem_Icc.mp hnI
    have hnpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
    have hnlt : 2^(Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self 2 (by omega)
    have hnle : n ≤ 2^(Nat.clog 2 n - 1 + 1) := by
      rw [Nat.sub_add_cancel hnpos]
      exact Nat.le_pow_clog (by norm_num) n
    rw [Finset.mem_biUnion]
    refine ⟨Nat.clog 2 n - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hmono : Nat.clog 2 n ≤ L := by rw [hL]; exact Nat.clog_mono_right 2 hnX
      omega
    · rw [hblk]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨le_of_lt hnlt, hnle⟩, hnb⟩
  -- Cardinality of a single dyadic block.
  have hsmall : ∀ j : ℕ, (blk j).card ≤ 2^j + 1 := by
    intro j
    rw [hblk]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Icc, pow_succ]
    omega
  -- Termwise: the bridge for `j ≥ j₀`, the trivial block size below.
  have hterm : ∀ j ∈ Finset.range (L+1),
      ((blk j).card : ℝ) ≤ C₁ * q^j + (if j < j₀ then (2:ℝ)^j + 1 else 0) := by
    intro j _
    by_cases hjj : j < j₀
    · rw [ite_eq_left hjj]
      have h1 : ((blk j).card : ℝ) ≤ (2:ℝ)^j + 1 := by
        have := hsmall j
        exact_mod_cast this
      have h2 : (0:ℝ) ≤ C₁ * q^j := by positivity
      linarith
    · rw [ite_eq_right (by omega : ¬ j < j₀)]
      have hjj' : j₀ ≤ j := by omega
      have h2j : N₁ ≤ 2^j := le_trans h2j₀ (Nat.pow_le_pow_right (by norm_num) hjj')
      have hpow : ((2:ℝ)^j)^(4/7+e) = q^j := by
        rw [hq]
        exact (Real.rpow_pow_comm (x := (2:ℝ)) (by norm_num) (4/7+e) j).symm
      have hpow2 : 2^(j+1) = 2*2^j := by rw [pow_succ, Nat.mul_comm]
      have hb' : ((blk j).card : ℝ) ≤ C₁ * q^j := by
        have hmain : ((Finset.filter bad (Finset.Icc (2^j) (2*2^j))).card : ℝ) ≤ C₁ * q^j := by
          refine (hbr (2^j) h2j).trans_eq ?_
          rw [Nat.cast_pow]
          norm_num only [Nat.cast_ofNat]
          rw [hpow]
        simpa [hblk, hpow2] using hmain
      simpa using hb'
  -- Sum the termwise bounds.
  have hsum : ∑ j ∈ Finset.range (L+1), ((blk j).card : ℝ) ≤
      C₁ * (∑ j ∈ Finset.range (L+1), q^j) + (j₀:ℝ) * ((2:ℝ)^j₀ + 1) := by
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ j ∈ Finset.range (L+1), (if j < j₀ then (2:ℝ)^j + 1 else 0) ≤
        (j₀:ℝ) * ((2:ℝ)^j₀ + 1) := by
      rw [← Finset.sum_filter]
      calc ∑ j ∈ (Finset.range (L+1)).filter (fun j => j < j₀), ((2:ℝ)^j + 1)
          ≤ ∑ _j ∈ (Finset.range (L+1)).filter (fun j => j < j₀), ((2:ℝ)^j₀ + 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j < j₀ := (Finset.mem_filter.mp hj).2
            have hle : (2:ℝ)^j ≤ (2:ℝ)^j₀ :=
              pow_le_pow_right₀ (by norm_num) (le_of_lt hj')
            linarith
        _ = (((Finset.range (L+1)).filter (fun j => j < j₀)).card : ℝ) * ((2:ℝ)^j₀ + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (j₀:ℝ) * ((2:ℝ)^j₀ + 1) := by
            have hcard : ((Finset.range (L+1)).filter (fun j => j < j₀)).card ≤ j₀ := by
              refine (Finset.card_le_card ?_).trans (le_of_eq (Finset.card_range j₀))
              intro x hx
              exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
            have hnn : (0:ℝ) ≤ (2:ℝ)^j₀ + 1 := by positivity
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
    have hmul : C₁ * (∑ j ∈ Finset.range (L+1), q^j) ≤
        C₁ * (∑ j ∈ Finset.range (L+1), q^j) := le_rfl
    rw [Finset.mul_sum]
    linarith
  -- The geometric series is dominated by a constant multiple of `X^(4/7+e)`.
  have hgeom : ∑ j ∈ Finset.range (L+1), q^j ≤ q^2 * (X:ℝ)^(4/7+e) / (q-1) := by
    rw [geom_sum_eq hqne]
    have hqL : q^L ≤ q * (X:ℝ)^(4/7+e) := by
      have h1 : ((2:ℝ)^L)^(4/7+e) ≤ ((2:ℝ) * (X:ℝ))^(4/7+e) := by
        refine Real.rpow_le_rpow (by positivity) ?_ hs.le
        exact_mod_cast hpowL.le
      have h2 : ((2:ℝ)^L)^(4/7+e) = q^L := by
        rw [hq]
        exact (Real.rpow_pow_comm (x := (2:ℝ)) (by norm_num) (4/7+e) L).symm
      have h3 : ((2:ℝ) * (X:ℝ))^(4/7+e) = q * (X:ℝ)^(4/7+e) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), hq]
      rw [h2, h3] at h1
      exact h1
    have hstep : q^(L+1) ≤ q * (q * (X:ℝ)^(4/7+e)) := by
      have h1 : q^(L+1) = q^L * q := by rw [pow_succ]
      rw [h1]
      calc q^L * q ≤ (q * (X:ℝ)^(4/7+e)) * q := mul_le_mul_of_nonneg_right hqL hq0.le
        _ = q * (q * (X:ℝ)^(4/7+e)) := by ring
    have hone : q^(L+1) - 1 ≤ q^(L+1) := by
      linarith [pow_pos hq0 (L+1)]
    calc (q^(L+1) - 1)/(q-1) ≤ q^(L+1)/(q-1) :=
          (div_le_div_iff_of_pos_right hqm).mpr hone
      _ ≤ (q * (q * (X:ℝ)^(4/7+e)))/(q-1) :=
          (div_le_div_iff_of_pos_right hqm).mpr hstep
      _ = q^2 * (X:ℝ)^(4/7+e)/(q-1) := by
          rw [show q * (q * (X:ℝ)^(4/7+e)) = q^2 * (X:ℝ)^(4/7+e) from by ring]
  -- Assemble: dyadic blocks plus the trimmed constant.
  have hX1' : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
  have hXs : (1:ℝ) ≤ (X:ℝ)^(4/7+e) := Real.one_le_rpow hX1' hs.le
  have hK : (0:ℝ) ≤ (j₀:ℝ) * ((2:ℝ)^j₀ + 1) := by positivity
  have hcardℝ : (((Finset.Icc 4 X).filter bad).card : ℝ) ≤
      ∑ j ∈ Finset.range (L+1), ((blk j).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hkey : ∑ j ∈ Finset.range (L+1), ((blk j).card : ℝ) ≤
      (C₁ * q^2/(q-1)) * (X:ℝ)^(4/7+e) + (j₀:ℝ) * ((2:ℝ)^j₀ + 1) := by
    have hCq : C₁ * (∑ j ∈ Finset.range (L+1), q^j) ≤
        (C₁ * q^2/(q-1)) * (X:ℝ)^(4/7+e) := by
      refine (mul_le_mul_of_nonneg_left hgeom hC₁.le).trans_eq ?_
      rw [show C₁ * (q^2 * (X:ℝ)^(4/7+e) / (q-1))
          = (C₁ * q^2/(q-1)) * (X:ℝ)^(4/7+e) from by ring]
    linarith
  have hfin : (C₁ * q^2/(q-1)) * (X:ℝ)^(4/7+e) + (j₀:ℝ) * ((2:ℝ)^j₀ + 1) ≤
      ((j₀:ℝ) * ((2:ℝ)^j₀ + 1) + C₁ * q^2/(q-1)) * (X:ℝ)^(4/7+e) := by
    have h5 : (j₀:ℝ) * ((2:ℝ)^j₀ + 1) ≤ (j₀:ℝ) * ((2:ℝ)^j₀ + 1) * (X:ℝ)^(4/7+e) := by
      nlinarith [hK, hXs]
    nlinarith [h5]
  rw [Finset.filter_congr_decidable]
  exact hcardℝ.trans (hkey.trans hfin)