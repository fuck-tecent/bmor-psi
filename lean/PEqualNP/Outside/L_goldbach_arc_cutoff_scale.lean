import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter

/-- The logarithmic cutoff eventually satisfies the separation inequality
for major arcs. -/
theorem PEqualNP.Outside.L_goldbach_arc_cutoff_scale :
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
    let arcs := fun n : ℕ =>
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * (Q n) ^ 2 < n := by
  intro Q arcs
  let C : ℝ := 2 * (2 / Real.log 2) ^ 4
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTail : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ)‖ ≤ (1 : ℝ) * ‖(n : ℝ) ^ (1 / 8 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).bound zero_lt_one)
  have hpowerTail : ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlogTail.and hpowerTail)
  refine ⟨max 2 N, ?_⟩
  intro n hn
  have hn₂ : 2 ≤ n := (max_le_iff.mp hn).1
  obtain ⟨hlogBound, hC⟩ := hN n (max_le_iff.mp hn).2
  have hx₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn₂
  have hx : (0 : ℝ) < n := by linarith
  let p : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)
  have hp : 0 ≤ p := Real.rpow_nonneg hx.le _
  have hlog : Real.log (n : ℝ) ≤ p := by
    change ‖Real.log (n : ℝ)‖ ≤ (1 : ℝ) * ‖p‖ at hlogBound
    simpa only [Real.norm_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ n)),
      Real.norm_of_nonneg hp, one_mul] using hlogBound
  have hadd : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith)
      (show 0 ≤ (n : ℝ) + 1 by linarith)]
  let L := Nat.log 2 (n + 2)
  have hpowNat : 2 ^ L ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have hpowReal : (2 : ℝ) ^ L ≤ (n : ℝ) + 2 := by exact_mod_cast hpowNat
  have hlogPow := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ L) hpowReal
  have hlogAdd := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) hadd
  rw [Real.log_pow] at hlogPow hlogAdd
  have hL : (L : ℝ) ≤ 2 * p / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr
      (hlogPow.trans (hlogAdd.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))))
  have hp4 : p ^ 4 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp only [p]
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  have hineq : 2 * (((L : ℝ) ^ 2) ^ 2) < (n : ℝ) := by
    calc
      _ ≤ 2 * ((2 * p / Real.log 2) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2) 2)
          (by norm_num)
      _ = C * p ^ 4 := by dsimp [C]; ring
      _ = C * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hp4]
      _ < (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hx _)
      _ = n := by
        rw [← Real.rpow_add hx, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  change 2 * (L ^ 2) ^ 2 < n
  exact_mod_cast hineq
