import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_finite_chen_square_numeric_loss :
    let P := fun n : ℕ => (Finset.range (n+1)).filter (fun p =>
      Nat.Prime p ∧ Nat.Prime (Nat.sqrt (n-p)) ∧ (Nat.sqrt (n-p))^2=n-p)
    ∀ n : ℕ, 4000000000000000000 ≤ n →
      ((P n).card:ℝ) ≤ (n:ℝ)/(10^6*(Real.log n)^2) := by
  dsimp only
  intro n hn
  let P := (Finset.range (n+1)).filter (fun p =>
    Nat.Prime p ∧ Nat.Prime (Nat.sqrt (n-p)) ∧ (Nat.sqrt (n-p))^2=n-p)
  change (P.card:ℝ) ≤ (n:ℝ)/(10^6*(Real.log n)^2)
  let root := fun p : ℕ => Nat.sqrt (n-p)
  have hstep (p : ℕ) (hp : p ∈ P) : n - (root p)^2 = p := by
    obtain ⟨hpn, _, _, hsq⟩ := Finset.mem_filter.mp hp
    have hpn' := Finset.mem_range.mp hpn
    change n - (Nat.sqrt (n-p))^2 = p
    rw [hsq]
    omega
  have hinj : Set.InjOn root P := by
    intro p hp q hq heq
    rw [← hstep p hp, ← hstep q hq, heq]
  have hsub : P.image root ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    have hprime := (Finset.mem_filter.mp hp).2.2.1
    exact Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ 2).trans hprime.two_le,
      Nat.sqrt_le_sqrt (Nat.sub_le n p)⟩
  have hcard : P.card ≤ Nat.sqrt n := by
    calc
      P.card = (P.image root).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card hsub
      _ = Nat.sqrt n := by simp
  refine (show (P.card:ℝ) ≤ (Nat.sqrt n:ℝ) by exact_mod_cast hcard).trans ?_
  refine Real.nat_sqrt_le_real_sqrt.trans ?_
  let c : ℝ := 4000000000000000000
  have hc : 0 < c := by norm_num [c]
  have hcn : c ≤ (n:ℝ) := by
    change (4000000000000000000:ℝ) ≤ (n:ℝ)
    exact_mod_cast hn
  have hn1 : (1:ℝ) < n := (by norm_num [c] : (1:ℝ) < c).trans_le hcn
  have hnpos : (0:ℝ) < n := zero_lt_one.trans hn1
  let r : ℝ := ((n:ℝ)/c)^(1/4:ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow ((one_le_div hc).mpr hcn) (by norm_num)
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hr4 : r^4 = (n:ℝ)/c := by
    dsimp only [r]
    rw [← Real.rpow_mul_natCast (by positivity), show (1/4:ℝ)*(4:ℕ)=1 by norm_num,
      Real.rpow_one]
  have hdecomp : (n:ℝ) = c * r^4 := by rw [hr4]; field_simp
  have hlogc : Real.log c ≤ 44 := by
    calc
      Real.log c ≤ Real.log ((2:ℝ)^62) := Real.log_le_log hc (by norm_num [c])
      _ = 62 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 44 := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log (n:ℝ) ≤ 44*r := by
    calc
      Real.log (n:ℝ) = Real.log c + 4*Real.log r := by
        rw [hdecomp, Real.log_mul hc.ne' (pow_ne_zero _ hrpos.ne'), Real.log_pow]
        norm_num
      _ ≤ 44 + 4*(r-1) := by linarith [Real.log_le_sub_one_of_pos hrpos]
      _ ≤ 44*r := by linarith
  have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos hn1
  have hbound : 10^6*(Real.log (n:ℝ))^2 ≤ Real.sqrt (n:ℝ) := by
    have hsqrt : Real.sqrt (n:ℝ) = 2000000000 * r^2 := by
      apply (Real.sqrt_eq_iff_mul_self_eq hnpos.le (by positivity)).2
      rw [hdecomp]
      norm_num [c]
      ring
    rw [hsqrt]
    have hsq := pow_le_pow_left₀ hlogpos.le hlog (2:ℕ)
    nlinarith [sq_nonneg r]
  apply (le_div_iff₀ (by positivity)).2
  exact (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)).trans_eq
    (by rw [← pow_two, Real.sq_sqrt hnpos.le])
