import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
This file adapts the Apache-2.0 finite divisor certificate of muxkin, Goldbach PR 2815.
The low columns share a product tree. In the high columns, one packed digit records both a weight
and a count. Exact masks recover both sums. The sparse envelope adds low digits first.
The divisor identities, residue counts, and finite-sum methods adapt the Apache-2.0
Goldbach proofs in PR 2645 by CATLILIZHOU and PR 2649 by nanzhiyan1.
A periodic factorial inequality gives the ordinary Chebyshev bound used for
the 79 active moduli. The two coefficient endpoints, the finite sums through
3000000, and the remaining discrepancy are checked with integer arithmetic.
The final estimate also bounds the contribution of proper prime powers.
-/

namespace FR7022
noncomputable def psi (n q r : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), if k % q = r then ArithmeticFunction.vonMangoldt k else 0
end FR7022
namespace FR7022
open Finset Real
end FR7022
namespace FR7022
open Filter
open scoped Topology
end FR7022
namespace FR7022
end FR7022
namespace GoldbachResidueLog
open Finset
private def r (q a x : ℕ) : ℕ := (x + (q - a % q)) % q
private noncomputable def u (q a x : ℕ) : ℝ := (r q a x : ℝ) / q
private theorem r_zero {q : ℕ} (hq : 0 < q) (a x : ℕ) :
    r q a x = 0 ↔ x % q = a % q := by
  let s := q - a % q
  have ha := Nat.mod_lt a hq
  have hs : (a+s) % q = 0 := by
    show a + s ≡ 0 [MOD q]
    calc
      a+s ≡ a % q+s [MOD q] := Nat.ModEq.add_right s (by simp [Nat.ModEq])
      _ = q := by dsimp [s]; omega
      _ ≡ 0 [MOD q] := by simp [Nat.ModEq]
  change (x+s) % q = 0 ↔ _
  rw [← hs]
  exact Nat.ModEq.add_iff_right (Nat.ModEq.refl s)
private theorem u_bounds {q : ℕ} (hq : 0 < q) (a x : ℕ) :
    0 ≤ u q a x ∧ u q a x ≤ 1 := by
  have h := Nat.mod_lt (x+(q-a % q)) hq
  have h' : (r q a x : ℝ) ≤ q := by exact_mod_cast h.le
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  unfold u
  exact ⟨by positivity, (div_le_one hq').mpr h'⟩
private theorem u_step {q : ℕ} (hq : 0 < q) (a x : ℕ) :
    u q a (x+1) = u q a x + 1/(q:ℝ) -
      (if (x+1) % q = a % q then 1 else 0) := by
  have hr : r q a x < q := Nat.mod_lt _ hq
  have hnext : r q a (x+1) = (r q a x + 1) % q := by
    dsimp [r]
    rw [show x+1+(q-a % q) = x+(q-a % q)+1 by omega]
    exact (Nat.mod_add_mod _ _ _).symm
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  by_cases h : r q a x + 1 = q
  · have h0 : r q a (x+1) = 0 := by rw [hnext,h,Nat.mod_self]
    rw [ite_eq_left ((r_zero hq a _).mp h0)]
    have he : (r q a x : ℝ)+1 = q := by exact_mod_cast h
    unfold u
    rw [h0]
    push_cast
    field_simp
    linarith
  · have hsmall : r q a x + 1 < q := by omega
    rw [Nat.mod_eq_of_lt hsmall] at hnext
    have hne : (x+1) % q ≠ a % q := fun hh => by
      have := (r_zero hq a _).mpr hh
      omega
    rw [ite_eq_right hne]
    unfold u
    rw [hnext]
    push_cast
    ring
noncomputable def F (q a x : ℕ) : ℝ :=
  ∑ k ∈ (range (x+1)).filter (fun k => k % q = a % q), Real.log (k:ℝ)
private theorem F_step (q a x : ℕ) :
    F q a (x+1) = F q a x +
      (if (x+1) % q = a % q then (1:ℝ) else 0) * Real.log ((x+1:ℕ):ℝ) := by
  simp only [F, Finset.sum_filter, Finset.sum_range_succ]
  split_ifs <;> simp_all
private noncomputable def adjusted (q a x : ℕ) : ℝ :=
  F q a x - Real.log (x.factorial : ℝ) / q + u q a x * Real.log (x:ℝ)
private theorem adjusted_step {q : ℕ} (hq : 0 < q) (a x : ℕ) :
    adjusted q a (x+1) = adjusted q a x + u q a x *
      (Real.log ((x+1:ℕ):ℝ) - Real.log (x:ℝ)) := by
  have hf : ((x.factorial : ℕ):ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero x)
  have hx : ((x+1:ℕ):ℝ) ≠ 0 := by positivity
  simp only [adjusted, Nat.factorial_succ, Nat.cast_mul, Real.log_mul hx hf, F_step]
  rw [u_step hq]
  ring
private theorem adjusted_bounds {q : ℕ} (hq : 0 < q) (a x : ℕ) :
    0 ≤ adjusted q a x ∧ adjusted q a x ≤ Real.log (x:ℝ) := by
  induction x with
  | zero => simp [adjusted,F,Finset.sum_filter]
  | succ x ih =>
    have hinc : 0 ≤ Real.log ((x+1:ℕ):ℝ) - Real.log (x:ℝ) := by
      apply sub_nonneg.mpr
      by_cases hx : x = 0
      · simp [hx]
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hx) (by exact_mod_cast Nat.le_succ x)
    rw [adjusted_step hq]
    have b := u_bounds hq a x
    constructor
    · exact add_nonneg ih.1 (mul_nonneg b.1 hinc)
    · have hi := mul_le_mul_of_nonneg_right b.2 hinc
      linarith [ih.2]
theorem abs_error_le_log (q a x : ℕ) (hq : 0 < q) :
    |F q a x - Real.log (x.factorial : ℝ) / q| ≤ Real.log (x:ℝ) := by
  have t := adjusted_bounds hq a x
  have b := u_bounds hq a x
  have hl := Real.log_natCast_nonneg x
  unfold adjusted at t
  have h₁ := mul_nonneg b.1 hl
  have h₂ := mul_le_mul_of_nonneg_right b.2 hl
  exact abs_le.mpr ⟨by linarith [t.1], by linarith [t.2]⟩
end GoldbachResidueLog
namespace FR7022Mertens
open Finset
open scoped ArithmeticFunction.Moebius
def residue (q a k : ℕ) : ℕ :=
  Nat.findGreatest (fun r => k*r % q = a % q) (q-1)
theorem residue_spec {q a k : ℕ} (hq : 0 < q) (hk : k.Coprime q) :
    residue q a k < q ∧ k * residue q a k % q = a % q := by
  obtain ⟨r,hr,h⟩ := Nat.exists_mul_mod_eq_of_coprime a hk hq.ne'
  refine ⟨lt_of_le_of_lt (Nat.findGreatest_le _) (by omega), ?_⟩
  exact Nat.findGreatest_spec (P := fun r => k*r % q = a % q) (show r ≤ q-1 by omega) h
private theorem rearrange {R : Type*} [AddCommMonoid R] (x : ℕ) (f : ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 x, ∑ d ∈ m.divisors, f m d) =
    ∑ k ∈ Icc 1 x, ∑ d ∈ Icc 1 (x/k), f (d*k) d := by
  rw [sum_sigma', sum_sigma']
  apply sum_nbij' (fun p : (Σ _ : ℕ, ℕ) => ⟨p.1/p.2,p.2⟩)
    (fun r : (Σ _ : ℕ, ℕ) => ⟨r.2*r.1,r.2⟩)
  · rintro ⟨m,d⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hm,hmx⟩,hdiv,hm0⟩ := h
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdiv hm
    have hk : 0 < m/d := Nat.div_pos (Nat.le_of_dvd hm hdiv) hd
    exact ⟨⟨hk,(Nat.div_le_self _ _).trans hmx⟩,hd,
      (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_div_cancel_left' hdiv] using hmx)⟩
  · rintro ⟨k,d⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    exact ⟨⟨Nat.mul_pos h.2.1 h.1.1,(Nat.le_div_iff_mul_le h.1.1).mp h.2.2⟩,
      dvd_mul_right _ _,(Nat.mul_pos h.2.1 h.1.1).ne'⟩
  · rintro ⟨m,d⟩ h
    simp only [mem_sigma, Nat.mem_divisors] at h
    simp [Nat.mul_div_cancel_left' h.2.1]
  · rintro ⟨k,d⟩ h
    simp only [mem_sigma, mem_Icc] at h
    simp [Nat.mul_div_cancel_left _ h.2.1]
  · rintro ⟨m,d⟩ h
    simp only [mem_sigma, Nat.mem_divisors] at h
    simp [Nat.mul_div_cancel_left' h.2.1]
end FR7022Mertens
namespace GoldbachResidueLog
noncomputable def mainTerm (t : ℝ) : ℝ := t * Real.log t - t
private theorem mainTerm_between {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (t-s) * Real.log s ≤ mainTerm t - mainTerm s ∧
    mainTerm t - mainTerm s ≤ (t-s) * Real.log t := by
  have hsmall := Real.log_le_sub_one_of_pos (div_pos hs ht : 0 < s/t)
  rw [Real.log_div hs.ne' ht.ne'] at hsmall
  have hlarge := Real.log_le_sub_one_of_pos (div_pos ht hs : 0 < t/s)
  rw [Real.log_div ht.ne' hs.ne'] at hlarge
  have hl := mul_le_mul_of_nonneg_right hsmall ht.le
  have hu := mul_le_mul_of_nonneg_right hlarge hs.le
  have e1 : (s/t-1)*t = s-t := by field_simp
  have e2 : (t/s-1)*s = t-s := by field_simp
  rw [e1] at hl
  rw [e2] at hu
  unfold mainTerm
  constructor <;> nlinarith only [hl,hu]
theorem factorial_main_bounds (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ Real.log (m.factorial:ℝ) - mainTerm m ∧
    Real.log (m.factorial:ℝ) - mainTerm m ≤ 1 + Real.log m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [mainTerm]
  | succ m hm ih =>
    have hp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hr : (0:ℝ) < m+1 := by positivity
    have h := mainTerm_between hp hr
    have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) hf]
    push_cast at *
    constructor <;> linarith [h.1,h.2,ih.1,ih.2]
theorem floor_main_error (q r m : ℕ) (hq : 0 < q) (hm : 1 ≤ m)
    (t : ℝ) (hmt : (m:ℝ) ≤ t) (htm : t ≤ (m:ℝ)+1) :
    |F q r m - mainTerm t / q| ≤ 2 * Real.log t + 1 := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0:ℝ) < m := by linarith
  have ht : 0 < t := lt_of_lt_of_le hp hmt
  have hlt := Real.log_nonneg (hm1.trans hmt)
  have hlm := Real.log_nonneg hm1
  have hlog := Real.log_le_log hp hmt
  have hmain := mainTerm_between hp ht
  have hprod0 := mul_nonneg (sub_nonneg.mpr hmt) hlm
  have hprod1 : (t-m)*Real.log t ≤ Real.log t := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr htm) hlt]
  have hfac := factorial_main_bounds m hm
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0:ℝ) < q := by positivity
  have ferr : |Real.log (m.factorial:ℝ) - mainTerm t| ≤ 1+Real.log t := by
    apply abs_le.mpr
    constructor <;> linarith [hfac.1,hfac.2,hmain.1,hmain.2]
  have ferr' : |Real.log (m.factorial:ℝ) / q - mainTerm t / q| ≤ 1+Real.log t := by
    rw [← sub_div, abs_div, abs_of_nonneg hqp.le]
    exact (div_le_self (abs_nonneg _) hq1).trans ferr
  calc
    _ ≤ |F q r m - Real.log (m.factorial:ℝ)/q| +
        |Real.log (m.factorial:ℝ)/q - mainTerm t/q| := abs_sub_le _ _ _
    _ ≤ Real.log m + (1+Real.log t) := add_le_add (abs_error_le_log q r m hq) ferr'
    _ ≤ _ := by linarith
theorem quotient_main_error (q r n k : ℕ) (hq : 0 < q) (hk : 0 < k) (hkn : k ≤ n) :
    |F q r (n/k) - mainTerm ((n:ℝ)/k) / q| ≤ 2 * Real.log ((n:ℝ)/k) + 1 := by
  have hkp : (0:ℝ) < k := by exact_mod_cast hk
  apply floor_main_error q r (n/k) hq (Nat.div_pos hkn hk)
  · apply (le_div_iff₀ hkp).mpr
    exact_mod_cast Nat.div_mul_le_self n k
  · apply (div_le_iff₀ hkp).mpr
    have hu : n < (n/k+1)*k := by
      calc
        n = n % k + k*(n/k) := (Nat.mod_add_div n k).symm
        _ < k + k*(n/k) := Nat.add_lt_add_right (Nat.mod_lt n hk) _
        _ = _ := by ring
    exact_mod_cast hu.le
theorem mainTerm_div (x k : ℝ) (hx : x ≠ 0) (hk : k ≠ 0) :
    mainTerm (x/k) = x * ((Real.log x - 1) / k - Real.log k / k) := by
  rw [mainTerm, Real.log_div hx hk]
  ring
end GoldbachResidueLog
namespace GoldbachResidueLog
open Finset
theorem weighted_main_error (q n : ℕ) (hq : 0 < q) (S : Finset ℕ)
    (C : ℕ → ℝ) (r : ℕ → ℕ)
    (hS : ∀ k ∈ S, 0 < k ∧ k ≤ n)
    (hcancel : (∑ k ∈ S, C k / k) = 0) :
    |(∑ k ∈ S, C k * F q (r k) (n/k)) -
      (-(n:ℝ)/q) * (∑ k ∈ S, C k * Real.log k / k)| ≤
      (2 * Real.log n + 1) * ∑ k ∈ S, |C k| := by
  have hmain : (∑ k ∈ S, C k * (mainTerm ((n:ℝ)/k) / q)) =
      (-(n:ℝ)/q) * (∑ k ∈ S, C k * Real.log k / k) := by
    calc
      _ = ∑ k ∈ S, (((n:ℝ)/q * (Real.log n-1)) * (C k/k) -
          ((n:ℝ)/q) * (C k*Real.log k/k)) := by
        apply sum_congr rfl
        intro k hk
        have hb := hS k hk
        have hkn : (k:ℝ) ≠ 0 := by exact_mod_cast hb.1.ne'
        have hnn : (n:ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hb.1 hb.2).ne'
        rw [mainTerm_div _ _ hnn hkn]
        ring
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hcancel, mul_zero, zero_sub]
        ring
  rw [← hmain, ← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k hk
  have hb := hS k hk
  have hkp : (0:ℝ) < k := by exact_mod_cast hb.1
  have hnp : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hb.1 hb.2)
  have hlog := Real.log_le_log (div_pos hnp hkp)
    (div_le_self hnp.le (show (1:ℝ) ≤ k by exact_mod_cast hb.1))
  have hterm := quotient_main_error q (r k) n k hq hb.1 hb.2
  rw [← mul_sub, abs_mul, mul_comm (2*Real.log n+1)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  linarith
end GoldbachResidueLog
namespace GoldbachResidueLog
open Finset
private theorem exp_threshold_lt_45 : Real.exp (19/5) < 45 := by
  have he : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hpow : Real.exp (19/5) ^ 5 < (45:ℝ)^5 := by
    calc
      _ = Real.exp 1 ^ 19 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        norm_num
      _ ≤ (2.72:ℝ)^19 := pow_le_pow_left₀ (Real.exp_pos _).le he _
      _ < _ := by norm_num
  by_contra! hn
  exact hpow.not_ge (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤45) hn _)
theorem weighted_main_error_91 (q n : ℕ) (hq : 0 < q) (S : Finset ℕ)
    (C : ℕ → ℝ) (r : ℕ → ℕ)
    (hS : ∀ k ∈ S, 0 < k ∧ k ≤ n)
    (hcancel : (∑ k ∈ S, C k / k) = 0)
    (hn : (n:ℝ) < Real.exp (Real.exp (19/5))) :
    |(∑ k ∈ S, C k * F q (r k) (n/k)) -
      (-(n:ℝ)/q) * (∑ k ∈ S, C k * Real.log k/k)| ≤
      91 * ∑ k ∈ S, |C k| := by
  have hnlog : Real.log n ≤ 45 := by
    rcases Nat.eq_zero_or_pos n with hz | hp
    · simp [hz]
    have hpos : 0 < (n:ℝ) := by exact_mod_cast hp
    exact ((Real.log_lt_iff_lt_exp hpos).mpr hn).le.trans exp_threshold_lt_45.le
  apply (weighted_main_error q n hq S C r hS hcancel).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (sum_nonneg fun k _ => abs_nonneg (C k))
end GoldbachResidueLog
namespace FR7022Steps
open Finset Real
end FR7022Steps
namespace FR7022Dirichlet
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
private theorem rearrange (x : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ m ∈ Icc 1 x, ∑ d ∈ m.divisors, f m d) =
    ∑ k ∈ Icc 1 x, ∑ d ∈ Icc 1 (x/k), f (d*k) d := by
  rw [sum_sigma', sum_sigma']
  apply sum_nbij' (fun p : (Σ _ : ℕ, ℕ) => ⟨p.1/p.2,p.2⟩)
    (fun r : (Σ _ : ℕ, ℕ) => ⟨r.2*r.1,r.2⟩)
  · rintro ⟨m,d⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hm,hmx⟩,hdiv,hm0⟩ := h
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdiv hm
    have hk : 0 < m/d := Nat.div_pos (Nat.le_of_dvd hm hdiv) hd
    exact ⟨⟨hk,(Nat.div_le_self _ _).trans hmx⟩,hd,
      (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_div_cancel_left' hdiv] using hmx)⟩
  · rintro ⟨k,d⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    exact ⟨⟨Nat.mul_pos h.2.1 h.1.1,(Nat.le_div_iff_mul_le h.1.1).mp h.2.2⟩,
      dvd_mul_right _ _,(Nat.mul_pos h.2.1 h.1.1).ne'⟩
  · rintro ⟨m,d⟩ h
    simp only [mem_sigma, Nat.mem_divisors] at h
    simp [Nat.mul_div_cancel_left' h.2.1]
  · rintro ⟨k,d⟩ h
    simp only [mem_sigma, mem_Icc] at h
    simp [Nat.mul_div_cancel_left _ h.2.1]
  · rintro ⟨m,d⟩ h
    simp only [mem_sigma, Nat.mem_divisors] at h
    simp [Nat.mul_div_cancel_left' h.2.1]
theorem slice (n q a : ℕ) (A B : ArithmeticFunction ℝ) :
    (∑ m ∈ Icc 1 n, if m % q = a % q then (A*B) m else 0) =
    ∑ k ∈ Icc 1 n, A k * ∑ d ∈ Icc 1 (n/k), if d*k % q = a % q then B d else 0 := by
  calc
    _ = ∑ m ∈ Icc 1 n, ∑ d ∈ m.divisors,
        if m % q = a % q then A (m/d) * B d else 0 := by
      apply sum_congr rfl
      intro m _
      by_cases h : m % q=a % q
      · simp only [h, ite_true, ArithmeticFunction.mul_apply]
        exact Nat.sum_divisorsAntidiagonal' (fun i j => A i * B j)
      · simp [h]
    _ = _ := by
      rw [rearrange]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      rw [Nat.mul_div_cancel_left _ hd0]
      split <;> simp_all
theorem expand (n q a : ℕ) (A : ArithmeticFunction ℝ) :
    (∑ k ∈ Icc 1 n, A k * ∑ d ∈ Icc 1 (n/k),
        if d*k % q = a % q then Real.log d else 0) =
    ∑ p ∈ Icc 1 n, vonMangoldt p * ∑ j ∈ Icc 1 (n/p),
        if j*p % q = a % q then ∑ k ∈ j.divisors, A k else 0 := by
  have sl := slice n q a A ArithmeticFunction.log
  simp only [ArithmeticFunction.log_apply] at sl
  rw [← sl]
  have h : A * ArithmeticFunction.log = vonMangoldt * (A * (ζ : ArithmeticFunction ℝ)) := by
    rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
    ac_rfl
  rw [h, slice]
  simp only [coe_mul_zeta_apply]
end FR7022Dirichlet
namespace FR7022ProgressionTail
open Finset
def firstResidue (q a : ℕ) := if a % q = 0 then q else a % q
def countTerms (y q a : ℕ) :=
  if firstResidue q a ≤ y then (y-firstResidue q a)/q+1 else 0
private theorem first_pos {q : ℕ} (hq : 0 < q) (a : ℕ) : 0 < firstResidue q a := by
  unfold firstResidue; split_ifs <;> omega
private theorem first_mod (q a : ℕ) : firstResidue q a % q = a % q := by
  unfold firstResidue; split_ifs <;> simp_all
private theorem first_le {q a m : ℕ} (hm : 0 < m) (hr : m % q = a % q) :
    firstResidue q a ≤ m := by
  unfold firstResidue
  split_ifs with ha
  · exact Nat.le_of_dvd hm (Nat.dvd_of_mod_eq_zero (hr.trans ha))
  · exact hr ▸ Nat.mod_le m q
private theorem lt_count_iff {q : ℕ} (hq : 0 < q) (y a j : ℕ) :
    j < countTerms y q a ↔ firstResidue q a + j*q ≤ y := by
  unfold countTerms
  split_ifs with h
  · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hq]
    omega
  · simp; omega
theorem class_card (q a y : ℕ) (hq : 0 < q) :
    ((Icc 1 y).filter fun m => m % q=a % q).card = countTerms y q a := by
  classical
  let f := fun j => firstResidue q a + j*q
  have hmap : ((Finset.range (countTerms y q a)).image f) =
      (Finset.Icc 1 y).filter (fun m => m % q=a % q) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨j,hj,rfl⟩
      have hr := first_pos hq a
      exact ⟨⟨by dsimp [f]; omega,(lt_count_iff hq y a j).mp hj⟩, by simp [f,Nat.add_mod,first_mod]⟩
    · rintro ⟨⟨hm, hy⟩,hr⟩
      have hb := first_le hm hr
      have hd : q ∣ m-firstResidue q a := (Nat.modEq_iff_dvd' hb).mp ((first_mod q a).trans hr.symm)
      have hv := Nat.div_mul_cancel hd
      have hj : f ((m-firstResidue q a)/q) = m := by dsimp [f]; omega
      exact ⟨_,(lt_count_iff hq y a _).mpr (hj.le.trans hy),hj⟩
  rw [← hmap, card_image_of_injOn, card_range]
  intro i _ j _ hij
  exact Nat.eq_of_mul_eq_mul_right hq (Nat.add_left_cancel hij)
def count (q h t k : ℕ) : ℕ :=
  ((Icc 1 (t/k)).filter fun m => (m*k) % q=h % q).card
noncomputable def G (S : Finset ℕ) (c : ℕ → ℝ) (q h t : ℕ) : ℝ :=
  ∑ k ∈ S, c k * (count q h t k:ℝ)
end FR7022ProgressionTail
namespace FR7022Dirichlet
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
open FR7022ProgressionTail
theorem kernel_eq (t q h : ℕ) (S : Finset ℕ) (A : ArithmeticFunction ℝ)
    (hs : ∀ k ∉ S, A k = 0) :
    (∑ j ∈ Icc 1 t, if j % q=h % q then ∑ k ∈ j.divisors, A k else 0) = G S A q h t := by
  have sl := slice t q h A (ζ : ArithmeticFunction ℝ)
  simp only [coe_mul_zeta_apply] at sl
  rw [sl, G]
  apply sum_congr_of_eq_on_inter
  · intro k _ hk
    simp [hs k hk]
  · intro k _ hk
    have hk0 : t/k = 0 := by
      by_cases h : k=0
      · simp [h]
      · exact Nat.div_eq_of_lt (by simp only [mem_Icc, not_and] at hk; exact Nat.lt_of_not_ge (hk (by omega)))
    simp [count,hk0]
  · intro k _ _
    congr 1
    rw [count, ← sum_boole]
    apply sum_congr rfl
    intro d hd
    have hdn : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
    by_cases hh : d*k % q=h % q <;> simp [hh, hdn]
private theorem eq_select (q a p r : ℕ) (hp : p.Coprime q)
    (hr : r*p ≡ a [MOD q]) (j : ℕ) :
    (j*p % q=a % q) ↔ j % q=r % q :=
  ⟨fun x => Nat.ModEq.cancel_right_of_coprime hp.symm ((show j*p ≡ a [MOD q] from x).trans hr.symm),
    fun x => ((show j ≡ r [MOD q] from x).mul_right p).trans hr⟩
private theorem not_select (q a p : ℕ) (ha : a.Coprime q) (hp : ¬p.Coprime q) (j : ℕ) :
    j*p % q ≠ a % q := by
  intro h
  have hc : (j*p).Coprime q := by
    change Nat.gcd (j*p) q = 1
    rw [Nat.gcd_comm (j*p) q, Nat.gcd_rec q (j*p), h, ← Nat.gcd_rec q a, Nat.gcd_comm]
    exact ha
  exact hp (Nat.coprime_mul_iff_left.mp hc).2
end FR7022Dirichlet
namespace FR7022Dirichlet
open Finset ArithmeticFunction FR7022ProgressionTail GoldbachResidueLog
private theorem split_zero_one (x : ℕ) : insert 0 (Icc 1 x) = range (x+1) := by
  ext k
  simp only [mem_insert, mem_Icc,mem_range]
  omega
private theorem suffices_for_main (n q a : ℕ) (hq : 0 < q) (S : Finset ℕ)
    (A : ArithmeticFunction ℝ) (hs : ∀ k ∉ S, A k = 0) (hS : ∀ k ∈ S, 0 < k ∧ k ≤ n)
    (hc : ∀ k ∈ S, k.Coprime q) :
    (∑ k ∈ Icc 1 n, A k * ∑ d ∈ Icc 1 (n/k), if d*k % q=a % q then Real.log d else 0) =
    ∑ k ∈ S, A k * F q (FR7022Mertens.residue q a k) (n/k) := by
  apply sum_congr_of_eq_on_inter
  · intro k _ hk
    simp [hs k hk]
  · intro k hk hk'
    exact (hk' (mem_Icc.mpr (hS k hk))).elim
  · intro k _ hk
    congr 1
    have hr' : FR7022Mertens.residue q a k * k ≡ a [MOD q] := by
      change _*k % q = a % q
      rw [Nat.mul_comm]
      exact (FR7022Mertens.residue_spec hq (hc k hk)).2
    have er := eq_select q a k _ (hc k hk) hr'
    simp_rw [er]
    rw [F, sum_filter, ← split_zero_one, sum_insert (by simp)]
    simp
end FR7022Dirichlet
namespace GoldbachCoefficientPrefix
open Finset
def divisorWeight (S : Finset ℕ) (A : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ k ∈ S, if k ∣ j then A k else 0
def progression (D : ℕ → ℤ) (q h t : ℕ) : ℤ :=
  ∑ i ∈ range t, if (i+1) % q=h % q then D (i+1) else 0
theorem progression_as_Icc (D : ℕ → ℤ) (q h t : ℕ) :
    progression D q h t =
    ∑ j ∈ Icc 1 t, if j % q=h % q then D j else 0 := by
  unfold progression
  apply sum_nbij' (fun i => i+1) (fun j => j-1)
  · simp only [mem_range, mem_Icc]
    omega
  · simp only [mem_range, mem_Icc]
    omega
  · simp
  · simp only [mem_Icc]
    omega
  · simp
@[simp] theorem progression_zero (D : ℕ → ℤ) (q h : ℕ) :
    progression D q h 0 = 0 := by simp [progression]
theorem progression_succ (D : ℕ → ℤ) (q h t : ℕ) :
    progression D q h (t+1) = progression D q h t +
       (if (t+1) % q=h % q then D (t+1) else 0) := by
  simp [progression,sum_range_succ]
private theorem constant_between (D : ℕ → ℤ) (q h a b : ℕ) (hab : a ≤ b)
    (hmiss : ∀ j, a < j → j ≤ b → j % q ≠ h % q) :
    progression D q h b = progression D q h a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [progression_succ, ite_eq_right (hmiss _ (by omega) (by omega)), add_zero]
    exact ih (fun j hj h => hmiss j hj (by omega))
private theorem mod_ne_between {q j i : ℕ} (hj : j-q < i) (hi : i < j) :
    i % q ≠ j % q := by
  intro he
  have hd : q ∣ j-i := (Nat.modEq_iff_dvd' hi.le).mp he
  have hpos : 0 < j-i := by omega
  have := Nat.le_of_dvd hpos hd
  omega
theorem progression_step_q (D : ℕ → ℤ) (q j : ℕ) (hq : 0 < q) (hj : 0 < j) :
    progression D q j j = D j + progression D q j (j-q) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [progression_succ, ite_eq_left rfl, add_comm]
  congr 1
  exact constant_between D q _ _ _ (by omega) fun z hz hz' =>
    mod_ne_between hz (by omega)
private theorem replace_residue (D : ℕ → ℤ) {q h h' t : ℕ} (hh : h % q=h' % q) :
    progression D q h t = progression D q h' t := by simp [progression,hh]
def rowPrefix (q : ℕ) (D : ℕ → ℤ) (j : ℕ) : ℤ :=
  if 0 < q ∧ 0 < j then D j + rowPrefix q D (j-q) else 0
termination_by j
decreasing_by omega
theorem table_correct (D P : ℕ → ℤ) (q T : ℕ) (hq : 0 < q)
    (hzero : P 0 = 0)
    (hstep : ∀ j, 0 < j → j ≤ T → P j = D j + P (j-q)) :
    ∀ j ≤ T, progression D q j j = P j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjT
    by_cases hj : j=0
    · simp [hj,hzero]
    rw [progression_step_q D q j hq (by omega), hstep j (by omega) hjT]
    congr 1
    by_cases hsmall : j < q
    · simp [Nat.sub_eq_zero_of_le hsmall.le,hzero]
    · have hmod : (j-q) % q = j % q := by
        have h : j-q+q=j := Nat.sub_add_cancel (by omega)
        calc
          _ = (j-q+q) % q := by simp
          _ = _ := by rw [h]
      exact (replace_residue D hmod.symm).trans
        (ih (j-q) (by omega) (by omega))
theorem prefix_correct (D : ℕ → ℤ) (q : ℕ) (hq : 0 < q) (j : ℕ) :
    progression D q j j = rowPrefix q D j := by
  apply table_correct D (rowPrefix q D) q j hq _ _ j (le_refl _)
  · rw [rowPrefix]; simp
  · intro i hi _
    rw [rowPrefix, ite_eq_left ⟨hq,hi⟩]
end GoldbachCoefficientPrefix
namespace GoldbachCoefficientPrefix
open Finset
end GoldbachCoefficientPrefix
namespace FR7022Lane
def pack (w : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n+1, v => 2^(w+1) * pack w n (fun i => v (i+1)) + v 0
theorem guard_digit (w n : ℕ) (v : ℕ → ℕ) (hv : ∀ i < n, v i < 2^(w+1))
    (i : ℕ) (hi : i<n) :
    (pack w n v).testBit ((w+1)*i+w) = (v i).testBit w := by
  induction n generalizing i v with
  | zero => omega
  | succ n ih =>
    rw [pack, Nat.testBit_two_pow_mul_add _ (hv 0 (by omega))]
    cases i with
    | zero => simp
    | succ i =>
      rw [Nat.mul_succ]
      have h : ¬((w+1)*i+(w+1)+w < w+1) := by omega
      rw [ite_eq_right h, show (w+1)*i+(w+1)+w-(w+1) = (w+1)*i+w by omega]
      exact ih (fun i => v (i+1)) (fun j h => hv (j+1) (by omega)) i (by omega)
theorem pack_const_mul (w n d : ℕ) :
    pack w n (fun _ => d) * (2^(w+1)-1) = d * (2^((w+1)*n)-1) := by
  let A := 2^(w+1)
  have hA : 0 < A := by unfold A; positivity
  have hpow (j : ℕ) : 0 < A^j := by positivity
  simp only [Nat.pow_mul]
  change pack w n (fun _ => d) * (A-1) = d * (A^n-1)
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, Nat.add_mul, Nat.mul_assoc, ih, Nat.pow_succ]
    change A*(d*(A^n-1)) + d*(A-1) = d*(A^n*A-1)
    have ha : A^n*A-1 = A*(A^n-1)+(A-1) := by
      obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (hpow n).ne'
      rw [ha,Nat.succ_mul]
      simp only [Nat.succ_sub_one, Nat.mul_comm A a]
      omega
    rw [ha, Nat.mul_add, Nat.mul_left_comm]
def upperDigits (w M : ℕ) (z : ℕ → ℤ) (i : ℕ) : ℕ :=
  ((2^w:ℕ) - (M:ℤ) - 1 + z i).toNat
def eval (B : ℤ) : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n+1, a => a 0 + B * eval B n (fun i => a (i+1))
theorem eval_sub (B : ℤ) (n : ℕ) (u v : ℕ → ℤ) :
    eval B n (fun i => u i - v i) = eval B n u - eval B n v := by
  induction n generalizing u v with
  | zero => simp [eval]
  | succ n ih => simp only [eval, ih]; ring
theorem eval_split (B : ℤ) (n m : ℕ) (v : ℕ → ℤ) :
    eval B (n+m) v = eval B n v + B^n * eval B m (fun i => v (i+n)) := by
  induction n generalizing v with
  | zero => simp [eval]
  | succ n ih =>
    rw [Nat.succ_add, eval, eval, ih, pow_succ]
    simp only [Nat.add_assoc, Nat.add_comm n 1]
    ring
def lag (q : ℕ) (v : ℕ → ℤ) (i : ℕ) : ℤ := if q ≤ i then v (i-q) else 0
theorem eval_lag (B : ℤ) (q n : ℕ) (v : ℕ → ℤ) :
    eval B n (lag q v) = B^min q n * eval B (n-q) v := by
  induction n generalizing q with
  | zero => simp [eval]
  | succ n ih =>
    cases q with
    | zero =>
      have h : lag 0 v = v := by funext i; simp [lag]
      simp [h]
    | succ q =>
      change lag (q+1) v 0 + B * eval B n (fun i => lag (q+1) v (i+1)) = _
      simp only [lag, show ¬ q+1 ≤ 0 by omega, ite_false, zero_add, Nat.add_le_add_iff_right,
        Nat.add_sub_add_right]
      change B * eval B n (lag q v) = _
      rw [ih, show min (q+1) (n+1) = min q n + 1 by omega, pow_succ]
      ring
theorem lag_mod (B : ℤ) (q n : ℕ) (h : q ≤ n) (v : ℕ → ℤ) :
    B^n ∣ eval B n (lag q v) - B^q * eval B n v := by
  rw [eval_lag, Nat.min_eq_left h]
  have hs : eval B n v = eval B (n-q) v + B^(n-q) * eval B q (fun i => v (i+(n-q))) := by
    simpa only [Nat.sub_add_cancel h] using eval_split B (n-q) q v
  rw [hs]
  use -(eval B q (fun i => v (i+(n-q))))
  have pow : B^q * B^(n-q) = B^n := by rw [← pow_add, Nat.add_sub_of_le h]
  rw [← pow]
  ring
def selectedMask (w n : ℕ) (sel : ℕ → Bool) := pack w n (fun i => if sel i then 2^w else 0)
theorem upper_selected (w n : ℕ) (v : ℕ → ℕ) (sel : ℕ → Bool) (hv : ∀ i<n, v i < 2^(w+1))
    (test : pack w n v &&& selectedMask w n sel = 0) :
    ∀ i < n, sel i = true → v i < 2^w := by
  intro i hi hsel
  have hlt : (2:ℕ)^w < 2^(w+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hm : ∀ j < n, (if sel j then 2^w else 0) < (2:ℕ)^(w+1) := by
    intro j _; split <;> omega
  have hh := congrArg (fun a : ℕ => a.testBit ((w+1)*i+w)) test
  simp only [Nat.testBit_and, Nat.zero_testBit, selectedMask, guard_digit w n _ hv i hi,
    guard_digit w n _ hm i hi, hsel, ite_true, Nat.testBit_two_pow_self, Bool.and_true] at hh
  by_contra! h
  simp [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h (hv i hi)] at hh
theorem pack_int (w n : ℕ) (v : ℕ → ℕ) :
    (pack w n v:ℤ) = eval ((2^(w+1):ℕ):ℤ) n (fun i => (v i:ℤ)) := by
  induction n generalizing v with
  | zero => simp [pack, eval]
  | succ n ih =>
    simp only [pack, eval, Nat.cast_add, Nat.cast_mul, ih]
    ring
theorem eval_affine (B a : ℤ) (n : ℕ) (v : ℕ → ℤ) :
    eval B n (fun i => a + v i) = a * eval B n (fun _ => 1) + eval B n v := by
  induction n generalizing v with
  | zero => simp [eval]
  | succ n ih => simp only [eval, ih]; ring
theorem upperDigits_word (w M n : ℕ) (z : ℕ → ℤ)
    (rough : ∀ i<n, |z i|+M+1 ≤ ((2^w:ℕ):ℤ)) :
    (pack w n (upperDigits w M z):ℤ) =
      (((2^w:ℕ):ℤ)-M-1) * (pack w n (fun _ => 1):ℕ) + eval ((2^(w+1):ℕ):ℤ) n z := by
  have ev (i : ℕ) (hi : i<n) :
      (upperDigits w M z i:ℤ) = ((2^w:ℕ):ℤ)-M-1 + z i := by
    unfold upperDigits
    apply Int.toNat_of_nonneg
    have b := rough i hi
    have := neg_abs_le (z i)
    omega
  have extfun (B : ℤ) (m : ℕ) (f g : ℕ → ℤ) (h : ∀ i< m, f i = g i) : eval B m f = eval B m g := by
    induction m generalizing f g with
    | zero => rfl
    | succ m ih =>
      simp only [eval, h 0 (by omega)]
      rw [ih (fun i => f (i+1)) (fun i => g (i+1)) (fun i hi => h (i+1) (by omega))]
  rw [pack_int, pack_int, extfun _ _ _ _ ev, eval_affine]
  simp
def prefixWord (B : ℤ) (q j n : ℕ) (D : ℤ) : ℤ :=
  (D * (B^(q*j)-1) / (B^q-1)) % B^n
theorem word_congruence (B : ℤ) (hB : 1 < B) (q j n : ℕ) (hq : 0<q)
    (hn : n ≤ q*j) (D : ℤ) :
    ((1-B^q)*prefixWord B q j n D-D) % B^n = 0 := by
  let F := B^q-1
  have hF : 0 < F := by
    unfold F
    have := one_lt_pow₀ hB hq.ne'; omega
  have hf : F ∣ B^(q*j)-1 := by
    rw [pow_mul]
    exact sub_dvd_pow_sub_pow (B^q) 1 j |> (by simpa [F] using ·)
  have hdf : F ∣ D * (B^(q*j)-1) := dvd_mul_of_dvd_right hf D
  let U := D * (B^(q*j)-1) / F
  have hu : U * F = D * (B^(q*j)-1) := Int.ediv_mul_cancel hdf
  have correction : B^n ∣ U % B^n-U := by
    use -(U / B^n)
    have z := Int.emod_add_ediv_mul U (B^n)
    linarith only [z]
  have divU : B^n ∣ (1-B^q)*U-D := by
    have fac : (1-B^q)*U-D = -D*B^(q*j) := by unfold F at hu; linarith only [hu]
    rw [fac]
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ hn) _
  have sum := dvd_add divU (dvd_mul_of_dvd_right correction (1-B^q))
  apply Int.emod_eq_zero_of_dvd
  change B^n ∣ (1-B^q)*(U % B^n)-D
  convert sum using 1; ring
open Finset
theorem eval_eq_sum (B : ℤ) (n : ℕ) (a : ℕ → ℤ) :
    eval B n a = ∑ i ∈ range n, B^i * a i := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
    rw [eval_split B n 1 a, sum_range_succ, ih]
    simp [eval]
def firstOffset (start k : ℕ) : ℕ := (k-start % k) % k
def numHits (r k n : ℕ) : ℕ := if r<n then (n-1-r)/k+1 else 0
def divisorWord (B : ℤ) (start n k : ℕ) : ℤ :=
  let r := firstOffset start k
  let m := numHits r k n
  if m=0 then 0 else if m=1 then B^r else B^r * ((B^(k*m)-1)/(B^k-1))
private theorem offset_iff (start k i : ℕ) (hk : 0<k) :
    k ∣ start+i ↔ i % k = firstOffset start k := by
  let r := firstOffset start k
  have small : r<k := Nat.mod_lt _ hk
  have h0 : start+r ≡ 0 [MOD k] := by
    change (start+(k-start % k) % k) % k=0 % k
    rw [Nat.add_mod_mod, ← Nat.mod_add_mod, Nat.add_sub_of_le (Nat.mod_lt _ hk).le, Nat.mod_self, Nat.zero_mod]
  rw [← Nat.modEq_zero_iff_dvd]
  change _ ↔ i % k=r
  constructor
  · intro h
    have e := Nat.ModEq.add_iff_left (Nat.ModEq.refl start) |>.mp (h.trans h0.symm)
    simpa [Nat.ModEq, Nat.mod_eq_of_lt small] using e
  · intro h
    have e : i ≡ r [MOD k] := by simpa [Nat.ModEq, Nat.mod_eq_of_lt small] using h
    exact (e.add_left start).trans h0
private theorem hit_iff (r k n j : ℕ) (hk : 0<k) :
    j<numHits r k n ↔ r+j*k<n := by
  unfold numHits
  split_ifs with hr
  · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hk]; omega
  · simp; omega
theorem divisor_word_spec (B : ℤ) (hB : 1<B) (start n k : ℕ) (hk : 0<k) :
    eval B n (fun i => if k ∣ start+i then 1 else 0) = divisorWord B start n k := by
  let r := firstOffset start k
  let m := numHits r k n
  have small : r<k := Nat.mod_lt _ hk
  have image_eq : (range m).image (fun j => r+j*k) = (range n).filter (fun i => i % k=r) := by
    ext i
    simp only [mem_image, mem_range, mem_filter]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨(hit_iff r k n j hk).mp hj, by simp [Nat.add_mod, Nat.mod_eq_of_lt small]⟩
    · rintro ⟨hi,hr⟩
      have e : r + (i/k)*k=i := by rw [← hr, Nat.mul_comm _ k, Nat.mod_add_div]
      exact ⟨i/k,(hit_iff r k n (i/k) hk).mpr (e.le.trans_lt hi),e⟩
  have hpoly : eval B n (fun i => if k ∣ start+i then 1 else 0) =
      B^r * ∑ j ∈ range m, (B^k)^j := by
    rw [eval_eq_sum]
    simp_rw [offset_iff start k _ hk, mul_ite, mul_one, mul_zero]
    change (∑ i ∈ range n, if i % k=r then B^i else 0) = _
    rw [← sum_filter, ← image_eq, sum_image, mul_sum]
    · apply sum_congr rfl
      intro j _
      rw [pow_add, Nat.mul_comm j k, pow_mul]
    · intro i _ j _ h
      exact Nat.eq_of_mul_eq_mul_right hk (Nat.add_left_cancel h)
  rw [hpoly]
  change B^r * ∑ j ∈ range m, (B^k)^j =
    if m=0 then 0 else if m=1 then B^r else B^r*((B^(k*m)-1)/(B^k-1))
  split_ifs with hm hm
  · simp [hm]
  · simp [hm]
  · have nz : B^k-1 ≠ 0 := by have := one_lt_pow₀ hB hk.ne'; omega
    rw [pow_mul, ← geom_sum_mul (B^k) m, Int.mul_ediv_cancel _ nz]
theorem divisor_block (S : Finset ℕ) (a : ℕ → ℤ) (B : ℤ) (hB : 1<B)
    (start n : ℕ) (hk : ∀ k ∈ S, 0<k) :
    eval B n (fun i => ∑ k ∈ S, if k ∣ start+i then a k else 0) =
      ∑ k ∈ S, a k * divisorWord B start n k := by
  rw [eval_eq_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k h
  rw [← divisor_word_spec B hB start n k (hk k h), eval_eq_sum, mul_sum]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp [*, mul_comm]
def binarySum : ℕ → ℕ → (ℕ → ℤ) → ℤ
  | 0, s, f => f s
  | j+1, s, f => binarySum j s f + binarySum j (s+2^j) f
theorem binarySum_spec (level start : ℕ) (f : ℕ → ℤ) :
    binarySum level start f = ∑ i ∈ range (2^level), f (start+i) := by
  induction level generalizing start with
  | zero => simp [binarySum]
  | succ j ih =>
    rw [binarySum, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    simp only [Nat.add_assoc]
theorem pack_lt (w n : ℕ) (v : ℕ → ℕ) (h : ∀ i<n, v i<2^(w+1)) :
    pack w n v < 2^((w+1)*n) := by
  induction n generalizing v with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, Nat.mul_succ, Nat.pow_add 2 ((w+1)*n) (w+1), Nat.mul_comm (2^((w+1)*n)) (2^(w+1))]
    have lo := h 0 (by omega)
    have hi := ih (fun a => v (a+1)) (fun a ha => h (a+1) (by omega))
    calc
      _ < 2^(w+1) * (pack w n (fun i => v (i+1))+1) := by rw [Nat.mul_add]; omega
      _ ≤ _ := Nat.mul_le_mul_left _ hi
def primePrefix (S : Finset ℕ) (a : ℕ → ℤ) (scale : ℤ) (t : ℕ) : ℤ :=
  (∑ k ∈ S, a k * (t/k:ℕ)) - scale
theorem prefix_succ (S : Finset ℕ) (a : ℕ → ℤ) (scale : ℤ) (t : ℕ) :
    primePrefix S a scale (t+1) = primePrefix S a scale t + ∑ k ∈ S, if k ∣ t+1 then a k else 0 := by
  unfold primePrefix
  rw [sub_add_eq_add_sub,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  split_ifs with hd
  · rw [Nat.succ_div_of_dvd hd,Nat.cast_add,Nat.cast_one]; ring
  · rw [Nat.succ_div_of_not_dvd hd,add_zero]
private theorem eval_add (B : ℤ) (n : ℕ) (u v : ℕ → ℤ) :
    eval B n (fun i => u i+v i) = eval B n u + eval B n v := by
  rw [eval_eq_sum,eval_eq_sum,eval_eq_sum]
  simp [mul_add,sum_add_distrib]
theorem prefix_word_mod (S : Finset ℕ) (a : ℕ → ℤ) (scale : ℤ) (B : ℤ) (s n : ℕ)
    (hB : 1<B) (hn : 0<n) (hk : ∀ k ∈ S, 0<k) :
    (1-B)*eval B n (fun i => primePrefix S a scale (s+1+i)) ≡
      primePrefix S a scale s + ∑ k ∈ S, a k * divisorWord B (s+1) n k [ZMOD B^n] := by
  let v := fun i => primePrefix S a scale (s+1+i)
  let d := fun i => ∑ k ∈ S, if k ∣ s+1+i then a k else 0
  let z := fun i : ℕ => if i=0 then primePrefix S a scale s else 0
  have hrec : (fun i => v i - lag 1 v i) = fun i => z i + d i := by
    funext i
    cases i with
    | zero => simp [v,z,d,lag,prefix_succ]
    | succ i =>
      simp only [v,z,d,lag,Nat.succ_ne_zero,ite_false,zero_add,show 1 ≤ i+1 by omega,ite_true,
        Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
      rw [Nat.add_succ,prefix_succ]; exact add_sub_cancel_left _ _
  have zval : eval B n z = primePrefix S a scale s := by
    rw [eval_eq_sum]
    simp [z,mul_ite,Finset.sum_ite_eq',hn]
  have e := congrArg (eval B n) hrec
  rw [eval_sub,eval_add,zval] at e
  have hd : eval B n d = ∑ k ∈ S, a k * divisorWord B (s+1) n k :=
    divisor_block S a B hB _ _ hk
  rw [hd] at e
  apply Int.modEq_iff_dvd.mpr
  have h := lag_mod B 1 n hn v
  rw [pow_one] at h
  change B^n ∣ primePrefix S a scale s + _ - (1-B)*eval B n v
  rw [←e]
  convert dvd_neg.mpr h using 1; ring
theorem prefix_mod_eval (S : Finset ℕ) (a : ℕ → ℤ) (scale : ℤ) (B : ℤ) (s n : ℕ)
    (hB : 1<B) (hn : 0<n) (hk : ∀ k ∈ S, 0<k) :
    eval B n (fun i => primePrefix S a scale (s+1+i)) ≡
      prefixWord B 1 n n (primePrefix S a scale s + ∑ k ∈ S, a k * divisorWord B (s+1) n k) [ZMOD B^n] := by
  let P := eval B n (fun i => primePrefix S a scale (s+1+i))
  let D := primePrefix S a scale s + ∑ k ∈ S, a k * divisorWord B (s+1) n k
  let Q := prefixWord B 1 n n D
  have p : (1-B)*P ≡ D [ZMOD B^n] := prefix_word_mod S a scale B s n hB hn hk
  have qw := word_congruence B hB 1 n n (by decide) (by omega) D
  rw [pow_one] at qw
  have q : (1-B)*Q ≡ D [ZMOD B^n] := by
    apply Int.modEq_iff_dvd.mpr
    simpa [Q,neg_sub] using (dvd_neg.mpr (Int.dvd_of_emod_eq_zero qw))
  have h := Int.modEq_iff_dvd.mp (p.trans q.symm)
  have factor : B^n ∣ (1-B)*(Q-P) := by convert h using 1; ring
  have d0 : B^n ∣ (1-B)*(Q-P)*((B^n-1)/(B-1)) := dvd_mul_of_dvd_left factor _
  have hdiv : B-1 ∣ B^n-1 := by simpa using sub_dvd_pow_sub_pow B 1 n
  have cancel := Int.ediv_mul_cancel hdiv
  have d1 : B^n ∣ (Q-P) - B^n*(Q-P) := by
    convert d0 using 1
    linear_combination (Q-P) * cancel
  have d2 := dvd_add d1 (dvd_mul_right (B^n) (Q-P))
  apply Int.modEq_iff_dvd.mpr
  change B^n ∣ Q-P
  simpa only [sub_add_cancel] using d2
def digit (width word i : ℕ) := word / 2^(width*i) % 2^width
theorem digit_pack (w n : ℕ) (f : ℕ → ℕ) (h : ∀ i<n, f i < 2^(w+1)) :
    ∀ i<n, digit (w+1) (pack w n f) i = f i := by
  induction n generalizing f with
  | zero => omega
  | succ n ih =>
    intro i hi
    have z := h 0 (by omega)
    cases i with
    | zero =>
      simp [digit,pack,Nat.add_mod,Nat.mod_eq_of_lt z]
    | succ i =>
      have d : (2^(w+1)*pack w n (fun i => f (i+1)) + f 0)/2^(w+1) =
          pack w n (fun i => f (i+1)) := by
        rw [Nat.add_comm,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt z,zero_add]
      unfold digit
      rw [pack,Nat.mul_succ,Nat.pow_add 2 ((w+1)*i) (w+1),Nat.mul_comm (2^((w+1)*i)) (2^(w+1)),← Nat.div_div_eq_div_mul,d]
      exact ih _ (fun k hk => h (k+1) (by omega)) i (by omega)
theorem decode_signed (w n : ℕ) (v : ℕ → ℤ) (Q : ℤ)
    (hQ : eval ((2^(w+1):ℕ):ℤ) n v ≡ Q [ZMOD ((2^(w+1):ℕ):ℤ)^n])
    (hsmall : ∀ i<n, |v i| < ((2^w:ℕ):ℤ)) :
    let A : ℤ := ((2^(w+1):ℕ):ℤ)
    let b : ℤ := ((2^w:ℕ):ℤ)
    let word := ((Q + b * ((A^n-1)/(A-1))) % A^n).toNat
    ∀ i<n, v i = (digit (w+1) word i:ℤ)-b := by
  dsimp only
  let A : ℤ := ((2^(w+1):ℕ):ℤ)
  let b : ℤ := ((2^w:ℕ):ℤ)
  let f := fun i => (b+v i).toNat
  have H0 (i : ℕ) (hi : i<n) : (f i:ℤ) = b + v i := by
    apply Int.toNat_of_nonneg
    have := (abs_lt.mp (hsmall i hi)).1; change (0:ℤ) ≤ ((2^w:ℕ):ℤ)+v i; omega
  have H1 : ∀ i<n, f i < 2^(w+1) := by
    intro i hi
    have h := (abs_lt.mp (hsmall i hi)).2
    have h' := H0 i hi
    unfold b at h'
    exact_mod_cast (show (f i:ℤ) < ((2^w:ℕ):ℤ)*2 by omega)
  have ez : (pack w n f:ℤ) = b*(∑ i ∈ Finset.range n, A^i) + eval A n v := by
    rw [pack_int,eval_eq_sum,eval_eq_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [H0 i (mem_range.mp hi)]
    change A^i*(b+v i) = b*A^i + A^i*v i
    ring
  have hA : 1<A := by
    unfold A
    exact_mod_cast (Nat.one_lt_pow (by omega) (by decide) : 1<(2:ℕ)^(w+1))
  have full : (pack w n f:ℤ) ≡ Q + b*((A^n-1)/(A-1)) [ZMOD A^n] := by
    rw [ez, ← geom_sum_mul A n,Int.mul_ediv_cancel _ (by omega)]
    rw [add_comm]
    exact hQ.add_right _
  have sz : (pack w n f:ℤ) < A^n := by
    unfold A; exact_mod_cast (by simpa [Nat.pow_mul] using pack_lt w n f H1)
  have eq : ((Q+b*((A^n-1)/(A-1))) % A^n).toNat = pack w n f := by
    have eq := full.symm
    change _ % A^n = (pack w n f:ℤ) % A^n at eq
    rw [Int.emod_eq_of_lt (by positivity) sz] at eq
    rw [eq,Int.toNat_natCast]
  change ∀ i<n, v i = (digit (w+1) (((Q+b*((A^n-1)/(A-1))) % A^n).toNat) i:ℤ)-b
  rw [eq]
  intro i hi
  rw [digit_pack w n f H1 i hi,H0 i hi]
  ring
end FR7022Lane
namespace FR7022Lane
open Finset
end FR7022Lane
namespace GoldbachCoefficientPrefix
open Finset
end GoldbachCoefficientPrefix
namespace FR7022Lane
open GoldbachCoefficientPrefix
def rows (q : ℕ) (D : ℕ → ℤ) (i : ℕ) := rowPrefix q D (i+1)
theorem row_lag (q : ℕ) (hq : 0<q) (D : ℕ → ℤ) (i : ℕ) :
    rows q D i - lag q (rows q D) i = D (i+1) := by
  change rowPrefix q D (i+1) - _ = _
  rw [rowPrefix,if_pos ⟨hq,by omega⟩]
  by_cases h : q ≤ i
  · simp only [lag,h,ite_true,rows,show i+1-q=i-q+1 by omega]
    ring
  · simp only [lag,h,ite_false,sub_zero,show i+1-q=0 by omega]
    rw [rowPrefix]
    simp
theorem rows_residue (B : ℤ) (q n : ℕ) (hq : 0<q) (hn : q≤n) (D : ℕ → ℤ) :
    B^n ∣ (1-B^q)*eval B n (rows q D) - eval B n (fun i => D (i+1)) := by
  have he : (fun i => D (i+1)) = (fun i => rows q D i - lag q (rows q D) i) :=
    funext (fun i => (row_lag q hq D i).symm)
  rw [he,eval_sub]
  convert lag_mod B q n hn (rows q D) using 1
  ring
theorem rows_rough (q n : ℕ) (hq : 0<q) (D : ℕ → ℤ) (cap : ℤ) (hc : 0≤cap)
    (hD : ∀ j, 0<j → j≤n → |D j| ≤ cap) :
    ∀ i<n, |rows q D i| ≤ (n:ℤ)*cap := by
  have aux (h t : ℕ) (ht : t≤n) : |progression D q h t| ≤ (t:ℤ)*cap := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [progression_succ]
      have upper : |(if (t+1) % q=h % q then D (t+1) else 0)| ≤ cap := by
        split
        · exact hD _ (by omega) ht
        · simpa using hc
      exact (abs_add_le _ _).trans (by
        simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using add_le_add (ih (by omega)) upper)
  intro i hi
  rw [rows,← prefix_correct D q hq]
  exact (aux _ _ (by omega)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hc)
theorem all_residues (q n : ℕ) (hq : 0<q) (D : ℕ → ℤ) (M : ℕ → ℤ)
    (hzero : 0≤M 0) (mono : Monotone M)
    (hrows : ∀ i<n, (i+1).Coprime q → |rows q D i| ≤ M (i+1)) :
    ∀ t≤n, ∀ h, h.Coprime q → |progression D q h t| ≤ M t := by
  intro t
  induction t with
  | zero => intro _ h _; simpa using hzero
  | succ t ih =>
    intro ht h hc
    by_cases he : (t+1) % q=h % q
    · have cp : (t+1).Coprime q := by
        rw [Nat.Coprime] at hc ⊢
        exact (Nat.ModEq.gcd_eq (show (t+1) ≡ h [MOD q] from he)).trans hc
      have rep : progression D q h (t+1) = progression D q (t+1) (t+1) := by
        simp [progression,he]
      rw [rep,prefix_correct D q hq]
      exact hrows t (by omega) cp
    · rw [progression_succ,if_neg he,add_zero]
      exact (ih (by omega) h hc).trans (mono (by omega))
end FR7022Lane
namespace FR7022RadixPrefix
theorem unique (B : ℤ) (q j n : ℕ) (hn : n ≤ q*j) (D x y : ℤ)
    (hx : B^n ∣ (1-B^q)*x-D) (hy : B^n ∣ (1-B^q)*y-D) :
    B^n ∣ x-y := by
  let s : ℤ := ∑ i ∈ Finset.range j, (B^q)^i
  have hg : s*(B^q-1)=B^(q*j)-1 := by
    rw [pow_mul]
    exact geom_sum_mul _ _
  have d1 := dvd_sub hx hy
  have d2 := dvd_mul_of_dvd_left d1 s
  have d3 := dvd_mul_of_dvd_left (pow_dvd_pow B hn) (x-y)
  convert dvd_add d2 d3 using 1
  linear_combination (x-y)*hg
private theorem double_geom (z : ℤ) (m : ℕ) :
    (1+z)*(∑ i ∈ Finset.range m, (z^2)^i) = ∑ i ∈ Finset.range (2*m), z^i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, mul_add, ih]
    rw [show 2*m+2=(2*m+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      pow_succ z (2*m), ← pow_mul]
    ring
def accumulate (B mod : ℤ) : ℕ → ℕ → ℤ → ℤ
 | 0, _, x => x % mod
 | d+1, stride, x => accumulate B mod d (2*stride) ((x+B^stride*x) % mod)
private theorem modDiff (x m : ℤ) : m ∣ x % m-x := by
  use -(x/m)
  linarith only [Int.emod_add_ediv_mul x m]
theorem accumulate_eq (B : ℤ) (n d q : ℕ) (x : ℤ) :
    B^n ∣ accumulate B (B^n) d q x - x * (∑ i ∈ Finset.range (2^d), (B^q)^i) := by
  induction d generalizing q x with
  | zero =>
    simp only [accumulate,pow_zero,Finset.sum_range_one,mul_one]
    exact modDiff _ _
  | succ d ih =>
    let v := x + B^q*x
    let s := ∑ i ∈ Finset.range (2^d), (B^(2*q))^i
    have ind := ih (2*q) (v % (B^n))
    have round : B^n ∣ (v % (B^n))-v :=
      modDiff _ _
    have rest := dvd_add ind (dvd_mul_of_dvd_left round s)
    have hs : (1+B^q)*s = ∑ i ∈ Finset.range (2^(d+1)), (B^q)^i := by
      unfold s
      rw [Nat.pow_succ, Nat.mul_comm (2^d) 2, Nat.mul_comm 2 q, pow_mul]
      exact double_geom (B^q) (2^d)
    change B^n ∣ accumulate B (B^n) d (2*q) (v % (B^n)) - _
    convert rest using 1
    rw [← hs]
    dsimp [v]
    ring
end FR7022RadixPrefix
namespace FR7022RadixPrefix
def prefixPacked (mask : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k+1, step, x => prefixPacked mask k (2*step) ((x+(x <<< (64*step))) &&& mask)
theorem packed_eq (n d q x : ℕ) (hx : x < 2^(64*n)) :
    (prefixPacked (2^(64*n)-1) d q x : ℤ) =
        accumulate (2^64) (2^(64*n)) d q x := by
  induction d generalizing q x with
  | zero =>
    simp only [prefixPacked,accumulate]
    symm
    apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
    exact_mod_cast hx
  | succ d ih =>
    rw [prefixPacked, Nat.and_two_pow_sub_one_eq_mod, ih _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
    rw [accumulate,Nat.shiftLeft_eq,Int.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_pow]
    push_cast
    have hp : (2:ℤ)^(64*q) = 18446744073709551616^q := by rw [pow_mul]; norm_num
    rw [hp, mul_comm (x:ℤ)]
theorem packed_solves (B : ℤ) (n d q : ℕ) (D : ℤ)
    (hn : n ≤ q*2^d) :
    B^n ∣ (1-B^q)*accumulate B (B^n) d q D - D := by
  let s := ∑ i ∈ Finset.range (2^d), (B^q)^i
  have h := accumulate_eq B n d q D
  have geom : s*(B^q-1) = B^(q*2^d)-1 := by
    rw [pow_mul]
    exact geom_sum_mul _ _
  have mul := dvd_mul_of_dvd_right h (1-B^q)
  have tail := dvd_mul_of_dvd_left (pow_dvd_pow B hn) D
  change B^n ∣ accumulate B (B^n) d q D - D*s at h
  convert dvd_sub mul tail using 1
  linear_combination -D*geom
end FR7022RadixPrefix
namespace FR7022Verified
open FR7022Lane FR7022RadixPrefix
abbrev A : ℤ := 2^64
def modN (n : ℕ) : ℕ := 2^(64*n)
def residue (n q d : ℕ) (T : ℤ) : ℕ :=
  prefixPacked (modN n-1) d q ((T % (modN n:ℤ)).toNat)
theorem modulus (n : ℕ) : (modN n:ℤ) = A^n := by simp [modN,A,pow_mul]
theorem initial (n : ℕ) (T : ℤ) :
    ((T % (modN n:ℤ)).toNat:ℤ) = T % (modN n:ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by simp [modN]))
theorem initial_lt (n : ℕ) (T : ℤ) : (T % (modN n:ℤ)).toNat < modN n := by
  apply Int.ofNat_lt.mp
  rw [initial]
  exact Int.emod_lt_of_pos _ (by simp [modN])
theorem residue_lt (n q d : ℕ) (T : ℤ) : residue n q d T < modN n := by
  have aux (x : ℕ) (hx : x< modN n) : ∀ d q, prefixPacked (modN n-1) d q x < modN n := by
    intro d
    induction d generalizing x with
    | zero => intro; exact hx
    | succ d ih =>
      intro q
      simp only [prefixPacked,modN,Nat.and_two_pow_sub_one_eq_mod]
      apply ih
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
  exact aux _ (initial_lt n T) d q
theorem residue_solves (n q d : ℕ) (T : ℤ) (hn : n ≤ q*2^d) :
    A^n ∣ (1-A^q)*(residue n q d T:ℤ) - T := by
  have eqn := packed_eq n d q _ (initial_lt n T)
  change (residue n q d T:ℤ) = accumulate A (2^(64*n)) d q _ at eqn
  have shift : (2:ℤ)^(64*n) = A^n := by rw [pow_mul]
  rw [shift,initial] at eqn
  rw [eqn]
  have h := packed_solves A n d q (T % (modN n:ℤ)) hn
  have z : A^n ∣ T % (modN n:ℤ)-T := by
    rw [modulus]
    use -(T/A^n)
    linarith only [Int.emod_add_ediv_mul T (A^n)]
  convert dvd_add h z using 1
  ring
theorem prefix_congruence (n q d : ℕ) (T : ℤ) (D : ℕ → ℤ)
    (hq : 0<q) (hn : q≤n) (hlen : n≤q*2^d) (hT : eval A n (fun i => D (i+1)) = T) :
    ((modN n):ℤ) ∣ eval A n (rows q D) - residue n q d T := by
  rw [modulus]
  apply unique A q (2^d) n hlen T _ _ _ (residue_solves n q d T hlen)
  simpa only [←hT] using rows_residue A q n hq hn D
end FR7022Verified
namespace FR7022Lane
theorem variable_guard (w n : ℕ) (z : ℕ → ℤ) (M : ℕ → ℕ) (sel : ℕ → Bool)
    (rough : ∀ i<n, |z i| + (M i:ℤ) + 1 ≤ ((2^w:ℕ):ℤ))
    (cert : pack w n (upperDigits w 0 (fun i => z i - M i)) &&& selectedMask w n sel = 0) :
    ∀ i<n, sel i = true → z i ≤ (M i:ℤ) := by
  let v (i : ℕ) := z i - M i
  have vr (i : ℕ) (h : i<n) : |v i| + 1 ≤ ((2^w:ℕ):ℤ) := by
    have t := abs_sub (z i) (M i:ℤ)
    rw [abs_of_nonneg (Int.natCast_nonneg _)] at t
    dsimp [v]
    exact (add_le_add t (le_rfl : (1:ℤ) ≤ 1)).trans (rough i h)
  have low (i : ℕ) (hi : i<n) : 0 ≤ ((2^w:ℕ):ℤ) - 0 - 1 + v i := by
    have := vr i hi
    have := neg_abs_le (v i)
    omega
  have width (i : ℕ) (hi : i<n) : upperDigits w 0 v i < 2^(w+1) := by
    unfold upperDigits
    simp only [Nat.cast_zero]
    rw [Int.toNat_lt (low i hi),Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    have := vr i hi
    have := le_abs_self (v i)
    omega
  intro i hi hs
  have h := upper_selected w n _ sel width cert i hi hs
  unfold upperDigits at h
  simp only [Nat.cast_zero] at h
  rw [Int.toNat_lt (low i hi)] at h
  dsimp [v] at h
  omega
theorem variable_word (w n : ℕ) (z : ℕ → ℤ) (M : ℕ → ℕ)
    (rough : ∀ i<n, |z i| + (M i:ℤ) + 1 ≤ ((2^w:ℕ):ℤ)) :
    (pack w n (upperDigits w 0 (fun i => z i-M i)):ℤ) =
      (((2^w:ℕ):ℤ)-1) * (pack w n (fun _ => 1):ℕ) +
      eval ((2^(w+1):ℕ):ℤ) n z - (pack w n M:ℤ) := by
  rw [upperDigits_word, eval_sub, pack_int w n M]
  · ring
  · intro i hi
    have h := abs_sub (z i) (M i:ℤ)
    rw [abs_of_nonneg (Int.natCast_nonneg _)] at h
    have hh := rough i hi
    simp only [Nat.cast_zero, add_zero]
    omega
end FR7022Lane
namespace FR7022Lane
theorem cut_mask (x g l : ℕ) (hg : g < 2^l) :
    x % 2^l &&& g = x &&& g := by
  have h : (2^l-1) &&& g = g := by
    rw [Nat.and_comm,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt hg]
  rw [← Nat.and_two_pow_sub_one_eq_mod,Nat.and_assoc,h]
theorem transfer_mask (x y g l : ℕ) (hg : g < 2^l)
    (cong : ((2^l:ℕ):ℤ) ∣ (y:ℤ)-x) (cert : x &&& g = 0) : y &&& g = 0 := by
  have eqn : x % 2^l = y % 2^l :=
    Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr cong)
  rw [← cut_mask y g l hg,← eqn,cut_mask x g l hg,cert]
theorem eval_neg (B : ℤ) (n : ℕ) (z : ℕ → ℤ) :
    eval B n (fun i => -(z i)) = -(eval B n z) := by
  induction n generalizing z with
  | zero => simp [eval]
  | succ n ih =>
    simp only [eval,ih (fun i => z (i+1))]
    ring
theorem bounds_of_word_residue (w n p slack : ℕ) (z : ℕ → ℤ) (M : ℕ → ℕ)
    (sel : ℕ → Bool)
    (rough : ∀ i<n, |z i| + (M i:ℤ) + 1 ≤ ((2^w:ℕ):ℤ))
    (hslack : (slack:ℤ) = (((2^w:ℕ):ℤ)-1)*(pack w n (fun _ => 1):ℕ) - pack w n M)
    (hg : selectedMask w n sel < 2^((w+1)*n))
    (hp : p < 2^((w+1)*n))
    (cong : ((2^((w+1)*n):ℕ):ℤ) ∣ eval ((2^(w+1):ℕ):ℤ) n z - p)
    (upper : (p+slack) &&& selectedMask w n sel = 0)
    (lower : (slack+2^((w+1)*n)-p) &&& selectedMask w n sel = 0) :
    ∀ i<n, sel i = true → |z i| ≤ (M i:ℤ) := by
  have rp (i : ℕ) (hi : i<n) : |-(z i)|+(M i:ℤ)+1 ≤ ((2^w:ℕ):ℤ) := by
    simpa using rough i hi
  have upper' := variable_guard w n z M sel rough (transfer_mask _ _ _ _ hg (by
    rw [variable_word w n z M rough,Nat.cast_add,hslack]
    convert cong using 1
    ring) upper)
  have nn : p ≤ slack+2^((w+1)*n) := by omega
  have lower' := variable_guard w n (fun i => -z i) M sel rp (transfer_mask _ _ _ _ hg (by
    rw [variable_word w n _ M rp,eval_neg,Nat.cast_sub nn,Nat.cast_add,hslack]
    have dvd := dvd_sub (dvd_neg.mpr cong) (dvd_refl ((2^((w+1)*n):ℕ):ℤ))
    convert dvd using 1
    ring) lower)
  intro i hi hsel
  exact abs_le.mpr ⟨by linarith only [lower' i hi hsel],upper' i hi hsel⟩
end FR7022Lane
namespace FR7022Lane
def ray (start value i : ℕ) : ℕ := if start ≤ i then value else 0
theorem pack_ext (w n : ℕ) (f g : ℕ → ℕ) (h : ∀ i<n, f i = g i) :
    pack w n f = pack w n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack]
    rw [h 0 (by omega), ih _ _ (fun i hi => h (i+1) (by omega))]
theorem pack_add (w n : ℕ) (f g : ℕ → ℕ) :
    pack w n (fun i => f i+g i) = pack w n f + pack w n g := by
  induction n generalizing f g with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack]
    rw [ih (fun i => f (i+1)) (fun i => g (i+1))]
    ring
theorem pack_ray (w n start value : ℕ) :
    let A : ℤ := ((2^(w+1):ℕ):ℤ)
    (A-1)*(pack w n (ray start value):ℤ) =
       (A^n-A^(min start n))*(value:ℤ) := by
  dsimp only
  let A : ℤ := ((2^(w+1):ℕ):ℤ)
  change (A-1)*_=(A^n-A^min start n)*_
  induction n generalizing start with
  | zero => simp [pack]
  | succ n ih =>
    cases start with
    | zero =>
      have hz : (fun i => ray 0 value (i+1)) = ray 0 value := by funext i; simp [ray]
      simp only [pack,hz,Nat.cast_add,Nat.cast_mul,Nat.zero_min,pow_zero,pow_succ]
      change (A-1)*(A*↑(pack w n (ray 0 value))+(ray 0 value 0:ℤ)) = _
      rw [show ray 0 value 0 = value by simp [ray]]
      have h := ih 0
      simp only [Nat.zero_min,pow_zero] at h
      linear_combination A*h
    | succ s =>
      have hz : (fun i => ray (s+1) value (i+1)) = ray s value := by funext i; simp [ray]
      simp only [pack,hz,Nat.cast_add,Nat.cast_mul,show min (s+1) (n+1) = min s n+1 by omega,pow_succ]
      rw [show ray (s+1) value 0 = 0 by simp [ray]]
      change (A-1)*(A*↑(pack w n (ray s value))+0) = _
      linear_combination A*(ih s)
def fromRises (xs : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  (xs.map (fun p => ray p.1 p.2 i)).sum
def risesNumer (w n : ℕ) (xs : List (ℕ × ℕ)) : ℤ :=
  let A : ℤ := ((2^(w+1):ℕ):ℤ)
  (xs.map (fun p => (A^n-A^(min p.1 n))*(p.2:ℤ))).sum
theorem pack_rises (w n : ℕ) (xs : List (ℕ × ℕ)) :
    (((2^(w+1):ℕ):ℤ)-1)*(pack w n (fromRises xs):ℤ) = risesNumer w n xs := by
  induction xs with
  | nil =>
    have h : pack w n (fromRises []) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih =>
        change 2^(w+1) * pack w n (fromRises []) + 0 = 0
        rw [ih]; simp
    simp [h,risesNumer]
  | cons p l ih =>
    have h : fromRises (p::l) = fun i => ray p.1 p.2 i+fromRises l i := by
      funext i; simp [fromRises]
    rw [h,pack_add,Nat.cast_add,mul_add,pack_ray,ih]
    rfl
end FR7022Lane
namespace FR7022Lane
theorem pack_lt_radix_power (w n : ℕ) (f : ℕ → ℕ) (h : ∀ i<n, f i < 2^(w+1)) :
    pack w n f < (2^(w+1))^n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have z := h 0 (by omega)
    have hi := ih (fun i => f (i+1)) (fun i hi => h (i+1) (by omega))
    have hp := Nat.mul_le_mul_left (2^(w+1)) (Nat.succ_le_iff.mpr hi)
    rw [pow_succ, Nat.mul_comm ((2^(w+1))^n), pack]
    rw [Nat.mul_succ] at hp
    omega
theorem packed_periods (B : ℤ) (q j : ℕ) (f : ℕ → ℤ)
    (per : ∀ i, f (i+q)=f i) :
    eval B (q*j) f = eval B q f * ∑ k ∈ Finset.range j, (B^q)^k := by
  have many (j i : ℕ) : f (i+q*j)=f i := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ,← Nat.add_assoc,per,ih]
  induction j with
  | zero => simp [eval]
  | succ j ih =>
    rw [Nat.mul_succ,eval_split,ih, Finset.sum_range_succ,← pow_mul]
    rw [show (fun i => f (i+q*j)) = f by funext i; exact many j i]
    ring
theorem periodic_formula (w n q j : ℕ) (f : ℕ → ℕ) (hq : 0<q)
    (h : n ≤ q*j) (per : ∀ i, f (i+q)=f i)
    (digits : ∀ i<n, f i < 2^(w+1)) :
    let A : ℕ := 2^(w+1)
    pack w n f = (pack w q f * ((A^(q*j)-1)/(A^q-1))) % (A^n) := by
  dsimp only
  let A : ℕ := 2^(w+1)
  let s : ℕ := ∑ k ∈ Finset.range j, (A^q)^k
  have hA : 1<A := Nat.one_lt_pow (by omega) (by decide)
  have hAq : 1<A^q := Nat.one_lt_pow hq.ne' hA
  have hg : s*(A^q-1)=A^(q*j)-1 := by
    rw [pow_mul]
    exact geom_sum_mul_of_one_le hAq.le j
  have hs : (A^(q*j)-1)/(A^q-1) = s := by
    rw [← hg,Nat.mul_div_cancel _ (by omega)]
  change pack w n f = (pack w q f * _ ) % (A^n)
  rw [hs]
  have full : (pack w (q*j) f:ℤ) = (pack w q f:ℤ)*(s:ℤ) := by
    rw [pack_int,pack_int,packed_periods _ q j (fun i => (f i:ℤ)) (fun i => congrArg (fun x : ℕ => (x:ℤ)) (per i))]
    simp [s,A]
  have split := eval_split (A:ℤ) n (q*j-n) (fun i => (f i:ℤ))
  rw [Nat.add_sub_of_le h, ← pack_int, ← pack_int, full] at split
  have dv : ((A^n:ℕ):ℤ) ∣ ((pack w q f*s:ℕ):ℤ)-(pack w n f:ℤ) := by
    use eval (A:ℤ) (q*j-n) (fun i => (f (i+n):ℤ))
    push_cast
    linarith only [split]
  have hm := Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr dv)
  exact (Nat.mod_eq_of_lt (pack_lt_radix_power w n f digits)).symm.trans hm
end FR7022Lane
namespace FR7022Verified
open FR7022Lane FR7022RadixPrefix
def envWord (n : ℕ) (xs : List (ℕ×ℕ)) : ℕ :=
  (risesNumer 63 n xs / (A-1)).toNat
theorem env_eq (n : ℕ) (xs : List (ℕ×ℕ)) :
    envWord n xs = pack 63 n (fromRises xs) := by
  have h := pack_rises 63 n xs
  change (A-1)*(pack 63 n (fromRises xs):ℤ) = _ at h
  simp [envWord,←h,Int.mul_ediv_cancel_left _ (by decide : A-1 ≠ 0)]
def select (q i : ℕ) : Bool := decide ((i+1).gcd q=1)
def digit (q i : ℕ) : ℕ := if select q i then 2^63 else 0
def mask (q n : ℕ) : ℕ :=
  let j := n/q+1
  let b := 2^64
  (pack 63 q (digit q) * ((b^(q*j)-1)/(b^q-1))) % (b^n)
theorem mask_eq (q n : ℕ) (hq : 0<q) : mask q n = selectedMask 63 n (select q) := by
  apply Eq.symm
  change pack 63 n (digit q) = _
  apply periodic_formula 63 n q (n/q+1) _ hq
  · have ht := Nat.mod_lt n hq
    have hh := Nat.mod_add_div n q
    rw [Nat.mul_add,Nat.mul_one]
    omega
  · intro i
    simp only [digit,select,show i+q+1=i+1+q by omega,Nat.gcd_add_self_left] <;> rfl
  · intro i _
    unfold digit
    split <;> decide
theorem mask_lt (q n : ℕ) : selectedMask 63 n (select q) < modN n := by
  rw [modN,pow_mul]
  apply pack_lt_radix_power
  intro i _
  split <;> decide
def rep (n : ℕ) := ((2^64)^n-1)/(2^64-1)
theorem rep_eq (n : ℕ) : rep n = pack 63 n (fun _ => 1) := by
  have pd : pack 63 1 (fun _ => 1) = 1 := by decide
  have h := periodic_formula 63 n 1 n (fun _ => 1) (by decide) (by simp) (fun _ => rfl)
    (fun _ _ => by decide)
  simp only [pd,one_mul,pow_one] at h
  have ha : 0<(2^64:ℕ)^n := by positivity
  have hb := Nat.div_le_self ((2^64:ℕ)^n-1) (2^64-1)
  have hc : ((2^64:ℕ)^n-1)/(2^64-1) < (2^64)^n := by omega
  exact (h.trans (Nat.mod_eq_of_lt hc)).symm
theorem pack_mono (w n : ℕ) (f g : ℕ → ℕ) (h : ∀ i<n, f i ≤ g i) :
    pack w n f ≤ pack w n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    apply Nat.add_le_add _ (h 0 (by omega))
    exact Nat.mul_le_mul_left _ (ih _ _ (fun i hl => h (i+1) (by omega)))
theorem pack_constant (w n v : ℕ) :
    pack w n (fun _ => v) = v * pack w n (fun _ => 1) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack,ih]
    ring
def verify (n q d : ℕ) (T : ℤ) (xs : List (ℕ×ℕ)) : Bool :=
  let p := residue n q d T
  let slack := (2^63-1)*rep n - envWord n xs
  let g := mask q n
  ((p+slack) &&& g)==0 && (((slack+modN n)-p) &&& g)==0
theorem verify_sound (n q d : ℕ) (T : ℤ) (D : ℕ → ℤ) (xs : List (ℕ×ℕ))
    (hq : 0<q) (hn : q≤n) (hlen : n≤q*2^d) (hT : eval A n (fun i => D (i+1)) = T)
    (rough : ∀ i<n, |rows q D i| + (fromRises xs i:ℤ)+1 ≤ 2^63)
    (test : verify n q d T xs = true) :
    ∀ i<n, (i+1).Coprime q → |rows q D i| ≤ (fromRises xs i:ℤ) := by
  let s := (2^63-1)*rep n - envWord n xs
  have leq : envWord n xs ≤ (2^63-1)*rep n := by
    rw [env_eq,rep_eq,← pack_constant]
    apply pack_mono
    intro i hi
    have hz := rough i hi
    have ha := abs_nonneg (rows q D i)
    omega
  have hs : (s:ℤ) = (((2^63:ℕ):ℤ)-1)*(pack 63 n (fun _ => 1):ℕ)-pack 63 n (fromRises xs) := by
    change (((2^63-1)*rep n - envWord n xs : ℕ):ℤ) = _
    rw [Nat.cast_sub leq,env_eq,rep_eq]
    push_cast
    norm_num
  simp only [verify,Bool.and_eq_true,beq_iff_eq,mask_eq q n hq] at test
  have result := bounds_of_word_residue 63 n (residue n q d T) s (rows q D) (fromRises xs)
    (select q) rough hs (mask_lt q n) (residue_lt n q d T)
    (prefix_congruence n q d T D hq hn hlen hT) test.1 test.2
  intro i hi hcop
  exact result i hi (decide_eq_true hcop)
end FR7022Verified
namespace FR7022Verified
open FR7022Lane FR7022RadixPrefix
def shiftPower (n : ℕ) : ℕ := 1 <<< (64*n)
theorem shift_power (n : ℕ) : shiftPower n = (2^64)^n := by
  simp [shiftPower,Nat.shiftLeft_eq,pow_mul]
def fastRep (n : ℕ) := (shiftPower n-1)/(2^64-1)
def fastEnv (n : ℕ) (xs : List (ℕ×ℕ)) : ℕ :=
  let whole : ℤ := shiftPower n
  ((xs.map (fun p => (whole-(shiftPower (min p.1 n):ℤ))*(p.2:ℤ))).sum/(A-1)).toNat
def fastMask (q n : ℕ) : ℕ :=
  (pack 63 q (digit q) * ((shiftPower (q*(n/q+1))-1)/(shiftPower q-1))) % shiftPower n
def fastVerify (n q d : ℕ) (T : ℤ) (xs : List (ℕ×ℕ)) : Bool :=
  let m := shiftPower n
  let p := prefixPacked (m-1) d q ((T % (m:ℤ)).toNat)
  let slack := (2^63-1)*fastRep n-fastEnv n xs
  let g := fastMask q n
  ((p+slack) &&& g)==0 && (((slack+m)-p) &&& g)==0
theorem fast_eq (n q d : ℕ) (T : ℤ) (xs : List (ℕ×ℕ)) :
    fastVerify n q d T xs = verify n q d T xs := by
  have he : fastEnv n xs = envWord n xs := by
    simp only [fastEnv,envWord,risesNumer,shift_power,Nat.cast_pow,Nat.cast_ofNat]
  simp only [fastVerify,verify,he,fastRep,fastMask,mask,rep,residue,shift_power,modN,pow_mul]
end FR7022Verified
namespace FR7022FiniteCount
open Finset GoldbachCoefficientPrefix FR7022ProgressionTail
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem divisor_card (q h t k : ℕ) (hk : 0<k) :
    ((Icc 1 t).filter (fun j => j % q=h % q ∧ k ∣ j)).card = count q h t k := by
  let ms := (Icc 1 (t/k)).filter (fun m => (m*k) % q=h % q)
  have he : ms.image (fun m => m*k) = (Icc 1 t).filter (fun j => j % q=h % q ∧ k ∣ j) := by
    ext j
    simp only [ms,mem_image,mem_filter,mem_Icc]
    constructor
    · rintro ⟨m,⟨⟨hm,ht⟩,hr⟩,rfl⟩
      exact ⟨⟨Nat.mul_pos hm hk,(Nat.le_div_iff_mul_le hk).mp ht⟩,hr,dvd_mul_left _ _⟩
    · rintro ⟨⟨hj,ht⟩,hr,hd⟩
      have heq := Nat.div_mul_cancel hd
      exact ⟨j/k,⟨⟨Nat.div_pos (Nat.le_of_dvd hj hd) hk,
        (Nat.le_div_iff_mul_le hk).mpr (heq.trans_le ht)⟩,by simpa [heq] using hr⟩,heq⟩
  rw [← he,card_image_of_injective ms (fun _ _ heq => Nat.eq_of_mul_eq_mul_right hk heq)]
  rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem prefix_counts (S : Finset ℕ) (A : ℕ → ℤ) (q h t : ℕ)
    (hS : ∀ k∈S, 0<k) :
    progression (divisorWeight S A) q h t =
      ∑ k∈S, (count q h t k:ℤ)*A k := by
  rw [progression_as_Icc,← sum_filter]
  simp only [divisorWeight]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter,sum_const,nsmul_eq_mul,filter_filter,divisor_card q h t k (hS _ hk)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem count_nonunit (q h t k : ℕ) (hh : h.Coprime q) (hk : ¬k.Coprime q) :
    count q h t k = 0 := by
  unfold count
  rw [card_eq_zero,filter_eq_empty_iff]
  intro m hm hr
  have gc : (m*k).Coprime q := (Nat.ModEq.gcd_eq (show m*k ≡ h [MOD q] from hr)).trans hh
  exact hk (Nat.Coprime.of_dvd_left (dvd_mul_left _ _) gc)
end FR7022FiniteCount
namespace FR7022FiniteCount
open Finset GoldbachCoefficientPrefix FR7022ProgressionTail FR7022Verified FR7022Lane
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def centered (S : Finset ℕ) (a : ℕ → ℤ) (scale : ℕ) (j : ℕ) : ℤ :=
  divisorWeight S a j - if j=1 then (scale:ℤ) else 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem progress_sub (f g : ℕ → ℤ) (q h t : ℕ) :
    progression (fun j => f j - g j) q h t = progression f q h t - progression g q h t := by
  simp only [progression,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  split <;> simp_all
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem impulse (scale q h t : ℕ) (ht : 0<t) :
    progression (fun j => if j=1 then (scale:ℤ) else 0) q h t =
      if 1 % q=h % q then (scale:ℤ) else 0 := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  simp [progression,sum_range_succ']
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem centered_count (S : Finset ℕ) (a : ℕ → ℤ) (scale q h t : ℕ)
    (hS : ∀ k∈S, 0<k) (ht : 0<t) :
    progression (centered S a scale) q h t =
      (∑ k∈S, (count q h t k:ℤ)*a k) - if 1 % q=h % q then (scale:ℤ) else 0 := by
  unfold centered
  rw [progress_sub,prefix_counts S a q h t hS,impulse _ _ _ _ ht]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem crude (S : Finset ℕ) (a : ℕ → ℤ) (scale cap j : ℕ)
    (ha : ∀ k∈S, |a k| ≤ cap) :
    |centered S a scale j| ≤ (S.card:ℤ)*cap+scale := by
  apply (abs_sub _ _).trans
  apply add_le_add
  · unfold divisorWeight
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have h (k : ℕ) (hk : k∈S) : |if k ∣ j then a k else 0| ≤ (cap:ℤ) := by
      split
      · exact ha k hk
      · simp
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum h
  · split <;> simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem fromRises_mono (xs : List (ℕ×ℕ)) : Monotone (fromRises xs) := by
  induction xs with
  | nil => intro _ _ _; rfl
  | cons p l ih =>
    intro u v huv
    change ray p.1 p.2 u+fromRises l u ≤ ray p.1 p.2 v+fromRises l v
    apply Nat.add_le_add _ (ih huv)
    unfold ray
    split <;> split <;> omega
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem certified_finite (S : Finset ℕ) (a : ℕ → ℤ) (scale n q d cap env : ℕ)
    (T : ℤ) (xs : List (ℕ×ℕ)) (hS : ∀ k∈S, 0<k) (ha : ∀ k∈S, |a k| ≤ cap)
    (hq : 0<q) (hn : q≤n) (hlen : n≤q*2^d)
    (hT : eval A n (fun i => centered S a scale (i+1)) = T)
    (henv : ∀ i<n, fromRises xs i ≤ env)
    (hsize : n*(S.card*cap+scale)+env+1 ≤ 2^63)
    (test : fastVerify n q d T xs = true) :
    ∀ t, 0<t → t≤n → ∀ h, h.Coprime q →
      |(∑ k∈S, (count q h t k:ℤ)*a k) - (if 1 % q=h % q then (scale:ℤ) else 0)| ≤
        (fromRises xs (t-1):ℤ) := by
  let D := centered S a scale
  have cr := rows_rough q n hq D ((S.card:ℤ)*cap+scale) (by positivity)
    (fun j _ _ => crude S a scale cap j ha)
  have rr (i : ℕ) (hi : i<n) : |rows q D i| + (fromRises xs i:ℤ) + 1 ≤ 2^63 := by
    have sz : (n:ℤ)*((S.card:ℤ)*cap+scale)+env+1 ≤ 2^63 := by exact_mod_cast hsize
    have e : (fromRises xs i:ℤ) ≤ env := by exact_mod_cast henv i hi
    exact (add_le_add (add_le_add (cr i hi) e) le_rfl).trans sz
  have atRow := verify_sound n q d T D xs hq hn hlen hT rr ((fast_eq n q d T xs).symm.trans test)
  let M (t : ℕ) : ℤ := fromRises xs (t-1)
  have inc : Monotone M := by
    intro u v huv
    dsimp only [M]
    exact_mod_cast fromRises_mono xs (Nat.sub_le_sub_right huv 1)
  have bounds := all_residues q n hq D M (Int.natCast_nonneg _) inc (by
    intro i hi hc
    simpa only [M,Nat.add_sub_cancel] using atRow i hi hc)
  intro t ht htn h hc
  rw [← centered_count S a scale q h t hS ht]
  exact bounds t htn h hc
end FR7022FiniteCount

namespace FR7022Division
open FR7022Verified FR7022RadixPrefix
def residueWith (den geo m : ℕ) (t : ℤ) : ℕ :=
  (((t % (den:ℤ))*(geo:ℤ)-t/(den:ℤ)) % (m:ℤ)).toNat
theorem div_congr (a : ℤ) (N j q : ℕ) (hn : N ≤ q*j) (den geo : ℤ)
    (hd : den=a^q-1) (hg : den*geo=a^(q*j)-1) (t : ℤ) :
    a^N ∣ (1-a^q)*((t % den)*geo-t/den)-t := by
  have hr := Int.emod_add_ediv_mul t den
  have dvd := dvd_mul_of_dvd_right (pow_dvd_pow a hn) (-(t % den))
  convert dvd using 1
  linear_combination -(t % den)*hg + hr + ((t % den)*geo-t/den)*hd
theorem residueWith_eq (n q d j den geo : ℕ) (hn : n≤q*j) (hlen : n≤q*2^d)
    (hd : (den:ℤ)=A^q-1) (hg : (den:ℤ)*(geo:ℤ)=A^(q*j)-1) (t : ℤ) :
    residueWith den geo (modN n) t = residue n q d t := by
  let u := (t % (den:ℤ))*(geo:ℤ)-t/(den:ℤ)
  have hm : (0:ℤ)< modN n := by simp [modN]
  have hu : (residueWith den geo (modN n) t : ℤ)=u % (modN n:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne')
  have hc := div_congr A n j q hn den geo hd hg t
  change A^n ∣ (1-A^q)*u-t at hc
  have hc' := unique A q j n hn t u (residue n q d t) hc (residue_solves n q d t hlen)
  rw [← modulus] at hc'
  have he : (residue n q d t:ℤ) ≡ u [ZMOD (modN n:ℤ)] := Int.modEq_iff_dvd.mpr hc'
  have hl : (residue n q d t:ℤ)< modN n := by exact_mod_cast residue_lt n q d t
  apply Int.ofNat_inj.mp
  rw [hu, ← he, Int.emod_eq_of_lt (Int.natCast_nonneg _) hl]
end FR7022Division
namespace FR7022Division
open FR7022Verified FR7022Lane FR7022RadixPrefix
def natBind {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)
theorem natBind_eq {α : Type} (x : Nat) (f : Nat → α) : natBind x f=f x := by cases x <;> rfl
def intBind {α : Type} (x : Int) (f : Int → α) : α :=
  match x with
  | .ofNat n => natBind n (fun v => f (.ofNat v))
  | .negSucc n => natBind n (fun v => f (.negSucc v))
theorem intBind_eq {α : Type} (x : Int) (f : Int → α) : intBind x f=f x := by
  cases x <;> simp only [intBind,natBind_eq]
def placed (n : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (p,v)::xs => (v <<< (64*(min p n))) + placed n xs
-- The recorded positions increase. Consume the low positions first, so the running sum stays short.
def placedAscending (n : ℕ) : List (ℕ × ℕ) → ℕ → ℕ
  | [], acc => acc
  | (p,v)::xs, acc =>
    natBind (acc + (v <<< (64 * min p n))) (placedAscending n xs)

private theorem placedAscending_eq (n : ℕ) (xs : List (ℕ × ℕ)) (acc : ℕ) :
    placedAscending n xs acc = acc + placed n xs := by
  induction xs generalizing acc with
  | nil => simp [placedAscending, placed]
  | cons entry xs ih =>
    rcases entry with ⟨p, v⟩
    simp only [placedAscending, natBind_eq, ih, placed, Nat.add_assoc]

def env (n : Nat) (xs : List (Nat × Nat)) : Nat :=
  (((shiftPower n : Int) * ((xs.map Prod.snd).sum : Nat) - (placedAscending n xs 0 : Int)) / (A-1)).toNat
-- The telescope is the sparse-envelope identity of the verified #2649 source.
private theorem telescoped (n : ℕ) (xs : List (ℕ × ℕ)) :
  (xs.map (fun p => ((shiftPower n : ℤ) - shiftPower (min p.1 n)) * (p.2:ℤ))).sum =
    (shiftPower n : ℤ) * ((xs.map Prod.snd).sum : ℕ) - (placed n xs : ℤ) := by
  induction xs with
  | nil => simp [placed]
  | cons hd xs ih =>
    obtain ⟨i,v⟩ := hd
    rw [List.map_cons,List.sum_cons,ih]
    simp only [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,placed,Nat.cast_add,Nat.shiftLeft_eq,Nat.cast_mul,
      shiftPower,one_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
theorem env_eq (n : ℕ) (xs : List (ℕ × ℕ)) : env n xs=fastEnv n xs := by
  unfold env fastEnv
  dsimp only
  rw [telescoped, placedAscending_eq, Nat.zero_add]
def checkWord (den geo g s m : ℕ) (T : ℤ) : Bool :=
  intBind T (fun t => natBind (residueWith den geo m t) (fun p =>
    ((p+s) &&& g)==0 && (((s+m)-p) &&& g)==0))
def check (n q : ℕ) (a b : ℤ) (xs : List (ℕ × ℕ)) : Bool :=
  natBind (shiftPower n) (fun m =>
  natBind (shiftPower q-1) (fun den =>
  natBind ((shiftPower (q*(n/q+1))-1)/den) (fun geo =>
  natBind ((pack 63 q (digit q)*geo) % m) (fun g =>
  natBind ((2^63-1)*fastRep n-env n xs) (fun s =>
    checkWord den geo g s m a && checkWord den geo g s m b)))))
theorem shape (n q : ℕ) (hq : 0<q) :
    let j := n/q+1
    let den := shiftPower q-1
    let geo := (shiftPower (q*j)-1)/den
    n≤q*j ∧ (den:ℤ)=A^q-1 ∧ (den:ℤ)*(geo:ℤ)=A^(q*j)-1 := by
  dsimp only
  have hpos : 1 < (2^64:ℕ)^q := Nat.one_lt_pow hq.ne' (by decide)
  let s := ∑ i ∈ Finset.range (n/q+1), ((2^64:ℕ)^q)^i
  have hgeom : s*((2^64:ℕ)^q-1)=(2^64)^(q*(n/q+1))-1 := by
    rw [pow_mul]; exact geom_sum_mul_of_one_le hpos.le _
  have hN : n≤q*(n/q+1) := by
    have a:=Nat.mod_lt n hq
    have b:=Nat.mod_add_div n q
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hbig : 1≤(2^64:ℕ)^(q*(n/q+1)) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  rw [shift_power,shift_power,←hgeom,Nat.mul_div_cancel _ (by omega)]
  refine ⟨hN,?_,?_⟩
  · simp [Nat.cast_sub hpos.le,A]
  · rw [← Nat.cast_mul,Nat.mul_comm, hgeom,Nat.cast_sub hbig]
    simp [A]
theorem check_eq (n q d : ℕ) (hq : 0<q) (hlen : n≤q*2^d) (a b : ℤ) (xs : List (ℕ × ℕ)) :
    check n q a b xs = (fastVerify n q d a xs && fastVerify n q d b xs) := by
  obtain ⟨hN,hd,hg⟩ := shape n q hq
  have hsm : shiftPower n=modN n := by simp [shiftPower,modN,Nat.shiftLeft_eq]
  simp only [check,checkWord,natBind_eq,intBind_eq,env_eq,fastVerify]
  change _ = (_ && _)
  simp only [fastMask]
  rw [show residueWith _ _ (shiftPower n) a = residue n q d a from
    hsm ▸ residueWith_eq n q d (n/q+1) _ _ hN hlen hd hg a,
    show residueWith _ _ (shiftPower n) b = residue n q d b from
    hsm ▸ residueWith_eq n q d (n/q+1) _ _ hN hlen hd hg b]
  simp only [residue, hsm]
end FR7022Division

namespace FR7022NextRows
open Finset FR7022Verified FR7022Lane FR7022FiniteCount FR7022ProgressionTail GoldbachCoefficientPrefix
structure Row where
  q : ℕ
  lo : ℤ
  hi : ℤ
  cap : ℕ
  finiteCost : ℕ
  tailCost : ℕ
  count : ℕ
  encoded : ℕ
def rises : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k+1, w => (w % 8388608,(w>>>23) % 8589934592)::rises k (w>>>56)
def envelope (r : Row) : List (ℕ × ℕ) := rises r.count r.encoded
def fee (scale : ℕ) (x : ℕ × ℕ) : ℕ :=
  (x.2*1000000000000 + scale*(x.1+1) - 1) / (scale*(x.1+1))
def valid (B scale K cap : ℕ) (r : Row) : Bool :=
  let e := envelope r
  let top := (e.map Prod.snd).sum
  decide (0<r.q ∧ r.q≤B ∧ B≤r.q*2^((B/r.q).log2+1) ∧
    B*(K*cap+scale)+top+1≤2^63 ∧
    (e.map (fee scale)).sum=r.finiteCost ∧ top≤r.cap ∧
    fee scale (B,r.cap-top)=r.tailCost ∧
    e.all (fun a => decide (a.1<B)) ∧ 0<scale)
def endpoint (b e a : ℤ) (scale : ℕ) : ℤ := 1000*b+a*e-scale
def check (B scale : ℕ) (b e : ℤ) (r : Row) : Bool :=
  FR7022Division.check B r.q (endpoint b e r.lo scale) (endpoint b e r.hi scale) (envelope r)
theorem rises_le (xs : List (ℕ × ℕ)) (i : ℕ) :
    fromRises xs i ≤ (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons x l ih =>
    change ray x.1 x.2 i+fromRises l i ≤ x.2+(l.map Prod.snd).sum
    apply Nat.add_le_add _ ih
    unfold ray
    split <;> omega
theorem word_eq (S : Finset ℕ) (b e : ℕ → ℤ) (w z u : ℤ) (B scale : ℕ) (hB : 0<B)
    (hw : eval A B (fun i => divisorWeight S b (i+1))=w)
    (hz : eval A B (fun i => divisorWeight S e (i+1))=z) :
    eval A B (fun i => centered S (fun k => 1000*b k+u*e k) scale (i+1)) =
      endpoint w z u scale := by
  have hlin (j : ℕ) : divisorWeight S (fun k => 1000*b k+u*e k) j =
      1000*divisorWeight S b j + u*divisorWeight S e j := by
    simp only [divisorWeight,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro k _
    split <;> simp
  have lone (N : ℕ) :
      eval A N (fun i => if i+1=1 then (scale:ℤ) else 0)= if 0<N then scale else 0 := by
    rw [eval_eq_sum]
    cases N with
    | zero => simp
    | succ k =>
      rw [Finset.sum_range_succ']
      simp
  rw [← hw,← hz]
  simp only [centered,hlin]
  rw [eval_sub,lone,if_pos hB]
  unfold endpoint
  simp only [eval_eq_sum,mul_add,mul_sum]
  congr 1
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring
theorem bound (S : Finset ℕ) (b e : ℕ → ℤ) (w z u : ℤ) (B scale K cap : ℕ) (r : Row)
    (hS : ∀ k∈S,0<k) (hlen : S.card≤K)
    (hcap : ∀ k∈S, |1000*b k+u*e k|≤cap)
    (hw : eval A B (fun i => divisorWeight S b (i+1))=w)
    (hz : eval A B (fun i => divisorWeight S e (i+1))=z)
    (endpt : u=r.lo ∨ u=r.hi) (ok : valid B scale K cap r=true) (hc : check B scale w z r=true) :
    ∀ t, 0<t → t≤B → ∀ h, h.Coprime r.q →
    |(∑ k∈S, (count r.q h t k:ℤ)*(1000*b k+u*e k))-
      (if 1 % r.q=h % r.q then (scale:ℤ) else 0)| ≤ (fromRises (envelope r) (t-1):ℤ) := by
  obtain ⟨hq,hn,hd,hs,_⟩ := of_decide_eq_true ok
  unfold check at hc
  rw [FR7022Division.check_eq B r.q ((B/r.q).log2+1) hq hd, Bool.and_eq_true] at hc
  apply certified_finite S _ scale B r.q ((B/r.q).log2+1) cap ((envelope r).map Prod.snd).sum
    (endpoint w z u scale) (envelope r) hS hcap hq hn hd
    (word_eq S b e w z u B scale (lt_of_lt_of_le hq hn) hw hz) (fun i _ => rises_le _ i)
  · exact le_trans (by gcongr) hs
  · rcases endpt with rfl | rfl
    · exact hc.1
    · exact hc.2
end FR7022NextRows

namespace FR7022NextRows
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q2 : Row := ⟨2, -6590, -6589, 26078289500, 3061398887, 1063016419, 18, 0x4673e18d7e6f0115fa670a8c9e001c2cea08814601c7831200e64301a091ae00a41e005edd28007c66016e3600005e4a01109158005b6e0545e54d0049b30046d3dd80477700cada63803d4301336a14003b67003cce090037db00bafc0c0036290001e9038032ec004ec967003160003c23b9802fe0000f6da1002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q4 : Row := ⟨4, -6590, -6589, 26078289500, 3440915108, 1056704973, 23, 0x9e2ad21b62930141b4da94c2ab0269755410bcc30108b7fa81849302625a0000676a016e3600005e4a03bfa5ec005b6e01e84800004e6200d2d322004c01010e65630049b300f9bf5f00454c00afa6bd004332000480ee804128000b7f50803f2e00e4c1fe803d430108f759803b67006216280037db000a79d10036290017df1b003484000080a40032ec0049b81e00316000341924002fe0000b64fe002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q6 : Row := ⟨6, -76812, -76811, 20266116500, 2900965142, 821644066, 17, 0x30df4e802a42a0221b273010c930055208300df480184cf98004c01016768700049b30265a5ac0047770225159800454c0064944600433200335d420041280094904600399a00374b920037db01125fe40036290041eea0003484003361b80032ec002dd64c003160000dfe40002fe000279310002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q8 : Row := ⟨8, -6590, -6589, 26089724500, 2984084803, 1061274352, 28, 0x269ccfa1f7a7018dae3501d36000810d0f81849301e10c4f81394200cf6a68812fc300650f1a01268e01f8219400b3ff01312d000078a000c265a000676a007a1200005e4a006ec760005b6e01312d000050d6007a1200004e6200560351004c0100594abb00454c010c813a00433200e487930041280125ae3d803f2e005fa2cd003d4300a55fa9803b670056a26b00399a0096ec220037db001fda9300362900651d09803484001c9e490032ec001f11cb8031600025e6ac002fe00009ca6d002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q10 : Row := ⟨10, -44964, -44963, 22160158000, 2712547560, 898629397, 19, 0x23ac6da82a42a02803e3980a41e01588ca4009f2401789807009a5102d3d7290095a3018921680058a8001dcfde0050d601196ee40049b3016dbeb000412800df7c2c003f2e006ce9a4003d430070cc3800399a004ee4120037db0081c8280036290030e1ba0034840023dfea0032ec0014257c003160001b290a002fe0000c856a002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q12 : Row := ⟨12, -76812, -76811, 20266116500, 2787095907, 820250424, 23, 0x1b62e7ab72d200b52fffa41fa101fcc5258953d8029bb59800df48009a925000a41e01ee2e4b80676a007a12000050d601312d00004e6202b4dd7c004c0100d7ae2e0049b3008fdabe004777009266d200454c01239384004332003223a4004128001ac1c0003f2e004a350400399a000619260037db00a0304400362900286cd80034840028c0940032ec00257f94003160000e8a82002fe00017c60a002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q14 : Row := ⟨14, -35153, -35152, 23153282500, 3375749271, 933210080, 26, 0x4b5b3b714219e003d09000078a002625a000074f801312d0000716c01e84800006aa6023cc77580676a00629b8a80613d02cbe3e1805e4a003d09000055f800774eaa80535d012ccac38050d60159a3078049b30036ecf680454c00584d5c80433200b255e380412800842800003f2e003fd390003d430014a888803b670030b5be00399a0063dd778037db002ce2260036290036c59a003484002859990032ec0023c538803160000a2230002fe0000c5184802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q16 : Row := ⟨16, -6590, -6589, 26297997500, 3478361154, 1065696585, 30, 0xb2e7d387c145008e2ce500c56a005fbfb300bf6e025ea15800b3ff0048f9ef00ae8a008f7c7b009f240489cb92009a51003d0900007c66016e3600006aa6007a120000676a007a1200006447016e3600005e4a003d090000535d02625a000050d6007a1200004e6200caa9d6004c01000ef3690049b3006a777780477700000b0600412800af6718803f2e005e70c6003d430126c4c1003b670040d96e00399a0041ef890037db005b1d55803629005249c48034840007f3f58032ec0027ff9f0031600015dc0d802fe000075a85002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q18 : Row := ⟨18, -76812, -76811, 20266116500, 2656414412, 821490398, 26, 0x98b8c42cce690031bbdc21f7a700c4bc1e083f4b00aefc7e06100b00056fb804104f016e360000804a00f424000074f802b8d52180716c00356ce8806dfc016e360000676a007a12000064470225510000613d00089ea60050d600556530004c01018235f000477700d2078c00454c001f93740043320039f71e0041280015a69a00399a00772ff00037db0093271c0036290039c23e0034840026510c0032ec000c165a003160001c6738002fe00010972e002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q20 : Row := ⟨20, -44964, -44963, 22167491000, 2304132602, 898278252, 35, 0x155b7ea0672910171cd5086408c00750bf886100b00111fe485e10201bc2c3e85b366004ee4580346b400022c7801624d003d090001430d007a120001394200203b04010c9300f5c76e00bf6e00587a1400b9a0028757e600a41e00b9a8ce009f24000af488009a51001c67f20095a300182928006aa601312d000058a801312d00004e62003cb34c004c01004ef5bc0049b300035d6600454c00c770598043320091412f00412800a3ecc5003f2e00e63140803d43003bb41a003b67003f054a00399a001efa180037db002ce5a2003629002780a60034840021bd680032ec002222b00031600014ad96002fe00008ee56002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q22 : Row := ⟨22, -25807, -25806, 24399262500, 2962593637, 985203130, 38, 0x132965d2b72d200e3afbb21f7a7007b09b1177acf00cc22f60d15c000663637099e77009467dd8953d800a1527788c55100bd7bb1049894006a6537032d4900658b56014d26006e7d25811da0014e3d3d80bf6e00204bb700b9a00048f99100b3ff000425d0808cb401312d0000716c009f134a806dfc007a1200006aa600b71b0000676a01ab3f00006447003d090000613d003d0900005e4a016e36000058a8027a61b58055f801ab3f000050d6002860e3804e6200330e84004777002002df00454c00650f4c003f2e007e72be003d430071c905003b670053134d80399a006f673180362900250c060034840018c1040032ec001ff7da803160001651eb002fe000089cd6802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q24 : Row := ⟨24, -76812, -76811, 20267887500, 2440875564, 816569133, 25, 0x2b7639b14219e0101cb6381579000c58c68014d26005648a101430d02d4de0f01394200568631811da003567e0000a41e016ac90c009f24017fbd6280676a00b71b000050d600df6140004e620084228200477700127ed800454c008a52fe00433200c4d8ee004128007613c1803f2e003b4686803b67000ce7b000399a007451940037db006e883e0036290047c94e003484001f50940032ec000fe5b20031600014b0dc002fe0000ee076002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q26 : Row := ⟨26, -26689, -26688, 24866562500, 3079158539, 1004211988, 32, 0x227abe01d1f96000898cf14c2ab0005c35914219e00cb75a3103aeb0244901a874ac5027f3e66809f240130a52c009a51016e360000887000b71b0000804a02625a00007c66003d09000078a0003d0900005e4a01fda2cc005b6e00439db68058a800b71b0000535d00f4a59b804e620145a7b60049b30079042000477700b408f800454c000153580043320004dc000041280003a748003f2e0074fc98003d43008277a4003b6700719b3c00399a006c7ee78037db003768610036290021b9ba803484000f3e490032ec00128ff000316000181d0b002fe0000635a1002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q28 : Row := ⟨28, -35153, -35152, 23355722500, 3134496468, 943689533, 33, 0xe73cd800df480068556000d8830288542000d1f3022b338000bf6e01ef808400b9a000281591008870007a1200007c66003d09000078a000f424000074f802dc6c0000716c007a1200006dfc00897768006aa600ff710700676a003d0900006447001b9c5c00613d0043c335005e4a007a12000058a8004c6e680055f800f42400004e6200be0792804c0100b995be80454c00411e3e004332003fb018003f2e00ecb050003d4300251fd0003b67006452d080399a002a7cee8037db001e107c803629002069c000348400087b188032ec001e78f40031600010fa8b802fe000076938802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q30 : Row := ⟨30, -337831, -337830, 18844120000, 2350468098, 762301865, 24, 0x183ce1b07ff500248029481f10c01666a4281e1fc0129a2078114f800f42400009f240110f10c009a51007a1200005e4a00b71b00005b6e00c831ab8058a800495bee0050d6008090a9004c01004ed99a8049b3010fc6d300433200c5a7870041280073d6e0003f2e00eee513803d43004b297200399a004fd2dc0037db0045c8298036290019331e00348400494ee40032ec002ee3310031600022c06e002fe0001b5ecb802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q32 : Row := ⟨32, -6590, -6589, 26882684500, 2804293767, 1085971837, 39, 0x1cce8d9a307650108912e98f85c0089dac802a42a00e777eb020095012653850190b800738d63018493007c4cb20178cc0057c7a8015790018cab2400e64301a9035700c56a0177f18b00bf6e009b83c200b9a0014491d300b3ff006a179c009f24016796fc009a5100e7cf0e0095a30035522000911a01292ca9008870001bdec4006dfc00d86288006aa6003cebb400644700b71b000050d6000d5043004e62010fc6a10049b3007f2c68004777002cbea100454c00da8df1804332002d2723804128005ff64a803f2e003ec9bd003d4300a7709f003b67001518d880399a0059c7500037db001dc2708036290047e5e0803484000e531c0032ec001a3ee3803160000df27c802fe0000677b4002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q34 : Row := ⟨34, -23843, -23842, 25609477000, 2956526824, 1030128591, 34, 0x10695d70243bb0056777e02322902c76a8a02211f0248478c02109a013baaeb8114f80160981780fc8a01e884c600f4e20263647700ed760134571100e64300fca01500c56a005f65fd00bf6e0024903300ae8a002a611900a93f0099c37280a41e007a120000613d029f6300005e4a00eae668805b6e017773978055f8005a9f3800535d0085564c804e62008ac1b60049b300517b1a004777002f02f680454c002c1b2d804332004adbdc004128006d5061003f2e00155493003d43001df2db003b67007243b680399a0041a2f600348400314b5e0032ec00206da78031600012822b002fe00005dd74002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q36 : Row := ⟨36, -76812, -76811, 20292148500, 2468873591, 815351794, 34, 0x1a5306802a42a009c63e5027bcd01398f358268880013b8fb8255d900ecf1090243bb00e114fc823229009c307f02211f01e36d50019d3e004977200190b801004824010c9300ec04c601046f019d66c300fc8a01128b3400804a011290d50078a0003d09000074f8000034f700716c00b71b00006aa601ab3f0000676a0037faeb006447003cd9240049b3009f454e00477700ffefc000454c00a3d0080043320073fa4f004128003ec577803f2e00326ab6803d43007f733700399a00473a0c0037db0033f17a00362900312f4c003484001ee2f80032ec001aaf0c0031600011248a002fe000097b1e002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q38 : Row := ⟨38, -23456, -23455, 25871148000, 2710489612, 1048567428, 42, 0x2e5f2c98f85c00370aed08c55101db1fbd04104f01424e0203f0c800b2287c01624d012e2c38011da0003430c20114f80044b27480df4800757f6980d8830013e99400cb960000897000bf6e000264a000b9a0001cd53c00b3ff01185a4480ae8a00b79e9000a93f0084a9d100a41e00893b8b009f24003d09000095a300e8b90d00911a00612dd5008cb401312d00007c6600b71b000078a001ab3f000074f80086f07d80716c003d0900005e4a006a11700058a800ae36c0004c0100d70be00049b300b73000004777008f9c4400454c0038790c00433200435c1b004128006482a2803f2e00ad15a6003d43001d3f1c803b67003cb3440037db004100a80036290022ba7c003484002497218032ec0006bb2f00316000113637802fe0000764f4002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q40 : Row := ⟨40, -44964, -44963, 22491314000, 2747666405, 906326322, 37, 0x27af7b2cce69011617db08c55100ff97460346b4017032d6032d4900ade12d0314a300163fe4016d60006b59c501624d00eb6038814d26016e557781430d00b71b0000fc8a0202df6c00f4e20161e6d400804a003d09000078a0007a12000074f801312d0000716c00b71b00006dfc00f42400006aa6007a12000064470100732c00613d0030b9d4005e4a00342c40005b6e0007c7680058a8012206220050d60000afa400454c005cea3200433200e4ee820041280133992e003f2e00411b20003d430095ad60003b670037f13600399a00186d6a0037db000eaec80036290024f290003484002110240032ec0010acc2003160001200be002fe00005b484002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q42 : Row := ⟨42, -269111, -269110, 19207219500, 2618016498, 775349498, 32, 0x1386e228c4dcf017a3bb002a42a0008a5bc028fac00f4240002009500916af481f10c003d0900007c6600b71b000078a0031975000074f80225510000716c00068d84806dfc00b71b00006aa60118c10c00676a006c0a6b8058a8003d09000050d601074bdc804e62001cac46804c01001deef98049b3005747bf804777007c207900454c00d00b8b804332001fca3c804128007f15d9803f2e0008da7e003d4300026a0d803b67004787d880399a00388b7a0037db00409ebf803629002ce817803484002071fd0032ec001ea3880031600018cd9b802fe000106a79002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q44 : Row := ⟨44, -25807, -25806, 24994774500, 3102052963, 1007784693, 36, 0x205fe8c01394201943e18012fc3017b61da01268e006326b2011da001a3f3940114f800b7a61c01046f0171a95380fc8a00e5a78780f4e2013d250a00ed76005971a600bf6e0112659d00b3ff0042535600a93f007a120000716c003d0900006dfc00b71b00006aa6007a120000613d00f42400005e4a022551000058a8016e36000050d6010291f1004e6200a63d220049b30090e8d7004777002b237680454c0036c29b0043320048b03e804128006c3d95003f2e001b444b003d4300412d9a803b67003ab7c380399a0013de130037db002a94690036290026d2f5003484001733f68032ec00170c15003160000bdd9f802fe0000600cd002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q46 : Row := ⟨46, -22503, -22502, 25839093500, 2646060863, 1044092507, 44, 0x314e8002b94c0396393f0255d9002d8e0e0232290158197e02211f017c0c9401f10c0036ea7701aa2800bdb86b013942007109d4012fc30033394b01046f005b9b4700fc8a007ebc6080ed7600c2603c00e6430074600280bf6e005438c800b9a0000b508500a93f003d032d00a41e02778dc8009f240055e743809a5100bec3e38095a300e002dd00911a004a06ee008cb4007a1200006dfc00681c5800676a007a1200005b6e0043f47c0058a800f424000055f800179b3900535d01312d00004e62007c2a3e804c010067c6ea8049b30006b8a6004777005c635500454c00512a25804332009ff2638041280062e375803f2e0019b3ea803d430016dfd4803b6700099e718037db0060a81a003629001b62b50034840027360d0032ec0014dda400316000107db8802fe000048159802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q48 : Row := ⟨48, -76812, -76811, 20486517500, 2714141310, 821964861, 31, 0x131f6c287c145012d738d819d3e02d0a88781849300b36e08016d6000b71b0000c56a01e8480000bf6e016e360000b9a0007a120000ae8a01312d0000a41e003d0900009f24007a1200009a51016e36000095a30214abba80911a009bad6f80804a01ab3f00005e4a003d09000055f80032c60c0050d60035e2c6004e6201004612004777004ebd9200454c0068ff3f00412800808bf7003f2e002108c4003d430063464c00399a004151ac0037db00538edc003629004ee4480034840010c2080032ec0015b1b4003160000eef9a002fe000086fe8002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q50 : Row := ⟨50, -44964, -44963, 22589846000, 2642920928, 911901177, 32, 0x20963e88f42ea009908678532b301ab3f00013942003d0900012fc3003d09000114f800f4240001046f01312d0000fc8a0219097000e643011ed0f780df4800f412bc80911a00b71b000078a001312d000074f800ea062800716c003d0900005e4a007a12000058a800b71b0000535d007a12000050d60103a1f4004e6201669f620049b3002bc71a80454c006173318043320077429e004128004fde90003f2e00231d88003d43008f1302003b67000057d20037db0063a7be003629000140c4003484001302e80032ec0025e0b4003160001479a0002fe00005b68a002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q52 : Row := ⟨52, -26689, -26688, 25193395500, 2802985327, 1013455837, 47, 0x753f90d15c001a21a9882fcbd011b310302e590002d976602109a0194e4d102009500ed778401e1fc00b25eae01c536015fbe8781b77a009670e581aa28006b1cca819d3e0092df0c8190b800477f0d8178cc004c7faf815790008e8d0e814d260163273b01430d00249c3981394200831d1e012fc300b751d180f4e2005b2c1680ed76015950040095a300691b1800911a00f4240000887000b71b0000844d0087bc0c00804a01ab3f0000676a00b71b00006447000f424000613d003d0900005e4a00e4e1c0005b6e001116478058a80090f9e380535d00632a1c8050d6005b1589804e6200a38af90049b301027531804777001645c080454c000f598c00433200266e20004128005810ac003d430079fe7e803b67003c0ea78037db00568821003629001c468b0034840009c0320032ec001e9e71803160000b47b8002fe000061776802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q53 : Row := ⟨53, -1494, -1493, 40195229500, 2392447275, 1637641290, 51, 0x332d90e0f42ea00a27f520ecc8502926286028fac02316c00027bcd00fa02e70268880023708d02322900d7f25802109a00ac99c701b77a00a87e21819d3e0027ce678190b800886554018493000629ca812fc30007ad0201268e004ee5fa011da000ce95f2810c930071593081046f007fd0f300f4e20026e73b00ed76011a7bbe80df4800880c7300d88300352ef400b9a00107d624809a5100e098730095a3009deb5880911a0005755a00844d000002eb00716c00cdb410006dfc002cf8e4006aa60022c2c400676a0077d3d6005e4a00bcc717005b6e00bc9f2e8058a80019e5e58055f80072c8c400535d0069f3f00050d60076be52004c0100a0b0690049b3005ad02800454c0043d0878043320011327400412800474e04003f2e0033de71803d4300551cb9003b67001b261700399a00086c340037db004219c800362900199d890034840019655a0032ec00114456003160000e9918802fe00003ecf3802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q54 : Row := ⟨54, -76812, -76811, 20569655500, 2456031214, 824979752, 39, 0x1046d4c2a21c300de8d7688c551038703fa050a5f01241f4604e344001a550e04bd59006680b4049894017f7816010c93003d090000b3ff00f4240000ae8a003d090000a93f01ab3f0000a41e007a1200009f2401312d00009a51007a12000095a3007a120000911a009fc464008cb400d01afe008870003d09000074f8016e360000716c002a4e7a006aa6003d09000058a8003d09000055f800b71b0000535d0065d79e0050d600e97bf8004c01008fd4c90049b300331a2f8047770074ae1180454c00360e7e0043320036043680412800184bdb803b67004bb8a000399a004c22d60037db00175f64003629002b438e0034840020572a0032ec001979f8003160000df1b2002fe000083b8a002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q55 : Row := ⟨55, -7209, -7208, 31071004500, 2614367238, 1262244885, 52, 0xbcecc504bd5900bc8c27849894001f573c84104f01ed74c883f0c8009228d683b491009740668397d2000e264f032d49012b49e701c536006b99c50178cc003d0900016d6001324cc181624d00ef9612013942004f50f000a93f00a6e1c400a41e00bc4390009f24001a28f4009a51008b3e540095a30103b99800911a0096ce60008cb400ab1824008870004ba19400844d009cebcc00804a00f1f79c007c66001ca56c0078a000acc8580074f80064a06c00716c002e4018006dfc00587218006aa60063d60100676a005a12230064470020178000613d00302de8005e4a00fd6e80005b6e0046e57b8058a800ba453a0050d6003d50a0004c0100a9fb268049b300626b52804777007ff62a00454c000cec2b804332001e85ea8041280021fe7c003f2e00229425803d430034e00f803b670019ff3380399a002987718037db001deaa3803629001bc6080034840020e4fc0032ec001b571c003160000f29c1802fe000049202802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q56 : Row := ⟨56, -35153, -35152, 23660843500, 2621254047, 953442737, 43, 0x1657246a8daeb02c4bf30890b7c011d757102a42a00576f69028fac00715e2f027bcd0073ac6400df480086ef0400d883014e3c8000d1f30012ffcc00cb960114e15400bf6e0173bcc000b9a000b6ff1000ae8a003cc84400a93f007780dc008cb400d683b8008870016e360000844d00d4bb4800804a003d09000078a0007a120000716c0001cdb0806dfc016c00cb80676a0062d4c800613d0056e6d8805e4a003d09000055f8003c9d9400535d003d0900004e6200c8b9a4004c01006cae1b0049b300a0761a8047770051523300454c003081f2804332004e5a228041280049c774803f2e002e13e9803d430066bf84003b67001c948b80399a0021d2578037db00083c75003629002d3e7800348400031f440032ec0015d516003160000bdf33802fe00004ed42802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q57 : Row := ⟨57, -11930, -11929, 29231437000, 2388351623, 1187337539, 49, 0x22cf2620e59b700144fc6027bcd00c1fde68268880112eeca023229021833db82211f003693cf02109a003bcccd01b77a0020d0fd8178cc0047f6ed012fc300647cbf810c93000644e101046f00753fc080f4e200888f6380ed76006348fc80e64300c9c12180df4800808dde00d883000af2df80d1f3001ddbd380cb960172831700c56a00f4240000b3ff003decd5009a5100c4d92a0095a3008099ae80911a007f4fbc807c6600c0b6fb0078a00004ef4d0074f80046430d006dfc00855dc9806aa600022b3e005e4a007a1200005b6e002381798058a8005b70340055f8007a120000535d00692477004e62006d0ac90049b300fc8cee004777005634f200454c0030f19c004332001059b880412800472bdc003f2e001ec827803d43009bd3bc003b67004981c900399a00132f27003629002efc7a003484001a21668032ec000b93b9003160000fa811802fe00004a8ad002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q58 : Row := ⟨58, -18529, -18528, 26302663500, 2483624531, 1060380830, 49, 0xb9b2008397d200617c1c837bf2014f732f8360ea009d67260346b401196235832d49011bdd838314a30244e62a82cf17002f8ac5020095001a0dd001aa280083c66c019d3e00f1f7080190b800e521c40184930028c66c011da0016074140114f800264174010c93007ab0e801046f007d7d9400fc8a016573f800d883006468a400d1f3001551d800cb9600a9a13c00c56a004f0be400bf6e002e0c2c00b9a000706064009a51007d5d500095a3003ca12800911a00ce12df008cb4009aa1ad0078a000b71b00006dfc0077bc58006aa6003d090000613d00b71b00005e4a004ed1bc0058a8007a120000535d003d0900004e6200afc688004c0100bc0c808049b3008b582380477700a66c1c003f2e003e6b00003d43004790a4803b67000e48c780399a0023f8e00037db002754440036290028b90000348400085c4c0032ec00227d72803160000a02d7002fe00004db72802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q59 : Row := ⟨59, -1457, -1456, 40820337500, 2658596976, 1664512968, 50, 0x18c25142cce6900fe123c2b72d2003e1551a30765015ea99a91ccc002037ab103b49101456ae282fcbd005558eb02cf1700b75af582a42a01c0f3dc01624d003a89b0014d260123b6f801430d004d7e588139420000485c812fc300980d9a811da0001f85ca010c930011c93800e643000005b100d1f3000944fc00cb96015a0a5380c56a00b0f17c00bf6e00bacee000b9a0009dca3200b3ff001963a000ae8a00f69c2400716c001abfe0806dfc0079a74d806aa6004d9a6680676a0077cb77005e4a000002d8805b6e003d09000058a800f424000055f800f4240000535d00f424000050d60079631c804e6200770cc8804c010038abdd8049b300d0d1a4004777002c6aed00454c0056a3e88043320064637080412800449ab8803f2e0041928f003d43002aa8ea003b67003758bf00399a00220f23803629002f9ee7003484001792708032ec0018b210003160000b1909802fe000034866802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q60 : Row := ⟨60, -337831, -337830, 18844120000, 2140614693, 759244322, 35, 0x2b43fe393857200957313067291000d9bca8430d20088976002a42a0060bd44828fac00a8c391027bcd002e43f18232290270cada8200950040e9a101f10c0065bfd681aa28002cac04019d3e0085657a81624d00f4240000ed7600d9728400e643001f3fab809f24003d0900005b6e00f424000058a8007a12000055f800b71b000050d6015603e6004e62008bb155804777001fb9b300454c0063385d00433200a34ab500412800a29d83003f2e0054de34803d4300347cd0003b670032e97a80399a005440fe0037db0024c1cc803629001401b3003484001b43260032ec00261b8080316000142c5d802fe00011a005802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q61 : Row := ⟨61, -1055, -1054, 40790887500, 2355555768, 1663404274, 61, 0x396951988c55100bc34e088814600246d0503b4910066b9d30397d20004460802b94c00812a20026888009d6b4e01d3600139e43601c5360063cb8301b77a006b35c581aa28001720ff01849300cb210e0178cc01506f05816d6000477f7c81624d00266f240157900047853181430d007facb401268e001740c2011da00042ec210114f800486fa8010c9300a47bb001046f00fbc99000fc8a00a377d100ed76005cd85f00e6430113e8de00df48003c9ce880d88300414f8080b9a0001fe4b500b3ff008cebe100ae8a0028039d00a93f004cdb4100a41e00757593009f24000357c7009a5100b327670095a301339d5100844d0069d8620078a0001c93c80074f800125c7d00716c000345420064470073e93200613d003cfa97005e4a003d09000058a800f424000055f80089a83c00535d003fbf5d004c01006f36dd0049b30031bdf4004777008a18c700454c00323c460043320038431d0041280012b204003f2e001f1bc0003d43001bd5a5003b67002e522c80399a004cc5340037db0023fe2b8036290019009d8034840020e29d0032ec00079628803160000fc98d802fe000046589802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q62 : Row := ⟨62, -19134, -19133, 26480658000, 2629276138, 1063655674, 48, 0x2327ce602e59001b5e32f02cf1701ed688a028fac01eec983027bcd0187ff9f0268880025bbea0243bb01dd9899023229000e35af02211f00865bdc0200950018d7a801f10c006d77be01e1fc0088405981579000cf1676014d2600f902cf81430d011d05cf012fc3000a77f301046f00e1632700fc8a0119f15980e6430098cd2c80df48004cbba000d883001396c700d1f3000baba780b3ff00f4240000844d007a120000804a00265d668078a000b3725d80716c007dbaa2806dfc0050fa78006aa600256ee580676a0040b1a28055f800b71b0000535d003d09000050d6016e3600004e62004bf93d004c01003666910049b3000bcbd00047770058d2ce00454c0125e8a3004332006befce004128008254da003b670015041800399a001419510037db000eabbd003629001a9e12003484003047410032ec00142188003160000d1f60002fe00005180b002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q63 : Row := ⟨63, -16921, -16920, 26538668500, 2768519992, 1076239844, 42, 0xc3f15681aa280143f4d2819d3e000a31528190b8002327a28178cc0057a9d101430d00f3ded0013942002e5ee30114f80221ce0c010c930006ae9381046f00fc20b700fc8a00dd1d1b80f4e20021705600ed760175554b00c56a00b2035700bf6e0044bfdc80b9a00017102480844d00c13a3a80804a006714770074f800d31a81806dfc015f1f97806aa600ecbef080676a003d09000058a8007a12000055f800b71b0000535d01abeb190050d60077364c004c01005f33a88049b300087d6a804777002c777000454c00aa2cb00043320047f680004128003a73fc003f2e0008354b003d43003cf26f803b67002ec36c00399a004d3a8f0037db001b99ee8036290025a308803484000cf1870032ec00101beb803160000e167f002fe0000421fa002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q64 : Row := ⟨64, -6590, -6589, 27096699500, 2856668797, 1094392530, 49, 0x1ab37860a8c9e00a0d3e18397d2006d79f88346b400bbd0bf827bcd002ff7d0826888003fda370200950061cd5301d36000dc4b6401c5360112c236819d3e005ee5bf0184930105df320178cc00d7e06000b9a0007e16c000b3ff01029c6f00ae8a004fc8fb00a93f0040b69000a41e003ca5be009f2401796656009a5100ac081e0095a30079e23a00911a003d563a008cb401ab3f0000887001a5dadf80844d003d090000804a00056420807c6600977a138074f8007a1200006aa6007a1200006447003d090000613d00b71b00005e4a01391470005b6e003d0900004e6200457d49804c01006f06210049b3002233ad8047770058bb4c80454c008086e80043320028220000412800679309803f2e000293ea803d4300a85b78003b670027d56180399a000a66ac0037db001e9cd2803629002b5af0803484000f656e8032ec001a4f050031600009f457002fe000050dac002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q65 : Row := ⟨65, -8142, -8141, 31842838000, 2126626152, 1295256601, 53, 0x21225632b72d2004cacf807ff50009a04e503b491001ef3fa02e59001bf01c9028fac0053abac02322901a9a15702211f0075cd4782109a0096df3981f10c001ff7ba819d3e0008fea4816d6000907e7d01430d00e0f2c2012fc300f26e7701268e00917066011da000705d2f0114f80130483681046f009f8edb00d1f300bac60780cb9600081cff00bf6e0017636a00b3ff004d2eec00a41e00d6deab009f2400236a9d0095a3000f5656008cb40095feb4008870006c52bc00844d0059249400804a00333d11007c660036e3f10074f80025130e00676a00a7d05c00613d0083a338005b6e004a83cc8058a800017b478055f8002481b400535d000b284d004e620003493b004c0100d4c7860049b3000858fc00477700bc556f00454c00717670004332002b81988041280000be4e003f2e005e9462803d430036e11c003b670021834700399a001efa290037db003ece1d003484001bf9d20032ec0011067a803160000addd3802fe00003bbee002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q66 : Row := ⟨66, -213232, -213231, 19732586000, 2508705747, 791357072, 39, 0x1e2a0411d1f96006620b40d15c00160f55e8cb03e01d3d5258243bb005761cc016d60009d491801624d0064d238014d2600c03f28010c930080ed2001046f0162e45c00fc8a003d090000c56a007a120000b9a000f4240000b3ff012e72bb00ae8a0197722500716c0013ccdb006aa600293c2500676a00b71b00006447003d090000613d00f42400005e4a00b71b00005b6e00b71b000058a800b71b000055f800a93f1400535d00914794004c01001ddf240049b3004924a4004332002a45ac004128008b1724003f2e007f2cd0003d430039fd6c003b670027311000399a0010108c0037db0034a7bc003629000b6730003484001ce4340032ec00164c6400316000121b88002fe0000a46b8002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q67 : Row := ⟨67, -1121, -1120, 40686383500, 2421521384, 1664267231, 50, 0x17efa109eb6b003ed2ba05872c00dbe9e7855c4900d2eedb8532b3002f547c032d49007717440314a300a5a2f802e5900024f9500243bb00c7608c02322900ef752c02109a004bebb4020095013f7dd801f10c0054a15d81e1fc00429c4181c5360106af250178cc003bd9cc00ed760178d90c00e6430024449c00df4800f7409900d883006f48b100cb960149bf4200c56a003fe06c00ae8a001325ca80a41e004a22908095a30099d9db808cb400700a1d00676a007095bb00644700865e6180613d0039a468005e4a007a12000058a8016e36000055f8011ac31c80535d005bf8ec0050d6007b0c79004e6200204147004c0100156b7f8049b300175812004777002da6f700454c0067129300433200007e7c00412800449d00003f2e007bf868003d4300146e25003b67004cdab600399a002e10ab80362900276b7f803484001ba55a8032ec0016870b003160000a74e4802fe00003f2c8002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q68 : Row := ⟨68, -23843, -23842, 25932172000, 2379699466, 1050065757, 37, 0x27856fe9a8e2102232a7a82009500b4b90301f10c007bc36f01e1fc000d16a481d36000d13d9481c5360151d05e013942004c7cc5812fc3000dfbb101268e004055658114f801b5711a00fc8a00dbb99100f4e20061d03600e643006a511b00a41e01c99a62009f24005737be009a51003d090000644700f4240000613d007a1200005e4a00f424000058a800b71b00004e6200eb960c004c0100e5349f0049b300c0b770004777004804b800454c00137a6a804332003ccd168041280037ec69003f2e0018702b003b670036aae800399a002a36728037db0020d8ee003629000d6c1a803484002e20cd0032ec001466dd003160000a583a002fe000042f0a002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q69 : Row := ⟨69, -10898, -10897, 29486039500, 2423636528, 1192440758, 43, 0x1bb3769045259028f99080430d203a3122804104f0016116283f0c800249f67028fac00fce965027bcd00ba488181394200e9da4c812fc3007e5df601268e015bfc7201046f00bde6ce80fc8a00a64ac600ed76004a8f2900e64300b7cc5600c56a00a6ba8480bf6e00b3f9790095a300e8731100911a00928193008cb40094e34480844d0066981300716c01605b71806dfc00519f56006447007d8d6e00613d0021562e805e4a007a12000058a80057d8b60055f800a48ef40050d6001308f6804e6200f7f7b900477700923b3400454c002d997c004332004fcd580041280021de29803f2e003b4087003d43000ec49d003b67001554bd00399a002461420037db0023f73100362900193422803484001a14960032ec00113533803160000ade8f002fe000038ef6002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q70 : Row := ⟨70, -160612, -160611, 20474450500, 2057592684, 824116402, 40, 0xebeeb402b94c01880efc02a42a00e3dcf0028fac000fab1c827bcd00438c8a02688800fec6e00255d902b0e64b0243bb000c343f8232290052173102109a00daffae02009501312d00019d3e0134165801849301f231aa00ae8a00851d9a00a93f0084a57800a41e003ea312009f24003a84e28095a300b71b000064470082bf6580613d00345b9a805e4a00046cd0005b6e00d93a1180535d008fd38e0050d6006f47c2004e6200729a020049b300aff8be004777003ea0e200454c00331336004332001dc08c004128002f1ebc003f2e0008347c003d430036fdec003b67003a988e00399a002bca4c0037db000153f6003629002d0a4a003484001e28620032ec0013be0c00316000128072002fe0000880a8002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q71 : Row := ⟨71, -1751, -1750, 40903873000, 2372913183, 1669964308, 52, 0x103376014c2ab003acdb6067291019eaca285872c005734c682cf1700c7476182b94c0051c71f827bcd01c1be5582688800d941720255d900ee499182109a008573a58200950043a82f81e1fc005b0748818493006dd3400178cc00e8e7a4816d60000c6f31815790018a6c2f813942004603e0012fc3004d838d81268e001faee180d883004c21e780d1f30055af8e009f240129df63809a5100aecc968095a3012ad09c808cb400eb715500887000e1c07b00844d00d2beaf00804a003346a5807c6600570f220074f80015781e006dfc004c19f980676a007a12000058a8006e3f248055f8007a12000050d60000a6ff004e62003c80c8804c01005195448049b3002664a28047770087cb3180454c005757640043320050d7f18041280000806b003f2e00961851003d430035bc59003b670031e08e00399a001bc5dd0037db001a81280036290017fd1d003484001765420032ec000cd523803160000bb787802fe00003d66c002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q72 : Row := ⟨72, -76812, -76811, 20702004500, 2205544768, 824935926, 52, 0x829dd39e08930255d66b1568c1007393fd14c2ab0020fb200b91cd003d090005b36600b660a585872c03270e258474ec007f5571045259009abae40314a3003d090001c53600ddaad001b77a00085be401aa28011f0e9e019d3e00e12d22014d2600c244c201430d012120f6011da000d1837c0114f800ad431a01046f0070f7ac00fc8a01ab06f600f4e2003b79d400ed76006ae52a80e6430058242780bf6e007a120000a93f003d090000a41e009e920c809f2400929af380804a003d09000078a001312d000074f8003563e600716c0010909a806dfc00f4240000676a00a1c5c3806447003d090000535d007a1200004e62002ad39c004c010035733a0049b30020b1600047770037aa9a00454c002ff074004332006366a8004128003f9867803f2e0042302e803d4300195bd2003b670002932c00399a004d3d8e0037db001a1cee003629002865ea0034840028276a0032ec000cf428003160000e2536002fe00005bf30002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q73 : Row := ⟨73, -1948, -1947, 41309084000, 2468397256, 1685918657, 48, 0x2a8cab804bd5901225edf8474ec01bb733e83f0c8004b2cdc03d23600262b8403b49100b669d0832d490145f72d02211f0096bf4282109a0025b7f201268e017690b2011da000fd697a0114f800733cfc010c93003d109c00f4e2014787c800ed760053fd3e00e643011a946000df48002bd73000d88300f7e15c00d1f300552fa400cb96009346b800804a00376210007c66007992a40074f80028e78a00716c002ca78a006dfc011fe774006aa60036b1c000644700edeefe00613d007a1200005b6e00b71b000058a8003d09000055f80060be8100535d00565c7f004e62007c149c004c01004a42228049b300e86ec800454c00343c210043320034830680412800002a42003f2e001e1044803d43001e0278003b6700448bb400399a001ca85a0037db0030b97c0036290017977a003484001b9aec8032ec000eaa6c803160000b9ff2802fe000035ee0002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q74 : Row := ⟨74, -18320, -18319, 26465773000, 2411830948, 1073444475, 52, 0x78f10920f0250000890b9ff09f006a669819c01f0093f6c004bd59013c41ad849894001850ca83b49101208954037bf2005dde280346b40128fb58032d49000fd73b02e590004d343d0243bb002b110881e1fc00b470fd019d3e00cad8868190b8003cd48b81849301073095011da000212b1b8114f80003826e810c9300b05b468095a300be8e0a80911a0181b506808cb40024cde0008870003ecc2600844d007a1200007c6600784eda0078a0003d09000074f8007a120000676a01198a380064470017a2c800613d00626f38005e4a00173d32005b6e007a12000055f800b71b0000535d007a12000050d60007ba8a004e6200441b2d004c01006c2c328049b300d0059e804777000048f900454c002cd958004332004a04c38041280044cc34003f2e00823ca2803d43003542a1003b67002dfc0800399a0024db640037db00170278003629001a793000348400197c810032ec00109183003160000e9980002fe000040da8002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q75 : Row := ⟨75, -21638, -21637, 25637307000, 2161192625, 1035930400, 49, 0x5c8b0418f85c02b787519836a600900fd18bee5c0018a0510ae10300efc99f84bd590105877e849894015449f903b491018045be02211f00931d1602109a007b234501f10c0011234401e1fc0023099e81c53601190b3d01aa2800a2c6ce019d3e0050ad930190b80002105501849300027783811da0014216b780ed76005b88ea80e6430045c5b300c56a0071dfb500bf6e007af90200911a007ff7f8008cb4004ce64a00887000a3420c00844d003fe84900804a005a2709007c6600129c850078a0007649ca00613d00a60f81005e4a00142615005b6e00b71b000050d6003d0900004e62007c7970004c01010e4b840049b3000dff500047770001114500454c00d0e76d0043320072eec9004128004e13d4803f2e003b3053803b67003021ee00399a001e135f0037db00214343803629001c4248803484001a5ae18032ec00116e23803160000a0b64002fe0000446d4002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q76 : Row := ⟨76, -23456, -23455, 26185682000, 2397426926, 1056920922, 49, 0x14da9ec06729101c71b3406408c000e0f140474ec009229b80430d20068978403f0c801e34a1803b49100651c8a0360ea01ddd0ca023229006a279c01f10c003143a101e1fc00477ab701b77a0075e21c01046f0075867c00fc8a00a00f2400f4e201354d2000b9a0003ee92000b3ff01301bf000ae8a01810c9c80a93f004ff22b80a41e007a3fd00095a300b928f000911a0042e974008cb400f4240000887000aa8a3400844d0030b8df00804a00495921007c660052e1dc0078a000a8abe780644700359f3c80613d001d4430005e4a000ff014005b6e00b71b00004e620075b918004c010085f2540049b3004b89af804777002cfe5c80454c0057ca18004332008a10870041280032e655003f2e003b8e78003d4300436098003b670000affc00399a0027ea680037db002b2b540036290011a3b6803484000faf658032ec0010740b803160000f2134802fe0000439b0002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q77 : Row := ⟨77, -5396, -5395, 33258715000, 2254273571, 1347231152, 53, 0x2209fc06100b0102e4dd85e102001a0d2905b36601e6670d85872c005c9c57055c49030a214c8532b3017c4510050a5f00394ba304525900f67b268430d201faf31a0314a3002124ab01e1fc0079bf3281d36000465fde81c5360189e07881b77a00fc6ece0190b800b1947e010c9300ca637e01046f003d483c00f4e2013c36b000ed7600982db000e64300fb2c5a00df4800055f0e80c56a0016486580ae8a0013d5a280911a0033a67100804a00b4f8fe8074f800a25e0b80716c00baccb2806dfc004dabf4006aa60020535000676a0076a05400613d00404322005e4a00d0f6ea005b6e007b56bc0058a8002089900055f80057223c0050d600032f30004c0100c07af40049b30003471f0047770002869500454c002a607a0043320097024d00412800636368803f2e001079ae803d430035bfba003b67002f561480399a0033af0b8037db002a1ff000362900103a42003484001c14c98032ec0012dcf2003160000c2184802fe00003d162002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q78 : Row := ⟨78, -201286, -201285, 19980860000, 2437252636, 796027262, 48, 0x33974b02a21c3024272ba9ef8d8002175ea9a8e21007e61371142aa01a164fd05e102014d4fe685b366004caee105872c001d2b21855c49007967a804bd590011c7cc0474ec00d7ba65832d490110b9d18243bb001b00bf01f10c0004f3dc012fc300f2abd281268e007a1200009f24003d09000095a300b71b0000911a003d0900008cb4007a120000887001312d0000844d01312d0000804a003d0900007c66003d09000074f801ab3f0000716c0092f769806dfc007a120000613d0077acb8005e4a003f6e48005b6e003d09000058a8003d090000535d00700b980050d6003d0900004e6200be4f50004c01007931650049b300568d9a804777001f9af7804128001c48cd003f2e008cc995003d43005f88cc003b6700438dcf00399a0012bc520037db001b34030036290003aa9e003484001dc1780032ec0020a8c6003160001612ac002fe0000a1c2c002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q79 : Row := ⟨79, -2339, -2338, 40927803000, 2254577171, 1672339207, 61, 0xdd05d25409f01210019055c4900e3ec200360ea013d8f410346b4004fa96f032d49004886620314a300112bfe02e5900035f5d302cf1700739a3102a42a0108bae9028fac008a6076027bcd008373100268880135faa501f10c0047dce601e1fc000460e001d36000d0fe5e01c5360063a65901b77a0023165e0190b8000d1191018493004114fc01268e011c1960811da0003584de8114f80079d82401046f006b47b800fc8a00231a3b80f4e2007980d700b9a0007edaad00b3ff0026b05d00ae8a0145534500a93f00e1724800a41e0022ddd0809f2400e3ead4009a510023f4810095a3005b94f68078a000584bc18074f800b7a79900716c001054ed006dfc000e8609006aa600436a2300676a00769107005e4a005e3b0c005b6e001bd6f40058a8007a12000055f8009358b400535d0049e7d70050d6002b6bd70049b30064d320004777008a10fd00454c0052594a0043320023ca1500412800448bb7003f2e0033753b803d4300366bb5003b6700018de000399a0034af060037db001f361f8036290012e961003484000e95640032ec0013eed4003160000818df002fe00003e944002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q80 : Row := ⟨80, -44964, -44963, 22887227000, 2417020032, 922163572, 49, 0xc122d90ecc85008ad1d502688801beaed68255d9001810e08243bb0071d1bb02109a003e0c0a820095002ce04781f10c00341c5801d36000f42400012fc3003d0900011da001ab3f000114f802dc6c00010c93007fb36801046f00ee829800fc8a0013b23000f4e2007a120000ed7600b6611a00e64300194b3a00df4800506a0c00d1f30056015e009f24015b1b18009a510049de780095a3003d090000844d003d090000804a007a12000078a0006a9b9a0074f8003d0900006aa6003d090000676a004be90200644700b71b000055f800a83afe00535d011c55100050d60027f651004e6200027b45804c01000da0c18049b30028d36b8047770012813080454c00590686004332009780bc004128003d8dca803f2e00563f2f803d430039d4c8803b6700434d1b8037db002325b20036290019271a003484000a96720032ec001266ba003160000c3a82002fe0000435ea002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q81 : Row := ⟨81, -3155, -3154, 30932521500, 2160274562, 1257427626, 50, 0x4204c71d1f9600b97ccf08c551010834388881460055829f86100b00cec249028fac0135b21b027bcd0086674a01f10c00bbf44801d3600079ed0a01c5360217547801b77a01ba0ca901aa28004b795d819d3e005a5d72816d600017d1d281624d00345fab815790002649390139420043093501268e0000f807011da001617e4a00f4e2007b37b700ed760092428300df4800292fa800cb96007a120000a93f00b71b0000a41e003d0900009f24007d2dac009a510035b7f38095a300307f46008cb40004910b0088700020461c80844d007a1200005b6e003d09000058a8003d090000535d01312d000050d600f42400004e6200f3d4c7804c010058a20f00454c004d4e7180433200575606004128003bc4c7003f2e001bfbe9003d4300041bfb003b6700160de200399a002bca1d8037db002f4aae0036290021b54380348400080b0b0032ec0015af3b00316000094d73002fe00003e54e002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q82 : Row := ⟨82, -18256, -18255, 26850598000, 2435485724, 1085198319, 46, 0xea1f005e10203892f2685b36600fadecc02fcbd00de38c802e590000aeaea02a42a00327382019d3e0182592301579000bd7a63014d2601cc5e15010c9300c262ad00d883009d22fb80d1f30079b89380cb960011537800c56a00f5ab0b80bf6e009704eb00b9a0005d418180a41e0156307d009f24020a9d678095a3003d0900008870006b5b4480844d003329280078a0007a1200006447007a120000613d0020dfab805e4a00f42400005b6e0052a5188058a8007a12000055f80025bba800535d001e9a7c0050d6007a1200004e62008cac2c004c01002085f40047770030801c00454c0068b830004332003919fb804128003ffb49803f2e000058d9003d4300091e16003b67004c28df00399a001082e10037db00255724003629001674fb003484001e4d468032ec0013d202803160000d4488002fe000038db4002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q83 : Row := ⟨83, -2723, -2722, 41100999500, 2352016690, 1673703838, 52, 0x779233279dfb004dffac1b62930013797a9a8e21029dc7e38532b30084e9a204e34401b492fd03b49100b112a50346b400c8e7c3032d490107f3a80314a30093996202e59000f624b702cf17007ad3fb81b77a00aa8811019d3e002a4ee981849300bac030816d6000e636ea012fc3005f276701268e016b4134811da0016e4b460114f80137a2aa010c9300862f4281046f00a7a2fa80fc8a0062ce1400bf6e006b2cc680b3ff0029dc48809f240033199c0095a300e7cba900911a00508822008870007b6b7e007c6600b33a010078a0006cf907006aa6005dd69400676a00a489180058a8001291e80055f8003d09000050d600a65a7c004e6200b29a3c004c01007924eb8049b30068f8a0004777005cfec280454c0034f12f00433200000551804128005a7e84803f2e0037eca0003b67004317bf80399a002848a58037db0021fa07003629000de7e60034840015a1540032ec000bfa13003160000bf3cb802fe00003676c802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q84 : Row := ⟨84, -269111, -269110, 19393750500, 2032457296, 775060815, 44, 0xf9d7a605b36601f0d46b05872c00f5879e855c4900cdced88314a30222bb4f02fcbd00ea3a05827bcd01071cfb826888006df19d02322900a2a2bf01f10c022d9c1101aa280083908e01849300fbdc580178cc000d32e7016d6000ef157d014d26003d090000d88300b71b0000d1f3007370bc00bf6e003d09000095a3003e0ad280911a003d09000078a0012342800074f80054ffc1806aa6011146c700613d00780e60005e4a00b71b000058a8002933178055f80016f6e800535d0017bbbc8050d6003260b30049b3001813690047770055b45200454c0093c6138043320071eeaa8041280037b548803f2e0048656b003d4300020d9b803b67000e3dd500399a0038bc4e0037db001f31ad0036290015cee60034840017ced58032ec001c763d803160000e8005802fe000099d96802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q85 : Row := ⟨85, -7403, -7402, 32835095000, 1986665427, 1339175646, 52, 0x6ef8d185872c00755b070532b302a65f04850a5f00238f3a849894000384e304104f001d67d683f0c8009b1e09027bcd0103baec0255d900b652fe0243bb003a697801624d00233e8e01579000f27e1b013942002b32f0012fc300524e4601268e014462e9011da000e79c2a0114f800ef72cf010c93009de00e81046f00a9118180d8830002bbf700a93f00b61e3e009f240037bcb5009a5100ac47e10095a30106d3da00911a002f9cde80844d002de9918074f800879da1806aa6001c40dc00676a002a0e710064470039eedd80613d007859ca005e4a0032f7040058a80021243c0055f8001e04e70050d6007a038b004e6200795d82004c010072c4700049b3006f8b898047770004ef5280454c0027d60d80433200466b20804128002db511803f2e002c372d003d4300312803803b67001522f900399a002959968037db001762bc803629000ceaab803484001aa2638032ec000ef80f803160000a4ad1802fe00002d435002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q86 : Row := ⟨86, -18277, -18276, 27004762000, 2350099668, 1088281406, 44, 0xa06bd20360ea0242ae920346b402ad3cdc032d490139d41c0314a301f00b6202fcbd00def6c202b94c002ed2ab82a42a010b4227014d26005e3cab8139420006676c812fc3018f4b8081268e01091893011da000ae90e28114f800b12f0b80fc8a0105d63b80f4e2003ca86d00d8830048339180d1f300b62ba400ae8a011564ba00a93f00683678009f24007a12000078a001312d000074f8003d090000716c006a5f95806aa6002160ec00676a0072038000613d003d09000058a8006feb3a8055f8007a1200004e6200e5e404804c0100537f2f0049b3002ad50e0043320072b0f0804128006670be003f2e003491cd003d430035c084803b67003cc56480399a000e1aab0037db002d452f00362900131bf4003484001a911e0032ec001225fe8031600008a132002fe00003c86b802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q87 : Row := ⟨87, -8177, -8176, 30234398000, 2181433691, 1224532279, 57, 0x5ed29c0532b3008f9ce0050a5f009dd68004e3440013ea4404bd590319bcb404989402a647f80474ec010efa58045259000128840430d20003db3d8346b4009afb8e82211f00a39a4002109a00b0310401e1fc01747ce001d360005db15401b77a0030cfd30190b80064749281849300353f580178cc0001f581016d600046847181624d000ff0e400ed76003cf90800e643003d33dc00df4800884d2800d88300bbb29000d1f3003771f000c56a003947f400bf6e00f4240000ae8a00b71b0000a93f00b8adc800a41e003d0900009f24003b3549809a5100571afa8095a3004e7205008cb4001340c58088700020d57980844d001c5d44007c6600448b600078a0007a12000058a800b71b000055f8003d090000535d00b71b000050d60092fa63004e620030d2bd00477700c4b81400454c0056a0f0004332002754f000412800630eec003f2e000301c4003d430037a98c003b6700351c6480399a0032d0478037db001cf7198036290014675a803484001054260032ec00139572803160000b8e6a002fe000038761802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q88 : Row := ⟨88, -25807, -25806, 25253543500, 2500390473, 1017527529, 48, 0x1b5fa8792ee010291c65101e1fc0014f32d01d36000ea0def016d6000b71b000157900062eb9a014d26003a6df781430d00dfd02501394200d9a3aa812fc3011150dc81268e004f8512011da000ff4b290114f8007aa7c6010c9300afae3b80fc8a0124426d80f4e2007cd14300ed7600373af200df4800e4e0b000cb960012a39f00c56a0041d73a80b9a000bb195580ae8a007cd0b000a93f00a1880700a41e01212d4c008870003d0900006dfc01312d00006aa60010810880676a007a120000613d00f424000058a8009eb47b8050d600678400004e620050e289004c0100022cf60049b30093e739004777002e6f0a00454c0055fdfe004332004e3ab580412800045765803f2e00471b14003d43004186d2003b67002f07f400399a001d76370037db00018a998036290033f922003484000f6c888032ec000c800a803160000b491e002fe00003f48a802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q89 : Row := ⟨89, -2346, -2345, 41254023000, 2249661324, 1678461762, 63, 0xeeedf006408c018775ae86100b017d09d485e10200edfe7e8532b30026ffae850a5f01c1992884bd59003aed1404989400b7badf832d490001bdd98314a30166e0e682fcbd01edd2f982e5900007d83682688801279fc90255d90025326c02109a00db662482009501d4cb3d81f10c0024579001e1fc008adf4d01c5360027cd9a01b77a005461c501aa2800307f22018493003a879f8178cc00a92ced01624d002634a00157900038acd1812fc3001341c901268e00fe727780df4800566d6680d883008c56a680d1f3005e26c600cb960037078a00c56a003d090000a93f006ff0a680a41e00324acb809a510019df118095a300734d33008cb400fc6e370088700022f931007c6600a9df01006aa60029723300676a00049df000644700335c70005b6e00b71b000055f8003d090000535d003d09000050d6007eb305004e6200000495004c0100a3804b0049b3009539520047770030790700454c007ab971004332006fe0c60041280027c0dc803f2e001cf20c803d4300150b3a003b670032cbc500399a00196f0b0037db00273ac40036290013bab68034840014262b8032ec0011db6b8031600009da8d802fe00003da67002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q90 : Row := ⟨90, -337831, -337830, 18923233000, 2240668447, 760735254, 34, 0x1bb5ea6acce690112ae47028fac0008fac602688800fe734e0243bb0217e6248232290021088181aa28003d090000d883003d090000c56a007a120000bf6e00f4240000b9a001ab3f0000b3ff016e360000ae8a01261eed00a41e01312d000074f801312d00006aa6005d56dc80676a0096cd23805b6e00f4240000535d00834aa40050d6007f5f650049b3000e1e8500477700813ee6804332005b397d004128005a7917803f2e001ed057803d430012cc79003b67001a82c080399a001b49568037db002becc6003629002d07a5803484001a5aba0032ec0014630d8031600014134e002fe0000a2a86802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q91 : Row := ⟨91, -6292, -6291, 33696322500, 2237310353, 1367118603, 57, 0x7b533e083f4b0197ac20071233010660ea06db5801072db206a6260252653b837bf201a324f502b94c00ca740b02a42a000aa3c8827bcd000f61238255d9011ececb8232290169c4d102211f002dd1dc02109a006fe3a6018493003a3c260178cc007aefd9814d26006d6ebc812fc3008deeef81268e00c747df8114f80023380c810c93001551c681046f00cafdd600fc8a004ca44480f4e2000737d780d1f30062665a00c56a010c6cba00bf6e001f987600b9a00072b23a00b3ff0001708000ae8a009be600009f240005e947809a5100dcffda00844d002433ec80804a005764bb8074f80013f05500716c010f91a9006dfc00332bc900676a007947b100613d0055756c805e4a007a12000050d6009927a0004e6201089d1c004c01003c6a120049b30033f064004777004bef8000454c002a902a004332004a297080412800032ef3003f2e00028980803d43005ac408003b67002300d780399a002824748037db0012e30c803629001811ca0034840014322d8032ec000b0efa003160000add16802fe00003905b802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q92 : Row := ⟨92, -22503, -22502, 26622853500, 2168217566, 1080044705, 40, 0x4800890430d2012ecb9804104f01f8c68603f0c800a63e8c03d2360165ae4403b49100182d700397d200ceb764037bf200a338f802cf170023bc3c028fac0055d07002109a021439c981d360007634bf81b77a0003c40f81aa2800359de18178cc003bfd6a00d883002081e180d1f30116167b80b3ff0048ed2080a93f003d090000844d01312d00007c6600ef58558078a0007eddaa80676a00b24f5580613d00f85b3a805b6e00b71b00004e6200a1378e004c01000cc68f8047770087652680454c0056bd1d0043320076e0ab8041280041b25f003f2e00976da9003d43002d9dcb003b670015f80d8037db00309392003629000c10e5803484002fd13d8032ec00108a77803160000ca254802fe00004100e802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q93 : Row := ⟨93, -9410, -9409, 30332791000, 2223961431, 1230700117, 55, 0xd43a4408814601770ac1883f4b00a7bd5287ff50006393f687c14500078e65828fac00de1e93027bcd0081f0bf026888011c76ce023229006e013a02109a006635c3820095008ca925819d3e00c4f9b18190b8007d0a08818493010a4cc40178cc004a2d9d816d6000669e2781624d0113cf3f0157900042810a014d26007a9082813942005ab3ba812fc300996c5e81268e00771682011da0008876928114f800392d14010c93005d679500fc8a006ee9df00df48002716c200d1f3002f63ef00cb96005b1742007c66008274ef0078a0008ae2a10074f8003d1b61006aa6007beb8e00676a0112a06f006447007fc12d005e4a00987c01005b6e003d09000055f8003d09000050d6003d0900004e6200773899004c0100a7e7d80049b3006201c18047770028d88000454c0050c73e804332004d3ec580412800536b61803d43000e38d6003b67003fd8a600399a0010e9600037db0021b8e9003629000e1aa0003484001841198032ec000ccc9f8031600009fbf0002fe00002f44f002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q94 : Row := ⟨94, -18308, -18307, 27133996500, 2324214604, 1091679486, 53, 0x377409a1b629300ffbc3e1a8e21000c93d486729101924bf106408c0003abaa05e102010d9f57050a5f001530df8430d2007fc94f03f0c8001ff342832d4900562a260314a3023780ab02fcbd00781b2c82e59000129d5202cf1700da4115023229015910b802109a001b6b6201aa2801a18bae019d3e0009f66f0190b8002cb77d8178cc000b4bb481430d0085139f8114f800558ae681046f00ac241180f4e2001a269380e64300d5fbf300d8830019be9900b3ff00a0020900ae8a003d090000804a003d09000078a0003d09000074f8016e360000716c00f42400006dfc011bba2a806aa6003d0900005e4a007a1200005b6e003d09000055f8006eaf6680535d00c27d998050d600a5a2dc804e62000023c2004c01003d4f6d8049b300d5ab3c8043320041c18a003f2e0047d382003d43002f100e803b670015852a80399a003552910037db000d496e803629001b41078034840019e20e0032ec0013c598803160000b2d2f802fe00003ebc2002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q95 : Row := ⟨95, -7823, -7822, 32816077500, 2023718553, 1332215753, 64, 0x1828b99083f4b00ee9ffe07ff50021cd57987c14500a0e0400712330027cf9786db5800098e6b06100b0036f74c05e10200683a1705b36600b370a905872c0006684e055c49000817eb8532b300bc7825850a5f0059224a0430d20021491f03f0c80032abf283d23601ef73a683b4910042ae368314a301340120026888008ced348255d90111d0b20190b80076f34e01430d00908ac80139420082824a012fc30016713c01268e003d0900011da0001971b00114f800531f0e010c930109f6c400cb960018f5d900c56a0078d21600bf6e0034ed7100b3ff003c219f00a93f0014fdee00a41e006cc503009f24001c2ce2009a51006cc43b0095a300358ea400911a003f44b1008870001831d200804a0067c2a2006dfc0002ffa100676a003d0900005b6e007a12000058a8003d09000055f8007a120000535d00b71b000050d600632676004e6200027909804c010039c8d90049b3009857e1004777008fe26f00454c001f6222804332006e47dc004128001a35fb003f2e003fef11003d430026996e003b670007523000399a001273eb0037db0030b74600362900252dcd803484000f3f198032ec000ed15a80316000093dce002fe000033efe802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q96 : Row := ⟨96, -76812, -76811, 20812174500, 2270624432, 836159959, 41, 0x749320177acf007ae0aa07851c02399b97874ac500025ce50712330220250b0255d900dba96c0243bb0157d10a82211f010ac94801f10c016e360000c56a01e8480000bf6e001a3a4680b9a000f4240000a93f005fd7b980a41e003d0900009f2400944c468095a3007a120000911a007a1200008cb4007a1200008870007a120000804a003d09000074f8007a120000716c0054c1d5806dfc00898d4200613d007a1200005e4a003d09000055f80017b3fe00535d007a6426004c01004359340049b300683a200047770062ceac00454c0081ac3580433200a47da3003f2e001b833f803d430017c4d600399a003da36a0037db00256e260036290032d62800348400271e280032ec0015e97e0031600008097e002fe0000536d6002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q97 : Row := ⟨97, -2053, -2052, 41696400000, 2078638859, 1702341566, 56, 0x3c0f941ef8d80212ebf69e0893000febef9836a600aa757a050a5f0148190404e3440052844a04bd5900b649e0049894016b490a045259009bb9fc0430d20026535403f0c800b19d4683d236007227688314a3001f89bb82fcbd005c43c681aa280080cb070190b8003b838381849300ab61798178cc00ed3de2816d600060fbf081579000c52c2801046f00dcf19600fc8a0093bd5a00f4e200c9735a00ed760044c23800e643003c16fc00d8830131de6e00ae8a0063e3a800a93f0110d75a00a41e009bef84009f2400167ea6009a51008e89da0095a30035924d808cb400739b6e808870001fd69980844d007ad77900613d000311ac805e4a00b71b00005b6e0023c2318058a800b71b00004e6200aff775804c010039284e0049b300441585804777002036e480454c00079118004332004c8cd800412800418314003f2e003b9b76003d43001b40ff003b6700303e2080399a00269f3c8037db001eb9db003629000ac5310034840017ffec8032ec000d9ce48031600008dfcb802fe00003a9cf802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q98 : Row := ⟨98, -35153, -35152, 24197982500, 2419774657, 974458841, 49, 0xe5515805872c020d77a5055c4900a29d3482e59000424d0d02cf170082a60c82a42a006babd0028fac00f901ef027bcd00de0c538268880256815f8255d900a14c828243bb000ba6408232290033ead501268e00b71b00010c930028052d01046f00b32b3200f4e2003f43be00ed760080338e00e643019dda2800df4800059f3400d88300080dc800c56a0018ed3400bf6e003e923800ae8a0059d2c800a41e00d661a00095a3002f77ec00911a00b71b00006aa600b71b0000676a00b71b0000644701a89b3800613d003facc8005e4a009ff72c005b6e003d09000058a8007a120000535d0062230c0050d60017aa4c004e6200881700004c01002fdd9c004777001e9acc00454c00418828003f2e005bd63c003d4300838664003b670025792a00399a002678da0037db001a4232803629002dd0958034840012b2380032ec001912788031600008986a002fe00003f0b5802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q99 : Row := ⟨99, -13079, -13078, 28509353000, 2062457649, 1156301841, 54, 0x2785cef9ff09f01b4837887c1450027a26c07851c00720ba005b3660083447e85872c003d83bf055c4900b0e9e3050a5f00987cd604e344010772138346b4003c9f9c832d49000fee1602109a014d383b01aa280071c8b1019d3e003a6840814d26008cb8ca81430d00535b85813942002ec34581268e0094f186010c93001458c301046f007da98900b3ff003b5983809a5100b3989d8095a30022a611008cb400a81fae00887000a739d400844d007983bb00804a00b4e1ec007c66001af89b0078a000ea20518074f800743b5280716c001a1bb8006dfc0072e20100644700b0657100613d0054630f005e4a003d0900005b6e005e98a50058a8003d48348055f8006e8058004c0100a1f1a60049b3001d4eaa80477700536b1e00454c00010dfe8043320042340980412800224dde003f2e0024de94803d43001a2993003b670025962c80399a00131d0a8037db002f51e600362900192681803484000fcc9e0032ec000a7106803160000c5ea2002fe00002fe16802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q100 : Row := ⟨100, -44964, -44963, 23052178000, 2190401576, 929471898, 51, 0x8bd8529a8e21006d481910bcc300cdd92605b366011905e80532b3004791930474ec001cee528430d20150eeeb04104f004cfacf83f0c8004347bd0397d20002c15e0346b40051eab1832d49003c4db78255d9015fd3a28243bb01bc996f82211f011bbd58013942003d090000ed76007ce8c780e64300d7008180df48003b960d00ae8a004ce9be00a93f00df3ac600a41e004eddbe009f24012a7524009a51007a1200008870003d090000804a003d0900007c6601276edc0078a0007a12000074f8002a5a1c00716c000f0b4000676a003d09000058a8003d09000055f8007366f800535d00facf080050d6004111fe004e62000172f4004c01003e21d40049b3007e9726004777000172f40043320028b19e0041280089cb0a003f2e005cb606003d43004efa66003b670041b3e400399a0013d68a8037db001f587b8036290013358c003484000a13f00032ec0019daca003160000b4682002fe0000464ca002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q101 : Row := ⟨101, -2345, -2344, 41865093000, 2119451705, 1704152974, 69, 0x538cf7c279dfb00c469f804bd5900b4ff7c045259017f6f290430d20018d38304104f0069b35783f0c80000137b8397d200104e510360ea003ccf4e0346b4003e01548314a300d4d2c602e590005d9ea402cf17003b4608826888000ca1af0255d9007a0d6c02211f009cf66c02109a013b060c020095014abf3481f10c00477ef301d36000b603c801b77a00674c3d019d3e006842778190b80012279e81849300e9d047810c9300f07c0d81046f0006b4ce80fc8a004c572c80e6430024281080df48003ba31c00d88300a073c580d1f30031d14b80cb9600c6a6ac00c56a0045cae000bf6e003d090000b9a0000947dc80b3ff003d0d9480a93f00c405d880a41e0019b45a009a5100073dfe8095a3000557e6008cb40034dc7800844d00175ce400804a0057cfae0078a000185f4e006dfc00b63ed800676a004c995000644700388d0c00613d00d9cd24005b6e003d09000058a8007a12000055f800260d5880535d003d0900004e6200ae2060804c0100348c850049b300324a768047770033c68380454c00291c0c004332004e946180412800218ca2003f2e0020021a003d430025717e803b67001ecf4400399a001d23e58037db000ee3e500362900273daa0034840013f1638032ec0011d4bd0031600007ba95802fe000036535802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q102 : Row := ⟨102, -182543, -182542, 20301451000, 2118457945, 818747009, 43, 0x762f9c903aeb0111b4ae03d236000a6455037bf200416a92027bcd00e12d190243bb007681ba02322900dcb32a02211f01fe80a201d3600062664c01b77a00934253819d3e006550128190b8004898b3018493006047c401624d00b38aba01430d003c455c0139420026f548012fc300b71b0000bf6e00e8a14a80b9a000b71b000078a0003d0900006dfc00b71b00006aa6016e360000676a003d0900006447003d090000613d01312d00005e4a003d0900005b6e00b71b000058a8000fb87f8050d6007a1200004e620004a044004c01005a13fd8049b3005a3c2480477700269c1c00454c0039085a0041280050bd41003f2e003503c6003d430000d26d803b670045eb7200399a0039447e00348400186a560032ec001ad57a003160000e4896002fe0000738e2802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q103 : Row := ⟨103, -2339, -2338, 41759491000, 2267756144, 1703717148, 63, 0xb401c38d7e6f00233ecf05872c001bae23855c4900f254d00532b3009922aa850a5f0026e6b004bd59001481b884989400d611a482e590021cab7b82cf17007f05cf82a42a027fdaee828fac0071a4df02211f00849b2802109a001c17220200950053122601f10c01719cd901e1fc000a8a8801d36000eccc9a01c5360029f49f01aa2800a404c00190b8000a58238184930068b6dc81624d002a0db601430d004d42100114f80000b6e800df4801303abb00d88300092aea00d1f300cc051800cb960039b06100c56a00d0b1ac0095a30044665800911a00baf3ed008cb4001fac9b008870003a9b38007c660069fe0d0078a0003c36b20074f800f6279200716c00047156806dfc006d00fe006aa600286bc180676a0034e31880613d0021d7b7805e4a007a12000058a8007a12000055f800b71b0000535d003d09000050d6007dd92d004e62003d6627804c01006113a98049b30017eba20047770023306400454c006bf7e90041280015fce1003f2e003e70fb003d43002e208a003b670028724400399a000046610037db001dad070036290021468c003484001908a00032ec000b08ea00316000094320802fe000031edc802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q104 : Row := ⟨104, -26689, -26688, 25848902500, 2387601437, 1040373615, 47, 0x3c4113405b36600a6844a855c49002b94618474ec0185a63c02b94c01a80f3002a42a0046ecdc028fac00dace84027bcd00ccae8c02688800fa58fc0255d901ba775e0243bb007dbb7b8200950024b8a7015790002c5ef2014d2600496f4481268e003f6fc200f4e2003c434200ed7600b6d24200e6430117107400df480009bee300d8830152903c0095a300383b04008cb4003d090000844d016d093800804a00f4240000676a007a1200006447003d090000613d007a1200005e4a003b8ffd805b6e007a120000535d003d09000050d600b71b00004e6200bae6da804c010035bb9c0049b300694f58004777005aa43800454c0089d5538043320008fb38804128002d6367003d4300016781803b67003047a300399a002660598037db00413cb20036290025b8ed003484000e9c8f0032ec0012a9610031600009851e802fe000041125802e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def q105 : Row := ⟨105, -78590, -78589, 22853513500, 1714116888, 926319325, 57, 0x5b2da02b72d20036ee880e59b7015ce70f8dea630000a1c38d7e6f0035817108814600a35d96083f4b0000d6a004104f00469d30037bf20081119f02a42a002da44c028fac01d2169d027bcd005606580268880031ef020255d9004c8a010243bb00c0a3780232290081285b0200950081ce9601f10c00157d0a018493003d090001430d001c16af813942009dae25010c930014698501046f008f6d1e80fc8a006a8c4d00e6430085774600d883003f2f1900d1f30082106d00bf6e003e410d00b9a00020c38500b3ff003d0900009f2400e24c9c809a51004c2c1b80911a000bf082008cb400092ea300844d003ae4b30078a00039a25c80676a009d6b77806447003d09000055f8003d09000050d6007ad09b004e6200b1dbf4004c0100715c960049b3005a47870047770047bff200454c002055f30043320000997f004128006d16d6003f2e001a75b1003d4300289baf003b6700181b8e80399a000a612c8037db0019f348003629001ba02b00348400108b140032ec0007c1e1003160000c24ed002fe00004b0b9002e6c⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def rows : List Row := [q2,q4,q6,q8,q10,q12,q14,q16,q18,q20,q22,q24,q26,q28,q30,q32,q34,q36,q38,q40,q42,q44,q46,q48,q50,q52,q53,q54,q55,q56,q57,q58,q59,q60,q61,q62,q63,q64,q65,q66,q67,q68,q69,q70,q71,q72,q73,q74,q75,q76,q77,q78,q79,q80,q81,q82,q83,q84,q85,q86,q87,q88,q89,q90,q91,q92,q93,q94,q95,q96,q97,q98,q99,q100,q101,q102,q103,q104,q105]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_valid : rows.all (valid 3000000 8000000 20000 10000000) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem row_valid (r : Row) (hr : r∈rows) : valid 3000000 8000000 20000 10000000 r=true :=
  (List.all_eq_true.mp all_valid) r hr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem row_costs (r : Row) (hr : r∈rows) :
    let xs := envelope r
    (xs.map (fee 8000000)).sum=r.finiteCost ∧ (xs.map Prod.snd).sum≤r.cap ∧
    fee 8000000 (3000000,r.cap-(xs.map Prod.snd).sum)=r.tailCost ∧
    ∀ x∈xs,x.1<3000000 := by
  obtain ⟨_,_,_,_,hc,ht,hf,ha,_⟩ := of_decide_eq_true (row_valid r hr)
  exact ⟨hc,ht,hf,fun x hx => of_decide_eq_true (List.all_eq_true.mp ha x hx)⟩
end FR7022NextRows

namespace ThetaScalar
def encodedSigns : ℕ := 0x4868a0a868a42824608864a048940068146480a4a0a8546854148888a850682868a81854088450a89468542054889850685864a828684498105498a89418880854a06464a018185448689088649498285804985018546440145444945060946854185884a860946498581098445490680468a8145884a06064a868a8089884a850909814a818a888a0409458541818a08858a09464a858189884689028946814141444682054a868a010a848a8406894a8581464442850845890640858441860985068a4289888986094546898241444449018a4486828a480a860684468442454405450a858940828544068a084a858582494409460686854681098446450a4285454249884449068a4945410548848909864a45424984454106890549424484494905454506804a44454905858a49014680860205428144818944498a0601488a82464489460a458989414a044586064445454184444a05058646450286448449094a42814185848984054a898a4146088681054a48864280484985020a86858285484649094a854902058881450a858a4582458881490a458686804588864a06880585418a88858606458a45410140858601898846828a488a860a8586894186484a89054582814186448646048a8a4a41884809890646864541868485410582858a428988488a098a4649010544498a0689458a4188408a81098a4a498244848589084989098084888a49054a4a8501868046450945468841868886460a09464a414a844a0509814a464146444a8a09488a0640858889050a4a8649424584450609894186804508854405458546810a084a490585864982424446890185858a414648860409864645014a484989068a850a828948814a09854906408588458a0a490a4a81468005850185894a8181444a85094588484185448a89068a8685424288098a05494682414684498504454688424a48064509468a494149888a880542498a410a4844450a498a45410a8886450a860a8a824544858105054606418048858605898906824a88468106468689828a40464209464448424a44898a0a05864a414a08894909898a894149444545044885894146888a0a0246888242468449490645414642888849440a868586418504464605058a88428a488a4601864646818648894a05498a85014a8441480a4a4546418944018609448645808984894606890a4a4209444646068949458181084985054a884a414548854a068982494286404a0506898682428488854504868589018544054a0a45468a8245448a460642864a428644848906464989810940844a0589454a8289484541048a854a42448446890a8a0a06014a88454a06860a894145808a8a0a89824442464489890a014585424a44864a0a418682408a448a4a06884586428684450a094a85494185804588068a81444185884540094485464242084685068a898a824a88464401894985814984898a0989880a024608464506464949414948424a098a858a4089488a49018606898245084a860546898881428486860a4548864286480a4a0189494a4186448a8605894642824980868908494a494186880a4605894945814688488901818581818a4844850605058a820a4809860a4689464189888982098a8a4a82444445820a864a054289884946098a848a4185408985048949448186088949060185458249448945094a89858185488681058845410249488605068985454245448a46094541458285448948090a4989428a0845490a468545824a88824a01468986814648424a0a458a49018a84864a06048a46414a88428909444a4a800a84818a09860a8582864881490549464a4241848589058a8086810a44868a06894945428484458a064646818145888a8a088a4a8a8086840a49054a458a42894489460941464a828580448a0945868a4109484189088682464289444541058606460144488a860a4a890a814a844a49060a868a4284404a4606414548824984464a060a8585404984468a06464685828544460909888a4a414a844a060549454a42458446490a81424a42828489880609454a81810446440986498a814644498601454909424544864505898945018540854a09894985824a8882890286488a4045448945098a05844146488a490845868a804244094a0a8448454185884a890a88898981454886880a458a81028584494508854646428548084a0a8a458682868849410582054a414944844a054686864109444685068a4a85418a44868105814a8680484845850681440681868889850a864545418500454a0949064041864886490a058585808584468409494682814648864a0848868a81868486060a894645814584460a080a8249424988494809894589414904864a06894989418a44424a02464649414a84864909848685024648068a098a4a85420948428a0a494985804180894a054a098a824a8885890586828542428446860a89844681848846840a854a46828a88494a06458542420648458604894a894185480589058945094286408586064189868249448489048a814542058881890545854a0285884a81058a868641888889890a458906428588488906810a8a804a40854a01458a8840854489850109864a81858485090a464a4a8286444a4609484988820648890a064a46858181444a8505868045818988868805858a46424904064a0a4a490581458449450286418a818644858a04494685018a848989028a8986814644418906864544408648868a054a054a414a48064206494a4682818886450a4a8885428a848a4a0a8a4505814a448649094a0582428a4848450409864a8288480a86098a0989824944864a0980454181454484460945054a4105488582064989864189448982054644058144848544098649058289048a850689854a814a80454505458648824a444a46090a4a81424648858209894986418948464609480a4a4185884a09050a494a414a888545094540858145844a88054a494641860081890a45454981468885490280468682860849890a464686020644894606468641414544828a06418a48408584498a0a450289818504454608864a8a428048864909854489014984864a054645414189844a850a084a418245444989048a858a8106400a460946858941464889890841464a818a488449054589880106444545064a49894189848641090a458942844486490a81860a4246488a4906450a8940464045490a4486884146484a0a0a0689498209448689098685454241884949064485454242488205064a8689828a444a4806488145014988858406424a05818a0449460544464a414a48864502858685418a44464902858a860285848a0509864984820a844289094a4a8a804a88054906490a45414a848909068a464682814485890a498885428a848a4a05454249428948488a08444941418a448a46004901498245440945068a8946414644454506418249424648488106854549820848494a098584454189884a810a4545898248048949098a840a818a484988054a4989828940468a06454540824988868506098a8a4286844a8a0686868a82468445860604858a424908850a09498446818588494902894146414640424809868a05824604894a0944494a8249448a4a02864989810a84494908868986028a8886050a8a8589404584828a09468146408548898609450a8a0148844945028a458a8181848686068a4045018a44494a058a4a85818a48494a0a8586418145408a860846868a81858805460446868941498849860542464a028a44488509894946810684498909468a4a01498448420a8189820048844a860689850a40454846850689854a414680460909864684818588860a0a0a89494249884a45058a894a4242844a860a84494582868885080a45854a428988858a06898108824a444944094a864a428a084246068a458a81428486850286858a42494445490a8a864801858885450586468541458402440945854a408a8849890982098942444405450a868a45028244868a05498405424684448609498589418244858a0a4a0581828548454904458a8a828a84058a08468686414a4845410982498a818548444905464445420a44898a01498945828a0486420586464941844449890545850542894889450546854042454086460a4a4a8882804481890a0a0a46414a44864505098a8982868805450684498a8145848509068945868246848186064580464245888584064886468249084a850549898a410a888a86028589464286448589094a45450286444a49094a414a818a088286098689868088848989058a0985804a48884a06498a8581828489450985488540458486860645868a4045404586068905424186844a4508898546828a84068505458a86028644498a06414641414a8484490949854581068845890a82464582898446820545494a404844454205458a06814544890a04454686814980458505498944824a4845450a0588498242848586094a8986824988888809488a8541494405090a894a0a414908450609460289814a408a8805068685828908464901464a454289848589024a4648824a4449850689864101894805860a86498981868842850585898280418845860641054a414648498905424686818288888a0646888a4146444a86068905864145844a4905468a818286848546088a458541464804810606854542864886450a41848a818888884609458945810a04894a0a8a8a46814a8446810a868a4582084845050a498601818a88468a0a864646424580824509454688824a84098a06098546814644898a0a86494a4186084a860a844949418a448205054a4a4a414548464a068442854246448a8406894945420908464105494a868245808a89014a8a4a828548868a0949418a0281848949068689494288884146044a4585408488868a054a054a814a848585098a818a82418485860986888a41894046460a8446464185444989044585028284484a89084246450149880a8a06494989814a404a4909814a4a41458488860a81854941098881860986498980498489410585864541484849060985050a4145448a4a06894886828940894506864684424140898a0906458942868046840585858a424948464906884a06424a8446060a858589418944464908858284424588484800410a8a4246088a4a09854a48428a484a4602858a86028588098a068589860289840686090a4985824548814a0685864640454446450a46094582858804890986894a41418449450949084581464489860a824945424944890905494941828588468208864a4a82464409850a4a4489408548498a0541464a81860448890a49454542098886850a894649820548850105458a428248488586068a4509804544894a06884a4542464089460a058a4482864882460909464642454486860685494581894441890a884689824288850509884a860289444a45054981854105888a840a46498581890846440941464a428a848689018942864185888846064945890188888a490989490681464441420a86454a4049884a4609860a4a8289488545094682468282404549068a884a4246488645088a49854249848686064a4941018a84890500458589418a88090806458642808548868606828a45414a8844450a4686884009888a840a85468682468885010a49864a818408458a098a8a06418a48094609494a458102804a890a8586488185844a84060a4586814a84494909854606428a48488a09444a8a414988850a09458a49428a844586024641494246488588068945844185048985018649854149480682004a89894186444485068546860289484a8505454545814a88424609458a4a40854484860546098a4249844689064505854141488949058a8446814a84464906498a4581894489400942498201458485850889484582868406890546064a818a0886420682468a81464888850688854a8205488a8a094a4a82828a884a82094a884a81444805490a864605818584894506098946814940464505458988824a08424902028546424688414605468645818548854906484985828548450a05864a86810a8486890a8a81894085448a4809898a8682450446460a854182828688468602868a85814848494a0a89864502854489090a4605854185484145044a8646804648898a09850586428a80454906898a8a8142448989040a8445414988458902458a8902498885860a454a418245844649088a4545418a440446058249868245448a850a81898a408148440a06454689420944410a05068645428a4846810949454a4184884a860486850981414485860a88844640058046880a4985844185448a460a05890a818a848a8905424a8a410a48464a0588898a414688460901494a46814a488a8909894248414a4849880a0a494a818a080946058a454a4246444586028609468245844546064a41490189444a8909868949814988804606854a45408684498909850a85818484458506854982824188464a064588464145444a8109468585828a44898a0a81444242868884460885854a428a040a89088685868186484a4906814a89420584844a0686894181054849490a4a4586424988858205414989828440050906068a0a81464886850589464a424580858506898648414a88418608044949428584854509444a46818644898a06884a8a82054849050a89868a028a4886490644824981498489440945814642050886450582494a424848494902464989818944854a0a4a8a86018a4446860689854581894842860a410986808980448509450646818a4845450486068a818188864906894846008a448a890a454549414548898a0646894282098845860881454a814a4805050686898a80854485490a418a4a41894484090a85854a8109488589098a4
def signs (k : ℕ) : ℤ := match (encodedSigns >>> (2*k)) % 4 with
  | 1 => 1
  | 2 => -1
  | _ => 0
end ThetaScalar

namespace ThetaScalar
open Finset
abbrev logScale : ℕ := 10000000000

def jet (a b i : ℕ) : ℕ :=
  2*logScale*a^(2*i+1)/((2*i+1)*b^(2*i+1))

def block (a b : ℕ) : ℕ := ∑ i∈range 7,jet a b i

def lg (k : ℕ) : ℕ := k.log2 * 6931471803 + block (k-2^k.log2) (k+2^k.log2)
def ug (k : ℕ) : ℕ := k.log2 * 6931471808 + block (k-2^k.log2) (k+2^k.log2) + 1600

private theorem jet_round (a b i : ℕ) (hb : 0<b) :
    (jet a b i:ℝ) ≤ 2*logScale*((a:ℝ)/b)^(2*i+1)/(2*i+1) ∧
     2*logScale*((a:ℝ)/b)^(2*i+1)/(2*i+1) ≤ (jet a b i:ℝ)+1 := by
  let d := (2*i+1)*b^(2*i+1)
  have hd : 0<d := by dsimp [d]; positivity
  let z := 2*logScale*a^(2*i+1)
  have hh : (z/d:ℕ)*d≤z := Nat.div_mul_le_self ..
  have hh' : z<(z/d+1)*d := by simpa [mul_comm] using Nat.lt_mul_div_succ z hd
  have eqn : 2*(logScale:ℝ)*((a:ℝ)/b)^(2*i+1)/(2*i+1) = (z:ℝ)/d := by
    dsimp only [z,d]; push_cast; rw [div_pow,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,mul_inv]; ring
  rw [eqn]
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  exact ⟨(le_div_iff₀ hd').mpr (by exact_mod_cast hh),
    (div_le_iff₀ hd').mpr (by exact_mod_cast hh'.le)⟩

theorem log_interval (k : ℕ) (hk : 0<k) :
    (lg k:ℝ)≤(logScale:ℝ)*Real.log k ∧ (logScale:ℝ)*Real.log k≤ug k := by
  let e := k.log2
  let p := 2^e
  have hp : 0<p := by dsimp [p]; positivity
  have hpk : p≤k := by simpa [p,e,Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hk.ne'
  have hkp : k<2*p := by
    simpa [p,e,Nat.log2_eq_log_two,pow_succ,mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1<2) k)
  let a := k-p
  let b := k+p
  let x : ℝ := (a:ℝ)/b
  have hbn : 0<b := by dsimp [b]; omega
  have hb : (0:ℝ)<b := by exact_mod_cast hbn
  have hr : (0:ℝ)<p := by exact_mod_cast hp
  have ha : (a:ℝ)=(k:ℝ)-p := Nat.cast_sub hpk
  have hbb : (b:ℝ)=(k:ℝ)+p := Nat.cast_add ..
  have hx0 : 0≤x := by dsimp [x]; positivity
  have hx3 : x≤1/3 := by
    apply (div_le_iff₀ hb).mpr
    rw [ha,hbb]
    have : (k:ℝ)<2*p := by exact_mod_cast hkp
    linarith
  have hx1 : x<1 := by linarith
  have hratio : (1+x)/(1-x) = (k:ℝ)/p := by
    apply (div_eq_div_iff (by linarith : (1:ℝ)-x≠0) hr.ne').mpr
    dsimp [x]; rw [ha,hbb]; field_simp; ring
  have logeq : Real.log k = e*Real.log 2 + Real.log ((1+x)/(1-x)) := by
    rw [hratio,Real.log_div (by exact_mod_cast hk.ne') hr.ne']
    have : Real.log (p:ℝ) = e*Real.log 2 := by dsimp [p];push_cast;rw [Real.log_pow]
    linarith
  let t (i : ℕ) : ℝ := 2*logScale*x^(2*i+1)/(2*i+1)
  let S := ∑ i∈range 7,x^(2*i+1)/(2*i+1)
  have ht : 2*logScale*S=∑ i∈range 7,t i := by
    dsimp only [S,t]; rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  have j1 : (block a b:ℝ)≤2*logScale*S := by
    rw [ht,block,Nat.cast_sum]
    exact sum_le_sum (fun i _=> (jet_round a b i hbn).1)
  have j2 : 2*logScale*S ≤ (block a b:ℝ)+7 := by
    rw [ht,block,Nat.cast_sum]
    calc
      _ ≤ ∑ i∈range 7,((jet a b i:ℝ)+1) := sum_le_sum (fun i _=>(jet_round a b i hbn).2)
      _ = _ := by simp [sum_add_distrib]
  have lo := Real.sum_range_le_log_div hx0 hx1 7
  have hi := Real.sum_range_sub_log_div_le (show |x|<1 by rwa [abs_of_nonneg hx0]) 7
  change |1/2*Real.log _-S|≤|x|^15/(1-x^2) at hi
  rw [abs_of_nonneg hx0] at hi
  have h2 : x^2 ≤ (1/3:ℝ)^2 := pow_le_pow_left₀ hx0 hx3 _
  have h15 := pow_le_pow_left₀ hx0 hx3 15
  have hrest : x^15/(1-x^2) ≤ (1/3:ℝ)^15/(1-(1/3:ℝ)^2) := by gcongr
  have hlogl : 2*logScale*S ≤ logScale*Real.log ((1+x)/(1-x)) := by
    change S ≤ 1/2*Real.log _ at lo
    norm_num [logScale] at lo ⊢; linarith
  have hlogu : logScale*Real.log ((1+x)/(1-x)) ≤ 2*logScale*S+1593 := by
    have hh := (le_abs_self _).trans (hi.trans hrest)
    norm_num [logScale] at hh ⊢; linarith
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have he : 0≤(e:ℝ) := Nat.cast_nonneg _
  have low : (e:ℝ)*6931471803 ≤ logScale*(e*Real.log 2) := by
    norm_num [logScale]; linarith only [mul_le_mul_of_nonneg_left h2l.le he]
  have high : logScale*(e*Real.log 2) ≤ (e:ℝ)*6931471808 := by
    norm_num [logScale]; linarith only [mul_le_mul_of_nonneg_left h2u.le he]
  change ((e*6931471803+block a b:ℕ):ℝ)≤_ ∧ _≤((e*6931471808+block a b+1600:ℕ):ℝ)
  push_cast
  rw [logeq,mul_add]
  norm_num [logScale] at j1 j2 hlogl hlogu low high ⊢
  constructor <;> linarith only [j1,j2,hlogl,hlogu,low,high]
end ThetaScalar
namespace ThetaScalar

abbrev gridN : ℕ := 512
def power2 (k : ℕ) := 2^k.log2
def idx (k : ℕ) := gridN*k/power2 k
def residual (k : ℕ) := gridN*k-idx k*power2 k
def floorLog (k : ℕ) := logScale*residual k/(gridN*k)
def ceilLog (k : ℕ) := logScale*residual k/(idx k*power2 k)+1

theorem idx_bounds {k : ℕ} (hk : 0<k) : gridN ≤ idx k ∧ idx k<2*gridN := by
  have hp : 0<power2 k := by dsimp [power2]; positivity
  have hle : power2 k≤k := by simpa [power2,Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hk.ne'
  have hlt : k<2*power2 k := by
    simpa [power2,Nat.log2_eq_log_two,pow_succ,mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) k
  exact ⟨(Nat.le_div_iff_mul_le hp).mpr (Nat.mul_le_mul_left gridN hle),
    (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_assoc,mul_comm,mul_left_comm] using Nat.mul_lt_mul_of_pos_left hlt (by decide : 0<gridN))⟩

private theorem residual_bound (k : ℕ) (hk : 0<k) :
    (floorLog k:ℝ) ≤ (logScale:ℝ)*Real.log ((gridN*k:ℕ)/(idx k*power2 k:ℕ):ℝ) ∧
    (logScale:ℝ)*Real.log ((gridN*k:ℕ)/(idx k*power2 k:ℕ):ℝ) ≤ ceilLog k := by
  let X := gridN*k
  let Y := idx k*power2 k
  have hX : 0<X := Nat.mul_pos (by decide) hk
  have hij : 0 < idx k := (show 0<gridN by decide).trans_le (idx_bounds hk).1
  have hY : 0<Y := Nat.mul_pos hij (by dsimp [power2];positivity)
  have hle : Y≤X := Nat.div_mul_le_self ..
  have hr : (residual k:ℝ)=(X:ℝ)-Y := Nat.cast_sub hle
  have hX' : (0:ℝ)<X := by exact_mod_cast hX
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hR : (0:ℝ)<(X:ℝ)/Y := div_pos hX' hY'
  have hl := Real.one_sub_inv_le_log_of_pos hR
  have hh := Real.log_le_sub_one_of_pos hR
  have bind0 : 1-((X:ℝ)/Y)⁻¹=((residual k:ℝ)/X) := by rw [hr];field_simp
  have bind1 : (X:ℝ)/Y-1=((residual k:ℝ)/Y) := by rw [hr];field_simp
  rw [bind0] at hl
  rw [bind1] at hh
  have lower : (floorLog k:ℝ)≤logScale*((residual k:ℝ)/X) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hX').mpr
    exact_mod_cast Nat.div_mul_le_self (logScale*residual k) X
  have upper : logScale*((residual k:ℝ)/Y)≤(ceilLog k:ℝ) := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hY').mpr
    exact_mod_cast (by simpa [mul_comm] using (Nat.lt_mul_div_succ (logScale*residual k) hY).le :
      logScale*residual k≤(logScale*residual k/Y+1)*Y)
  exact ⟨lower.trans (mul_le_mul_of_nonneg_left hl (by positivity)),
    (mul_le_mul_of_nonneg_left hh (by positivity)).trans upper⟩

-- Grid entry at j is the certified seven-term series for j/512.
def tableBody (j : ℕ) := block (j-gridN) (j+gridN)
def gridWord : ℕ := 0xce4863dce6fee332f36cc58ef9ad0a6aacd1d7da8e6694a96b321e676598791743cbf16a7fe5d31b33f2d6bbd47961f2a65cac42800e53c53d9f28b4510393c2db3dc995b3c3e4a4f353b23f818f1916424f9c8660b5be40cf86871f370b458f0302aac7352c4fe37461dbf1a711e178c9f6f58c603142362db2e6f315a6475b8a3965fec4cfc04f62415cddb10d67ce987d0e183c39b2e4661a6ebdfb0c01b4838565dcc0c2655b74610bda28b0727e3b982f8527dc12e4539e070266a70249000b80883d75bff5e8f1dfd3cf4eefd64fec97e15984dbebc43eddf36d37faf87bd5317ba05d9cbd8153775e99319eef38d7855792887e7bc4514ceddfae84c6ee99dd2376ae11a5bb07852b5d5bf6236e9a0f8697430f535b9c8a1bc5cbc59b9ae4a2bed371b12ce9b88867a75c1c11a12df9f24e16f2eb2fdb746d409db7b1c666da961ef76ca9819fb603e3f5dad97892ed587a14d6a2192e3b4bf94755a3724a92d0739ff36796e0d1b379e28959941f28acb5a0edb65096559b232cb2558f0668aec63ae1c562791a56b0ea4b37584bf9446c1160c4f5fe5f994afa05fa157a6d5c52bbeb81e55d4ffcc5ae550538d700fa76ab6bb35dd5ab71d88ad0838cbd65a65beeb1851b41581b5568abb9f71bd5b315fdaac492515557c9dd4aa6a3ce0550b098c2a707461552daf030a91906c554623ebf6a1bf70d9503645bea7c6516b53b8b3e5e9c7197d54d8e97b0a6721966530e67496971dad3d4ae3df1da51c5b40d263572c691c3a32348361504a3c51376d1b781cc28c636b5f4585324fa26c3e7ad10ae55fe86fcf7a942d12fd1a111d8b0505d8017e81903969401a063d9fb5de704faf501f27c1d21eb3d5fae2e9e584c044f005399276a3a24b3aa2202b9cf91dacce5088a367123ab5d37e154979b984f984d9fed54e6b9d2dcb351d43c69a35ddea4cee7fbd266101a093255e5e298d1c4b9cc3c3de52607c60492f8b3305976c000b4b8925ce25ae1f0932cbd232696048bdacad53573a5540baa529ebae22949b640eca206ac824f98ae112716cbb793308485c96ac3b7e49e9ba27243e738491c3e909c8b43e2664433cded21629d0a90558d5747fcd7f063e76d8471e833fa98ee56d1cc7448eea638b2c7b11ba052a58d7383f4468b60e0232e78a8f18b9cd1c8bffcd6c45d14b9622d150eef15cfa6108a8a44ff45164cc7a273b429512e1d45c8912e617c45a6227a215a13070ff04ebc8799ac0ec39d8960e1b716d930cfb0bc5861e922b42dfc014a15813f210a0201ee84a193a2c22103da20f89746d070527848322ab9641615241a0989f9d7040472b081a1d51840a0a8d020382bb7700ffd975801f0b22bfdf0501dfd73a51afdf751af7e9a48a1bf1c64481f75ca238faead10f7d1388663e58c40b1f13d9e02f7da4d227b8ac533bd9421a85eb168350f4c5bb4e79fff9b53cce7a73de4e73ca2f1ad10c7787320803c07cbb4ddeafb428ee90429676e43415bb4012a99d86fd3b8eb6f459f75532ee03a774c851d22784d0e84a0e9373c00b33b9ad766c5cbd6b08ee52091fa722ac34c38e28d7cdc57d3fbae1f2c4277093514fb8168ec51bf1b1ab6dec0993e6ef9af48374977485b8b02980db8a05376d5dd72d367b43fe5b23c53b6d84efbd66bbfc2d935abf1d05abbf809ad50f70a56a1f6c0cb4db7d9bda53996f4d1cb5704687ccc6d3409e431d9eaa7d30ce82a21666d7dd883337225459812193ecb3544cb653098ce326334b75917050b2c7e331d86386f792b18e180258ac508a0c48c5bbd61daf30e30b7c8ce1841025a6c130b4bd602c845b2fe043a297d518bfcbdd02edb5e7ba4742f0784fad76891f52ba6abbea5cc84c38ae2d8941d6fb6c2dcb7004d6e5b1274652d524cd2168da5956b390d4b6595a15982c75cbf7161f3c4f0b01c42cf579f284eab9802ea15b02e764aca2887b55e1a4e32ab8edd555407a1d0a92396405421838ea9d888d094d01d4d8a59f5c5b525ebc67a8f6cfe1d45f16088a215cac05099475e2813befdd3ed624569e86d11a4ed11c3fa72f5205137afff329af25ec94d0632b0264984c6d307ecf64975862e14b388232256252fd12942729893b8cc244968021c2479b84fd21fac5e0901389064794a99ca38fb05051aa7a5a48c6887a745be6fba22a4367c11348eda688b7b5d143e54b4e21b7463bd0bde78f8850100f74209330920c8dae15046821fe81445635402a1d6c1fd8efa6cfce5c2607d81a2483e4800ca9ee77fb10f557331279b8d1943c62d3489df4860c8edbc4c4a75e9d0163a7a8adb9cfffdac8e614e56e7214896f388f1d451c09e16c8de60d5246e38e8d736a080151b122c0d0d69ff1446a56d91d34aea8a59a18d835cced20ece666e44a732b98c1d191de0720c6f701f0627f156e30c11f6918213f324bf0e9de85e8934fb2ec557401722eec9cb718b5225a8c8c632cc6281d9622e96f4af151912568904402ac386411521293b0a7039a40527e84ba28bd65ad141da82709ee408384e6cf57926b3ba251318600c496b631884a543d9f24a6772d92114aa488e79e3ba463443d32295900591086187c862eeb46420cee2e2080f7aa8ffd9e2b07dd513923dde223f1e68a0d08ef0f9e08756c26e639a7c5061c4c7de68de26dd586cf3ee683569baf11a2c81100cd1f3130646c32043123e7d218089c228bbf8279c5bd4b8862cd62ee315e0c0a78aab14c48532d4766288072ba13b4dfd60994a28484a75a2dc242295491184ea92087c2420c41ad8dd21fbc77d80f50d168876191d5838d4c9ca1b4dfaff0d1884908644e3b282feb16ec16d6fea20adbf3e485261199826f033e4125761e9089b0ee10405133cc1de3ddee0dcf033f0655c4a282e1e01ec14c5d0aa093dc048040c03e201bc6f8ec0b95c63a04a375db01bdbaf20094b8a8c0253771200000000
def gridVal (j : ℕ) := (gridWord >>> (33*(j-gridN))) % 2^33
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem gridOK : (List.range 512).all (fun i=>decide (gridVal (512+i)=tableBody (512+i))) = true := by decide +kernel
theorem grid_spec {k : ℕ} (hk : 0<k) : gridVal (idx k)=tableBody (idx k) := by
  obtain ⟨hl,hu⟩:=idx_bounds hk
  have h : idx k-gridN ∈ List.range 512 := List.mem_range.mpr (by dsimp only [gridN] at *;omega)
  simpa [Nat.add_sub_of_le hl] using of_decide_eq_true ((List.all_eq_true.mp gridOK) _ h)

def gl (k : ℕ) : ℤ := (k.log2*6931471803+gridVal (idx k)+floorLog k:ℕ)-45
def gh (k : ℕ) : ℤ := (k.log2*6931471808+gridVal (idx k)+ceilLog k+1645:ℕ)

theorem fast_log_interval (k : ℕ) (hk : 0<k) :
    (gl k:ℝ)≤logScale*Real.log k ∧ logScale*Real.log k≤gh k := by
  obtain ⟨h512,h1024⟩:=idx_bounds hk
  have hj : 0 < idx k := lt_of_lt_of_le (by decide : 0<gridN) h512
  have he : (idx k).log2 = 9 := by
    rw [Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact h512
    · exact h1024
  have h0 := log_interval (idx k) hj
  simp only [lg,ug,he,show 2^9=gridN by decide] at h0
  change (((9*6931471803+tableBody (idx k):ℕ):ℝ)≤_ ∧ _≤((9*6931471808+tableBody (idx k)+1600:ℕ):ℝ)) at h0
  have hc := residual_bound k hk
  have hp : 0<power2 k := by unfold power2;positivity
  have hR : Real.log ((gridN*k:ℕ)/(idx k*power2 k:ℕ):ℝ) =
      9*Real.log 2+Real.log k-(Real.log (idx k)+k.log2*Real.log 2) := by
    push_cast
    rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    dsimp only [power2];push_cast;rw [Real.log_pow]
    have : Real.log (gridN:ℝ)=9*Real.log 2 := by rw [show (gridN:ℝ)=(2:ℝ)^9 by norm_num [gridN],Real.log_pow];norm_num
    change Real.log 512 + _ - _ = _; rw [show Real.log 512=9*Real.log 2 from this]
  rw [hR] at hc
  have hE0 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg (α:=ℝ) k.log2)
  have hE1 := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg (α:=ℝ) k.log2)
  simp only [gl,gh,grid_spec hk]
  norm_num [logScale] at h0 hc ⊢
  constructor <;> linarith only [h0.1,h0.2,hc.1,hc.2,hE0,hE1,Real.log_two_lt_d9,Real.log_two_gt_d9]
end ThetaScalar

/- Oriented integer rounding and signed moment bounds from CGandGameEngineLearner/goldbach-proofs, PRs 2645 (CATLILIZHOU) and 2649 (nanzhiyan1), Apache-2.0. -/
namespace ThetaScalar
open Finset
def signedLow (v l h : ℤ) : ℤ := if 0 ≤ v then v*l else v*h
def signedHigh (v l h : ℤ) : ℤ := if 0 ≤ v then v*h else v*l
theorem signed_bounds (v l h : ℤ) (x : ℝ) (hx : (l:ℝ) ≤ x ∧ x ≤ h) :
    (signedLow v l h:ℝ) ≤ v*x ∧ v*x ≤ (signedHigh v l h:ℝ) := by
  by_cases hv : 0 ≤ v
  · have p : (0:ℝ) ≤ v := by exact_mod_cast hv
    simp only [signedLow,signedHigh,hv,ite_true,Int.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 p, mul_le_mul_of_nonneg_left hx.2 p⟩
  · have p : (v:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hv)
    simp only [signedLow,signedHigh,hv,ite_false,Int.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 p, mul_le_mul_of_nonpos_left hx.1 p⟩
theorem int_lower (z : ℤ) (k : ℕ) (hk : 0 < k) :
    ((z/(k:ℤ):ℤ):ℝ) ≤ (z:ℝ)/k := by
  apply (le_div_iff₀ (show (0:ℝ)<k by exact_mod_cast hk)).mpr
  exact_mod_cast Int.ediv_mul_le z (by exact_mod_cast hk.ne' : (k:ℤ) ≠ 0)
theorem int_upper (z : ℤ) (k : ℕ) (hk : 0 < k) :
    (z:ℝ)/k ≤ ((-((-z)/(k:ℤ)):ℤ):ℝ) := by
  have h := int_lower (-z) k hk
  push_cast at h ⊢
  rw [neg_div] at h
  linarith
theorem real_interval (S : Finset ℕ) (C : ℕ → ℝ)
    (cl ch ll lh : ℕ → ℤ) (D W : ℝ)
    (hk : ∀ k ∈ S, 0 < k)
    (hc : ∀ k ∈ S, (cl k:ℝ) ≤ D*C k ∧ D*C k ≤ ch k)
    (hl : ∀ k ∈ S, (ll k:ℝ) ≤ W*Real.log k ∧ W*Real.log k ≤ lh k)
    (hW : 0 ≤ W) :
    ((∑ k ∈ S, signedLow (cl k) (ll k) (lh k)/(k:ℤ):ℤ):ℝ) ≤
        (D*W)*(∑ k ∈ S, C k*Real.log k/k) ∧
    (D*W)*(∑ k ∈ S, C k*Real.log k/k) ≤
        ((∑ k ∈ S, -((-signedHigh (ch k) (ll k) (lh k))/(k:ℤ)):ℤ):ℝ) := by
  rw [Int.cast_sum, Int.cast_sum, mul_sum]
  have one (k : ℕ) (h : k ∈ S) :
      ((signedLow (cl k) (ll k) (lh k)/(k:ℤ):ℤ):ℝ) ≤ (D*W)*(C k*Real.log k/k) ∧
      (D*W)*(C k*Real.log k/k) ≤ ((-((-signedHigh (ch k) (ll k) (lh k))/(k:ℤ)):ℤ):ℝ) := by
    have hp : (0:ℝ)<k := by exact_mod_cast hk k h
    have hn : 0 ≤ W*Real.log k := mul_nonneg hW (Real.log_nonneg (by exact_mod_cast (hk k h)))
    have L := (signed_bounds (cl k) _ _ _ (hl k h)).1
    have U := (signed_bounds (ch k) _ _ _ (hl k h)).2
    have c1 := L.trans (mul_le_mul_of_nonneg_right (hc k h).1 hn)
    have c2 := (mul_le_mul_of_nonneg_right (hc k h).2 hn).trans U
    have eqn : (D*W)*(C k*Real.log k/k) = (D*C k)*(W*Real.log k)/k := by ring
    rw [eqn]
    exact ⟨(int_lower _ _ (hk k h)).trans (div_le_div_of_nonneg_right c1 hp.le),
      (div_le_div_of_nonneg_right c2 hp.le).trans (int_upper _ _ (hk k h))⟩
  exact ⟨sum_le_sum (fun k h => (one k h).1), sum_le_sum (fun k h => (one k h).2)⟩
theorem bracket_from_rounding (S : Finset ℕ) (v0 v1 : ℕ → ℤ) (W : ℕ)
    (hW : 0 < W) (hk : ∀ k ∈ S, 0 < k)
    (h0 : (∑ k ∈ S, -((-(W:ℤ)*v0 k)/(k:ℤ))) ≤ 0)
    (h1 : 0 ≤ ∑ k ∈ S, (W:ℤ)*v1 k/(k:ℤ)) :
    (∑ k ∈ S, (v0 k:ℝ)/k) ≤ 0 ∧ 0 ≤ ∑ k ∈ S, (v1 k:ℝ)/k := by
  have wp : (0:ℝ)<W := by exact_mod_cast hW
  have hL := sum_le_sum (fun k (h : k ∈ S) => int_upper ((W:ℤ)*v0 k) k (hk k h))
  have hU := sum_le_sum (fun k (h : k ∈ S) => int_lower ((W:ℤ)*v1 k) k (hk k h))
  have hh0 : (∑ k ∈ S, ((-((-((W:ℤ)*v0 k))/(k:ℤ)):ℤ):ℝ)) ≤ 0 := by
    exact_mod_cast (by simpa [neg_mul] using h0 : ∑ k ∈ S, -((-((W:ℤ)*v0 k))/(k:ℤ)) ≤ 0)
  have hh1 : 0 ≤ (∑ k ∈ S, ((((W:ℤ)*v1 k)/(k:ℤ):ℤ):ℝ)) := by exact_mod_cast h1
  have lo := hL.trans hh0
  have hi := hh1.trans hU
  simp only [Int.cast_mul, Int.cast_natCast, mul_div_assoc, ← mul_sum] at lo hi
  exact ⟨nonpos_of_mul_nonpos_right lo wp, nonneg_of_mul_nonneg_right hi wp⟩
theorem normalized_error (M : ℝ) (Z q φ : ℕ) (lo hi : ℤ)
    (hZ : 0 < Z) (hq : 0 < q) (hφ : 0 < φ)
    (e : (lo:ℝ) ≤ Z*M ∧ Z*M ≤ hi) :
    |(-M)/q - 1/φ| ≤
      ((max (((φ:ℤ)*lo+(Z*q:ℕ)).natAbs) (((φ:ℤ)*hi+(Z*q:ℕ)).natAbs) : ℕ): ℝ) /
        ((Z:ℝ)*q*φ) := by
  have pZ : 0<(Z:ℝ) := by exact_mod_cast hZ
  have pq : 0<(q:ℝ) := by exact_mod_cast hq
  have pφ : 0<(φ:ℝ) := by exact_mod_cast hφ
  let A : ℤ := (φ:ℤ)*lo+(Z*q:ℕ)
  let B : ℤ := (φ:ℤ)*hi+(Z*q:ℕ)
  let K := max A.natAbs B.natAbs
  have LA : |(A:ℝ)| ≤ K := by
    have h : ((A.natAbs:ℕ):ℝ) ≤ K := by exact_mod_cast (le_max_left A.natAbs B.natAbs)
    exact_mod_cast (show |A| ≤ (K:ℤ) by rw [Int.abs_eq_natAbs]; exact_mod_cast (le_max_left A.natAbs B.natAbs))
  have UB : |(B:ℝ)| ≤ K := by
    have h : ((B.natAbs:ℕ):ℝ) ≤ K := by exact_mod_cast (le_max_right A.natAbs B.natAbs)
    exact_mod_cast (show |B| ≤ (K:ℤ) by rw [Int.abs_eq_natAbs]; exact_mod_cast (le_max_right A.natAbs B.natAbs))
  have l := (abs_le.mp LA).1
  have u := (abs_le.mp UB).2
  simp only [A,B,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul] at l u
  have mm : |(φ:ℝ)*(Z*M)+(Z:ℝ)*q| ≤ K := by
    rw [abs_le]
    constructor
    · exact l.trans (add_le_add (mul_le_mul_of_nonneg_left e.1 pφ.le) le_rfl)
    · exact (add_le_add (mul_le_mul_of_nonneg_left e.2 pφ.le) le_rfl).trans u
  change |(-M)/q-1/φ| ≤ (K:ℝ)/((Z:ℝ)*q*φ)
  apply (le_div_iff₀ (by positivity)).mpr
  have eqn : ((-M)/q-1/φ)*((Z:ℝ)*q*φ) = -((φ:ℝ)*(Z*M)+(Z:ℝ)*q) := by
    field_simp
    ring
  rw [← abs_of_pos (show 0<(Z:ℝ)*q*φ by positivity),← abs_mul,eqn,abs_neg]
  exact mm
end ThetaScalar

namespace ThetaScalar
open Finset
noncomputable section

def support (K q : ℕ) := (Icc 1 K).filter (fun k => k.Coprime q)
def base (K L : ℕ) (sg : ℕ→ℤ) (k : ℕ) : ℤ := sg k * (min (K-L) (K-k):ℕ)
def bump (L k : ℕ) : ℤ := if L<k then 1 else 0

def weight (K L : ℕ) (sg : ℕ→ℤ) (z : ℤ) (k : ℕ) : ℤ :=
  1000*base K L sg k+z*bump L k

def harm (S : Finset ℕ) (w : ℕ→ℤ) : ℝ := ∑ k∈S,(w k:ℝ)/k

def alpha (K L q : ℕ) (sg : ℕ→ℤ) : ℝ :=
  -harm (support K q) (base K L sg)/harm (support K q) (bump L)

def co (K L q : ℕ) (sg : ℕ→ℤ) (k : ℕ) : ℝ :=
  ((base K L sg k:ℝ)+alpha K L q sg*(bump L k:ℝ))/(K-L:ℕ)

theorem slope_pos (K L q : ℕ) {k : ℕ} (hk : k∈support K q) (hkL : L<k) :
    0<harm (support K q) (bump L) := by
  apply sum_pos' (fun j _=>by dsimp only [bump]; split <;> positivity)
  refine ⟨k,hk,?_⟩
  have hkp : 0<k := (mem_Icc.mp (mem_filter.mp hk).1).1
  simp [bump,hkL]; positivity

theorem slope_zero (K L q : ℕ) (sg : ℕ→ℤ) (hp : 0<harm (support K q) (bump L)) :
    (∑ k∈support K q,co K L q sg k/k) = 0 := by
  let S := support K q
  have h0 : harm S (base K L sg)+alpha K L q sg*harm S (bump L) = 0 := by
    change harm S _ + (-harm S _/harm S _)*harm S _ = 0
    have hn : harm S (bump L)≠0 := hp.ne'
    field_simp [hn]; ring
  calc
    _ = (harm S (base K L sg)+alpha K L q sg*harm S (bump L))/(K-L:ℕ) := by
      dsimp only [harm,co,S]
      rw [mul_sum,←sum_add_distrib,sum_div]
      apply sum_congr rfl; intro k _; ring
    _ = 0 := by rw [h0,zero_div]

abbrev den (K L : ℕ) : ℕ := 1000*(K-L)
abbrev zden (K L : ℕ) : ℕ := den K L * logScale

theorem coeff_in (K L q : ℕ) (sg : ℕ→ℤ) (lo hi : ℤ) (hK : L<K)
    (ha : (lo:ℝ)/1000 ≤ alpha K L q sg ∧ alpha K L q sg ≤ (hi:ℝ)/1000) (k : ℕ) :
    (weight K L sg lo k:ℝ) ≤ den K L * co K L q sg k ∧
    den K L * co K L q sg k ≤ (weight K L sg hi k:ℝ) := by
  have hd : (0:ℝ)<(K-L:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hK
  have he : 0≤(bump L k:ℝ) := by unfold bump; split <;> norm_num
  have h1 := mul_le_mul_of_nonneg_right ha.1 he
  have h2 := mul_le_mul_of_nonneg_right ha.2 he
  unfold weight den co
  push_cast
  rw [show 1000*((K-L:ℕ):ℝ)*(((base K L sg k:ℝ)+alpha K L q sg*(bump L k:ℝ))/(K-L:ℕ)) =
    1000*((base K L sg k:ℝ)+alpha K L q sg*(bump L k:ℝ)) by field_simp]
  constructor <;> linarith only [h1,h2]

def rateNum (φ q Z : ℕ) (M₀ M₁ : ℤ) : ℕ :=
  max (((φ:ℤ)*M₀+(Z*q:ℕ)).natAbs) (((φ:ℤ)*M₁+(Z*q:ℕ)).natAbs)
def passes (K L q φ : ℕ) (M₀ M₁ : ℤ) (mass bound : ℕ) : Prop :=
  (rateNum φ q (zden K L) M₀ M₁*(den K L*10^16)+
    91*mass*(zden K L*q*φ))*10^9 ≤ bound*((zden K L*q*φ)*(den K L*10^16))

end
end ThetaScalar


namespace ThetaScalar
open Finset
abbrev Vec := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

def W : ℕ := 10^16
def gvec (K L : ℕ) (sg : ℕ→ℤ) (k : ℕ) : Vec :=
  let b := base K L sg k
  let e := bump L k
  let zL := gl k
  let zH := gh k
  (W*b/(k:ℤ),W*e/(k:ℤ),
   signedLow b zL zH/(k:ℤ),-((-signedHigh b zL zH)/(k:ℤ)),
   e*zL/(k:ℤ),-((-e*zH)/(k:ℤ)),|b|,e)

def fullsum (K L q : ℕ) (sg : ℕ→ℤ) : Vec := ∑ k∈support K q,gvec K L sg k

def dsum (K L d : ℕ) (sg : ℕ→ℤ) : Vec := ∑ j∈range (K/d),gvec K L sg (d*(j+1))

private theorem multiples {A : Type*} [AddCommMonoid A] (K d : ℕ) (hd : 0<d) (f : ℕ→A) :
    ∑ k∈(Icc 1 K).filter (d∣·),f k = ∑ j∈range (K/d),f (d*(j+1)) := by
  apply sum_nbij' (fun k=>k/d-1) (fun j=>d*(j+1))
  · intro k hk
    obtain ⟨hm,hdv⟩:=mem_filter.mp hk
    obtain ⟨hl,hu⟩:=mem_Icc.mp hm
    have h1 : 0<k/d:=Nat.div_pos (Nat.le_of_dvd hl hdv) hd
    have h2 : k/d≤K/d := Nat.div_le_div_right hu
    exact mem_range.mpr (by omega)
  · intro j hj
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd (by omega),?_⟩,dvd_mul_right ..⟩
    have h1:=mem_range.mp hj
    simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp (show j+1≤K/d by omega)
  · intro k hk
    obtain ⟨hm,hdv⟩:=mem_filter.mp hk
    have h1:=Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hm).1 hdv) hd
    rw [Nat.sub_add_cancel h1,Nat.mul_div_cancel' hdv]
  · intro j _
    simp [Nat.mul_div_cancel_left _ hd]
  · intro k hk
    obtain ⟨hm,hdv⟩:=mem_filter.mp hk
    have h1:=Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hm).1 hdv) hd
    rw [Nat.sub_add_cancel h1,Nat.mul_div_cancel' hdv]

def signsList (q : ℕ) (ds : List (ℕ×ℤ)) : Bool :=
  ds.all (fun z=>decide (0<z.1 ∧ z.1∣q)) &&
    (List.range q).all (fun t=>decide ((if t.Coprime q then (1:ℤ) else 0)=
      (ds.map fun z=>if z.1∣t then z.2 else 0).sum))

private theorem list_sum_mod (q k : ℕ) (ds : List (ℕ×ℤ))
    (h : ∀ z∈ds,z.1∣q) :
    (ds.map fun z=>if z.1∣k % q then z.2 else 0).sum =
      (ds.map fun z=>if z.1∣k then z.2 else 0).sum := by
  congr 1
  apply List.map_congr_left
  intro z hz
  simp only [Nat.dvd_mod_iff (h z hz)]

theorem divide_sum {K L q : ℕ} (sg : ℕ→ℤ) (hq : 0<q) (ds : List (ℕ×ℤ))
    (hd : signsList q ds=true) :
    fullsum K L q sg = (ds.map fun z=>z.2 • dsum K L z.1 sg).sum := by
  obtain ⟨hd1,hd2⟩:=Bool.and_eq_true_iff.mp hd
  have pdiv (z : ℕ×ℤ) (hz : z∈ds) : 0<z.1∧z.1∣q := of_decide_eq_true (List.all_eq_true.mp hd1 z hz)
  have hi (k : ℕ) : (if k.Coprime q then (1:ℤ) else 0)=
      (ds.map fun z=>if z.1∣k then z.2 else 0).sum := by
    have h0:=of_decide_eq_true (List.all_eq_true.mp hd2 (k % q) (List.mem_range.mpr (Nat.mod_lt _ hq)))
    have he : (k % q).Coprime q ↔ k.Coprime q := by
      simp only [Nat.coprime_iff_gcd_eq_one]
      rw [←Nat.gcd_rec q k,Nat.gcd_comm q k]
    simpa only [he,list_sum_mod q k ds (fun z hz=>(pdiv z hz).2)] using h0
  let f := gvec K L sg
  have factor (v : List (ℕ×ℤ)) (hdv : ∀ z∈v,0<z.1) :
      (∑ k∈Icc 1 K, ((v.map fun z=>if z.1∣k then z.2 else 0).sum) • f k) =
        (v.map fun z=>z.2 • dsum K L z.1 sg).sum := by
    induction v with
    | nil=>simp
    | cons a ds ih=>
      simp only [List.map_cons,List.sum_cons,add_smul,sum_add_distrib]
      rw [ih (fun z hz=>hdv z (List.mem_cons_of_mem _ hz))]
      congr 1
      unfold dsum
      rw [←multiples K a.1 (hdv _ (by simp)) f,sum_filter,smul_sum]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp_all
  unfold fullsum support; rw [sum_filter]
  rw [←factor ds (fun z hz=>(pdiv z hz).1)]
  apply sum_congr rfl; intro k _
  rw [←hi]
  split_ifs <;> simp [f]
end ThetaScalar

namespace ThetaScalar
open Finset
noncomputable def moment (S : Finset ℕ) (f : ℕ→ℤ) : ℝ := ∑ k∈S,(f k:ℝ)*Real.log k/k

private theorem harmonic_rounded (K q : ℕ) (f : ℕ→ℤ) :
    (((∑ k∈support K q,(W:ℤ)*f k/(k:ℤ)):ℤ):ℝ) ≤ (W:ℝ)*harm (support K q) f ∧
    (W:ℝ)*harm (support K q) f ≤ ((∑ k∈support K q,(W:ℤ)*f k/(k:ℤ)):ℤ)+(K:ℝ) := by
  let S := support K q
  have hcard : S.card≤K := by
    apply (card_le_card (filter_subset ..)).trans
    simp
  have hW (k : ℕ) (hk : k∈S) :
      (((W:ℤ)*f k/(k:ℤ):ℤ):ℝ)≤(W:ℝ)*((f k:ℝ)/k) ∧
      (W:ℝ)*((f k:ℝ)/k)≤(((W:ℤ)*f k/(k:ℤ):ℤ):ℝ)+1 := by
    have hpk : 0<k := (mem_Icc.mp (mem_filter.mp hk).1).1
    have hl:=int_lower ((W:ℤ)*f k) k hpk
    have hh:=Int.emod_lt ((W:ℤ)*f k) (by exact_mod_cast hpk.ne' : (k:ℤ)≠0)
    have he:=Int.emod_add_ediv_mul ((W:ℤ)*f k) (k:ℤ)
    have ku : (W:ℤ)*f k≤(((W:ℤ)*f k/(k:ℤ))+1)*(k:ℤ) := by
      simp only [Int.natAbs_natCast] at hh
      linarith
    simpa only [Int.cast_mul,Int.cast_natCast,mul_div_assoc] using And.intro hl
      ((div_le_iff₀ (show 0<(k:ℝ) by exact_mod_cast hpk)).mpr (by exact_mod_cast ku) :
        (((W:ℤ)*f k:ℤ):ℝ)/k ≤ (((W:ℤ)*f k/(k:ℤ):ℤ):ℝ)+1)
  simp only [harm,mul_sum,Int.cast_sum]
  refine ⟨sum_le_sum (fun k hk=>(hW k hk).1),?_⟩
  calc
    _ ≤ ∑ k∈S,(((((W:ℤ)*f k/(k:ℤ)):ℤ):ℝ)+1) := sum_le_sum (fun k hk=>(hW k hk).2)
    _ ≤ _ := by rw [sum_add_distrib];simp only [sum_const,nsmul_eq_mul,mul_one]; exact add_le_add_right (by exact_mod_cast hcard : (#S:ℝ)≤K) _

theorem fullsum_values (K L q : ℕ) (sg : ℕ→ℤ) :
    fullsum K L q sg =
      let S := support K q
      let b := base K L sg
      let e := bump L
      (∑ k∈S,(W:ℤ)*b k/(k:ℤ),∑ k∈S,(W:ℤ)*e k/(k:ℤ),
       ∑ k∈S,signedLow (b k) (gl k) (gh k)/(k:ℤ),
       ∑ k∈S,-((-signedHigh (b k) (gl k) (gh k))/(k:ℤ)),
       ∑ k∈S,e k*gl k/(k:ℤ),∑ k∈S,-((-e k*gh k)/(k:ℤ)),
       ∑ k∈S,|b k|,∑ k∈S,e k) := by
  unfold fullsum
  generalize support K q=S
  induction S using Finset.induction_on with
  | empty=>rfl
  | @insert k s hk ih=>
    dsimp only
    simp only [sum_insert hk,ih]
    rfl

structure Values (K L q : ℕ) (sg : ℕ→ℤ) (h0 h1 l0 u0 l1 u1 m cnt : ℤ) : Prop where
  hbase : (h0:ℝ) ≤ W*harm (support K q) (base K L sg) ∧ W*harm (support K q) (base K L sg)≤h0+(K:ℝ)
  hextra : (h1:ℝ) ≤ W*harm (support K q) (bump L) ∧ W*harm (support K q) (bump L)≤h1+(K:ℝ)
  mbase : (l0:ℝ)≤logScale*moment (support K q) (base K L sg) ∧ logScale*moment (support K q) (base K L sg)≤u0
  mextra : (l1:ℝ)≤logScale*moment (support K q) (bump L) ∧ logScale*moment (support K q) (bump L)≤u1
  baseAbs : (∑ k∈support K q,|(base K L sg k:ℝ)|)=m
  count : (∑ k∈support K q,(bump L k:ℝ))=cnt

theorem values_of_sum (K L q : ℕ) (sg : ℕ→ℤ) (h0 h1 l0 u0 l1 u1 m cnt : ℤ)
    (h : fullsum K L q sg=(h0,h1,l0,u0,l1,u1,m,cnt)) :
    Values K L q sg h0 h1 l0 u0 l1 u1 m cnt := by
  rw [fullsum_values] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩:=h
  let S:=support K q
  have H (f : ℕ→ℤ) := real_interval S (fun k=>(f k:ℝ)) f f gl gh 1 logScale
    (fun k hk=>(mem_Icc.mp (mem_filter.mp hk).1).1) (fun k _=>by simp)
    (fun k hk=>fast_log_interval k (mem_Icc.mp (mem_filter.mp hk).1).1) (by positivity)
  refine ⟨harmonic_rounded ..,harmonic_rounded ..,?_,?_,?_,?_⟩
  · simpa [moment,S] using H (base K L sg)
  · have eh (k : ℕ) : 0≤bump L k := by unfold bump; split <;> decide
    simpa [moment,S,signedLow,signedHigh,eh,neg_mul] using H (bump L)
  · simp only [Int.cast_sum,Int.cast_abs]
  · simp only [Int.cast_sum]

end ThetaScalar
namespace ThetaScalar
open Finset

private theorem mul_window (t x a b : ℝ) (hx : a≤x ∧ x≤b) :
    min (t*a) (t*b) ≤ t*x ∧ t*x ≤ max (t*a) (t*b) := by
  rcases le_total 0 t with ht|ht
  · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_left hx.1 ht),
      (mul_le_mul_of_nonneg_left hx.2 ht).trans (le_max_right ..)⟩
  · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hx.2 ht),
      (mul_le_mul_of_nonpos_left hx.1 ht).trans (le_max_left ..)⟩

structure PriceRow (K L q φ M price : ℕ) (sg : ℕ→ℤ) (lo hi : ℤ) : Prop where
  bracket : (lo:ℝ)/1000 ≤ alpha K L q sg ∧ alpha K L q sg ≤ (hi:ℝ)/1000
  zero : (∑ k∈support K q,co K L q sg k/k) = 0
  mass_le : (∑ k∈support K q,|co K L q sg k|)≤(M:ℝ)
  scalar : |-(∑ k∈support K q,co K L q sg k*Real.log k/k)/(q:ℝ)-1/(φ:ℝ)|+
      91*(∑ k∈support K q,|co K L q sg k|)/(10^16:ℝ) ≤ price/(10^9:ℝ)

def priceOK (K L q φ M price : ℕ) (lo hi : ℤ) (v : Vec) : Prop :=
  let (h0,h1,l0,u0,l1,u1,m,cnt) := v
  0<h1 ∧ 1000*(h0+K)+max (lo*h1) (lo*(h1+K))≤0 ∧
    0≤1000*h0+min (hi*h1) (hi*(h1+K)) ∧
    1000*m+(max lo.natAbs hi.natAbs:ℕ)*cnt≤(den K L * M:ℕ) ∧
    passes K L q φ (1000*l0+min (lo*l1) (lo*u1)) (1000*u0+max (hi*l1) (hi*u1)) (den K L*M) price

instance priceDec (K L q φ M price : ℕ) (lo hi : ℤ) (v : Vec) : Decidable (priceOK K L q φ M price lo hi v) := by
  obtain ⟨h0,h1,l0,u0,l1,u1,m,cnt⟩:=v
  unfold priceOK passes
  infer_instance

theorem price_of_values (K L q φ M price : ℕ) (sg : ℕ→ℤ) (lo hi : ℤ)
    (hK : L<K) (hq : 0<q) (hφ : 0<φ) (v : Vec)
    (hv : fullsum K L q sg=v) (hp : priceOK K L q φ M price lo hi v) :
    PriceRow K L q φ M price sg lo hi := by
  obtain ⟨h0,h1,l0,u0,l1,u1,m,cnt⟩:=v
  obtain ⟨hh1,hlo,hhi,hm,hpr⟩:=hp
  have va:=values_of_sum K L q sg h0 h1 l0 u0 l1 u1 m cnt hv
  let S:=support K q
  let b:=base K L sg
  let e:=bump L
  let α:=alpha K L q sg
  let c:=co K L q sg
  let B:=harm S b
  let E:=harm S e
  have wh : (0:ℝ)<W := by norm_num [W]
  have hB : (h0:ℝ)≤W*B ∧ W*B≤h0+(K:ℝ):=va.hbase
  have hE : (h1:ℝ)≤W*E ∧ W*E≤h1+(K:ℝ):=va.hextra
  have epos : 0<E := pos_of_mul_pos_right ((show (0:ℝ)<h1 by exact_mod_cast hh1).trans_le hE.1) wh.le
  have hL : 1000*((h0:ℝ)+K)+max ((lo:ℝ)*h1) ((lo:ℝ)*(h1+K))≤0 := by exact_mod_cast hlo
  have hH : 0≤1000*(h0:ℝ)+min ((hi:ℝ)*h1) ((hi:ℝ)*(h1+K)) := by exact_mod_cast hhi
  have low := (mul_window lo (W*E) _ _ hE).2
  have high := (mul_window hi (W*E) _ _ hE).1
  have lh : (W:ℝ)*(1000*B+lo*E)≤0 := by linarith only [hB.2,low,hL]
  have uh : 0≤(W:ℝ)*(1000*B+hi*E) := by linarith only [hB.1,high,hH]
  have alo := nonpos_of_mul_nonpos_right lh wh
  have ahi := nonneg_of_mul_nonneg_right uh wh
  have bracket : (lo:ℝ)/1000 ≤ α ∧ α ≤ (hi:ℝ)/1000 := by
    change (lo:ℝ)/1000 ≤ -B/E ∧ -B/E ≤ (hi:ℝ)/1000
    constructor
    · apply (le_div_iff₀ epos).mpr; linarith only [alo]
    · apply (div_le_iff₀ epos).mpr; linarith only [ahi]
  have scaled : (lo:ℝ)≤1000*α ∧ 1000*α≤(hi:ℝ) := by
    constructor <;> linarith only [bracket.1,bracket.2]
  let T := max lo.natAbs hi.natAbs
  have habs : |1000*α|≤(T:ℝ) := by
    rw [abs_le]
    have hl : |(lo:ℝ)|≤(T:ℝ) := by
      rw [←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast];exact_mod_cast le_max_left lo.natAbs hi.natAbs
    have hh : |(hi:ℝ)|≤(T:ℝ) := by
      rw [←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast];exact_mod_cast le_max_right lo.natAbs hi.natAbs
    exact ⟨(abs_le.mp hl).1.trans scaled.1,scaled.2.trans (abs_le.mp hh).2⟩
  have ne (k:ℕ) : 0≤(e k:ℝ) := by dsimp [e,bump];split <;> norm_num
  have hd : 0<(K-L:ℕ) := Nat.sub_pos_of_lt hK
  have hd' : (0:ℝ)<(K-L:ℕ) := by exact_mod_cast hd
  have dpos : (0:ℝ)<den K L := by unfold den;push_cast;positivity
  have mstep (k:ℕ) : (den K L:ℝ)*|c k| ≤ 1000*|(b k:ℝ)|+(T:ℝ)*(e k:ℝ) := by
    have hdv : (den K L:ℝ)*c k=1000*(b k:ℝ)+(1000*α)*(e k:ℝ) := by
      dsimp only [den,c,co,b,e,α,Nat.cast_mul,Nat.cast_ofNat]; field_simp; push_cast; ring
    rw [←abs_of_pos dpos,←abs_mul,hdv]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (ne k),abs_of_nonneg (by norm_num : (0:ℝ)≤1000)]
    exact add_le_add_right (mul_le_mul_of_nonneg_right habs (ne k)) _
  have massCap : (∑k∈S,|c k|)≤(M:ℝ) := by
    apply le_of_mul_le_mul_left _ dpos
    calc
      _ = ∑ k∈S,((den K L:ℝ)*|c k|) := mul_sum ..
      _ ≤ ∑ k∈S,(1000*|(b k:ℝ)|+(T:ℝ)*(e k:ℝ)) := sum_le_sum (fun k _=>mstep k)
      _ = 1000*(m:ℝ)+(T:ℝ)*cnt := by
        rw [sum_add_distrib,←mul_sum,←mul_sum,va.baseAbs,va.count]
      _ ≤ _ := by exact_mod_cast hm
  refine ⟨bracket,slope_zero K L q sg epos,massCap,?_⟩
  let P:= (logScale:ℝ)*moment S b
  let R:= (logScale:ℝ)*moment S e
  have hP : (l0:ℝ)≤P ∧ P≤u0 := va.mbase
  have hR : (l1:ℝ)≤R ∧ R≤u1 := va.mextra
  have rnn : 0≤R := by
    apply mul_nonneg (by positivity)
    apply sum_nonneg
    intro k hk
    exact div_nonneg (mul_nonneg (ne k) (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hk).1).1))) (by positivity)
  let Z := zden K L
  let A := ∑k∈S,c k*Real.log k/k
  have ha : (Z:ℝ)*A=1000*P+(1000*α)*R := by
    dsimp only [Z,zden,den,A,P,R,moment,α,c,co,b,e,Nat.cast_mul,Nat.cast_ofNat]
    simp only [mul_sum]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro k _
    field_simp
    push_cast
    ring
  let ml:=1000*l0+min (lo*l1) (lo*u1)
  let mh:=1000*u0+max (hi*l1) (hi*u1)
  have mid : (ml:ℝ)≤(Z:ℝ)*A ∧ (Z:ℝ)*A≤(mh:ℝ) := by
    rw [ha]
    simp only [ml,mh,Int.cast_add,Int.cast_min,Int.cast_max,Int.cast_mul,Int.cast_ofNat]
    constructor
    · exact add_le_add (mul_le_mul_of_nonneg_left hP.1 (by norm_num : (0:ℝ)≤1000)) ((mul_window lo R _ _ hR).1.trans (mul_le_mul_of_nonneg_right scaled.1 rnn))
    · exact add_le_add (mul_le_mul_of_nonneg_left hP.2 (by norm_num : (0:ℝ)≤1000)) ((mul_le_mul_of_nonneg_right scaled.2 rnn).trans (mul_window hi R _ _ hR).2)
  have zpos : 0<Z := Nat.mul_pos (Nat.mul_pos (by decide) hd) (by decide)
  let N:=rateNum φ q Z ml mh
  have err := normalized_error A Z q φ ml mh zpos hq hφ mid
  change _≤(N:ℝ)/((Z:ℝ)*q*φ) at err
  let D:=den K L
  have hb : ((N:ℝ)*(D*10^16)+91*((D:ℝ)*M)*(Z*q*φ))*10^9 ≤
      (price:ℝ)*((Z*q*φ)*(D*10^16)) := by exact_mod_cast hpr
  have hz : (0:ℝ)<Z := by exact_mod_cast zpos
  have hqn : (0:ℝ)<q := by exact_mod_cast hq
  have hφn : (0:ℝ)<φ := by exact_mod_cast hφ
  have hD : (0:ℝ)<D := dpos
  change |(-A)/(q:ℝ)-1/(φ:ℝ)|+91*(∑ k∈S,|c k|)/(10^16:ℝ)≤(price:ℝ)/(10^9:ℝ)
  calc
    _ ≤ (N:ℝ)/((Z:ℝ)*q*φ)+91*(M:ℝ)/10^16 := by apply add_le_add err;gcongr
    _ ≤ _ := by
      field_simp
      apply le_of_mul_le_mul_left _ hD
      linarith only [hb]
end ThetaScalar
namespace ThetaScalar
open Finset
def divtree (f : ℕ→Vec) : ℕ→ℕ→Vec
  | 0,k=> f k
  | dep+1,k=> divtree f dep k + divtree f dep (k+2^dep)
private theorem divtree_eq (f : ℕ→Vec) (dep k : ℕ) :
    divtree f dep k = ∑ i∈range (2^dep),f (k+i) := by
  induction dep generalizing k with
  | zero=>simp [divtree]
  | succ d ih=>
    rw [divtree,ih,ih,pow_succ,Nat.mul_two,sum_range_add]
    simp [Nat.add_assoc]
def dfold (d depth : ℕ) :=
  divtree (fun j=>if j<20000/d then gvec 20000 12000 signs (d*(j+1)) else 0) depth 0
def eqVec (v z : Vec) : Bool :=
  let (a,b,c,d,e,f,g,h):=v
  let (A,B,C,D,E,F,G,H):=z
  decide (a=A ∧ b=B ∧ c=C ∧ d=D ∧ e=E ∧ f=F ∧ g=G ∧ h=H)
theorem eqVec_spec (v z : Vec) (h : eqVec v z = true) : v=z := by
  obtain ⟨a,b,c,d,e,f,g,i⟩:=v
  obtain ⟨A,B,C,D,E,F,G,I⟩:=z
  simpa only [eqVec,decide_eq_true_eq,Prod.mk.injEq] using h
theorem dfold_eq (d dep : ℕ) (h : 20000/d≤2^dep) :
    dfold d dep = dsum 20000 12000 d signs := by
  rw [dfold,divtree_eq,dsum]
  simp only [zero_add]
  rw [←sum_filter]
  congr
  ext k
  simp [and_iff_right_of_imp (fun (hk : k<20000/d) => lt_of_lt_of_le hk h)]
end ThetaScalar


namespace FR7022Steps
open Finset Real
theorem weighted_error_general (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (T : Finset ℕ) (w : ℕ → ℝ) (e : ℕ → ℝ)
    (hw : ∀ t ∈ T, 0 ≤ w t)
    (ht : ∀ t ∈ T, 0 < t)
    (hy : ∀ t ∈ T, Chebyshev.psi (n/t : ℕ) ≤ C * (↑(n/t):ℝ))
    (he : ∀ d ∈ Ioc 0 n, |e d| ≤ ∑ t ∈ T, if d ≤ n/t then w t else 0) :
    |∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * e d| ≤
      C*(n:ℝ)*∑ t ∈ T, w t/t := by
  calc
    _ ≤ ∑ d ∈ Ioc 0 n, |ArithmeticFunction.vonMangoldt d * e d| := abs_sum_le_sum_abs ..
    _ ≤ ∑ d ∈ Ioc 0 n, ∑ t ∈ T,
        if d ≤ n/t then ArithmeticFunction.vonMangoldt d * w t else 0 := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      refine (mul_le_mul_of_nonneg_left (he d hd) ArithmeticFunction.vonMangoldt_nonneg).trans_eq ?_
      rw [mul_sum]
      apply sum_congr rfl
      intro t _
      split <;> simp_all
    _ = ∑ t ∈ T, Chebyshev.psi (n/t : ℕ) * w t := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      rw [← sum_filter, ← sum_mul, Chebyshev.psi, Nat.floor_natCast]
      congr 2
      ext d
      simp only [mem_filter,mem_Ioc]
      have := Nat.div_le_self n t
      omega
    _ ≤ ∑ t ∈ T, (C*(n:ℝ)) * (w t/t) := by
      apply sum_le_sum
      intro t ts
      have pos : 0 < (t:ℝ) := by exact_mod_cast ht t ts
      have u := mul_le_mul_of_nonneg_right (hy t ts) (hw t ts)
      have v : (↑(n/t):ℝ) * t ≤ n := by exact_mod_cast Nat.div_mul_le_self n t
      have z := mul_le_mul_of_nonneg_right v (hw t ts)
      rw [← mul_div_assoc]
      apply (le_div_iff₀ pos).mpr
      nlinarith only [mul_le_mul_of_nonneg_right u pos.le, mul_le_mul_of_nonneg_left z hC]
    _ = _ := by rw [mul_sum]
end FR7022Steps
namespace FR7022Dirichlet
open Finset ArithmeticFunction FR7022ProgressionTail GoldbachResidueLog
theorem effective_error_general (C : ℝ) (hC : 0 ≤ C) (n q a : ℕ) (hq : 0 < q) (ha : a.Coprime q)
    (S : Finset ℕ) (A : ArithmeticFunction ℝ) (hs : ∀ k ∉ S, A k = 0)
    (T : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ t ∈ T, 0 ≤ w t) (ht : ∀ t ∈ T, 0 < t) (hy : ∀ t ∈ T, Chebyshev.psi (n/t : ℕ) ≤ C * (↑(n/t):ℝ))
    (he : ∀ r u : ℕ, 0 < u → r.Coprime q →
      |G S A q r u - (if r % q=1 % q then (1:ℝ) else 0)| ≤
      ∑ t ∈ T, if t ≤ u then w t else 0) :
    |(∑ k ∈ Icc 1 n, A k * ∑ d ∈ Icc 1 (n/k), if d*k % q=a % q then Real.log d else 0) -
      ∑ p ∈ Icc 1 n, vonMangoldt p * (if p % q=a % q then 1 else 0)| ≤
      C*(n:ℝ)*∑ t ∈ T, w t/t := by
  rw [expand, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  have eqset : Icc 1 n = Ioc 0 n := by ext j; simp only [mem_Icc, mem_Ioc]; omega
  rw [eqset]
  apply FR7022Steps.weighted_error_general C hC n T w _ hw ht hy
  intro p hp0
  have hpos := (mem_Ioc.mp hp0).1
  by_cases hp : p.Coprime q
  · obtain ⟨r, _, hr⟩ := Nat.exists_mul_mod_eq_of_coprime a hp hq.ne'
    have hr' : r*p ≡ a [MOD q] := by change r*p % q=a % q; rwa [Nat.mul_comm]
    have er := eq_select q a p r hp hr'
    simp_rw [er, kernel_eq _ _ _ S A hs]
    have e1 : (r % q=1 % q) ↔ p % q=a % q := by simpa [eq_comm] using (er 1).symm
    have hrc : r.Coprime q := by
      have hrcp : (r*p).Coprime q := by
        change Nat.gcd (r*p) q = 1
        rw [Nat.gcd_comm (r*p) q, Nat.gcd_rec q (r*p), (show r*p % q=a % q from hr'),
          ← Nat.gcd_rec q a, Nat.gcd_comm]
        exact ha
      exact (Nat.coprime_mul_iff_left.mp hrcp).1
    have e := he r (n/p) (Nat.div_pos (mem_Ioc.mp hp0).2 hpos) hrc
    simp only [e1] at e
    refine e.trans_eq (sum_congr rfl (fun t h => ?_))
    have b : t ≤ n/p ↔ p ≤ n/t := by
      rw [Nat.le_div_iff_mul_le hpos, Nat.le_div_iff_mul_le (ht t h), Nat.mul_comm]
    simp only [b]
  · have ex := not_select q a p ha hp
    have e1 : p % q ≠ a % q := by simpa using ex 1
    simp only [ex, e1, ite_false, sum_const_zero, sub_zero, abs_zero]
    apply sum_nonneg
    intro t h
    split <;> simp_all
theorem bound_of_steps (C ε : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 0 < N) (n q a : ℕ) (hq : 0 < q) (ha : a.Coprime q)
    (hn : N ≤ n) (hu : (n:ℝ) < Real.exp (Real.exp (19/5)))
    (S : Finset ℕ) (A : ArithmeticFunction ℝ) (hs : ∀ k ∉ S, A k = 0)
    (hS : ∀ k ∈ S, 0 < k ∧ k ≤ N) (hc : ∀ k ∈ S, k.Coprime q)
    (hz : ∑ k ∈ S, A k / k = 0)
    (T : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t)
    (ht : ∀ t ∈ T, 0 < t)
    (hψ : ∀ t ∈ T, Chebyshev.psi (n/t : ℕ) ≤ C * (↑(n/t):ℝ))
    (he : ∀ r u : ℕ, 0 < u → r.Coprime q →
      |G S A q r u - (if r % q=1 % q then (1:ℝ) else 0)| ≤ ∑ t ∈ T, if t ≤ u then w t else 0)
    (budget : C*(∑ t ∈ T, w t/t) +
      |-(∑ k ∈ S, A k * Real.log k / k)/(q:ℝ) - 1/(q.totient:ℝ)| +
      91*(∑ k ∈ S, |A k|)/N ≤ ε) :
    |(∑ k ∈ (range (n+1)).filter (fun k => k % q = a % q), vonMangoldt k) -
      (n:ℝ)/q.totient| ≤ (n:ℝ)*ε := by
  have sp := fun k hk => And.intro (hS k hk).1 ((hS k hk).2.trans hn)
  have e := effective_error_general C hC n q a hq ha S A hs T w hw ht hψ he
  rw [suffices_for_main n q a hq S A hs sp hc] at e
  let Fsum := ∑ k ∈ S, A k * F q (FR7022Mertens.residue q a k) (n/k)
  let M := ∑ k ∈ S, A k * Real.log k/k
  let V := ∑ k ∈ S, |A k|
  let P := ∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), vonMangoldt k
  have same : (∑ p ∈ Icc 1 n, vonMangoldt p * (if p % q=a % q then (1:ℝ) else 0)) = P := by
    dsimp only [P]
    rw [sum_filter, ← split_zero_one, sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero,ite_self,zero_add]
    apply sum_congr rfl
    intro k _
    split <;> simp_all
  rw [same] at e
  change |Fsum-P| ≤ _ at e
  have z := weighted_main_error_91 q n hq S A (FR7022Mertens.residue q a) sp hz hu
  change |Fsum - (-(n:ℝ)/q)*M| ≤ 91*V at z
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hV : 0 ≤ V := sum_nonneg (fun k _ => abs_nonneg _)
  have qcost := mul_le_mul_of_nonneg_left budget (Nat.cast_nonneg n)
  change _ * (C*(∑ t ∈ T, w t/t) + |(-M)/(q:ℝ) - 1/(q.totient:ℝ)| + 91*V/N) ≤ _ at qcost
  have err := abs_sub_le P Fsum ((-(n:ℝ)/q)*M)
  have err' := abs_sub_le P ((-(n:ℝ)/q)*M) ((n:ℝ)/q.totient)
  rw [abs_sub_comm P Fsum] at err
  have eqm : (-(n:ℝ)/q)*M - n/q.totient = n * (-M/(q:ℝ)-1/(q.totient:ℝ)) := by ring
  rw [eqm,abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)] at err'
  change |P - (n:ℝ)/q.totient| ≤ _
  have hp : (0:ℝ) < N := by exact_mod_cast hN
  have hh : 91*V ≤ (n:ℝ)*(91*V/N) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hn' hV]
  nlinarith only [qcost, err, err', z, e, hh]
end FR7022Dirichlet

/- Odd-modulus lifting from CATLILIZHOU/PR #2645 and PR #2649, Apache-2.0. -/
namespace FR7022OddModuli
open Finset
noncomputable def psi (q a n : ℕ) : ℝ :=
  ∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k
def oddLift (q a : ℕ) : ℕ := if a % 2=1 then a else a+q
theorem lift_data {a q : ℕ} (hq : Odd q) (ha : a.Coprime q) :
    oddLift q a % 2 = 1 ∧ oddLift q a % q = a % q ∧ (oddLift q a).Coprime (2*q) := by
  have hq2 : q % 2=1 := by obtain ⟨u,hu⟩ := hq; omega
  have oddB : oddLift q a % 2 = 1 := by unfold oddLift; split_ifs <;> omega
  have cls : oddLift q a % q = a % q := by unfold oddLift; split_ifs <;> simp
  have cb : (oddLift q a).Coprime q := by
    unfold oddLift
    split_ifs
    · exact ha
    · exact Nat.coprime_add_self_left.mpr ha
  refine ⟨oddB,cls,Nat.coprime_mul_iff_right.mpr ⟨Nat.coprime_two_right.mpr ?_,cb⟩⟩
  exact ⟨oddLift q a / 2, by omega⟩
theorem even_mass (q a n : ℕ) (hn : 0<n) :
    (∑ k ∈ (range (n+1)).filter (fun k => k % 2=0 ∧ k % q=a % q), ArithmeticFunction.vonMangoldt k)
      ≤ Real.log n := by
  classical
  let E := (range (n+1)).filter (fun k => k % 2=0 ∧ k % q=a % q)
  let D := (2:ℕ)^Nat.log 2 n
  have incl : E.filter IsPrimePow ⊆ D.divisors := by
    intro k hk
    obtain ⟨hkE,hp⟩ := mem_filter.mp hk
    obtain ⟨hkn,he,_⟩ := mem_filter.mp hkE
    have hle : k≤n := by simpa only [mem_range,Nat.lt_succ_iff] using hkn
    obtain ⟨p,j,pp,_,rfl⟩ := (isPrimePow_nat_iff k).mp hp
    have hp2 : 2=p := Nat.prime_eq_prime_of_dvd_pow Nat.prime_two pp (Nat.dvd_of_mod_eq_zero he)
    subst p
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow 2 (Nat.le_log_of_pow_le (by decide) hle),
       pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)⟩
  change (∑ k ∈ E, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ E.filter IsPrimePow, ArithmeticFunction.vonMangoldt k := by
      conv_rhs => rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hp : IsPrimePow k
      · simp [hp]
      · simp [hp,ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
    _ ≤ ∑ k ∈ D.divisors, ArithmeticFunction.vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg incl (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log D := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast (pow_pos (by decide : 0<(2:ℕ)) _))
         (by exact_mod_cast Nat.pow_log_le_self 2 hn.ne')
theorem odd_lift_error (q a n : ℕ) (hq : Odd q) (ha : a.Coprime q) (hn : 0<n) :
    |psi q a n - psi (2*q) (oddLift q a) n| ≤ Real.log n := by
  classical
  let b := oddLift q a
  obtain ⟨hp,hr,_⟩ := lift_data hq ha
  have co : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq
  have cls (k : ℕ) : k % (2*q)=b % (2*q) ↔ k % 2=1 ∧ k % q=a % q := by
    change (k ≡ b [MOD 2*q]) ↔ _
    rw [←Nat.modEq_and_modEq_iff_modEq_mul co]
    change (k % 2=b % 2 ∧ k % q=b % q) ↔ _
    change b % 2=1 at hp
    change b % q=a % q at hr
    rw [hp,hr]
  let extra := ∑ k ∈ (range (n+1)).filter (fun k => k % 2=0 ∧ k % q=a % q),
    ArithmeticFunction.vonMangoldt k
  have split : psi q a n = psi (2*q) b n + extra := by
    simp only [psi,extra,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro k _
    simp only [cls k]
    rcases (show k % 2=0 ∨ k % 2=1 by omega) with h | h <;> by_cases r : k % q=a % q <;> simp [h,r]
  change |psi q a n-psi (2*q) b n| ≤ _
  rw [split,add_sub_cancel_left,abs_of_nonneg (show 0≤extra from sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))]
  exact even_mass q a n hn
end FR7022OddModuli




namespace SmallModulusTheta
open Finset Real FR7022OddModuli
open ArithmeticFunction

noncomputable def primeWeight (k : ℕ) : ℝ :=
  if k.Prime then vonMangoldt k else 0

private theorem primeWeight_le (k : ℕ) : primeWeight k ≤ vonMangoldt k := by
  unfold primeWeight
  split <;> simp [vonMangoldt_nonneg]

private theorem full_prime (n : ℕ) :
    ∑ k ∈ range (n+1), primeWeight k = Chebyshev.theta n := by
  have hs : range (n+1) = insert 0 (Ioc 0 n) := by ext k; simp
  rw [hs,sum_insert (by simp),Chebyshev.theta,Nat.floor_natCast, sum_filter]
  simp only [primeWeight,Nat.not_prime_zero,ite_false,zero_add]
  refine sum_congr rfl fun k _ => ?_
  split_ifs with h
  · exact vonMangoldt_apply_prime h
  · rfl

private theorem full_mass (n : ℕ) : ∑ k ∈ range (n+1), vonMangoldt k = Chebyshev.psi n := by
  have hs : range (n+1) = insert 0 (Ioc 0 n) := by ext k; simp
  rw [hs,sum_insert (by simp),Chebyshev.psi,Nat.floor_natCast]
  simp

private theorem prime_part_error (q a n : ℕ) (hn : 1≤n) :
    |psi q a n - ∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), primeWeight k| ≤
    2 * Real.sqrt n * Real.log n := by
  let T := (range (n+1)).filter (fun k => k % q=a % q)
  let err := fun k:ℕ => vonMangoldt k-primeWeight k
  have hnon (k : ℕ) : 0≤err k := sub_nonneg.mpr (primeWeight_le k)
  change |(∑ k∈T,vonMangoldt k) - ∑ k∈T,primeWeight k| ≤ _
  rw [← sum_sub_distrib,abs_of_nonneg (sum_nonneg (fun k _ => hnon k))]
  calc
    _ ≤ ∑ k∈range (n+1),err k := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun k _ _ => hnon k)
    _ = Chebyshev.psi n - Chebyshev.theta n := by rw [←full_prime,←full_mass,←sum_sub_distrib]
    _ ≤ _ := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hn))

theorem theta_half_of_active
    (input : ∀ q a n : ℕ, 1≤q → q≤105 → (Even q ∨ 51<q) → a.Coprime q →
      10^16≤n → (n:ℝ)<Real.exp (Real.exp (19/5)) →
      |psi q a n-(n:ℝ)/q.totient| ≤ (49/10000:ℝ)*n) :
    ∀ q a n : ℕ, 1≤q → q≤105 → a.Coprime q → 10^16≤n →
      (n:ℝ)<Real.exp (Real.exp (19/5)) →
      |(∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), primeWeight k) -
        (n:ℝ)/q.totient| ≤ (n:ℝ)/200 := by
  intro q a n hq hQ ha hn hu
  have hn' : (10:ℝ)^16≤n := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := by linarith
  have hlog : Real.log n ≤ 81 := by
    apply ((Real.log_lt_iff_lt_exp hn0).mpr hu).le.trans
    calc
      Real.exp (19/5) ≤ Real.exp ((4:ℕ)*1) := Real.exp_le_exp.mpr (by norm_num)
      _ = Real.exp 1 ^ 4 := Real.exp_nat_mul 1 4
      _ ≤ (3:ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
      _ = 81 := by norm_num
  have hpsi : |psi q a n-(n:ℝ)/q.totient| ≤ (49/10000:ℝ)*n + Real.log n := by
    by_cases active : Even q ∨ 51<q
    · exact le_add_of_le_of_nonneg (input q a n hq hQ active ha hn hu) (Real.log_nonneg (by linarith))
    have ho : Odd q := (Nat.even_or_odd q).resolve_left (fun h => active (Or.inl h))
    have hsmall : q≤51 := le_of_not_gt (fun h => active (Or.inr h))
    have hl := input (2*q) (oddLift q a) n (by omega) (by omega)
      (Or.inl ⟨q,by omega⟩) (lift_data ho ha).2.2 hn hu
    rw [Nat.totient_two_mul_of_odd ho] at hl
    have hz := odd_lift_error q a n ho ha (by omega)
    exact (abs_sub_le _ (psi (2*q) (oddLift q a) n) _).trans (by linarith)
  let θq := ∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q),primeWeight k
  have herr : |θq - psi q a n| ≤ 2*Real.sqrt n*Real.log n := by
    rw [abs_sub_comm]; exact prime_part_error q a n (by omega)
  have hs : (10^8:ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) hn0.le).mpr (by linarith)
  have hs2 := Real.sq_sqrt hn0.le
  have h1 := mul_le_mul_of_nonneg_left hlog (show 0≤2*Real.sqrt n by positivity)
  have h2 := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n:ℝ))
  exact (abs_sub_le θq (psi q a n) ((n:ℝ)/q.totient)).trans (by nlinarith only [herr,hpsi,h1,h2,hs2,hn',hlog])

end SmallModulusTheta

namespace SmallModulusSteps
open Finset FR7022Lane FR7022NextRows
def ceilRatio (n d : ℕ) := (n+d-1)/d
theorem ceilRatio_mul (n d : ℕ) (hd : 0 < d) : n ≤ ceilRatio n d * d := by
  unfold ceilRatio
  have h := Nat.div_add_mod (n+d-1) d
  rw [Nat.mul_comm d] at h
  have hr := Nat.mod_lt (n+d-1) hd
  omega
theorem per_jump_cost (v W D b : ℕ) (hW : 0 < W) (hD : 0 < D) (hb : 0 < b) :
    ((v:ℝ)/D)/b ≤ (ceilRatio (v*W) (D*b):ℝ)/W := by
  have hc := ceilRatio_mul (v*W) (D*b) (Nat.mul_pos hD hb)
  have hc' : (v:ℝ)*W ≤ (ceilRatio (v*W) (D*b):ℝ) * ((D:ℝ)*b) := by exact_mod_cast hc
  have pW : (0:ℝ)<W := by exact_mod_cast hW
  have pD : (0:ℝ)<D := by exact_mod_cast hD
  have pb : (0:ℝ)<b := by exact_mod_cast hb
  rw [div_div]
  exact (div_le_div_iff₀ (mul_pos pD pb) pW).mpr hc'
abbrev last : ℕ := 3000001
def thresholds : Finset ℕ := Icc 1 last
noncomputable def weights (D : ℕ) (xs : List (ℕ×ℕ)) (t : ℕ) : ℝ :=
  match xs with
  | [] => 0
  | p::rest => (if p.1+1=t then (p.2:ℝ)/D else 0)+weights D rest t
theorem weight_nonneg (D : ℕ) (xs : List (ℕ×ℕ)) (t : ℕ) : 0≤weights D xs t := by
  induction xs with
  | nil => simp [weights]
  | cons p tail ih =>
    simp only [weights]
    exact add_nonneg (by split <;> positivity) ih
theorem unroll (D : ℕ) (xs : List (ℕ×ℕ)) (v : ℕ → ℝ)
    (hb : ∀ p ∈ xs, p.1<last) :
    ∑ t ∈ thresholds, weights D xs t*v t =
      (xs.map (fun p => (p.2:ℝ)/D*v (p.1+1))).sum := by
  induction xs with
  | nil => simp [weights]
  | cons p tail ih =>
    have hr : p.1+1 ∈ thresholds := mem_Icc.mpr ⟨by omega,by have := hb p (by simp); omega⟩
    have h : (∑ t ∈ thresholds, (if p.1+1=t then (p.2:ℝ)/D else 0)*v t) =
        (p.2:ℝ)/D*v (p.1+1) := by
      rw [sum_eq_single (p.1+1)]
      · simp
      · intro s _ ne
        simp [Ne.symm ne]
      · exact fun hh => (hh hr).elim
    simp only [weights,List.map_cons,List.sum_cons,add_mul,sum_add_distrib]
    rw [h, ih (fun z hz => hb z (by simp [hz]))]
theorem realized (D : ℕ) (xs : List (ℕ×ℕ)) (u : ℕ) (hu : 0<u)
    (hb : ∀ p ∈ xs, p.1<last) :
    (∑ t ∈ thresholds, if t≤u then weights D xs t else 0) =
        (fromRises xs (u-1):ℝ)/D := by
  have eq := unroll D xs (fun t => if t≤u then 1 else 0) hb
  simp only [mul_ite,mul_one,mul_zero] at eq
  rw [eq]
  clear hb eq
  induction xs with
  | nil => simp [fromRises]
  | cons p tail ih =>
    change (if p.1+1≤u then (p.2:ℝ)/D else 0) + (tail.map (fun z => if z.1+1≤u then (z.2:ℝ)/D else 0)).sum =
      ((ray p.1 p.2 (u-1) + fromRises tail (u-1):ℕ):ℝ)/D
    rw [ih,Nat.cast_add,add_div]
    by_cases h:p.1+1≤u
    · simp [h,ray,show p.1≤u-1 by omega]
    · simp [h,ray,show ¬p.1≤u-1 by omega]
theorem full_value (xs : List (ℕ×ℕ)) (i : ℕ) (h : ∀ p∈xs, p.1 ≤ i) :
    fromRises xs i = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    change ray p.1 p.2 i + fromRises rest i = p.2+(rest.map Prod.snd).sum
    simp only [ray,ite_eq_left (h p (by simp)),ih (fun z hz => h z (by simp [hz]))]
end SmallModulusSteps

/- The factorial expansion and elementary psi bound adapt the arguments of
SmallModulusCheb and the Apache-2.0 Goldbach proofs, PRs 2645 by CATLILIZHOU
and 2649 by nanzhiyan1. The period-1260 coefficients and certificate are new. -/
namespace SmallModulus106
open Finset Real ArithmeticFunction GoldbachResidueLog
open scoped ArithmeticFunction.zeta

def S : Finset ℕ := [1,2,3,5,6,7,10,12,14,15,18,20,21,28,30,35,36,42,45,60,63,70,84,90,105,126,180,210,252,315,420,1260].toFinset
def a : ℕ → ℤ
  | 1 => 2
  | 2 => -2
  | 3 => -2
  | 5 => -2
  | 6 => 2
  | 7 => -2
  | 10 => 2
  | 12 => -2
  | 14 => 1
  | 15 => 1
  | 18 => -2
  | 20 => -1
  | 21 => 1
  | 28 => 1
  | 30 => -3
  | 35 => 1
  | 36 => 3
  | 42 => -3
  | 45 => -1
  | 60 => 3
  | 63 => -1
  | 70 => -2
  | 84 => 1
  | 90 => 3
  | 105 => -3
  | 126 => 1
  | 180 => -4
  | 210 => 4
  | 252 => -2
  | 315 => -2
  | 420 => -1
  | 1260 => -4
  | _ => 0
def K (t : ℕ) : ℤ := ∑ d∈S, a d*(t/d:ℕ)
def w (d : ℕ) : ℤ := a d*(1260/d:ℕ)
noncomputable def C (d : ℕ) : ℝ := (a d:ℝ)/2
noncomputable def V (n : ℕ) : ℝ := ∑ d∈S,C d*F 1 0 (n/d)

theorem supportD : ∀ d∈S, 0<d ∧ d∣1260 ∧ d≤1260 := by decide +kernel
theorem slopeD : ∑ d∈S,w d = 0 := by decide +kernel
theorem weightsD : ∑ d∈S,(a d).natAbs ≤ 200 := by decide +kernel
theorem momentD : 10000*(∑ d∈S,ThetaScalar.signedHigh (-w d) (ThetaScalar.gl d) (ThetaScalar.gh d)) ≤
    (10584:ℤ)*2520*ThetaScalar.logScale := by decide +kernel

theorem periodic (t:ℕ) : K (t+1260)=K t := by
  unfold K
  have he (d : ℕ) (hd : d∈S) : a d * (((t+1260)/d:ℕ):ℤ) =
      a d*(t/d:ℕ)+w d := by
    rw [Nat.add_div_of_dvd_left (supportD d hd).2.1]
    simp [w,mul_add]
  rw [sum_congr rfl he,sum_add_distrib,slopeD,add_zero]

theorem onPeriod : ∀ i : Fin 1260, (if i.val=0 then (0:ℤ) else 2) ≤ K i.val := by
  decide +kernel

theorem boundsK (t:ℕ) : 0≤K t ∧ (0<t → t<1260 → 2≤K t) := by
  have ex (u : ℕ) : K u=K (u % 1260) := by
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      by_cases h : u<1260
      · rw [Nat.mod_eq_of_lt h]
      · calc
          _ = K (u-1260+1260) := by rw [Nat.sub_add_cancel (by omega)]
          _ = K (u-1260) := periodic _
          _ = K ((u-1260) % 1260) := ih _ (by omega)
          _ = _ := congrArg K (by omega : (u-1260) % 1260=u % 1260)
  have hh : (if t % 1260=0 then (0:ℤ) else 2)≤K (t % 1260) := onPeriod ⟨t % 1260,Nat.mod_lt _ (by decide)⟩
  refine ⟨?_,?_⟩
  · rw [ex];split_ifs at hh <;> omega
  · intro ht hu
    rw [Nat.mod_eq_of_lt hu] at hh
    simpa [ht.ne'] using hh

theorem F_exp (n : ℕ) :
    F 1 0 n = ∑ p ∈ Icc 1 n, vonMangoldt p * (n/p : ℕ) := by
  have hh := FR7022Dirichlet.slice n 1 0 vonMangoldt (ζ : ArithmeticFunction ℝ)
  simp only [Nat.mod_one,ite_true,vonMangoldt_mul_zeta,ArithmeticFunction.log_apply] at hh
  have hpos (p : ℕ) : (∑ d ∈ Icc 1 (n/p), (ζ : ArithmeticFunction ℝ) d) = (n/p:ℕ) := by
    rw [sum_congr rfl (g:=fun _ => (1:ℝ)) (fun d hd => by
      simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply,show d≠0 by have := (mem_Icc.mp hd).1; omega])]
    simp
  simp_rw [hpos] at hh
  rw [←hh]
  have hs : range (n+1)=insert 0 (Icc 1 n) := by ext i; simp; omega
  simp [F, hs, Nat.mod_one, Finset.sum_filter]

theorem F_scaled (n k : ℕ) :
    F 1 0 (n/k) = ∑ p ∈ Icc 1 n,vonMangoldt p * ((n/p/k : ℕ):ℝ) := by
  rw [F_exp]
  have eqdiv (p : ℕ) : n/k/p=n/p/k := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.mul_comm k p]
  simp_rw [eqdiv]
  apply sum_subset (fun p h => mem_Icc.mpr ⟨(mem_Icc.mp h).1,(mem_Icc.mp h).2.trans (Nat.div_le_self ..)⟩)
  intro p hp hno
  have hp' := (mem_Icc.mp hp).1
  have hl : n/k<p := by by_contra! h; exact hno (mem_Icc.mpr ⟨hp',h⟩)
  rw [←eqdiv,Nat.div_eq_of_lt hl,Nat.cast_zero,mul_zero]

theorem raw_psi (x : ℝ) (hx : 360000≤x) : Chebyshev.psi x ≤ (31/20)*x := by
  have hx0 : 0<x := by linarith
  have hs : (600:ℝ) ≤ √x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
  have hs0 := Real.sqrt_pos.mpr hx0
  have sq := Real.sq_sqrt hx0.le
  have hlog : Real.log (600:ℝ) ≤ 10 := by
    have t := Real.log_le_log (by norm_num : (0:ℝ)<600) (by norm_num : (600:ℝ) ≤ 2^10)
    rw [Real.log_pow] at t
    norm_num at t
    linarith [Real.log_two_lt_d9]
  have h := Real.log_le_sub_one_of_pos (show 0<√x/600 by positivity)
  rw [Real.log_div hs0.ne' (by norm_num)] at h
  have hl : Real.log x = 2 * Real.log (√x) := by simpa [sq] using (Real.log_pow (√x) 2)
  have hl' : Real.log x ≤ (20/600)*√x := by linarith
  have h4 : Real.log 4 ≤ 7/5 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hpsi := Chebyshev.psi_le (show 1 ≤ x by linarith)
  have a := mul_le_mul_of_nonneg_left hl' hs0.le
  have b := mul_le_mul_of_nonneg_right h4 hx0.le
  nlinarith only [hpsi,a,b,sq,hx0]

end SmallModulus106
namespace SmallModulus106
open Finset Real ArithmeticFunction GoldbachResidueLog
open scoped ArithmeticFunction.zeta

private theorem scale (d:ℕ) (hd:d∈S) : (2520:ℝ)*(C d/(d:ℝ))=(w d:ℝ) := by
  obtain ⟨hpos,hdiv,_⟩:=supportD d hd
  have h := Nat.div_mul_cancel hdiv
  have he : ((1260/d:ℕ):ℝ)*(d:ℝ)=1260 := by exact_mod_cast h
  have hr : (0:ℝ)<d := by exact_mod_cast hpos
  have fr : ((1260/d:ℕ):ℝ)=1260/(d:ℝ) := (eq_div_iff hr.ne').mpr he
  simp only [C,w,Int.cast_mul,Int.cast_natCast]
  rw [fr]
  ring

private theorem V_le (n:ℕ) (hn:1260≤n) (hu:(n:ℝ)<Real.exp (Real.exp (19/5))) :
    V n ≤ (10584/10000:ℝ)*n+9100 := by
  have zero : ∑ d∈S,C d/(d:ℝ)=0 := by
    have z : (2520:ℝ)*(∑ d∈S,C d/(d:ℝ))=0 := by
      rw [mul_sum,sum_congr rfl (fun d hd=>scale d hd),←Int.cast_sum,slopeD,Int.cast_zero]
    linarith only [z]
  have err := weighted_main_error_91 1 n (by decide) S C (fun _=>0)
    (fun d hd=>⟨(supportD d hd).1,(supportD d hd).2.2.trans hn⟩) zero hu
  let H:=∑ d∈S, C d*Real.log d/d
  have hs : (2520:ℝ)*(-H)=∑ d∈S,((-w d:ℤ):ℝ)*Real.log d := by
    dsimp only [H]
    rw [←sum_neg_distrib,mul_sum]
    apply sum_congr rfl;intro d hd
    simp only [Int.cast_neg]
    rw [←scale d hd]; ring
  have lm : (2520*ThetaScalar.logScale:ℝ)*(-H) ≤ (10584/10000:ℝ)*2520*ThetaScalar.logScale := by
    calc
      _ = (ThetaScalar.logScale:ℝ)*∑ d∈S,((-w d:ℤ):ℝ)*Real.log d := by rw [←hs];ring
      _ ≤ ∑ d∈S,((ThetaScalar.signedHigh (-w d) (ThetaScalar.gl d) (ThetaScalar.gh d):ℤ):ℝ) := by
        rw [mul_sum]; apply sum_le_sum
        intro d hd
        have hb:= (ThetaScalar.signed_bounds (-w d) (ThetaScalar.gl d) (ThetaScalar.gh d)
          ((ThetaScalar.logScale:ℝ)*Real.log d) (ThetaScalar.fast_log_interval d (supportD d hd).1)).2
        simpa only [mul_left_comm] using hb
      _ ≤ _ := by
        rw [←Int.cast_sum]
        have hh := (Int.cast_le (R:=ℝ)).mpr momentD
        simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] at hh
        norm_num [ThetaScalar.logScale] at hh ⊢
        linarith only [hh]
  have hlog : -H≤(10584/10000:ℝ) := by norm_num [ThetaScalar.logScale] at lm ⊢; linarith only [lm]
  have hb : ∑ d∈S,|C d|≤100 := by
    have he : 2*(∑ d∈S,|C d|)=((∑d∈S,(a d).natAbs:ℕ):ℝ) := by
      rw [mul_sum,Nat.cast_sum]
      apply sum_congr rfl;intro d _
      rw [C,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]
      ring
    have hw : ((∑ d∈S,(a d).natAbs:ℕ):ℝ)≤200 := by exact_mod_cast weightsD
    linarith only [hw,he]
  have ez:=(abs_le.mp err).2
  change V n- (-(n:ℝ)/1)*H≤91*∑ d∈S,|C d| at ez
  linarith only [ez,hb,mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg n : (0:ℝ)≤n)]

private theorem recurrence (n:ℕ) : Chebyshev.psi n≤V n+Chebyshev.psi (n/1260:ℕ) := by
  have hex : V n=∑ p∈Icc 1 n,vonMangoldt p*((K (n/p):ℝ)/2) := by
    unfold V
    simp only [F_scaled,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl;intro p hp
    unfold K
    rw [Int.cast_sum,sum_div,mul_sum]
    apply sum_congr rfl;intro d hd
    simp only [C,Int.cast_mul,Int.cast_natCast]; ring
  have hpsi (t:ℕ) : Chebyshev.psi t=∑p∈Icc 1 t,vonMangoldt p := by
    unfold Chebyshev.psi;rw [Nat.floor_natCast];rfl
  have sub : (∑p∈Icc 1 (n/1260),vonMangoldt p)=
      ∑p∈Icc 1 n,if p≤n/1260 then vonMangoldt p else 0 := by
    rw [←sum_filter];congr 1;ext p;simp;omega
  rw [hex,hpsi,hpsi,sub,←sum_add_distrib]
  apply sum_le_sum;intro p hp
  have pp:=(mem_Icc.mp hp).1
  have hv:=vonMangoldt_nonneg (n:=p)
  have bound:=boundsK (n/p)
  by_cases hl:p≤n/1260
  · rw [if_pos hl]
    have bz : 0≤(K (n/p):ℝ) := by exact_mod_cast bound.1
    linarith only [mul_nonneg hv bz]
  · rw [if_neg hl,add_zero]
    have hq : n/p<1260 := (Nat.div_lt_iff_lt_mul pp).mpr (by
      simpa [Nat.mul_comm] using Nat.lt_mul_of_div_lt (show n/1260<p by omega) (by decide))
    have hz : (2:ℝ)≤K (n/p) := by exact_mod_cast bound.2 (Nat.div_pos (mem_Icc.mp hp).2 pp) hq
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith only [hz] : (1:ℝ)≤(K (n/p):ℝ)/2) hv

theorem psi_le_106 (n : ℕ) (hn : 10^9≤n) (hu : (n:ℝ)<Real.exp (Real.exp (19/5))) :
    Chebyshev.psi n ≤ (106/100:ℝ)*n := by
  have hmin : 360000≤n/1260 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have hb := raw_psi (n/1260:ℕ) (by exact_mod_cast hmin)
  have hc : ((n/1260:ℕ):ℝ)*1260≤(n:ℝ) := by exact_mod_cast Nat.div_mul_le_self n 1260
  have hn' : (10:ℝ)^9≤n := by exact_mod_cast hn
  linarith only [recurrence n,V_le n (by omega) hu,hb,hc,hn']
end SmallModulus106

namespace SmallModulusSteps
open Finset FR7022Lane FR7022NextRows FR7022ProgressionTail ThetaScalar

def allEdges (r : Row) := (3000000,r.cap-((envelope r).map Prod.snd).sum)::envelope r

theorem edge_lt (r : Row) (hr : r∈FR7022NextRows.rows) {x : ℕ×ℕ} (hx : x∈allEdges r) : x.1 < last := by
  have h := (row_costs r hr).2.2.2
  rcases List.mem_cons.mp hx with hx|hx
  · subst x; exact (by decide : 3000000<3000001)
  · exact (h x hx).trans (by decide)

theorem combined (r : Row) (hr : r∈FR7022NextRows.rows) (err : ℕ→ℝ)
    (hfin : ∀ u,0<u → u≤3000000 → err u≤(fromRises (envelope r) (u-1):ℝ)/8000000)
    (htail : ∀u, err u≤(r.cap:ℝ)/8000000) (u : ℕ) (hu : 0<u) :
    err u ≤ ∑ t∈thresholds, if t≤u then weights 8000000 (allEdges r) t else 0 := by
  rw [realized _ _ u hu (fun _ hx => edge_lt r hr hx)]
  by_cases small : u≤3000000
  · have before : ¬3000000≤u-1 := by omega
    simpa [allEdges,fromRises,ray,before] using hfin u hu small
  · have hfull := full_value (allEdges r) (u-1) (by
      intro p hp; have h:=edge_lt r hr hp; change p.1<3000001 at h; omega)
    rw [hfull]
    have right := (row_costs r hr).2.1
    simpa [allEdges,Nat.sub_add_cancel right] using htail u

private theorem fee_le (p : ℕ×ℕ) :
    (p.2:ℝ)/8000000 * ((p.1+1:ℕ):ℝ)⁻¹ ≤ (fee 8000000 p:ℝ)/1000000000000 := by
  have hp : 0<8000000*(p.1+1) := by positivity
  have e : ceilRatio (p.2*1000000000000) (8000000*(p.1+1)) = fee 8000000 p := by
    unfold ceilRatio fee
    congr 1
  simpa only [←div_eq_mul_inv,Nat.cast_ofNat,e] using
    per_jump_cost p.2 1000000000000 8000000 (p.1+1) (by decide) (by decide) (by omega)

private theorem priced (xs : List (ℕ×ℕ)) :
    (xs.map (fun p => (p.2:ℝ)/8000000 * ((p.1+1:ℕ):ℝ)⁻¹)).sum ≤
    (((xs.map (fee 8000000)).sum:ℕ):ℝ)/1000000000000 := by
  induction xs with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div]
    simpa only [Nat.cast_add] using add_le_add (fee_le p) ih

theorem total_cost (r : Row) (hr : r∈FR7022NextRows.rows) :
    (∑ t∈thresholds, weights 8000000 (allEdges r) t/t) ≤
      (((r.finiteCost+r.tailCost:ℕ):ℝ)/1000000000000) := by
  have z := row_costs r hr
  have eqn : ((allEdges r).map (fee 8000000)).sum = r.finiteCost+r.tailCost := by
    simp only [allEdges,List.map_cons,List.sum_cons,z.1,z.2.2.1,Nat.add_comm]
  have u := unroll 8000000 (allEdges r) (fun t => (t:ℝ)⁻¹) (fun _ hx => edge_lt r hr hx)
  calc
    _ = ((allEdges r).map (fun p => (p.2:ℝ)/8000000 * ((p.1+1:ℕ):ℝ)⁻¹)).sum := by
      simpa only [div_eq_mul_inv,Nat.cast_ofNat] using u
    _ ≤ _ := eqn ▸ priced (allEdges r)

abbrev rsupp (r : Row) := support 20000 r.q
noncomputable abbrev cf (r : Row) := co 20000 12000 r.q signs

theorem restrict_sum (q h t : ℕ) (hh : h.Coprime q) (f : ℕ→ℤ) :
    (∑ k∈support 20000 q,(count q h t k:ℤ)*f k) =
    ∑ k∈Icc 1 20000,(count q h t k:ℤ)*f k := by
  apply sum_subset (filter_subset _ _)
  intro k hk hn
  have h : ¬k.Coprime q := fun hc => hn (mem_filter.mpr ⟨hk,hc⟩)
  rw [FR7022FiniteCount.count_nonunit _ _ _ _ hh h,Nat.cast_zero,zero_mul]

def EndpointBound (r : Row) (a : ℤ) : Prop :=
  ∀ t, 0<t → t≤3000000 → ∀ h, h.Coprime r.q →
    |(∑ k∈Icc 1 20000,(count r.q h t k:ℤ)*weight 20000 12000 signs a k)-
      (if 1 % r.q=h % r.q then (8000000:ℤ) else 0)| ≤ (fromRises (envelope r) (t-1):ℤ)

theorem finite_real (r : Row)
    (ha : (r.lo:ℝ)/1000 ≤ alpha 20000 12000 r.q signs ∧ alpha 20000 12000 r.q signs ≤ (r.hi:ℝ)/1000)
    (cl : EndpointBound r r.lo) (ch : EndpointBound r r.hi)
    (t h : ℕ) (ht : 0<t) (hT : t≤3000000) (hu : h.Coprime r.q) :
    |G (rsupp r) (cf r) r.q h t - (if h % r.q=1 % r.q then (1:ℝ) else 0)| ≤
      (fromRises (envelope r) (t-1):ℝ)/8000000 := by
  let z : ℤ := if 1 % r.q=h % r.q then 8000000 else 0
  let v (a : ℤ) := ∑ k∈rsupp r,(count r.q h t k:ℤ)*weight 20000 12000 signs a k
  let E := fromRises (envelope r) (t-1)
  let main := G (rsupp r) (cf r) r.q h t
  have bound (a : ℤ) (H : EndpointBound r a) : |v a-z|≤(E:ℤ) := by
    simpa only [v,z,rsupp,restrict_sum r.q h t hu,E] using H t ht hT h hu
  have lr : -(E:ℝ) ≤ (v r.lo:ℝ)-(z:ℝ) := by exact_mod_cast (abs_le.mp (bound _ cl)).1
  have ur : (v r.hi:ℝ)-(z:ℝ) ≤ E := by exact_mod_cast (abs_le.mp (bound _ ch)).2
  have eqn : 8000000*main = ∑ k∈rsupp r,(count r.q h t k:ℝ)*(8000000*cf r k) := by
    dsimp only [main,G]; rw [mul_sum]; apply sum_congr rfl; intro k _; ring
  have boundc (k : ℕ) : (weight 20000 12000 signs r.lo k:ℝ) ≤ 8000000*cf r k ∧
      8000000*cf r k ≤ (weight 20000 12000 signs r.hi k:ℝ) :=
    coeff_in _ _ _ _ _ _ (by decide) ha k
  have vlo : (v r.lo:ℝ) ≤ 8000000*main := by
    rw [eqn]; dsimp only [v]; push_cast
    exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (boundc k).1 (by positivity))
  have vhi : 8000000*main ≤ (v r.hi:ℝ) := by
    rw [eqn]; dsimp only [v]; push_cast
    exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (boundc k).2 (by positivity))
  let target : ℝ := if h % r.q=1 % r.q then 1 else 0
  have z_eq : (z:ℝ)=8000000*target := by
    dsimp only [z,target]
    by_cases hh : 1 % r.q=h % r.q
    · rw [ite_eq_left hh,ite_eq_left hh.symm]; norm_num
    · rw [ite_eq_right hh,ite_eq_right (Ne.symm hh)]; norm_num
  change |main-target|≤(E:ℝ)/8000000
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<8000000)).mpr
  rw [show (8000000:ℝ)=|8000000| by norm_num,←abs_mul,abs_le]
  rw [z_eq] at lr ur
  constructor <;> linarith

end SmallModulusSteps

namespace SmallModulusSteps
open Finset Real ArithmeticFunction FR7022NextRows FR7022ProgressionTail ThetaScalar

set_option maxRecDepth 4096 in
private noncomputable def af (r : Row) : ArithmeticFunction ℝ :=
  ⟨fun k => if k∈rsupp r then cf r k else 0, by simp [rsupp,support]⟩

set_option maxRecDepth 4096 in
private theorem inside (r : Row) {k : ℕ} (hk : k∈rsupp r) : af r k=cf r k := if_pos hk
set_option maxRecDepth 4096 in
private theorem outside (r : Row) {k : ℕ} (hk : k∉rsupp r) : af r k=0 := if_neg hk

set_option maxRecDepth 4096 in
def rateOK (r : Row) (b : ℕ) : Prop :=
  106*(r.finiteCost+r.tailCost)+100000*b≤490000000000

set_option maxRecDepth 4096 in
structure Evidence (r : Row) : Prop where
  positive : 0<harm (rsupp r) (bump 12000)
  bracket : (r.lo:ℝ)/1000 ≤ alpha 20000 12000 r.q signs ∧
    alpha 20000 12000 r.q signs ≤ (r.hi:ℝ)/1000
  low : EndpointBound r r.lo
  high : EndpointBound r r.hi
  tail : ∀ h t, |G (rsupp r) (cf r) r.q h t - (if h % r.q=1 % r.q then (1:ℝ) else 0)|≤(r.cap:ℝ)/8000000
  scalar : ∃ b : ℕ, rateOK r b ∧
    |-(∑ k∈rsupp r,cf r k*Real.log k/k)/(r.q:ℝ)-1/(r.q.totient:ℝ)|+
      91*(∑ k∈rsupp r,|cf r k|)/(10^16:ℝ) ≤ b/(10^9:ℝ)

set_option maxRecDepth 4096 in
theorem psi_of_evidence (r : Row) (hr : r∈FR7022NextRows.rows) (e : Evidence r) (n a : ℕ)
    (hq : 0<r.q) (ha : a.Coprime r.q) (hn : 10^16≤n) (hu : (n:ℝ)<exp (exp (19/5))) :
    |FR7022OddModuli.psi r.q a n-(n:ℝ)/r.q.totient| ≤ (49/10000:ℝ)*n := by
  let S := rsupp r
  have s_eq {M : Type} [AddCommMonoid M] (f : ℕ→ℝ→M) :
      (∑ k∈S,f k (af r k))=∑ k∈S,f k (cf r k) :=
    sum_congr rfl fun k hk => by rw [inside r hk]
  have hz : (∑ k∈S,af r k/k)=0 := (s_eq (fun k x => x/k)).trans (slope_zero _ _ _ _ e.positive)
  have hnψ (t : ℕ) (ht : t∈thresholds) : Chebyshev.psi (n/t:ℕ) ≤ (106/100:ℝ)*(n/t:ℕ) := by
    obtain ⟨tp,tt⟩:=mem_Icc.mp ht
    change t≤3000001 at tt
    have cut : 10^9≤n/t := (Nat.le_div_iff_mul_le tp).mpr (by omega)
    exact SmallModulus106.psi_le_106 (n/t) cut (lt_of_le_of_lt (by exact_mod_cast Nat.div_le_self n t) hu)
  have env (h u : ℕ) (hu0 : 0<u) (hh : h.Coprime r.q) :
      |G S (af r) r.q h u-(if h % r.q=1 % r.q then (1:ℝ) else 0)| ≤
        ∑ t∈thresholds,if t≤u then weights 8000000 (allEdges r) t else 0 := by
    have ar : G S (af r) r.q h u = G S (cf r) r.q h u := s_eq (fun k v => v*(count r.q h u k:ℝ))
    rw [ar]
    exact combined r hr _ (fun t ht hT => finite_real r e.bracket e.low e.high t h ht hT hh) (e.tail h) u hu0
  obtain ⟨b,p,z⟩:=e.scalar
  have num : 106*((r.finiteCost:ℝ)+r.tailCost)+100000*(b:ℝ) ≤ 490000000000 := by exact_mod_cast p
  have total := total_cost r hr
  have budget :
      106/100*(∑ t∈thresholds,weights 8000000 (allEdges r) t/t)+
        |-(∑ k∈S,af r k*Real.log k/k)/(r.q:ℝ)-1/(r.q.totient:ℝ)|+
        91*(∑ k∈S,|af r k|)/(10^16:ℝ) ≤ 49/10000 := by
    rw [s_eq (fun k x => x*Real.log k/k),s_eq (fun _ x => |x|)]
    push_cast at total
    dsimp only [S] at *
    linarith only [num,total,z]
  have upper_t (t : ℕ) (ht : t∈thresholds) : 0<t := (mem_Icc.mp ht).1
  have main := FR7022Dirichlet.bound_of_steps (106/100) (49/10000) (by norm_num) (10^16) (by decide)
    n r.q a hq ha hn hu S (af r) (fun _ hk => outside r hk)
    (fun k hk => by have h := mem_Icc.mp (mem_filter.mp hk).1; exact ⟨h.1,by omega⟩)
    (fun k hk => (mem_filter.mp hk).2) hz thresholds (weights 8000000 (allEdges r))
    (fun t _ => weight_nonneg _ _ t) upper_t hnψ env (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using budget)
  simpa only [FR7022OddModuli.psi,mul_comm] using main

set_option maxRecDepth 4096 in
private theorem registered : (List.range 106).all (fun q =>
    !(decide (1≤q ∧ (q % 2=0 ∨ 51<q))) || FR7022NextRows.rows.any (fun r => r.q==q)) = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem theta_of_rows (all : ∀ r∈FR7022NextRows.rows,Evidence r) :
    ∀ q a n : ℕ, 1≤q → q≤105 → a.Coprime q → 10^16≤n →
      (n:ℝ)<Real.exp (Real.exp (19/5)) →
      |(∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), SmallModulusTheta.primeWeight k) -
        (n:ℝ)/q.totient| ≤ (n:ℝ)/200 := by
  apply SmallModulusTheta.theta_half_of_active
  intro q a n hq hQ ha hc hn hu
  have zm : q % 2=0 ∨ 51<q := ha.imp (fun h => Nat.even_iff.mp h) id
  have h:=List.all_eq_true.mp registered q (List.mem_range.mpr (by omega))
  have h' : FR7022NextRows.rows.any (fun r => r.q==q)=true := by simpa [hq,zm] using h
  obtain ⟨r,hr,hqr⟩ := List.any_eq_true.mp h'
  obtain rfl := beq_iff_eq.mp hqr
  exact psi_of_evidence r hr (all r hr) n a (by omega) hc hn hu

end SmallModulusSteps

-- Centered estimates adapted from PRs 2645 and 2649, Apache-2.0.
namespace FR7022ProgressionTail
open Finset
private theorem lt_count_residue_iff {q : ℕ} (hq : 0 < q) (y a j : ℕ) :
    j < countTerms y q a ↔ firstResidue q a + j*q ≤ y := by
  unfold countTerms
  split_ifs with h
  · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hq]
    omega
  · simp; omega
noncomputable def residueCenter (q r : ℕ) : ℝ :=
  1 / 2 - (firstResidue q r : ℝ)/q
theorem count_of_residue (q h t k r : ℕ) (hq : 0 < q) (hc : k.Coprime q)
    (hr : r*k ≡ h [MOD q]) : count q h t k = countTerms (t/k) q r := by
  rw [← class_card q r (t/k) hq]
  unfold count
  congr 1
  ext m
  have iff : (m*k ≡ h [MOD q]) ↔ m ≡ r [MOD q] :=
    ⟨fun hm => Nat.ModEq.cancel_right_of_coprime hc.symm (hm.trans hr.symm),
     fun hm => (hm.mul_right k).trans hr⟩
  simpa only [mem_filter, Nat.ModEq] using (and_congr_right fun _ => iff)
theorem count_centered (q h t k r : ℕ) (hq : 0 < q) (hk : 0 < k)
    (hc : k.Coprime q) (hr : r*k ≡ h [MOD q]) :
    |(count q h t k : ℝ) - (t:ℝ)/((k:ℝ)*q) - residueCenter q r| ≤ 1/2 := by
  rw [count_of_residue q h t k r hq hc hr]
  let C := countTerms (t/k) q r
  let R := firstResidue q r
  have hR : R ≤ q := by unfold R firstResidue; split_ifs; exact le_rfl; exact (Nat.mod_lt _ hq).le
  have lower : t ≤ (R+C*q)*k := by
    have hn : t/k < R+C*q := by
      by_contra! hh
      exact (Nat.lt_irrefl C) ((lt_count_residue_iff hq (t/k) r C).mpr hh)
    exact ((Nat.div_lt_iff_lt_mul hk).mp hn).le
  have upper : (R+C*q)*k ≤ t+q*k := by
    cases hz : C with
    | zero => simpa using (Nat.mul_le_mul_right k hR).trans (Nat.le_add_left (q*k) t)
    | succ j =>
      have hj : j < countTerms (t/k) q r := by change j<C; omega
      have hh := (Nat.le_div_iff_mul_le hk).mp ((lt_count_residue_iff hq (t/k) r j).mp hj)
      change (R+j*q)*k ≤ t at hh
      rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_mul]
      omega
  have hQ : (0:ℝ) < q := by exact_mod_cast hq
  have hden : (0:ℝ) < (k:ℝ)*q := by positivity
  have a : (t:ℝ)/((k:ℝ)*q) ≤ (R:ℝ)/q+C := by
    apply (div_le_iff₀ hden).mpr
    calc
      (t:ℝ) ≤ ((R:ℝ)+(C:ℝ)*q)*k := by exact_mod_cast lower
      _ = ((R:ℝ)/q+C)*((k:ℝ)*q) := by field_simp
  have b : (R:ℝ)/q+C-1 ≤ (t:ℝ)/((k:ℝ)*q) := by
    apply (le_div_iff₀ hden).mpr
    have b' : ((R:ℝ)+(C:ℝ)*q)*k ≤ (t:ℝ)+q*k := by exact_mod_cast upper
    calc
      ((R:ℝ)/q+C-1)*((k:ℝ)*q) = ((R:ℝ)+(C:ℝ)*q)*k-q*k := by field_simp
      _ ≤ (t:ℝ) := by linarith
  change |(C:ℝ) - (t:ℝ)/((k:ℝ)*q) - (1/2 - (R:ℝ)/q)| ≤ 1/2
  rw [abs_le]
  constructor <;> linarith only [a,b]
theorem centered_tail_bound (S : Finset ℕ) (c : ℕ → ℝ) (q h t : ℕ) (res : ℕ → ℕ)
    (hq : 0 < q) (hk : ∀ k ∈ S, 0 < k) (hc : ∀ k ∈ S, k.Coprime q)
    (hr : ∀ k ∈ S, res k*k ≡ h [MOD q]) (hz : ∑ k ∈ S, c k / k = 0) (target : ℝ) :
    |G S c q h t - target| ≤ |(∑ k ∈ S, c k * residueCenter q (res k)) - target| +
                               (∑ k ∈ S, |c k|)/2 := by
  have cancel : ∑ k ∈ S, c k * ((t:ℝ)/((k:ℝ)*q)) = 0 := by
    calc
      _ = ∑ k ∈ S, (t/q) * (c k / k) := by
        apply sum_congr rfl; intro k _
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = 0 := by rw [← mul_sum, hz, mul_zero]
  let E := fun k : ℕ => (count q h t k:ℝ) - (t:ℝ)/((k:ℝ)*q) - residueCenter q (res k)
  let center := ∑ k ∈ S, c k * residueCenter q (res k)
  have balance : G S c q h t - target = (center - target) + (∑ k ∈ S, c k * E k) := by
    simp only [center, E, mul_sub, sum_sub_distrib, cancel, sub_zero, G]
    ring
  rw [balance]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  apply (abs_sum_le_sum_abs _ _).trans
  rw [div_eq_mul_one_div, Finset.sum_mul]
  apply sum_le_sum
  intro k hs
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (count_centered q h t k (res k) hq (hk k hs) (hc k hs) (hr k hs)) (abs_nonneg _)
end FR7022ProgressionTail

namespace SmallModulusTail
open Finset FR7022ProgressionTail

def lanes (q K : ℕ) := ((Icc 1 K).filter fun k => k.Coprime q)
def cls (q : ℕ) := (range q).filter fun u => u.Coprime q
def lane (K q u : ℕ) := (lanes q K).filter fun k => k % q = u

theorem lane_mem (K q k : ℕ) (hq : 0<q) (hk : k∈lanes q K) : k % q∈cls q := by
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),?_⟩
  change Nat.gcd (k % q) q = 1
  rw [←Nat.gcd_rec q k,Nat.gcd_comm]
  exact (mem_filter.mp hk).2

theorem unit_cap (K q : ℕ) (hq : 0<q) (c : ℕ→ℝ)
    (hz : ∑ k∈lanes q K, c k/k=0) (h t : ℕ) :
    |G (lanes q K) c q h t - (if h % q=1 % q then (1:ℝ) else 0)| ≤
      1+((∑ u∈cls q, |∑ k∈lane K q u,c k|)+(∑ k∈lanes q K,|c k|))/2 := by
  classical
  let inv := fun u : ℕ => if hu : u.Coprime q then
    Classical.choose (Nat.exists_mul_mod_eq_of_coprime h hu hq.ne') else 0
  let Z : ℝ := if h % q=1 % q then 1 else 0
  have rz : |Z| ≤ 1 := by dsimp only [Z]; split <;> norm_num
  have m k (hk : k∈lanes q K) : inv (k % q)*k ≡ h [MOD q] := by
    have hc := (mem_filter.mp (lane_mem K q k hq hk)).2
    have hh := (Classical.choose_spec (Nat.exists_mul_mod_eq_of_coprime h hc hq.ne')).2
    change (inv (k % q)*k) % q=h % q
    dsimp only [inv]; rw [dif_pos hc,Nat.mul_comm,←Nat.mod_mul_mod]; exact hh
  have rcap u : |residueCenter q (inv u)| ≤ 1/2 := by
    have hn : firstResidue q (inv u) ≤ q := by
      unfold firstResidue; split_ifs; exact le_rfl; exact (Nat.mod_lt _ hq).le
    have hq' : (0:ℝ)<q := by exact_mod_cast hq
    have d : (firstResidue q (inv u):ℝ)/q ≤ 1 := (div_le_one hq').mpr (by exact_mod_cast hn)
    have e : 0≤(firstResidue q (inv u):ℝ)/q := by positivity
    unfold residueCenter; rw [abs_le]; constructor <;> linarith
  have grouping : (∑ k∈lanes q K,c k*residueCenter q (inv (k % q))) =
      ∑ u∈cls q,(∑ k∈lane K q u,c k)*residueCenter q (inv u) := by
    rw [←sum_fiberwise_of_maps_to (fun k hk => lane_mem K q k hq hk) (fun k => c k*residueCenter q (inv (k % q)))]
    apply sum_congr rfl; intro u _
    rw [sum_mul]; apply sum_congr rfl; intro k hk
    rw [(mem_filter.mp hk).2]
  have center : |∑ k∈lanes q K,c k*residueCenter q (inv (k % q))| ≤ (∑ u∈cls q, |∑ k∈lane K q u,c k|)/2 := by
    rw [grouping,div_eq_mul_one_div,sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro u _; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (rcap u) (abs_nonneg _)
  have b := centered_tail_bound (lanes q K) c q h t (fun k => inv (k % q)) hq
    (fun k hk => (mem_Icc.mp (mem_filter.mp hk).1).1) (fun k hk => (mem_filter.mp hk).2) m hz Z
  dsimp only [Z] at b ⊢
  linarith only [b,center,rz,show |(∑ k∈lanes q K,c k*residueCenter q (inv (k % q)))-Z| ≤
    |∑ k∈lanes q K,c k*residueCenter q (inv (k % q))|+|Z| from abs_sub _ _]

end SmallModulusTail

namespace FR7022Rational
def withNat {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)
theorem withNat_eq {α} (x : Nat) (f : Nat → α) : withNat x f = f x := by cases x <;> rfl
end FR7022Rational
namespace FR7022Unpack
open FR7022Lane
theorem pack_split (w n m : ℕ) (f : ℕ→ℕ) :
    pack w (n+m) f = pack w n f + (2^(w+1))^n * pack w m (fun i => f (i+n)) := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [Nat.succ_add,pack,pack,ih,pow_succ]
    simp only [Nat.add_assoc,Nat.add_comm n 1]
    ring
end FR7022Unpack
namespace FR7022Hyperbola
open Finset FR7022Lane
private theorem slotBit (w n : ℕ) (v : ℕ → ℕ) (h : ∀ i < n, v i<2^(w+1)) (i j : ℕ)
    (hi : i < n) (hj : j < w+1) :
    (pack w n v).testBit ((w+1)*i+j) = (v i).testBit j := by
  induction n generalizing i v with
  | zero => omega
  | succ n ih =>
    rw [pack, Nat.testBit_two_pow_mul_add _ (h 0 (by omega))]
    cases i with
    | zero => simp [hj]
    | succ i =>
      rw [Nat.mul_succ]
      have hh : ¬ ((w+1)*i+(w+1)+j < w+1) := by omega
      rw [ite_eq_right hh, show (w+1)*i+(w+1)+j-(w+1)=(w+1)*i+j by omega]
      exact ih (fun a => v (a+1)) (fun a ha => h (a+1) (by omega)) i (by omega)
private theorem slotMul (w n c : ℕ) (v : ℕ → ℕ) :
    pack w n v * c = pack w n (fun i => v i*c) := by
  induction n generalizing v with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack, Nat.add_mul, Nat.mul_assoc, ih]
def word (u n : ℕ) (a : ℕ → ℕ) := pack (u-1) n a
theorem word_bit {u n : ℕ} (hu : 0 < u) (a : ℕ → ℕ) (ha : ∀ i < n, a i<2^u)
    (i b : ℕ) (hi : i < n) (hb : b < u) :
    (word u n a).testBit (u*i+b) = (a i).testBit b := by
  have hw : u-1+1=u := by omega
  simpa only [word,hw] using slotBit (u-1) n a
    (fun i h => by simpa only [hw] using ha i h) i b hi (by simpa only [hw] using hb)
theorem word_small {u n : ℕ} (hu : 0 < u) (a : ℕ → ℕ) (ha : ∀ i < n, a i<2^u) :
    word u n a < 2^(u*n) := by
  have hw : u-1+1=u := by omega
  simpa only [word,hw,←pow_mul] using pack_lt_radix_power (u-1) n a (fun i h => by simpa only [hw] using ha i h)
theorem word_const (u n c : ℕ) : c*word u n (fun _ => 1) = word u n (fun _ => c) := by
  rw [Nat.mul_comm c]
  simpa only [word,one_mul] using slotMul (u-1) n c (fun _ => 1)
def slice (u table lo n : ℕ) := (table >>> (u*lo)) &&& ((1 <<< (u*n))-1)
theorem word_of_slots {u N table : ℕ} (hu : 0 < u) (hsize : table < 2^(u*N))
    (a : ℕ → ℕ) (ha : ∀ i < N, a i<2^u)
    (hs : ∀ i < N, slice u table i 1 = a i) : table = word u N a := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < u*N
  · let i := j/u
    let b := j % u
    have hi : i < N := (Nat.div_lt_iff_lt_mul hu).mpr (by simpa [Nat.mul_comm] using h)
    have hb : b < u := Nat.mod_lt _ hu
    have rep : u*i+b=j := Nat.div_add_mod _ _
    have eqb := congrArg (fun z : ℕ => z.testBit b) (hs i hi)
    simp [slice,Nat.testBit_shiftRight,Nat.shiftLeft_eq,
      hb] at eqb
    rw [←rep,word_bit hu a ha i b hi hb]
    exact eqb
  · have larger : 2^(u*N)≤(2:ℕ)^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (hsize.trans_le larger),
      Nat.testBit_lt_two_pow ((word_small hu a ha).trans_le larger)]
end FR7022Hyperbola
namespace FR7022Flat
open FR7022Hyperbola
theorem split_lanes {s a n : ℕ} (hs : 0 < s) (ha : 2*a ≤ s) (lo hi : ℕ→ℕ)
    (hl : ∀ i < n, lo i<2^a) (hh : ∀ i < n, hi i<2^a) :
    let z := word s n (fun i => lo i+2^a*hi i)
    let u := word s n (fun _ => 1)
    let mask := (u <<< a)-u
    z &&& mask = word s n lo ∧ (z >>> a) &&& mask = word s n hi := by
  dsimp only
  let u := word s n (fun _ => 1)
  let z := word s n (fun i => lo i+2^a*hi i)
  let m := word s n (fun _ => 2^a-1)
  have mask : (u <<< a)-u=m := by
    rw [Nat.shiftLeft_eq,Nat.mul_comm,show 2^a*u-u = (2^a-1)*u by rw [Nat.sub_mul,Nat.one_mul]]
    exact word_const s n _
  change z &&& ((u <<< a)-u) = _ ∧ (z >>> a) &&& ((u <<< a)-u) = _
  rw [mask]
  have ap : 2^a≤2^s := Nat.pow_le_pow_right (by decide) (by omega)
  have mf (i : ℕ) (_ : i < n) : 2^a-1<2^s := by have := Nat.two_pow_pos a; omega
  have lf := fun i h => (hl i h).trans_le ap
  have hf := fun i h => (hh i h).trans_le ap
  have zf (i : ℕ) (h : i < n) : lo i+2^a*hi i<2^s := by
    calc
      _ < 2^a+2^a*hi i := Nat.add_lt_add_right (hl i h) _
      _ = 2^a*(hi i+1) := by rw [Nat.mul_succ,Nat.add_comm]
      _ ≤ 2^a*2^a := Nat.mul_le_mul_left _ (hh i h)
      _ = 2^(2*a) := by rw [two_mul,pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  have both (j : ℕ) : (z &&& m).testBit j=(word s n lo).testBit j ∧
      ((z >>> a) &&& m).testBit j=(word s n hi).testBit j := by
    simp only [Nat.testBit_and,Nat.testBit_shiftRight]
    by_cases inside : j < s*n
    · let i := j/s
      let b := j % s
      have ii : i < n := (Nat.div_lt_iff_lt_mul hs).mpr (by simpa [Nat.mul_comm] using inside)
      have bs : b < s := Nat.mod_lt _ hs
      have atj : s*i+b=j := Nat.div_add_mod j s
      rw [←atj,word_bit hs _ mf i b ii bs,word_bit hs lo lf i b ii bs,word_bit hs hi hf i b ii bs,
        Nat.testBit_two_pow_sub_one]
      by_cases keep : b < a
      · have hf2 : a+b < s := by omega
        rw [show a+(s*i+b)=s*i+(a+b) by omega,word_bit hs _ zf i b ii bs,
          word_bit hs _ zf i (a+b) ii hf2,Nat.add_comm (lo i) (2^a*hi i)]
        simp [Nat.testBit_two_pow_mul_add _ (hl i ii),keep]
      · have p := Nat.pow_le_pow_right (n:=2) (by decide) (show a ≤ b by omega)
        simp [keep,Nat.testBit_lt_two_pow ((hl i ii).trans_le p),
          Nat.testBit_lt_two_pow ((hh i ii).trans_le p)]
    · have p := Nat.pow_le_pow_right (n:=2) (by decide) (show s*n ≤ j by omega)
      have clear (f : ℕ→ℕ) (fit : ∀ i < n, f i<2^s) : (word s n f).testBit j=false :=
        Nat.testBit_lt_two_pow ((word_small hs f fit).trans_le p)
      rw [clear _ mf,clear lo lf,clear hi hf]
      simp
  exact ⟨Nat.eq_of_testBit_eq (fun j => (both j).1),Nat.eq_of_testBit_eq (fun j => (both j).2)⟩
end FR7022Flat
namespace FR7022Flat
open FR7022Rational
def expand (iw ow : Nat) : Nat → Nat → Nat → Nat
  | 0,z,_ => z
  | d+1,z,u =>
    let h := 2^d
    withNat ((u <<< (iw*h))-u) (fun m =>
      withNat ((z &&& m) + (((z >>> (iw*h)) &&& m) <<< (ow*h))) (fun x =>
        withNat (u + (u <<< (ow*h))) (fun v => expand iw ow d x v)))
end FR7022Flat
namespace FR7022Flat
open FR7022Hyperbola FR7022Lane FR7022Rational
private theorem word_step (s n : ℕ) (hs : 0 < s) (f : ℕ→ℕ) :
    word s (n+1) f=2^s*word s n (fun i=>f (i+1))+f 0 := by
  simp only [word,pack,show s-1+1=s by omega]
private theorem word_one' (s : ℕ) (hs : 0 < s) (f : ℕ→ℕ) : word s 1 f = f 0 := by
  rw [word_step s 0 hs]; simp [word,pack]
private theorem alternate (s n : ℕ) (hs : 0 < s) (f : ℕ→ℕ) :
    word (2*s) n (fun i=>f (2*i)) + (word (2*s) n (fun i=>f (2*i+1)) <<< s) =
    word s (2*n) f := by
  rw [Nat.shiftLeft_eq]
  induction n generalizing f with
  | zero => simp [word,pack]
  | succ n ih =>
    have hs' : 0<2*s := by omega
    rw [Nat.mul_succ,word_step _ _ hs',word_step _ _ hs',word_step s (2*n+1) hs,
      word_step s (2*n) hs]
    have e := ih (fun i=>f (i+2))
    simp only [Nat.mul_succ]
    rw [show (fun i=>f (i+1+1)) = fun i=>f (i+2) from rfl,←e,
      show 2^(2*s)=(2^s)*(2^s) by rw [two_mul,pow_add]]
    simp only [Nat.mul_zero,Nat.zero_add]
    rw [show (fun i=>f (2*i+2+1)) = fun i=>f (2*i+1+2) from rfl]
    ring
def grouped (iw h : ℕ) (f : ℕ→ℕ) (j : ℕ) := word iw h (fun k=>f (j*h+k))
private theorem group_pair (iw h : ℕ) (hi : 0 < iw) (f : ℕ→ℕ) (j : ℕ) :
    grouped iw (2*h) f j =
      grouped iw h f (2*j) + 2^(iw*h) * grouped iw h f (2*j+1) := by
  unfold grouped word
  rw [two_mul,FR7022Unpack.pack_split,show iw-1+1=iw by omega,←pow_mul]
  congr 1
  · congr 1; funext k; congr 1; ring
  · congr 2; funext k; congr 1; ring
def SplitRule : Prop :=
  ∀ {s a n : ℕ}, 0 < s → 2*a ≤ s → ∀ (lo hi : ℕ→ℕ),
    (∀ i < n, lo i<2^a) → (∀ i < n, hi i<2^a) →
    let z := word s n (fun i=>lo i+2^a*hi i)
    let u := word s n (fun _=>1)
    let m := (u<<<a)-u
    z &&& m = word s n lo ∧ (z>>>a) &&& m = word s n hi
theorem expand_groups (rule : SplitRule) (iw ow : ℕ) (hi : 0 < iw) (ho : iw ≤ ow)
    (f : ℕ→ℕ) (hf : ∀ i, f i<2^iw) (d n : ℕ) :
    expand iw ow d (word (ow*2^d) n (grouped iw (2^d) f)) (word (ow*2^d) n (fun _=>1)) =
    word ow (n*2^d) f := by
  induction d generalizing n with
  | zero =>
    have one : grouped iw 1 f = f := by
      funext j; simp [grouped,word_one' iw hi]
    simp [expand,one]
  | succ d ih =>
    let H := 2^d
    have hp : 0 < H := by dsimp [H]; positivity
    have sp : 0 < ow*H := Nat.mul_pos (by omega) hp
    have db : 2^(d+1)=2*H := by simp [H,pow_succ,Nat.mul_comm]
    have room : 2*(iw*H) ≤ 2*(ow*H) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right H ho)
    have sm (j : ℕ) : grouped iw H f j < 2^(iw*H) := word_small hi _ (fun i _ => hf _)
    have sep := rule (show 0<2*(ow*H) by omega) room
      (fun j=>grouped iw H f (2*j)) (fun j=>grouped iw H f (2*j+1))
      (fun j _=>sm _) (fun j _=>sm _) (n:=n)
    dsimp only at sep
    have g : (fun i=>grouped iw H f (2*i)+2^(iw*H)*grouped iw H f (2*i+1)) =
      grouped iw (2*H) f := funext (fun i=>(group_pair iw H hi f i).symm)
    rw [g] at sep
    rw [expand,withNat_eq,withNat_eq,withNat_eq,db,show ow*(2*H)=2*(ow*H) by ring]
    change expand iw ow d _ _ = _
    rw [sep.1,sep.2,alternate (ow*H) n sp (grouped iw H f),alternate (ow*H) n sp (fun _=>1)]
    convert ih (2*n) using 2 <;> dsimp [H] <;> ring
theorem expand_word (rule : SplitRule) (iw ow : ℕ) (hi : 0 < iw) (ho : iw ≤ ow)
    (f : ℕ→ℕ) (hf : ∀ i, f i<2^iw) (d : ℕ) :
    expand iw ow d (word iw (2^d) f) 1=word ow (2^d) f := by
  have hs : 0 < ow*2^d := Nat.mul_pos (by omega) (by positivity)
  simpa only [word_one' _ hs,grouped,Nat.zero_mul,Nat.zero_add,Nat.one_mul] using
    expand_groups rule iw ow hi ho f hf d 1
end FR7022Flat

namespace SmallModulusPack
open Finset FR7022Lane ThetaScalar

abbrev X : ℕ := 4294967296
def slot (n q : ℕ) (f : ℕ→ℕ) (u : ℕ) := ∑ k∈(range n).filter (fun k => k % q=u), f k

private theorem ex (n : ℕ) (f : ℕ→ℕ) : pack 31 n f = ∑ i∈range n,X^i*f i := by
  have h:= (pack_int 31 n f).trans (eval_eq_sum _ _ _)
  change (pack 31 n f:ℤ)=∑ i∈range n,(4294967296:ℤ)^i*(f i:ℤ) at h
  exact_mod_cast h

private theorem add_mod_sum {m : ℕ} (s : Finset ℕ) (f g : ℕ→ℕ) (h : ∀ i∈s,f i ≡ g i [MOD m]) :
    (∑ i∈s,f i) ≡ (∑ i∈s,g i) [MOD m] := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert x s hx ih =>
    rw [sum_insert hx,sum_insert hx]
    exact (h x (mem_insert_self ..)).add (ih (fun i hi => h i (mem_insert_of_mem hi)))

private theorem congr_mod (n q : ℕ) (hq : 0<q) (f : ℕ→ℕ) :
    pack 31 n f ≡ pack 31 q (slot n q f) [MOD X^q-1] := by
  have xlo : 3≤X^q := (by decide : 3≤X).trans (le_self_pow₀ (by decide : 1≤X) hq.ne')
  have one : X^q ≡ 1 [MOD X^q-1] := by
    change X^q % (X^q-1)=1 % (X^q-1)
    rw [Nat.mod_eq_sub_mod (by omega : X^q-1≤X^q),show X^q-(X^q-1)=1 by omega]
  have step (k : ℕ) : X^k ≡ X^(k % q) [MOD X^q-1] := by
    calc
      X^k = X^(k % q)*((X^q)^(k/q)) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
      _ ≡ X^(k % q)*(1^(k/q)) [MOD X^q-1] := (one.pow _).mul_left _
      _ = _ := by simp
  rw [ex,ex]
  apply (add_mod_sum _ _ (fun k => X^(k % q)*f k) (fun k _ => (step k).mul_right _)).trans
  apply Nat.ModEq.of_dvd (dvd_refl _)
  have eqn : (∑ k∈range n,X^(k % q)*f k) = ∑ u∈range q,X^u*slot n q f u := by
    rw [←sum_fiberwise_of_maps_to (fun k (_ : k∈range n) => mem_range.mpr (Nat.mod_lt k hq)) (fun k => X^(k % q)*f k)]
    apply sum_congr rfl; intro u hu
    rw [slot,mul_sum]; apply sum_congr rfl; intro k hk; rw [(mem_filter.mp hk).2]
  rw [eqn]

theorem digit_mod (n q : ℕ) (hq : 0<q) (f : ℕ→ℕ)
    (hs : ∀ u<q,slot n q f u+1<X) (u : ℕ) (hu : u<q) :
    digit 32 (pack 31 n f % (X^q-1)) u = slot n q f u := by
  let s:=slot n q f
  have b : pack 31 q s+1 ≤ pack 31 q (fun i => s i+1) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    simp only [pack]
    have x:= FR7022Verified.pack_mono 31 j (fun i => s (i+1)) (fun i => s (i+1)+1) (fun i _ => by omega)
    omega
  have p:=pack_lt_radix_power 31 q (fun i => s i+1) hs
  change pack 31 q (fun i => s i+1)<X^q at p
  have e:=congr_mod n q hq f
  change pack 31 n f % (X^q-1) = pack 31 q s % (X^q-1) at e
  rw [Nat.mod_eq_of_lt (show pack 31 q s<X^q-1 by omega)] at e
  rw [e]
  exact digit_pack 31 q s (fun i hi => (Nat.lt_succ_self _).trans (hs i hi)) u hu

def tree (f : ℕ→ℕ) : ℕ → ℕ → ℕ
  | 0,k => f k
  | h+1,k => tree f h k + (tree f h (k+2^h) <<< (32*2^h))

theorem tree_eq (f : ℕ→ℕ) (h k : ℕ) : tree f h k = pack 31 (2^h) (fun i => f (k+i)) := by
  induction h generalizing k with
  | zero => simp [tree,pack]
  | succ h ih =>
    rw [pow_succ,Nat.mul_two,FR7022Unpack.pack_split,tree,ih,ih,Nat.shiftLeft_eq]
    simp only [show (31+1:ℕ)=32 by decide,←pow_mul]
    congr 1
    rw [Nat.mul_comm]; congr 2; funext i; congr 1; omega
end SmallModulusPack

namespace SmallModulusPack
open Finset FR7022Lane ThetaScalar SmallModulusTail

def tab (neg : Bool) (k : ℕ) : ℕ := if 1≤k ∧ k≤20000 then
  (if neg then -(base 20000 12000 signs k) else base 20000 12000 signs k).toNat else 0

private theorem tab_small (b : Bool) (k : ℕ) : tab b k ≤ 8000 := by
  have hs : |signs k|≤1 := by unfold signs; split <;> decide
  have H : |base 20000 12000 signs k|≤(8000:ℤ) := by
    unfold base; rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    exact (mul_le_mul_of_nonneg_right hs (Int.natCast_nonneg _)).trans
      (by rw [one_mul]; exact_mod_cast (min_le_left (20000-12000) (20000-k)))
  have hg:=abs_le.mp H
  unfold tab
  split
  · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · decide

private theorem slot_small (q r : ℕ) (b : Bool) : slot 32768 q (tab b) r+1 < X := by
  let s := (range 32768).filter (fun k => k % q=r)
  have c : s.card≤32768 := (card_le_card (filter_subset _ _)).trans_eq (card_range _)
  have h : slot 32768 q (tab b) r ≤ s.card*8000 := by
    change (∑ k∈s,tab b k)≤_
    calc _ ≤ ∑ _∈s,8000 := sum_le_sum fun k _ => tab_small b k
         _ = _ := by simp
  change _<4294967296; omega

private theorem lane_total (q u : ℕ) (hu : u∈cls q) (b : Bool) :
    slot 32768 q (tab b) u = ∑ k∈lane 20000 q u,tab b k := by
  symm
  apply sum_subset
  · intro k hk
    obtain ⟨hS,he⟩:=mem_filter.mp hk
    have h: k≤20000 := (mem_Icc.mp (mem_filter.mp hS).1).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),he⟩
  · intro k hk hn
    have he := (mem_filter.mp hk).2
    have hku : k.Coprime q := by
      change k.gcd q=1
      rw [Nat.gcd_comm,Nat.gcd_rec,he]
      exact (mem_filter.mp hu).2
    have kk : ¬(1≤k ∧ k≤20000) := fun a => hn (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr a,hku⟩,he⟩)
    simp [tab,kk]

noncomputable def pos : {a:ℕ // a=tree (tab false) 15 0} := by
  have h : tree (tab false) 15 0=tree (tab false) 15 0 := rfl
  conv at h => lhs; reduce
  exact ⟨_,h⟩
noncomputable def neg : {a:ℕ // a=tree (tab true) 15 0} := by
  have h : tree (tab true) 15 0=tree (tab true) 15 0 := rfl
  conv at h => lhs; reduce
  exact ⟨_,h⟩

def calcLane (q w u : ℕ) := digit 32 (w % (X^q-1)) u
theorem signed_lane (q : ℕ) (hq : 0<q) (u : ℕ) (hu : u∈cls q) :
    (calcLane q pos.1 u:ℤ)-(calcLane q neg.1 u:ℤ) =
    ∑ k∈lane 20000 q u,base 20000 12000 signs k := by
  have dig (w : ℕ) (b : Bool) (hw : w=tree (tab b) 15 0) :
      calcLane q w u = ∑ k∈lane 20000 q u,tab b k := by
    have huQ:=mem_range.mp (mem_filter.mp hu).1
    rw [calcLane,hw,tree_eq]
    simp only [zero_add]
    exact (digit_mod 32768 q hq (tab b) (fun j _ => slot_small q j b) u huQ).trans (lane_total q u hu b)
  rw [dig _ _ pos.2,dig _ _ neg.2,Nat.cast_sum,Nat.cast_sum,←sum_sub_distrib]
  apply sum_congr rfl; intro k hk
  have h := mem_Icc.mp (mem_filter.mp (mem_filter.mp hk).1).1
  simp only [tab,ite_eq_left h,Bool.false_eq_true,ite_false,ite_true]
  omega

def rawAbs (q p n : ℕ) : ℕ := (((List.range q).filter fun u => u.Coprime q).map
  (fun u => ((calcLane q p u:ℤ)-(calcLane q n u:ℤ)).natAbs)).sum
noncomputable def packedAbs (q : ℕ) := rawAbs q pos.1 neg.1
theorem abs_spec (q : ℕ) (hq : 0<q) : packedAbs q =
    ∑ u∈cls q,(∑ k∈lane 20000 q u,base 20000 12000 signs k).natAbs := by
  let l:=(List.range q).filter fun u => u.Coprime q
  have nd : l.Nodup := List.Nodup.filter _ List.nodup_range
  have eq : l.toFinset=cls q := by ext i; simp [l,cls]
  unfold packedAbs rawAbs; change (l.map _).sum=_
  rw [←List.sum_toFinset _ nd,eq]
  apply sum_congr rfl; intro u hu; rw [signed_lane q hq u hu]
end SmallModulusPack

namespace SmallModulusPack
open Finset FR7022ProgressionTail SmallModulusTail ThetaScalar

private theorem bump_nonneg (k : ℕ) : 0≤(bump 12000 k:ℝ) := by unfold bump; split <;> norm_num

private theorem bump_limit (q : ℕ) : (∑ k∈lanes q 20000,(bump 12000 k:ℝ))≤8000 := by
  calc
    _ ≤ ∑ k∈Icc 1 20000,(bump 12000 k:ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => bump_nonneg k)
    _ = _ := by
      have eq : (Icc 1 20000).filter (fun k:ℕ=>12000<k) = Icc 12001 20000 := by
        ext k; simp; omega
      simp only [bump,apply_ite,Int.cast_one,Int.cast_zero,←sum_filter,eq,sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc]
      norm_num

def capCheck (q M C : ℕ) (lo hi : ℤ) : Prop :=
  16000000+8000000*M+1000*packedAbs q+8000*max lo.natAbs hi.natAbs≤2*C

theorem packed_cap (q M C : ℕ) (lo hi : ℤ) (hq : 0<q)
    (hz : ∑ k∈support 20000 q,co 20000 12000 q signs k/k=0)
    (ha : (lo:ℝ)/1000 ≤ alpha 20000 12000 q signs ∧ alpha 20000 12000 q signs ≤ (hi:ℝ)/1000)
    (hm : (∑ k∈support 20000 q,|co 20000 12000 q signs k|)≤(M:ℝ))
    (hC : capCheck q M C lo hi) (h t : ℕ) :
    |G (support 20000 q) (co 20000 12000 q signs) q h t-(if h % q=1 % q then (1:ℝ) else 0)|≤C/(8000000:ℝ) := by
  let c:=co 20000 12000 q signs
  let A := max lo.natAbs hi.natAbs
  let a:=alpha 20000 12000 q signs
  have alo : |(lo:ℝ)|≤(A:ℝ) := by
    rw [←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]; exact Nat.cast_le.mpr (le_max_left ..)
  have ahi : |(hi:ℝ)|≤(A:ℝ) := by
    rw [←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]; exact Nat.cast_le.mpr (le_max_right ..)
  have bound : 1000*|a|≤(A:ℝ) := by
    rw [←abs_of_pos (by norm_num : (0:ℝ)<1000),←abs_mul,abs_le]
    dsimp only [a]; constructor <;> linarith only [ha.1,ha.2,(abs_le.mp alo).1,(abs_le.mp ahi).2]
  let ubase := fun u => ∑ k∈lane 20000 q u,base 20000 12000 signs k
  let ubump := fun u => ∑ k∈lane 20000 q u,(bump 12000 k:ℝ)
  have mid (u : ℕ) : 8000*(∑ k∈lane 20000 q u,c k)=(ubase u:ℝ)+a*ubump u := by
    simp only [ubase,ubump,Int.cast_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl; intro k hk
    dsimp only [c,co,a]; norm_num; ring
  have ups u : 0≤ubump u := sum_nonneg (fun k _ => bump_nonneg k)
  have single (u : ℕ) :
      8000000*|∑ k∈lane 20000 q u,c k| ≤ 1000*|(ubase u:ℝ)|+(A:ℝ)*ubump u := by
    have e := congrArg abs (mid u)
    rw [abs_mul,show |(8000:ℝ)|=8000 by norm_num] at e
    have v := abs_add_le (ubase u:ℝ) (a*ubump u)
    rw [abs_mul,abs_of_nonneg (ups u)] at v
    nlinarith only [e,v,mul_le_mul_of_nonneg_right bound (ups u)]
  have agg := sum_le_sum (s:=cls q) (fun u _ => single u)
  simp only [sum_add_distrib,←mul_sum] at agg
  have absData : (∑ u∈cls q,|(ubase u:ℝ)|) = (packedAbs q:ℝ) := by
    rw [abs_spec q hq,Nat.cast_sum]; apply sum_congr rfl; intro u _
    rw [←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]
  have p : (∑ u∈cls q,ubump u)≤8000 := by
    have e : (∑ u∈cls q,ubump u) = ∑ k∈lanes q 20000,(bump 12000 k:ℝ) :=
      sum_fiberwise_of_maps_to (fun k hk => lane_mem 20000 q k hq hk) _
    rw [e]; exact bump_limit _
  rw [absData] at agg
  have x := unit_cap 20000 q hq c hz h t
  have cap : 16000000+8000000*(M:ℝ)+1000*packedAbs q+8000*(A:ℝ)≤2*(C:ℝ) := by exact_mod_cast hC
  change (∑ k∈lanes q 20000,|c k|)≤(M:ℝ) at hm
  change |G (lanes q 20000) c q h t-(if h % q=1 % q then (1:ℝ) else 0)|≤C/(8000000:ℝ)
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<8000000)).mpr
  linarith only [x,hm,agg,cap,mul_le_mul_of_nonneg_left p (Nat.cast_nonneg A)]
end SmallModulusPack

namespace SmallModulusSteps
open Finset FR7022NextRows FR7022ProgressionTail ThetaScalar

private theorem base_all : ∀ q∈Icc 1 105, (12007:ℕ).Coprime q := by decide +kernel

theorem positive_all (r : Row) (hq : 1≤r.q) (hQ : r.q≤105) : 0<harm (rsupp r) (bump 12000) :=
  slope_pos _ _ _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by decide,by decide⟩,
    base_all r.q (mem_Icc.mpr ⟨hq,hQ⟩)⟩) (by decide : 12000<12007)

private theorem weight_bound (a : ℤ) (ha : |a|≤2000000) (k : ℕ) :
    |1000*base 20000 12000 signs k+a*bump 12000 k| ≤ (10000000:ℕ) := by
  have z : |signs k|≤1 := by unfold signs; split <;> decide
  have m : (min (20000-12000) (20000-k):ℕ)≤8000 := min_le_left ..
  have m' : (min (20000-12000) (20000-k):ℕ)≥0 := Nat.zero_le _
  have b : |base 20000 12000 signs k|≤(8000:ℤ) := by
    unfold base; rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    exact (mul_le_mul_of_nonneg_right z (Int.natCast_nonneg _)).trans (by rw [one_mul];exact_mod_cast m)
  have f : |bump 12000 k|≤1 := by unfold bump; split <;> decide
  have g : |a*bump 12000 k|≤2000000 := by
    rw [abs_mul]; calc
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left f (abs_nonneg a)
      _ ≤ _ := by simpa using ha
  have A := abs_add_le (1000*base 20000 12000 signs k) (a*bump 12000 k)
  rw [abs_mul,show |(1000:ℤ)|=1000 by decide] at A
  change _≤(10000000:ℤ); linarith only [A,b,g]

abbrev wordSpec (f : ℕ→ℤ) (w : ℤ) : Prop :=
  FR7022Lane.eval FR7022Verified.A 3000000
    (fun i => GoldbachCoefficientPrefix.divisorWeight (Icc 1 20000) f (i+1))=w

theorem endpoint_of_check (r : Row) (hr : r∈FR7022NextRows.rows) (a w z : ℤ)
    (ha : a=r.lo ∨ a=r.hi) (hb : |a|≤2000000)
    (hw : wordSpec (base 20000 12000 signs) w) (hz : wordSpec (bump 12000) z)
    (ck : check 3000000 8000000 w z r=true) : EndpointBound r a :=
  bound (Icc 1 20000) (base 20000 12000 signs) (bump 12000) w z a 3000000 8000000 20000 10000000 r
    (fun k hk => (mem_Icc.mp hk).1) (by simp) (fun k _ => weight_bound a hb k)
    hw hz ha (row_valid r hr) ck

theorem make_evidence (r : Row) (hr : r∈FR7022NextRows.rows) (hq : 2≤r.q) (hQ : r.q≤105)
    (φ M b : ℕ) (hφ : r.q.totient=φ)
    (price : PriceRow 20000 12000 r.q φ M b signs r.lo r.hi) (cost : rateOK r b)
    (cap : SmallModulusPack.capCheck r.q M r.cap r.lo r.hi)
    (left : EndpointBound r r.lo) (right : EndpointBound r r.hi) : Evidence r := by
  have hp:=positive_all r (by omega) hQ
  refine ⟨hp,price.bracket,left,right,?_,⟨b,cost,?_⟩⟩
  · exact SmallModulusPack.packed_cap r.q M r.cap r.lo r.hi (by omega) price.zero price.bracket price.mass_le cap
  · simpa only [hφ,rsupp,cf] using price.scalar
end SmallModulusSteps

namespace SmallModulusSteps
open Finset FR7022NextRows ThetaScalar

def Ready (r : Row) : Prop := ∀ (w z : ℤ), wordSpec (base 20000 12000 signs) w → wordSpec (bump 12000) z →
  r∈FR7022NextRows.rows → check 3000000 8000000 w z r=true → Evidence r

theorem certified (r : Row) (φ M b : ℕ) (bounds : 2≤r.q ∧ r.q≤105 ∧ r.q.totient=φ ∧
    |r.lo|≤2000000 ∧ |r.hi|≤2000000 ∧ rateOK r b)
    (price : PriceRow 20000 12000 r.q φ M b signs r.lo r.hi)
    (cap : SmallModulusPack.capCheck r.q M r.cap r.lo r.hi) : Ready r := by
  intro w z hw hz hr ck
  obtain ⟨hq,hQ,hφ,lb,ub,rate⟩:=bounds
  exact make_evidence r hr hq hQ φ M b hφ price rate cap
    (endpoint_of_check r hr r.lo w z (Or.inl rfl) lb hw hz ck)
    (endpoint_of_check r hr r.hi w z (Or.inr rfl) ub hw hz ck)

def allReady : List Row → Prop
  | [] => True
  | r::rs => Ready r ∧ allReady rs
theorem at_row {xs : List Row} (H : allReady xs) {r : Row} (hr : r∈xs) : Ready r := by
  induction xs with
  | nil => cases hr
  | cons x ls ih =>
    rcases List.mem_cons.mp hr with eq|mem
    · exact eq ▸ H.1
    · exact ih H.2 mem

theorem theta_certificate (w z : ℤ) (hw : wordSpec (base 20000 12000 signs) w)
    (hz : wordSpec (bump 12000) z) (data : allReady FR7022NextRows.rows)
    (checks : ∀ r∈FR7022NextRows.rows,check 3000000 8000000 w z r=true) :
    ∀ q a n : ℕ, 1≤q → q≤105 → a.Coprime q → 10^16≤n →
      (n:ℝ)<Real.exp (Real.exp (19/5)) →
      |(∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), SmallModulusTheta.primeWeight k) -
        (n:ℝ)/q.totient| ≤ (n:ℝ)/200 :=
  theta_of_rows (fun r hr => at_row data hr w z hw hz hr (checks r hr))
end SmallModulusSteps



namespace ThetaWide
open Finset FR7022Hyperbola FR7022Flat FR7022Lane
def powBit (n : ℕ) := (1:ℕ) <<< n
theorem powBit_eq (n : ℕ) : powBit n=2^n := by simp [powBit,Nat.shiftLeft_eq]
theorem word_split (s n m : ℕ) (hs : 0<s) (f : ℕ→ℕ) :
    word s (n+m) f=word s n f+2^(s*n)*word s m (fun i=>f (i+n)) := by
  simpa only [word,show s-1+1=s by omega,←pow_mul] using FR7022Unpack.pack_split (s-1) n m f
theorem word_congr (s n : ℕ) (f g : ℕ→ℕ) (h : ∀ i<n,f i=g i) : word s n f=word s n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    change 2^(s-1+1)*word s n (fun i=>f (i+1))+f 0 = _
    rw [ih _ (fun i=>g (i+1)) (fun i hi => h (i+1) (by omega)),h 0 (by omega)]
    rfl
theorem word_zeros (s n : ℕ) : word s n (fun _=>0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => change 2^(s-1+1)*word s n (fun _=>0)+0=0; rw [ih]; simp
theorem word_pad (s m n : ℕ) (hs : 0<s) (hm : m≤n) (f : ℕ→ℕ) :
    word s n (fun i=>if i< m then f i else 0)=word s m f := by
  rw [show n=m+(n-m) by omega,word_split _ _ _ hs]
  have a := word_congr s m (fun i=>if i< m then f i else 0) f (fun i hi=>if_pos hi)
  have b := word_congr s (n-m) (fun i=>if i+m< m then f (i+m) else 0) (fun _=>0)
    (fun i _=>if_neg (by omega))
  rw [b,word_zeros,mul_zero,add_zero,a]
theorem low_slice (s m n : ℕ) (hs : 0<s) (hm : m≤n) (f : ℕ→ℕ)
    (hf : ∀i< m,f i<2^s) : word s n f &&& (powBit (s*m)-1)=word s m f := by
  rw [powBit_eq,Nat.and_two_pow_sub_one_eq_mod,show n=m+(n-m) by omega,word_split _ _ _ hs]
  simp [Nat.mod_eq_of_lt (word_small hs f hf)]
def spread (iw ow tip : ℕ) : ℕ → ℕ → ℕ
  | 0, z => z
  | p+1, z =>
    if p+1≤tip then expand iw ow (p+1) z 1 else
    let h:=2^p
    spread iw ow tip p (z &&& (powBit (iw*h)-1)) +
      (spread iw ow tip p (z >>> (iw*h)) <<< (ow*h))
theorem spread_eq (iw ow tip : ℕ) (hi : 0 < iw) (ho : iw≤ow) (f : ℕ→ℕ) (hf : ∀i,f i<2^iw)
    (p : ℕ) : spread iw ow tip p (word iw (2^p) f)=word ow (2^p) f := by
  induction p generalizing f with
  | zero => simp [spread,word,pack]
  | succ p ih =>
    rw [spread]
    split
    · exact expand_word (@split_lanes) iw ow hi ho f hf _
    · let h:=2^p
      change spread iw ow tip p (word iw (2^(p+1)) f &&& (powBit (iw*h)-1)) +
        (spread iw ow tip p ((word iw (2^(p+1)) f) >>> (iw*h)) <<< (ow*h)) = _
      have pw : 2^(p+1)=h+h := by simp [h,pow_succ,Nat.mul_two]
      rw [low_slice iw h (2^(p+1)) hi (by rw [pw]; exact Nat.le_add_right h h) f (fun i _=>hf i),pw,word_split iw h h hi,
        Nat.shiftRight_eq_div_pow,Nat.add_mul_div_left _ _ (by positivity : 0<(2:ℕ)^(iw*h)),
        Nat.div_eq_of_lt (word_small hi f (fun i _ =>hf i)),Nat.zero_add,
        ih f hf,ih (fun i=>f (i+h)) (fun i=>hf _),word_split ow h h (by omega),
        Nat.shiftLeft_eq,Nat.mul_comm _ (2^(ow*h))]
end ThetaWide

namespace ThetaWide
open Finset FR7022Rational FR7022Lane FR7022Hyperbola
def unit (s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | depth+1, n =>
    let h:=n/2
    withNat (unit s depth h) (fun x =>
      (x+(x <<< (s*h))) + if n % 2=1 then powBit (s*(h+h)) else 0)
theorem unit_eq (s : ℕ) (hs : 0<s) (depth n : ℕ) (hn : n<2^depth) :
    unit s depth n=word s n (fun _=>1) := by
  induction depth generalizing n with
  | zero =>
    have hz : n=0:=by simpa using hn
    subst n
    rfl
  | succ dep ih =>
    let h:=n/2
    have hm:=Nat.mod_add_div n 2
    have hp:=Nat.mod_lt n (by decide : 0<2)
    have hh : h<2^dep := by rw [pow_succ] at hn; dsimp [h]; omega
    rw [unit,withNat_eq,ih (n/2) hh]
    change word s h _ + ((word s h _) <<< (s*h)) + _ = _
    have hhalf := word_split s h h hs (fun _=>1)
    rw [Nat.shiftLeft_eq,Nat.mul_comm _ (2^(s*h)),←hhalf]
    split
    · have he : n=(h+h)+1 := by dsimp [h];omega
      rw [show word s n (fun _=>1)=word s ((h+h)+1) (fun _=>1) from congrArg (fun m=>word s m (fun _=>1)) he,
        word_split s (h+h) 1 hs,powBit_eq]
      simp [word,pack,h]
    · have he : n=h+h := by dsimp [h];omega
      simp [he]
def positive (iw tip D K B d tab : ℕ) : ℕ :=
  let n:=min K (B/d)-D
  let out:=spread iw (64*d) tip ((n-1).log2+1) (tab &&& (powBit (iw*n)-1))
  out <<< (64*(d*(D+1)-1))
def units (D K B d : ℕ) : ℕ :=
  let n:=min K (B/d)-D
  unit (64*d) (n.log2+1) n <<< (64*(d*(D+1)-1))
theorem word_cast (s n : ℕ) (hs : 0<s) (f : ℕ→ℕ) :
    (word s n f:ℤ)=∑ i∈range n,(2:ℤ)^(s*i)*(f i:ℤ) := by
  rw [word,pack_int,eval_eq_sum]
  simp [show s-1+1=s by omega,pow_mul]
theorem positive_row (iw tip D K B d : ℕ) (a : ℕ→ℕ) (hi : 0 < iw) (ho : iw≤64*d)
    (ha : ∀ i, a i<2^iw) :
    let t:=word iw (K-D) a
    let n:=min K (B/d)-D
    (positive iw tip D K B d t:ℤ) =
      ∑ i∈range n,(2:ℤ)^(64*(d*(D+1)-1))*(2:ℤ)^((64*d)*i)*(a i:ℤ) := by
  dsimp only
  let n:=min K (B/d)-D
  let p:=(n-1).log2+1
  have hmn : n≤K-D := Nat.sub_le_sub_right (min_le_left _ _) _
  have hcap : n≤2^p := by
    have hh:=(Nat.lt_log2_self (n:=n-1))
    dsimp [p]; omega
  have fit (i : ℕ) : (if i<n then a i else 0)<2^iw := by
    split <;> first | exact ha _ | positivity
  change ((spread iw (64*d) tip p (word iw (K-D) a &&& (powBit (iw*n)-1)) <<<
    (64*(d*(D+1)-1))):ℤ) = _
  rw [low_slice iw n _ hi hmn a (fun i _=>ha i),← word_pad iw n (2^p) hi hcap a,
    spread_eq iw (64*d) tip hi ho _ fit p,word_pad (64*d) n _ (by omega) hcap,
    Nat.shiftLeft_eq,Nat.cast_mul,word_cast _ _ (by omega)]
  simp only [sum_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply sum_congr rfl
  intro i _
  ring
theorem unit_row (D K B d : ℕ) (hd : 0<d) :
    (units D K B d:ℤ) =
      ∑ i∈range (min K (B/d)-D),(2:ℤ)^(64*(d*(D+1)-1))*(2:ℤ)^((64*d)*i) := by
  unfold units
  dsimp only
  rw [unit_eq _ (by positivity) _ _ (Nat.lt_log2_self),Nat.shiftLeft_eq,Nat.cast_mul,
    word_cast _ _ (by positivity)]
  simp only [Nat.cast_one,mul_one,sum_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply sum_congr rfl
  intro i _
  ring
end ThetaWide

namespace ThetaWide
open Finset FR7022Hyperbola
def accumulate (f : ℕ→ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,j => f j+accumulate f n (j+1)
theorem accumulate_spec (f : ℕ→ℕ) (n s : ℕ) :
    (accumulate f n s:ℤ)=∑i∈range n,(f (i+s):ℤ) := by
  induction n generalizing s with
  | zero => simp [accumulate]
  | succ n ih =>
    rw [accumulate,Nat.cast_add,ih,sum_range_succ']
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,add_comm]
def build (s : ℕ) (a : ℕ→ℕ) : ℕ → ℕ → ℕ
  | 0,j => a j
  | p+1,j => let h:=2^p
             build s a p j + (build s a p (j+h) <<< (s*h))
theorem build_spec (s : ℕ) (hs : 0<s) (a : ℕ→ℕ) (p j : ℕ) :
    build s a p j=word s (2^p) (fun i=>a (j+i)) := by
  induction p generalizing j with
  | zero => simp [build,word,FR7022Lane.pack]
  | succ p ih =>
    rw [build,ih,ih,show 2^(p+1)=2^p+2^p by rw [pow_succ,Nat.mul_two],word_split _ _ _ hs,
      Nat.shiftLeft_eq,Nat.mul_comm _ (2^(s*2^p))]
    congr 2; apply word_congr; intro i _; congr 1; omega
def input (D K : ℕ) (f : ℕ→ℤ) : ℕ :=
  let m:=K-D
  let a:=fun i=>if i< m then (f (D+1+i)+8192).toNat else 0
  build 15 a (m.log2+1) 0
theorem input_spec (D K : ℕ) (f : ℕ→ℤ) :
    input D K f=word 15 (K-D) (fun i=>(f (D+1+i)+8192).toNat) := by
  unfold input
  dsimp only
  rw [build_spec _ (by decide)]
  simp only [Nat.zero_add]
  exact word_pad 15 (K-D) _ (by decide) (Nat.le_of_lt Nat.lt_log2_self) _
def highPositive (D K B tip tab : ℕ) : ℕ :=
  accumulate (fun d=>positive 15 tip D K B d tab) (B/(D+1)) 1
def highUnits (D K B : ℕ) : ℕ := accumulate (units D K B) (B/(D+1)) 1
def highBase (D K B tip tab : ℕ) : ℤ :=
  (highPositive D K B tip tab:ℤ)-8192*(highUnits D K B:ℤ)
theorem sumShift (D M : ℕ) (F : ℕ→ℤ) :
    ∑ i∈range (M-D),F (D+1+i)=∑ k∈Ioc D M,F k := by
  apply sum_bij' (fun i _=>D+1+i) (fun k _=>k-(D+1))
  · intro i hi; simp only [mem_range] at hi; simp only [mem_Ioc];omega
  · intro k hk; simp only [mem_Ioc] at hk; simp only [mem_range];omega
  · intro i hi;omega
  · intro k hk; simp only [mem_Ioc] at hk;omega
  · intros; rfl
theorem factor_power (D d i : ℕ) (hd : 0<d) :
    (2:ℤ)^(64*(d*(D+1)-1))*(2:ℤ)^((64*d)*i)=(2^64:ℤ)^(d*(D+1+i)-1) := by
  rw [← pow_add,← pow_mul]
  congr 1
  have hh : 0<d*(D+1) := Nat.mul_pos hd (by omega)
  rw [Nat.mul_add d (D+1) i,show d*(D+1)+d*i-1=(d*(D+1)-1)+d*i by omega]
  ring
theorem highUnits_spec (D K B : ℕ) :
    (highUnits D K B:ℤ)=∑ d∈Ioc 0 (B/(D+1)),
      ∑ k∈Ioc D (min K (B/d)),(2^64:ℤ)^(d*k-1) := by
  rw [highUnits,accumulate_spec,← sumShift 0 (B/(D+1))]
  simp only [Nat.sub_zero,Nat.zero_add]
  apply sum_congr rfl
  intro j _
  rw [unit_row _ _ _ _ (by omega),←sumShift]
  apply sum_congr (by rw [Nat.add_comm j 1])
  intro i _
  rw [factor_power D _ i (by omega),Nat.add_comm j 1]
theorem highBase_spec (D K B tip tab : ℕ) (f : ℕ→ℤ)
    (ht : tab=input D K f) (hf : ∀k,|f k|≤8000) :
    highBase D K B tip tab=∑ d∈Ioc 0 (B/(D+1)),
      ∑ k∈Ioc D (min K (B/d)), f k*(2^64:ℤ)^(d*k-1) := by
  let a (i : ℕ) := (f (D+1+i)+8192).toNat
  have hnn (i : ℕ) : 0≤f (D+1+i)+8192 := by have hj:=neg_abs_le (f (D+1+i));have he:=hf (D+1+i);omega
  have cast (i : ℕ) : (a i:ℤ)=f (D+1+i)+8192 := Int.toNat_of_nonneg (hnn i)
  have room (i : ℕ) : a i<2^15 := by
    have hj:=le_abs_self (f (D+1+i));have he:=hf (D+1+i)
    exact_mod_cast (show (a i:ℤ)<(2^15:ℕ) by rw [cast];norm_num;omega)
  rw [highBase,highPositive,highUnits,accumulate_spec,accumulate_spec,mul_sum,← sum_sub_distrib,
    ←sumShift 0 (B/(D+1))]
  simp only [Nat.sub_zero,Nat.zero_add]
  apply sum_congr rfl
  intro j _
  rw [ht,input_spec,positive_row 15 tip D K B (j+1) a (by decide) (by omega) room,
    unit_row _ _ _ _ (by omega),mul_sum,←sum_sub_distrib,←sumShift]
  apply sum_congr (by rw [Nat.add_comm j 1])
  intro i _
  rw [factor_power D _ i (by omega),cast,Nat.add_comm j 1]
  ring
end ThetaWide

namespace ThetaWindow
open Finset ThetaWide FR7022Hyperbola
def cutoff (D K t d : ℕ) := max D (min K (t/d))
def column (tip tab d first len : ℕ) : ℕ :=
  let z := (tab >>> (15*first)) &&& (powBit (15*len)-1)
  spread 15 (64*d) tip ((len-1).log2+1) z
def constantColumn (d _first len : ℕ) : ℕ := unit (64*d) (len.log2+1) len
def digitRow (D K off len d : ℕ) (motor : ℕ→ℕ→ℕ→ℕ) : ℕ :=
  let x:=cutoff D K off d
  let y:=cutoff D K (off+len) d
  if x<y then motor d (x-D) (y-x) <<< (64*(d*(x+1)-1-off)) else 0
def window (D K B off len : ℕ) (motor : ℕ→ℕ→ℕ→ℕ) : ℕ :=
  accumulate (fun d=>digitRow D K off len d motor) (B/(D+1)) 1
theorem dropped (s N p : ℕ) (hs : 0<s) (hp : p≤N) (a : ℕ→ℕ) (ha : ∀i,a i<2^s) :
    (word s N a >>> (s*p))=word s (N-p) (fun i=>a (i+p)) := by
  conv_lhs => rw [show N=p+(N-p) by omega,word_split _ _ _ hs]
  rw [Nat.shiftRight_eq_div_pow,Nat.add_mul_div_left _ _ (by positivity : 0<(2:ℕ)^(s*p)),
    Nat.div_eq_of_lt (word_small hs a (fun i _=>ha i)),Nat.zero_add]
def MotorLaw (N : ℕ) (a : ℕ→ℕ) (f : ℕ→ℕ→ℕ→ℕ) : Prop :=
  ∀ d p n, 0<d → p+n≤N → (f d p n:ℤ)=∑ i∈range n,(2:ℤ)^(64*d*i)*(a (p+i):ℤ)
theorem column_law (N tip tab : ℕ) (a : ℕ→ℕ) (ht : tab=word 15 N a) (ha : ∀i,a i<2^15) :
    MotorLaw N a (column tip tab) := by
  intro d p n hd hlen
  let q:=(n-1).log2+1
  have hq : n≤2^q := by have h:=(Nat.lt_log2_self (n:=n-1)); dsimp [q]; omega
  have hb (i : ℕ) : (if i<n then a (i+p) else 0)<2^15 := by split <;> first | exact ha _ | decide
  unfold column
  rw [ht,dropped 15 N p (by decide) (by omega) a ha,
    low_slice 15 n (N-p) (by decide) (by omega) _ (fun i _=>ha _),
    ← word_pad 15 n (2^q) (by decide) hq (fun i=>a (i+p)),
    spread_eq 15 (64*d) tip (by decide) (by omega) _ hb q,
    word_pad (64*d) n _ (by omega) hq,word_cast _ _ (by omega)]
  simp [Nat.add_comm]
theorem one_law (N : ℕ) : MotorLaw N (fun _=>1) constantColumn := by
  intro d p n hd hlen
  simp only [constantColumn,unit_eq _ (show 0<64*d by omega) _ _ Nat.lt_log2_self,
    word_cast _ _ (show 0<64*d by omega)]
def partialSum (D K d t : ℕ) (a : ℕ→ℕ) : ℤ :=
  ∑ k∈Ioc D (cutoff D K t d),(a (k-(D+1)):ℤ)*(2^64:ℤ)^(d*k-1)
theorem row_value (D K off len d : ℕ) (hDK : D≤K) (hd : 0<d) (a : ℕ→ℕ) (mot : ℕ→ℕ→ℕ→ℕ)
    (hm : MotorLaw (K-D) a mot) :
    (digitRow D K off len d mot:ℤ)*(2^64:ℤ)^off=partialSum D K d (off+len) a-partialSum D K d off a := by
  let l:=cutoff D K off d
  let r:=cutoff D K (off+len) d
  have hD : D≤l := le_max_left _ _
  have hK : r≤K := max_le hDK (min_le_left _ _)
  have hl : l≤r := max_le_max_left _ (min_le_min_left _ (Nat.div_le_div_right (by omega)))
  let F (k:ℕ) := (a (k-(D+1)):ℤ)*(2^64:ℤ)^(d*k-1)
  have hun : Ioc D l ∪ Ioc l r=Ioc D r := by ext k;simp only [mem_union,mem_Ioc];omega
  have hdis : Disjoint (Ioc D l) (Ioc l r) := by rw [disjoint_left];intro k hx hy;simp only [mem_Ioc] at hx hy;omega
  have hsum := sum_union (f:=F) hdis
  rw [hun] at hsum
  change (digitRow D K off len d mot:ℤ)*(2^64:ℤ)^off=(∑k∈Ioc D r,F k)-∑k∈Ioc D l,F k
  rw [hsum,add_sub_cancel_left]
  change (↑(if l<r then mot d (l-D) (r-l) <<< (64*(d*(l+1)-1-off)) else 0):ℤ)*_ = _
  split
  · rename_i hlt
    have hdiv : off/d≤l := by
      dsimp only [l,r,cutoff] at hlt ⊢
      omega
    have hx : off<(l+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (by omega)
    rw [Nat.shiftLeft_eq,Nat.cast_mul,hm _ _ _ hd (by omega),sum_mul,sum_mul,←sumShift l r]
    apply sum_congr rfl
    intro i _
    have idx : l-D+i=l+1+i-(D+1) := by omega
    have hx' : off ≤ d*(l+1)-1 := by rw [Nat.mul_comm] at hx;omega
    have exp : 64*(d*(l+1)-1-off)+64*off=64*(d*(l+1)-1) := by
      rw [← Nat.mul_add];congr 1;omega
    dsimp [F]
    rw [idx]
    have hh : (18446744073709551616:ℤ)^off=(2:ℤ)^(64*off) := by
      rw [pow_mul]; norm_num
    rw [hh]
    calc
      _ = ↑(a (l+1+i-(D+1)))*((2:ℤ)^(64*(d*(l+1)-1-off))*(2:ℤ)^(64*off))*(2:ℤ)^(64*d*i) := by ring
      _ = _ := by rw [←pow_add,exp,mul_assoc,factor_power _ _ _ hd]; norm_num
  · have he : l=r := by omega
    simp [he]
end ThetaWindow

namespace ThetaWindow
open Finset ThetaWide FR7022Hyperbola
def cumulative (D K B t : ℕ) (a : ℕ→ℕ) : ℤ :=
  ∑ j∈range (B/(D+1)),partialSum D K (j+1) t a
theorem window_sound (D K B off len : ℕ) (a : ℕ→ℕ) (mot : ℕ→ℕ→ℕ→ℕ)
    (hD : D≤K) (hh : MotorLaw (K-D) a mot) :
    (window D K B off len mot:ℤ)*(2^64:ℤ)^off =
      cumulative D K B (off+len) a-cumulative D K B off a := by
  rw [window,accumulate_spec,sum_mul,cumulative,cumulative,←sum_sub_distrib]
  exact sum_congr rfl (fun i _=>row_value D K off len (i+1) hD (by omega) a mot hh)
theorem cumulative_zero (D K B : ℕ) (a : ℕ→ℕ) : cumulative D K B 0 a=0 := by
  simp [cumulative,partialSum,cutoff]
theorem cumulative_end (D K B : ℕ) (a : ℕ→ℕ) :
    cumulative D K B B a=∑d∈Ioc 0 (B/(D+1)),∑k∈Ioc D (min K (B/d)),
      (a (k-(D+1)):ℤ)*(2^64:ℤ)^(d*k-1) := by
  rw [←sumShift 0 (B/(D+1))]
  simp only [cumulative,Nat.sub_zero,Nat.zero_add]
  apply sum_congr rfl
  intro i _
  unfold partialSum cutoff
  rw [Nat.add_comm i 1]
  apply sum_congr _ (fun _ _=>rfl)
  ext k
  simp only [mem_Ioc]
  omega
structure Tile (f : ℕ→ℤ) (lo size : ℕ) where
  value : ℕ
  valid : (value:ℤ)*(2^64:ℤ)^lo=f (lo+size)-f lo
def join {f : ℕ→ℤ} {lo a b : ℕ} (l : Tile f lo a) (r : Tile f (lo+a) b) : Tile f lo (a+b) where
  value := l.value+(r.value <<< (64*a))
  valid := by
    have hp : (2:ℤ)^(64*a)=(2^64:ℤ)^a := pow_mul 2 64 a
    rw [Nat.shiftLeft_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,hp]
    rw [add_mul,mul_assoc,←pow_add,Nat.add_comm a lo,l.valid,r.valid,Nat.add_assoc]
    ring
def verified {D K B off len : ℕ} {a : ℕ→ℕ} {mot : ℕ→ℕ→ℕ→ℕ}
    (hD : D≤K) (hh : MotorLaw (K-D) a mot) (v : {w : ℕ // w=window D K B off len mot}) :
    Tile (fun t=>cumulative D K B t a) off len where
  value := v.1
  valid := by rw [v.2]; exact window_sound D K B off len a mot hD hh
theorem tile_value (D K B : ℕ) (a : ℕ→ℕ) (t : Tile (fun x=>cumulative D K B x a) 0 B) :
    (t.value:ℤ)=∑d∈Ioc 0 (B/(D+1)),∑k∈Ioc D (min K (B/d)),
      (a (k-(D+1)):ℤ)*(2^64:ℤ)^(d*k-1) := by
  have h:=t.valid
  rw [pow_zero,mul_one,Nat.zero_add,cumulative_zero,sub_zero,cumulative_end] at h
  exact h
end ThetaWindow

namespace ThetaWindow
open Finset ThetaWide FR7022Hyperbola FR7022Flat
theorem packed_ones (s n : ℕ) (hs : 0<s) :
    (powBit (s*n)-1)/(powBit s-1) = word s n (fun _=>1) := by
  have he : (word s n (fun _=>1) : ℤ) = ∑ i∈Finset.range n,((2:ℤ)^s)^i := by
    simpa [pow_mul] using word_cast s n hs (fun _=>1)
  have hn : word s n (fun _=>1) = ∑ i∈Finset.range n,((2:ℕ)^s)^i := by exact_mod_cast he
  have hp : (1:ℕ)<2^s := Nat.one_lt_pow hs.ne' (by decide)
  rw [powBit_eq,powBit_eq,hn,pow_mul]
  rw [←geom_sum_mul_of_one_le hp.le n, Nat.mul_div_cancel _ (by omega)]
theorem packed_scatter_word (s n : ℕ) (f : ℕ→ℕ) (hfit : ∀ i<n, f i<2^22) (hsep : 22*(n+1)<s) :
  (word (s-22) n (fun _=>word 22 n f) &&& word s n (fun _=>2^22-1))=word s n f := by
  let v := s-22
  have hv : 0<v := by dsimp [v]; omega
  have hs : 0<s := by omega
  have hn : 22*n≤v := by dsimp [v]; omega
  have hjoin : v+22=s := by dsimp [v]; omega
  have hpow : (2:ℕ)^22 ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)
  have mask (i : ℕ) (_ : i<n) : (2:ℕ)^22-1<2^s := lt_of_lt_of_le (by decide) hpow
  have out (i : ℕ) (hi : i<n) : f i<2^s := (hfit i hi).trans_le hpow
  have input : word 22 n f < 2^v :=
    (word_small (by decide) _ hfit).trans_le (Nat.pow_le_pow_right (by decide) hn)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  let i:=j/s
  let b:=j % s
  have hb : b<s := Nat.mod_lt _ hs
  have split : s*i+b=j := Nat.div_add_mod j s
  by_cases hi : i<n
  · rw [←split,word_bit hs _ mask i b hi hb,word_bit hs _ out i b hi hb,Nat.testBit_two_pow_sub_one]
    by_cases hlow : b<22
    · have hpos : 22*i+b<v := by omega
      have he : s*i+b=v*i+(22*i+b) := by
        conv_lhs => rw [←hjoin]
        ring
      rw [he,word_bit hv _ (fun _ _=>input) i _ hi hpos,
        word_bit (by decide) _ hfit i b hi hlow]
      simp [hlow]
    · have hz := Nat.testBit_lt_two_pow ((hfit i hi).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hlow)))
      simp [hlow,hz]
  · have hsn : s*n ≤ j := by
      have hh := Nat.mul_le_mul_left s (Nat.le_of_not_gt hi)
      omega
    have hpow2 : (2:ℕ)^(s*n) ≤ 2^j := Nat.pow_le_pow_right (by decide) hsn
    have hm := Nat.testBit_lt_two_pow ((word_small hs _ mask).trans_le hpow2)
    have ho := Nat.testBit_lt_two_pow ((word_small hs _ out).trans_le hpow2)
    simp only [hm,ho,Bool.and_false]
def smallColumn (tip tab d p n : ℕ) : ℕ :=
  let z := (tab >>> (22*p)) &&& (powBit (22*n)-1)
  spread 22 (64*d) tip ((n-1).log2+1) z

theorem smallColumn_law (N tip tab : ℕ) (a : ℕ→ℕ) (ht : tab=word 22 N a) (ha : ∀i,a i<2^22) :
    MotorLaw N a (smallColumn tip tab) := by
  intro d p n hd hlen
  let q := (n-1).log2+1
  have hq : n≤2^q := by have h:=(Nat.lt_log2_self (n:=n-1)); dsimp [q]; omega
  have hb (i : ℕ) : (if i<n then a (i+p) else 0)<2^22 := by split <;> first | exact ha _ | decide
  unfold smallColumn
  rw [ht,dropped 22 N p (by decide) (by omega) a ha,
    low_slice 22 n (N-p) (by decide) (by omega) _ (fun i _=>ha _),
    ← word_pad 22 n (2^q) (by decide) hq (fun i=>a (i+p)),
    spread_eq 22 (64*d) tip (by decide) (by omega) _ hb q,
    word_pad (64*d) n _ (by omega) hq,word_cast _ _ (by omega)]
  simp [Nat.add_comm]
def packedColumn (tip tab d p n : ℕ) : ℕ :=
  if 22*(n+1)<64*d then
    let z := (tab >>> (22*p)) &&& (powBit (22*n)-1)
    let rep (s : ℕ) := (powBit (s*n)-1)/(powBit s-1)
    (z*rep (64*d-22)) &&& ((2^22-1)*rep (64*d))
  else smallColumn (if d≤8 then 15 else if d≤30 then 8 else tip) tab d p n

theorem packedColumn_law (N tip tab : ℕ) (a : ℕ→ℕ) (ht : tab=word 22 N a) (ha : ∀i,a i<2^22) :
    MotorLaw N a (packedColumn tip tab) := by
  intro d p n hd hlen
  by_cases hh : 22*(n+1)<64*d
  · unfold packedColumn
    rw [if_pos hh]
    dsimp only
    rw [ht,dropped 22 N p (by decide) (by omega) a ha,
      low_slice 22 n (N-p) (by decide) (by omega) _ (fun i _=>ha _),
      packed_ones _ _ (by omega),packed_ones _ _ (by omega),word_const,word_const,
      packed_scatter_word _ _ _ (fun i _=>ha _) hh, word_cast _ _ (by omega)]
    simp [Nat.add_comm]
  · simpa only [packedColumn,if_neg hh] using (smallColumn_law N _ tab a ht ha d p n hd hlen)
end ThetaWindow
namespace ThetaWidePinned
open ThetaWide ThetaWindow
def coeff (k : ℕ) : ℤ := ThetaScalar.signs k * (min 8000 (20000-k):ℕ)
theorem coeff_le (k : ℕ) : |coeff k|≤8000 := by
  have sg : |ThetaScalar.signs k|≤1 := by
    unfold ThetaScalar.signs
    generalize ((ThetaScalar.encodedSigns >>> (2*k)) % 4) = v
    rcases v with _|(_|(_|v)) <;> first | exact (by decide : |(0:ℤ)|≤1) | exact (by decide : |(1:ℤ)|≤1)
  rw [coeff,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  calc
    _ ≤ (1:ℤ)*((min 8000 (20000-k):ℕ):ℤ) := mul_le_mul_of_nonneg_right sg (Int.natCast_nonneg _)
    _ ≤ 8000 := by simp
def packedDigit (i : ℕ) : ℕ := 256*(coeff (12001+i)+8192).toNat+1
theorem digit_cast (i : ℕ) : (packedDigit i : ℤ)=256*(coeff (12001+i)+8192)+1 := by
  have hl := (neg_abs_le (coeff (12001+i))).trans' (neg_le_neg (coeff_le _))
  unfold packedDigit
  push_cast
  rw [Int.toNat_of_nonneg (by omega)]
theorem digit_fit (i : ℕ) : packedDigit i<2^22 := by
  have hu := (le_abs_self (coeff (12001+i))).trans (coeff_le _)
  have hc := digit_cast i
  exact_mod_cast (show (packedDigit i:ℤ)<(2:ℤ)^22 by norm_num; omega)
def packedInput : ℕ := build 22 (fun i=>if i<8000 then packedDigit i else 0) 13 0
def sourceValue : ℕ := 0x80000600101800005ffd01800006005017fe805ff901800005ff7017fd80600001800005ff3017fc805ff101800006011017fb805fed01800005feb017fa80601701800006000017f9805fe501800006000017f880601f01800006021017f780600001800005fdb01800005fd901800006029017f580602b01800005fd3017f48060000180000603101800005fcd01800005fcb0180d80603701800006000018000060000180000603d017f0805fc1018000060000181080604301800006045017ee80604701800005fb70180000600001800005fb3017ec80604f01800005faf017eb80600001800005fab017ea805fa9018000060590181680605b0180000605d017e8805fa10180000606101818806063018000060000181980606701800005f9701800005f9501800005f9301800005f9101800005f8f017e3805f8d018000060750181d80600001800006079017e1805f8501800006000017e0805f8101800006081017df805f7d01800005f7b017de805f790180000600001822805f750180000608d0182380608f0180000600001800005f6d01800005f6b01800006097018000060990182680600001800005f63017d8805f6101800005f5f018288060a3018000060a5017d6805f59018000060a90182a8060ab01800006000017d4806000018000060b10182c8060b301800005f4b01800005f4901800005f470182e805f45018000060bd0182f806000018000060c1017cf805f3d018000060c501831805f39018000060c9017cd8060cb01800005f33017cc805f3101800006000017cb805f2d018000060d5017ca805f29018000060d9018000060db01800005f2301837805f210180000600001838806000018000060e5018398060e701800005f170183a805f1501800005f13017c4805f1101800005f0f0183c8060f3018000060000183d805f0901800005f0701800005f050180000600001800005f01018000061010184080610301800005efb017be80600001800006109017bd80610b0180000610d017bc80610f01800005eef017bb8060000180000600001845805ee90180000600001846805ee50180000611d0184780611f0180000612101800005edd01800006125017b6805ed901800005ed70184a80600001800005ed301800005ed101800006131017b380613301800005ecb0184d80613701800005ec70184e805ec501800006000017b0805ec10180000614101850805ebd018000060000180000614701800005eb701852805eb50180000614d018538060000180000600001854805ead018000061550185580615701800006159017a980615b0180000615d0180000600001800006000018588061630180000616501859806167018000061690180000616b01800005e930185b80616f018000061710185c80600001800006175017a280600001800005e870185e80617b0180000617d017a0805e8101800006181018608061830180000600001861805e790180000618901862805e7501800005e730180000618f01800005e6f0179b805e6d018000061950179a80600001800005e670186680619b0180000619d0179880619f01800005e5f01868805e5d018000061a501869805e59018000060000186a80600001800005e530186b805e51018000061b1018000061b3018000061b50186d8061b701800005e470186e806000018000061bd01790805e4101800006000018000061c3018000061c50178e805e3901800005e370178d805e3501800006000018738061cf018000061d101874805e2d01800005e2b018000061d701800005e2701789806000018000061dd01788806000018000061e1017878061e301800005e1b01786805e19018000061e901785805e1501800005e1301784805e110180000600001800005e0d01800005e0b0187d805e0901800005e07018000061fb01800005e0301780805e01018000062010188080600001800005dfb0188180600001800005df701882805df5018000060000188380620f01800005def0177b805ded0180000600001885805de901800005de701779805de501800005de301800005de101800005ddf01777806000018000062250180000600001800005dd70188a80622b0180000622d0188b805dd1018000062310188c806233018000060000188d805dc9018000060000188e805dc501800005dc30177080600001800005dbf01800005dbd0180000624501891805db901800005db70176d80600001800005db30189380624f018000062510176b80625301800005dab0176a805da90180000625901896805da50180000600001897805da101800005d9f01898805d9d01800005d9b018000062670180000626901765805d9501800005d930189b8060000180000600001763805d8d01800005d8b0189d8062770180000627901761805d85018000060000189f80627f01800006000018a080628301800006000018a1806287018000062890180000628b0180000628d0175c805d71018000060000175b80600001800006295018a580629701800005d6701759805d650180000629d01758805d6101800005d5f0175780600001800006000018a980600001800005d5701755805d55018000062ad01800005d5101800005d4f01753805d4d018000062b501800006000018000062b901751805d4501800005d43018af8062bf01800005d3f0174f805d3d018000062c5018b1805d3901800006000018b28062cb018000062cd0174c8062cf018000062d1018000062d3018000060000174a805d29018000062d9018b680600001800005d23018000062df018000062e1018b8805d1d01800005d1b018b9806000018000062e9017458062eb0180000600001800005d11018000062f1018bc805d0d018000062f5018000062f701800006000018be805d05018000062fd0174080600001800005cff018c0805cfd01800006305018c1806000018000063090173d805cf501800005cf30173c80630f018000060000173b805ced01800005ceb018c5805ce901800005ce701800005ce501800005ce3018c7805ce1018000063210173780600001800005cdb018c980632701800006329018ca80632b0180000632d01734805cd101800005ccf018cc805ccd018000060000173280633701800006000018ce80633b0180000633d0180000633f018000063410180000634301800005cbb018d180600001800006000018d2805cb501800005cb30172c80634f0180000635101800005cad018000063550172a805ca90180000600001729805ca501800005ca30172880635f01800005c9f0180000600001800005c9b01726805c9901800006369017258060000180000636d01724805c9101800006371018000063730180000637501722805c89018000063790180000637b018000060000172080637f01800006381018e0806383018000063850180000600001800006389018e280638b0180000638d018e380600001800005c6f0171b805c6d01800006395018e5805c6901800005c67018e680639b0180000600001800005c610180000600001717805c5d018000063a5018e98063a7018000063a901800006000018000063ad01714805c5101800005c4f0171380600001800005c4b018000063b701800005c4701711805c45018000063bd018ef805c41018000063c1018f0805c3d018000060000170e8063c701800005c37018f28063cb018000063cd0180000600001800005c2f018f48063d3018000063d50170a806000018000063d901709805c25018000063dd01708805c21018000063e1018f88063e3018000063e501706805c1901800006000018fa80600001800005c13018fb805c11018000063f1018000063f3018000063f5017028063f7018000063f9018fe80600001800005c03017008063ff01800006000016ff805bfd0180000640501901806407018000064090190280640b01800006000016fc80640f01800005bef01904805bed01800005beb01800006417018000064190180000641b01800005be30190780600001800006421016f7805bdd01800005bdb016f680642701800005bd70190a80642b0180000642d0190b80642f018000060000190c806000018000064350190d80643701800005bc701800005bc50180000643d01800005bc101800005bbf0191080600001800005bbb01911805bb901800006449016ed80644b01800005bb3016ec80644f018000064510191480645301800006000016ea80645701800005ba701916805ba50180000645d0180000645f0180000646101918806463018000060000191980600001800006469016e5805b9501800005b930191b806000018000064710191c80647301800005b8b0191d80647701800006000016e180647b0180000647d01800005b81018000064810180000648301800005b7b0192180648701800005b77019228060000180000648d0192380648f0180000649101924806493018000064950192580600001800006499016d9805b65018000060000180000649f01800005b5f016d78064a3018000064a5018000064a7018000064a90192a8064ab01800005b530192b806000018000064b10192c805b4d018000064b50192d805b4901800005b47016d18064bb01800005b430192f80600001800006000019308064c3018000064c5016ce805b390180000600001800005b35018000064cd016cc80600001800006000016cb806000018000064d5019358064d701800006000016c9805b2501800006000019378064df018000064e101800005b1d0180000600001939805b1901800005b170193a8064eb018000064ed018000064ef01800005b0f0193c805b0d01800005b0b016c2806000018000064f9016c1806000018000060000193f8064ff01800005aff01800005afd01800005afb016be805af901800006000016bd80650b0180000650d016bc80650f0180000651101800005aed01800005aeb0194580651701800006519016b980600001800005ae3016b880651f0180000652101948805add01800005adb01949805ad901800005ad70194a80652b018000060000194b80652f01800005acf016b38060000180000653501800006537018000065390194e805ac50180000653d016b080600001800006541016af8065430180000654501800006547018000065490195280654b0180000654d0195380654f0180000600001954805aad0180000655501800006557018000065590180000655b01800005aa3016a880600001800006561019588060000180000656501959805a9901800006569016a580656b0180000656d016a480656f018000065710195c80600001800006000016a2805a8901800006579016a180657b0180000657d01800005a81018000065810180000658301800005a7b0196180600001800005a770196280658b01800005a730169c80658f018000060000169b805a6d01800006000019658065970180000600001966805a650180000659d01967805a61018000065a101800005a5d01800005a5b01969805a59018000065a901800006000018000065ad0196b8065af01800005a4f01693805a4d01800005a4b0196d805a4901800005a47016918065bb018000060000196f8065bf018000065c10168f80600001800005a3b01800005a39018000065c90168d805a350180000600001973806000018000065d1019748065d301800005a2b0168a8065d701800005a2701800005a25018000065dd016888065df0180000600001687805a1d01800006000018000065e701800005a17018000065eb01800005a130197b805a11018000065f10197c806000018000060000168280600001800005a0701681805a05018000065fd01680805a0101800006601019808059fd018000060000167e8059f9018000066090198280660b018000059f30180000660f018000066110167b806613018000059eb01985806000018000059e70198680661b018000059e3016788059e10180000662101988806623018000059db0198980600001800006000016758060000180000662d0198b8059d1018000059cf018000059cd018000060000198d806637018000066390198e806000018000059c3016708059c101800006641019908059bd018000059bb0166e80664701800006649019928059b5018000060000166c80664f01800006651019948059ad018000059ab018000059a9018000060000199680665b018000059a3019978060000180000599f01667806663018000066650199980599901800006669016658059950180000666d016648059910180000600001800006673018000066750199d80598901800005987018000059850180000667d0166080667f0180000597f0165f806000018000066850165e80597901800005977018000060000180000668d019a380597101800006691019a480669301800006000019a580596901800005967016598059650180000596301800005961018000066a1019a880595d018000066a501656806000018000066a9016558066ab018000066ad019ab8059510180000594f016538066b3018000066b5019ad8066b701800006000019ae80600001800006000019af8066bf018000060000180000593d018000066c5019b1805939018000066c90164d80600001800006000019b38059310180000592f019b480592d0180000592b018000066d7018000066d90164980592501800006000016488059210180000591f016478066e30180000591b018000059190180000591701645805915018000066ed016448060000180000590f0164380590d018000066f5019bd805909018000066f90164180590501800005903019bf8066ff01800006000019c08058fd018000067050163e806707018000058f70180000670b018000058f30163c8058f1018000058ef019c480600001800006715019c580671701800006719019c68058e501800006000016388058e101800006000019c880672301800006000019c98058d9018000067290163580672b0180000672d018000058d10180000673101633806733018000067350163280600001800006739018000058c5018000058c3016308058c1018000058bf0162f806743018000058bb0162e80674701800006000019d28058b5018000058b30180000674f018000058af01800006000018000058ab019d58058a9018000058a7019d68060000180000675d0162880675f018000067610162780589d018000067650162680676701800006769019da80676b01800006000019db805891018000067710162380588d018000067750180000588901800006779019de80677b01800006000019df80600001800006781019e080587d018000060000161e80587901800006789019e2805875018000058730161c80678f018000060000161b80586d0180000586b019e5805869018000058670180000679b01800005863018000058610180000585f016178060000180000585b019e980585901800005857016158067ab018000067ad016148067af0180000584f019ec80600001800006000019ed806000018000067b9019ee8067bb018000067bd018000067bf0180000583f019f080583d0180000583b0160e806000018000067c90160d80583501800005833019f38067cf018000067d1019f480582d0180000582b0160a8067d701800006000019f680582501800005823018000067df018000060000180000581d0180000581b0160680581901800006000019fa80600001800005813019fb8058110180000580f016038067f30180000580b016028067f701800005807019fe80580501800006000016008067ff01800006801018000057fd01800006805018000057f90180000680901a028057f5018000057f301a03806000018000057ef01800006813018000057eb01a058057e9018000057e701a06806000018000057e301a078057e101800006000018000057dd01800006825018000057d9018000057d7018000057d5018000057d3015f480682f018000057cf01a0c8060000180000683501a0d806837018000057c7015f180683b018000057c3015f08057c10180000684101a108060000180000600001a118057b901800006849015ed8057b5018000060000180000684f01800006851015eb8068530180000685501a15806000018000057a701a1680685b0180000685d01a1780685f01800006861015e780579d0180000579b018000068670180000600001a1a8057950180000686d015e48057910180000578f0180000578d01800006875015e280687701800006879015e180600001800005783015e08060000180000577f01a2080688301800006885015de80688701800005777015dd80688b0180000600001a2380688f0180000576f015db80576d018000068950180000689701800005767015d98060000180000689d01a278060000180000575f01a2880575d0180000600001a298068a701800005757015d58068ab018000068ad015d48068af0180000600001a2c8068b3018000068b5015d28068b7018000068b9018000068bb01800005743015d08057410180000573f015cf8060000180000573b01a318068c7018000057370180000573501800005733015cc806000018000068d1015cb8068d30180000600001800005729018000068d901a3680572501800005723018000057210180000571f01a38806000018000068e501a3980600001800005717015c58068eb01800005713015c4805711018000068f1015c38068f30180000570b01a3d8068f701800006000015c18068fb018000068fd01a3f80570101800006901018000069030180000690501a4180600001800006909015bd806000018000056f301a438056f1018000056ef01a448069130180000600001a458056e901800006919015b98056e5018000060000180000691f0180000692101a48806000018000056db018000056d90180000692901a4a80692b0180000692d018000060000180000693101a4c8069330180000693501a4d8056c90180000693901a4e80693b0180000693d015b08056c10180000600001a50806000018000056bb015ae806000018000056b70180000694b018000056b3015ac80694f018000056af01a548060000180000695501a558056a90180000695901a568056a50180000695d015a880695f0180000569f01a5880569d01800006000015a680696701800006000015a580696b0180000696d0180000696f01800006971015a380568d0180000568b01a5d8060000180000600001a5e8056850180000697d01a5f8056810180000698101a6080567d0180000567b0159e8069870180000600001a6280698b0180000698d0159c80698f0180000566f0180000566d018000069950159a80600001800006999018000060000180000566301a67805661018000069a1015978069a3018000069a5015968069a7018000069a901a6a8060000180000600001a6b8069af0180000564f015938069b30180000564b018000069b70180000564701a6e8056450180000564301a6f806000018000069c10158f80563d0180000563b0158e805639018000069c901a72806000018000056330158c805631018000060000158b80562d0180000562b01a758069d701800005627018000056250180000600001a778069df0180000561f015878060000180000561b01a79805619018000069e901a7a8069eb0180000561301a7b806000018000069f1015838069f30180000600001800005609018000069f901a7e80560501800005603018000069ff01800006a0101a808055fd018000055fb0157e806000018000055f70157d806a0b018000055f301a83806000018000055ef0157b806a13018000055eb0157a8055e90180000600001a86806a1b01800006a1d015788055e1018000060000180000600001800006a2501a898055d901800006a2901a8a8060000180000600001a8b8055d101800006a3101a8c8055cd018000055cb01a8d806a37018000055c7015718055c50180000600001a8f8055c10180000600001a90806a4301800006a4501800006a47018000055b70156d8055b501800006a4d01a93806000018000055af01a94806a5301800006a5501a958055a9018000055a701800006a5b018000055a301800006a5f0180000600001a9880559d01800006a6501a99806a6701800006a690180000559501800005593015648055910180000558f01a9c80600001800006a7501562805589018000055870156180558501800006a7d0156080558101800006a8101aa0806a83018000060000155e806a87018000060000155d80557501800005573018000060000180000556f01aa480556d0180000556b0155a80600001800006a9901aa6806a9b0180000556301aa7806a9f01800006aa10155780555d0180000600001556806aa70180000600001aaa806aab01800006aad0155480555101800006ab101800006ab30180000554b01aad80554901800006ab901aae80600001800006abd01800006abf01800006ac101ab0806ac301800006ac50154e8055390180000553701800006acb018000060000154c806acf0180000552f0154b806ad30180000552b0180000600001800006ad901549806adb01800006add01ab78060000180000551f01ab8806ae301800006ae5015468055190180000551701545806aeb0180000551301abb806aef0180000600001abc806af30180000550b01abd80550901800005507018000055050180000550301540805501018000054ff0180000600001800006b0501ac1806b07018000060000153d806b0b018000054f301ac38054f1018000054ef0153b806b130180000600001ac5806000018000054e701539806b1b018000054e301800006b1f01800006b2101800006b2301800006b2501ac9806000018000054d701535806b2b018000054d301acb8054d1018000054cf01533806b3301800006b3501acd806b370180000600001ace806000018000054c3015308054c1018000054bf018000054bd01800006b450152e806b4701800006b4901ad2806000018000054b30152c8054b101800006b510152b806000018000054ab0152a8054a9018000054a7015298054a50180000600001528806b5f01800006b6101ad8806b6301800006b650180000549901800006b6901ada8054950180000600001adb80600001800006b7101adc80600001800006b7501add806b7701800006b790152180600001800006b7d01520806b7f0180000600001ae080547d0180000600001800006b87018000054770180000547501800006b8d01ae380547101800006b910151b80600001800006b9501ae58054690180000546701ae68054650180000546301ae780600001800006ba10151780545d0180000600001516806ba701800005457015158054550180000545301800006baf01800006bb10151380544d0180000600001aed80600001800006bb901511806bbb01800006bbd0151080544101800006bc10150f80543d0180000543b01af1805439018000060000150d805435018000054330150c806bcf0180000600001800006bd301800006bd50150a806bd701800006000015098060000180000542301af7806bdf01800006be101507806be301800006be501800006be70180000541701800006beb0180000600001504806bef0180000540f01503806bf301800006bf5018000054090180000540701afe8054050180000540301500806000018000053ff014ff80600001800006c0501b018053f901800006c09014fd806c0b018000053f3014fc806c0f0180000600001b04806c13018000053eb014fa806000018000053e7018000053e5018000053e301b07806c1f018000053df01b08806000018000053db01b098053d9018000053d701b0a8053d5018000053d3014f48053d1018000053cf01b0c806c330180000600001b0d806c37018000053c701b0e806c3b01800006c3d01800006c3f01800006c4101b10806c4301800006c4501b1180600001800006c4901800006c4b018000053b3018000053b101800006c5101b148053ad018000053ab01b15806c570180000600001b16806c5b01800006c5d014e88053a10180000539f0180000539d0180000539b014e680600001800005397014e580600001800006000014e4806c6f01800006c71014e380538d0180000538b0180000538901800006000014e1806c7b01800006000014e0806c7f01800006c81014df80537d01800006c8501800006c870180000537701b22806c8b0180000537301b2380600001800006c91014db806c9301800006c9501b25806c970180000600001b26806c9b01800006c9d014d8806c9f01800006000014d780535d0180000535b018000053590180000535701800006cab0180000535301b2b806caf01800006cb1018000060000180000534b014d280534901800006cb9014d180534501800006cbd01b2f80534101800006cc1014cf806cc30180000600001b3180533901800006cc901b3280600001800006ccd01800006ccf01800006cd1014cb806cd301800006cd5014ca80600001800006cd901b3680600001800006cdd01b378053210180000531f014c780531d0180000531b01800006ce701800006000014c580531501800005313014c4806cef0180000530f0180000530d0180000530b014c2806cf701800006cf9014c18060000180000600001b3f80530101800006d01014bf806d0301800006d05014be806d0701800006d09014bd8052f50180000600001b438052f101800006d11014bb806d13018000052eb018000052e9018000052e701b46806d1b018000052e3014b880600001800006d2101b48806d23018000052db01b498052d9018000052d7014b58052d501800006d2d01b4b8060000180000600001b4c806d33018000052cb014b28052c901800006d3901800006d3b0180000600001b4f806d3f018000052bf01800006000018000052bb014ae806d47018000052b7014ad806d4b01800006d4d01b53806d4f01800006d51014ab806d530180000600001b558052a9018000052a701b56806d5b01800006d5d018000060000180000600001b5880529d01800006d65014a68060000180000529701b5a806d6b01800006d6d0180000529101800006d71014a3806d7301800006d7501b5d80528901800006000018000052850180000528301b5f80528101800006d810180000527d0180000527b01b61806d8701800006d890149d80600001800006d8d0149c8052710180000526f01b648060000180000526b0149a806d970180000526701499806d9b01800006000014988060000180000525f01b68806da301800006da501800006da701800006da901495806dab01800006dad0149480600001800006db10149380524d0180000524b01b6d806db70180000524701b6e806dbb01800006dbd01b6f8052410180000600001b7080523d0180000600001b718060000180000523701800006dcb0180000523301b7380523101800006dd101b7480600001800006dd501b75806dd701800005227014898052250180000522301800006ddf0180000521f01487806de30180000600001b79806de701800006de901b7a806deb018000052130180000521101800006df101b7c806df30180000520b0148280600001800006df9014818052050180000520301b7f805201018000060000147f806e03018000051fb01b81806e07018000060000147d8051f501800006e0d0147c806e0f0180000600001800006e13018000051eb0147a80600001800006e1901b8680600001800006e1d014788051e1018000051df01b888051dd01800006e25014768051d90180000600001475806e2b01800006000014748051d101800006e31018000051cd018000051cb018000051c901800006e3901b8e806e3b01800006e3d01b8f80600001800006e41018000051bd01800006e450146e8051b901800006e4901b928051b5018000051b301b938060000180000600001b948051ad01800006e5501b95806e5701800006e590180000600001800006e5d01b97806e5f0180000519f014678060000180000519b01466806e6701800006e6901b9a806e6b01800006e6d014648051910180000518f0146380518d0180000600001462806e7701800006e7901b9e806e7b01800006e7d018000051810180000517f0145f806e8301800006e850145e80600001800006e890145d806e8b018000060000145c80517101800006e910145b806e930180000516b0145a806e97018000060000145980516501800006e9d01458806e9f01800006ea10180000515d01800006ea5018000051590180000515701baa80600001800006ead01454806eaf01800006eb101453806eb30180000514b01bad8051490180000514701bae8051450180000600001baf8060000180000513f01bb0806ec3018000060000180000513901800006ec901800006ecb018000051330144c80600001800006ed101bb480512d0180000512b01bb5806ed701800006ed901bb6806edb0180000512301448805121018000060000144780511d0180000511b01bb9806ee70180000511701800006eeb01800006eed01bbb806eef0180000600001bbc80600001800006ef501800005109018000051070144180510501800006efd01bbf806eff018000050ff0143f806f03018000060000143e806f0701800006f09018000050f501800006f0d01800006f0f01800006f110143b8050ed018000050eb01bc5806000018000050e7014398050e5018000050e301438806000018000050df0143780600001800006f25014368060000180000600001bca806f2b018000050d3014348050d1018000050cf01800006f3301800006f3501bcd806f37018000050c70143180600001800006f3d014308050c101800006f410142f806000018000050bb0142e8050b9018000050b701bd2806f4b0180000600001bd3806f4f01800006f5101bd48050ad01800006000018000050a9018000050a7014298050a5018000050a3014288060000180000509f0142780509d0180000509b01bd98050990180000600001425806f6b01800006f6d01800006f6f0180000600001423806f7301800006f7501422806f7701800006f79018000050850180000508301bdf8050810180000507f01be08060000180000507b0141e8060000180000600001be2806f8b01800006f8d01be380507101800006f9101be4806f93018000060000141a806f970180000506701419806f9b01800006f9d0180000506101800006fa101417806fa30180000505b014168060000180000505701415806fab0180000600001beb80505101800006fb10141380504d0180000600001412806fb701800006000018000050450180000504301410806fbf01800006fc10180000503d0180000503b0140e806fc7018000050370140d80600001800006fcd0140c8050310180000502f01800006fd301800006fd501bf580502901800006fd901409806fdb018000060000140880502101800006fe10140780501d01800006fe501800006fe701800006fe901bfa80600001800005013014048060000180000500f01bfc806ff30180000500b0140280500901800006ff901bfe806ffb0180000500301bff806fff0180000600001c00804ffd0180000700501c01804ff9018000060000180000700b0180000700d01c03804ff101800004fef0180000600001800007015013fa804fe901800004fe7013f9804fe50180000600001c0780701f01800007021018000070230180000600001c09804fd90180000702901c0a804fd501800004fd30180000702f0180000703101c0c807033018000060000180000600001800004fc701c0e80703b0180000703d01800004fc10180000704101c1080704301800007045013ee80704701800006000013ed80704b01800006000013ec80600001800004faf0180000705301800007055013ea804fa90180000705901c168060000180000705d013e8804fa101800004f9f013e7804f9d01800004f9b01c19804f9901800004f97013e5804f9501800006000013e480706f01800004f8f013e3804f8d01800004f8b0180000707701800007079013e180707b0180000707d018000060000180000600001c20804f7d01800004f7b01c2180708701800004f7701c22804f750180000708d01c23804f710180000600001c2480709301800004f6b01c25804f690180000709901800004f6501800004f6301c27804f6101800004f5f013d780600001800004f5b01c29804f5901800004f5701c2a804f5501800004f530180000600001800004f4f013d380600001800006000013d28070b7018000070b9013d180600001800004f43018000070bf018000070c1013cf8070c3018000070c501c31806000018000070c9013cd8070cb018000070cd013cc8070cf01800004f2f01c348070d301800004f2b01c358070d70180000600001c368070db01800004f2301c378070df01800004f1f018000070e301800006000013c68070e701800004f17013c580600001800004f1301c3b804f1101800004f0f013c3804f0d018000070f501c3d804f0901800004f07013c18070fb0180000600001800004f0101800004eff01c4080710301800004efb01800004ef901800004ef7013bd80710b01800004ef301c438060000180000600001c44804eed01800007115013ba80600001800007119013b9804ee501800004ee301c47804ee101800006000013b78071230180000712501c4980600001800004ed70180000712b01800004ed3013b4804ed101800007131013b38060000180000713501c4d80713701800007139013b1804ec501800004ec301c4f804ec101800004ebf01800004ebd0180000600001c5180714701800006000013ad804eb50180000714d01800004eb101800007151013ab804ead01800007155013aa80600001800004ea7013a980715b0180000715d01c5780715f01800004e9f01800004e9d01800007165013a680716701800006000013a5804e950180000716d013a480716f01800004e8f0180000600001800004e8b013a280717701800004e87013a18060000180000600001c5f804e8101800004e7f01c6080718301800004e7b01c6180718701800004e770139d80718b0180000600001c63804e71018000071910139b8071930180000719501800004e6901800004e6701399804e650180000719d01398806000018000071a101c68804e5d01800004e5b01c698071a7018000071a9013958071ab0180000600001394804e5101800006000013938071b301800004e4b01c6d804e490180000600001800004e45018000071bd01390804e4101800004e3f01c7080600001800004e3b018000071c701800004e3701c728071cb01800004e330138c8071cf01800004e2f01c748071d30180000600001c75804e29018000071d901389804e2501800004e230180000600001800004e1f013878071e3018000071e501386806000018000071e901c7a804e1501800004e1301c7b8071ef01800004e0f01c7c8071f3018000071f501c7d804e090180000600001c7e8071fb018000071fd01380804e0101800004dff0180000720301800004dfb01800004df901800004df701c828060000180000600001c83804df10180000600001c84804ded0180000721501c85804de90180000600001c86804de50180000600001c87804de101800004ddf0137780722301800004ddb018000072270180000722901800004dd50180000722d01c8b80600001800007231013738060000180000723501c8d8060000180000723901c8e804dc501800004dc301370804dc1018000060000136f80600001800004dbb0136e80724701800004db70180000600001800004db301c93804db1018000072510136b80600001800004dab0136a8072570180000725901369804da501800004da301c9780725f01800007261013678072630180000600001c99804d9901800004d9701c9a804d9501800004d9301800004d9101800004d8f01c9c804d8d018000060000136280600001800004d8701c9e804d8501800004d8301360804d8101800004d7f0135f80728301800004d7b0135e804d79018000060000135d80728b0180000728d0180000728f01800007291018000072930180000729501ca5804d69018000060000135980600001800004d6301358804d61018000072a1013578072a301800004d5b01356806000018000072a901caa8072ab0180000600001354804d5101800004d4f01cac804d4d01800004d4b018000072b701800004d4701cae8072bb018000072bd0135080600001800004d3f01cb0804d3d01800004d3b0134e804d39018000072c901800004d3501800004d330134c8072cf0180000600001cb4804d2d018000072d501cb58072d70180000600001800004d2501800004d2301cb7804d21018000072e101cb8806000018000072e501800004d1901800004d1701cba8072eb01800004d1301cbb8072ef018000072f101800004d0d0180000600001cbd804d09018000072f90134180600001800004d0301800004d0101800004cff01cc080730301800004cfb01cc1806000018000073090133d8060000180000600001cc3804cf10180000731101cc48073130180000731501cc5804ce9018000060000133980731b01800004ce301cc780731f0180000732101800004cdd01800004cdb01cc98073270180000732901cca80600001800004cd301ccb80732f01800004ccf01333804ccd01800004ccb01ccd804cc90180000733901cce804cc50180000600001ccf804cc10180000734101cd080734301800004cbb01800004cb9018000073490132d804cb50180000600001cd38060000180000735101cd4804cad01800004cab018000073570180000735901cd680735b0180000600001cd7806000018000060000132780736301800004c9b01cd980736701800004c9701800004c950180000736d013248060000180000737101cdc8060000180000737501322804c8901800004c8701cde804c850180000737d01cdf80737f0180000738101ce0807383018000060000131e8073870180000738901ce280738b0180000738d01800004c7101800004c6f0131b807393018000073950131a80600001800004c6701ce680739b0180000739d01ce780739f0180000600001ce88073a3018000073a501ce9804c590180000600001315804c55018000073ad01ceb8073af018000073b101800004c4d01800004c4b01ced8073b701800004c470180000600001800004c4301cef80600001800004c3f0130f8073c301800004c3b01cf1804c3901800004c3701cf28073cb018000060000130c804c3101800004c2f0130b80600001800004c2b018000073d7018000073d901cf68073db01800004c2301cf780600001800004c1f013078073e3018000073e501306804c19018000073e901cfa8073eb018000073ed01cfb804c1101800006000013038073f301800004c0b01302804c0901800004c0701800004c0501800006000013008073ff01800004bff012ff8060000180000600001d0180740701800007409012fd804bf501800004bf301d03804bf101800007411012fb804bed0180000600001d0580741701800007419012f980741b01800004be30180000741f01800006000012f780742301800004bdb012f680600001800004bd7012f580742b0180000742d01d0b804bd101800004bcf012f380743301800004bcb01d0d8060000180000600001d0e804bc501800004bc3012f0804bc10180000744101800004bbd01800007445012ee80744701800004bb7012ed8060000180000744d012ec8060000180000745101800004bad01800004bab012ea80745701800007459012e980745b0180000600001d1780745f01800004b9f012e7804b9d01800004b9b0180000746701800006000012e5804b9501800004b9301d1b80600001800004b8f01d1c807473018000074750180000747701800004b87012e180747b01800004b83012e0804b81018000060000180000600001800004b7b012de804b790180000748901800004b750180000600001d23804b7101800004b6f012db80600001800004b6b01d25804b6901800007499012d980600001800004b63012d8804b61018000074a101d28804b5d01800006000012d6804b59018000074a9012d58074ab01800004b5301800004b510180000600001d2c8074b301800004b4b01d2d806000018000074b901d2e8074bb01800004b4301d2f8074bf018000074c1012cf8074c301800004b3b012ce8074c701800006000012cd8074cb0180000600001d33804b31018000074d101800004b2d018000074d501d35804b2901800004b2701d36806000018000074dd01d37804b2101800004b1f012c7804b1d0180000600001800004b19018000074e9012c5804b150180000600001d3b80600001800004b0f012c38074f3018000074f501800004b09018000074f9012c1804b0501800004b03012c080600001800007501012bf804afd01800004afb01d4180750701800004af701d4280750b0180000750d01d4380750f01800006000012bb804aed0180000751501800004ae9018000075190180000751b0180000751d01d47804ae101800004adf012b780600001800007525012b680752701800007529012b580752b0180000752d012b4804ad10180000600001d4c804acd0180000600001d4d8075370180000753901d4e804ac501800004ac301800004ac101800004abf012af804abd01800004abb012ae80600001800004ab701800004ab501800004ab3012ac80754f01800004aaf012ab804aad01800004aab012aa804aa90180000600001800004aa50180000755d012a8804aa1018000075610180000600001800004a9b012a680756701800004a9701d5a8060000180000756d01d5b80756f01800004a8f012a38075730180000757501d5d804a8901800004a87012a180757b01800006000012a0804a8101800004a7f01d608075830180000758501800004a7901800004a7701d6280758b0180000758d0129c80600001800004a6f01d648075930180000600001d65807597018000075990129980759b01800004a6301298804a610180000600001297804a5d018000075a501d69804a5901800006000018000075ab018000075ad01800004a5101800004a4f0129380600001800004a4b01d6d8075b7018000075b901d6e804a45018000075bd01290804a4101800004a3f0128f8075c30180000600001d7180600001800004a3701d728075cb01800004a33018000075cf0180000600001d74804a2d01800004a2b01d7580600001800004a2701800004a25018000075dd01288804a2101800006000012878075e3018000075e5012868075e70180000600001285804a1501800004a1301d7b8075ef018000075f1018000075f3018000075f501d7d8075f70180000600001d7e806000018000075fd01d7f804a01018000076010127f806000018000076050127e807607018000076090127d8060000180000600001d8380760f0180000761101800007613018000049eb018000049e9018000049e7012798049e50180000761d01278806000018000049df01277807623018000049db012768049d9018000049d701d8a806000018000049d3012748049d10180000600001d8c807633018000049cb012728049c9018000076390180000763b018000049c30127080763f018000049bf01d90806000018000076450126e806000018000049b70126d8049b50180000764d0126c8049b1018000049af0126b807653018000060000126a8049a9018000076590180000765b018000060000180000765f0180000499f012678076630180000766501266806000018000076690126580766b0180000600001d9b80766f0180000767101d9c8076730180000498b01800004989018000060000126180767b0180000498301d9f8049810180000768101800007683018000076850125e807687018000049770125d8060000180000768d0125c8060000180000496f0125b80496d0180000769501da58049690180000769901da680769b018000060000180000769f0180000495f01da880495d018000076a5018000076a7018000076a9012558049550180000495301254806000018000076b1012538076b3018000076b5012528076b7018000076b901251804945018000076bd01daf804941018000060000124f80493d018000076c501db18076c7018000076c9018000076cb018000076cd0124c8060000180000492f01db48060000180000492b01db5804929018000049270180000492501800004923012488076df0180000491f012478076e30180000600001db98076e70180000491701245804915018000076ed018000076ef0180000490f01243806000018000076f501242806000018000076f901dbe8076fb0180000490301dbf8076ff0180000770101dc0807703018000048fb0123e807707018000060000123d80770b0180000770d01dc38048f10180000771101800007713018000077150123a807717018000048e701dc6806000018000048e3012388048e10180000600001dc88077230180000600001236807727018000048d70123580772b01800006000012348048d101800006000012338048cd01800007735018000048c9018000048c701dce8048c5018000048c301800006000018000077410122f806000018000048bb01dd18077470180000774901dd280774b018000048b30122c8048b10180000600001dd48048ad0180000600001dd5806000018000077590180000775b0180000775d0122880775f01800007761018000060000180000489b01dd9804899018000077690122580776b0180000489301ddb8048910180000488f0122380488d0180000600001ddd807777018000077790122180777b0180000777d0180000777f0180000487f01de080487d018000077850121e8060000180000600001de280778b0180000778d01de380778f0180000486f01de48060000180000486b01de5807797018000060000121980779b0180000779d01de780779f018000077a10180000485d018000077a5012168077a7018000077a901dea806000018000077ad01deb8048510180000484f01dec80484d0180000484b01ded8077b7018000077b901dee8060000180000600001def804841018000077c101df08077c30180000600001800004839018000077c901df28077cb018000048330120c8060000180000482f01df480482d0180000482b01df58077d70180000482701df6804825018000077dd01df780482101800006000012078077e30180000481b01206804819018000048170180000481501800006000012048048110180000480f01dfc8060000180000600001202804809018000077f9012018077fb0180000480301800004801018000047ff011ff80780301800006000018000078070180000780901e0280780b0180000780d018000047f1018000047ef01e048078130180000781501e05806000018000047e701e068047e5018000047e3011f88060000180000782101e088047dd01800007825018000078270180000600001e0a80782b0180000782d011f480782f018000047cf018000047cd018000047cb011f2807837018000047c701e0e806000018000047c30180000783f0180000784101e108047bd01800007845011ee8047b9018000047b7011ed8047b5018000060000180000784f01800006000011eb8078530180000785501800006000018000047a701e1680785b018000047a3011e88060000180000479f011e780479d0180000786501800007867018000047970180000786b0180000786d01e1b80786f0180000600001e1c80478d0180000787501e1d804789018000047870180000787b01800004783011e08047810180000477f01e208060000180000477b011de80477901800004777018000047750180000477301e238047710180000476f01e2480476d0180000600001e258078970180000789901e2680789b0180000476301800004761018000078a1011d780475d0180000475b0180000600001800004757011d58078ab018000078ad01e2b8047510180000474f011d380474d0180000600001e2d80600001800006000011d1804745018000078bd01e2f804741018000078c1018000078c30180000473b01e318078c7018000078c901e328060000180000473301800004731018000078d101e348078d3018000078d5011ca8078d7018000078d9011c98078db01800006000011c8804721018000078e101e388078e30180000471b0180000600001800004717018000078eb01800004713011c48060000180000470f011c380470d0180000470b011c28078f7018000078f901e3e804705018000078fd011c080470101800006000011bf8046fd01800007905011be8046f9018000046f70180000790b018000046f301e4380790f0180000600001e448060000180000791501e458046e901800006000011b98060000180000791d01e4780791f018000046df011b78079230180000600001e49807927018000046d701e4a80792b0180000792d018000046d10180000793101800007933018000046cb011b28060000180000793901e4e80793b0180000793d011b08046c101800007941011af8046bd01800007945011ae8079470180000600001e52806000018000046b301e5380794f018000079510180000795301800007955011aa8046a90180000795901e568060000180000795d011a88046a10180000469f011a78079630180000469b011a68046990180000796901e5a80796b0180000600001e5b8046910180000468f011a3807973018000079750180000468901800007979011a18046850180000600001e5f8060000180000798101e6080467d0180000600001e61807987018000046770119d8046750180000798d0119c80467101800006000018000079930180000466b01800007997018000046670180000799b0180000799d01e67804661018000079a101e68806000018000079a5011968046590180000600001e6a8079ab018000079ad01800006000018000079b10119380464d0180000600001e6d804649018000079b90119180464501800004643018000046410180000463f01e7080463d018000079c501e71806000018000046370118d804635018000079cd0118c8079cf018000079d101e748079d3018000079d501e758079d70180000600001e76804625018000079dd01e7780600001800006000018000079e3018000079e501e798079e701800004617011858060000180000461301e7b8079ef0180000460f01e7c806000018000079f5011828079f701800006000018000079fb0180000600001e7f80460101800007a010117f807a03018000045fb018000045f901800007a090117d807a0b018000045f301e83806000018000045ef0117b80600001800007a1501e858045e901800007a1901e868045e501800007a1d01e878045e101800006000018000045dd01800007a2501e898045d901800007a2901800007a2b01800007a2d011748045d101800007a3101800006000018000045cb01e8d807a37018000045c701e8e807a3b01800007a3d011708045c1018000060000116f8045bd0180000600001e91807a4701800007a490116d807a4b018000045b3018000045b101800007a510116b807a53018000045ab0116a806000018000045a701800007a5b018000045a3018000045a101800007a610116780459d0180000459b011668045990180000600001e9a80459501800007a6d0116480459101800007a710180000458d01800007a750116280600001800007a790116180600001800004583011608045810180000457f01ea0807a8301800007a850115e807a8701800007a8901ea28045750180000600001ea3807a8f01800007a9101ea480456d01800007a9501800007a9701800007a990115980600001800004563011588060000180000455f018000060000180000455b011568045590180000600001155807aab0180000455301eab807aaf0180000600001153807ab30180000454b01ead8045490180000454701800007abb0180000454301eaf807abf0180000453f018000060000180000453b01eb18045390180000453701eb2807acb01800007acd01eb38045310180000452f01eb4807ad30180000600001eb5807ad70180000452701eb680600001800007add0180000452101800007ae101147807ae30180000451b0114680600001800007ae9011458045150180000451301ebb807aef0180000450f01ebc80450d0180000450b01ebd807af70180000600001ebe8045050180000450301140807aff01800007b0101800007b03018000060000113e807b07018000044f70113d806000018000060000113c807b0f01800007b110113b807b1301800007b150113a807b17018000044e701ec6807b1b0180000600001ec7807b1f018000044df011378044dd01800007b25018000044d901800007b2901135807b2b018000044d301ecb806000018000044cf01ecc8044cd01800007b35018000044c901800007b39011318044c501800007b3d01ecf806000018000060000112f807b4301800007b450112e807b47018000044b70180000600001800007b4d0112c8044b1018000044af0112b806000018000044ab01ed58044a9018000044a701129807b5b018000044a3011288044a101800007b6101ed8807b6301800006000011268060000180000449701eda807b6b0180000449301800007b6f018000060000112380448d0180000448b011228060000180000448701121807b7b0180000448301edf807b7f0180000447f01ee080447d01800007b8501ee18044790180000600001800007b8b0180000600001ee3804471018000060000180000446d0180000446b01ee5807b97018000044670111980600001800007b9d01ee7807b9f0180000445f011178060000180000445b01ee980445901800004457011158044550180000600001114807baf0180000444f0111380444d0180000444b0180000444901800007bb901eee8044450180000444301eef80600001800007bc101ef080443d01800007bc50110e804439018000060000110d80443501800007bcd01ef3807bcf018000060000110b807bd3018000060000110a80442901800007bd901800007bdb01800007bdd0110880442101800007be1011078060000180000441b011068044190180000441701efa80441501800007bed01800007bef01800007bf10110380440d0180000600001efd80440901800007bf9018000044050180000440301800007bff01800007c01010ff8043fd01800007c0501800006000018000043f7010fd8043f501800007c0d01f03807c0f018000043ef010fb807c1301800007c15010fa8043e901800006000010f98043e5018000043e3010f88043e1018000043df01800007c23018000043db01f09807c27018000043d7010f580600001800007c2d010f4807c2f01800007c3101f0c8043cd01800007c3501f0d807c3701800006000010f1807c3b01800006000010f080600001800007c41010ef807c43018000043bb01800007c4701800007c4901f128043b501800007c4d010ec80600001800007c51018000043ad018000043ab01f15807c57018000043a7010e98043a5018000043a301f17807c5f0180000600001f1880439d01800007c6501f19807c67018000043970180000600001800007c6d01f1b8043910180000438f01f1c80600001800007c7501f1d8043890180000438701f1e807c7b01800007c7d01f1f8060000180000437f01f20807c8301800006000010de80437901800007c89010dd807c8b018000060000180000437101800007c9101f2480436d01800007c95010da80600001800007c99010d9807c9b0180000600001f278043610180000435f01f2880435d01800007ca5010d680435901800006000010d5807cab0180000435301f2b807caf01800007cb10180000434d01800007cb5018000043490180000434701f2e80600001800007cbd018000043410180000433f010cf80433d0180000600001f31807cc701800007cc901f32807ccb01800006000010cc80600001800007cd101f3480432d0180000432b018000043290180000600001f368043250180000432301f3780600001800007ce101f38807ce301800007ce501f3980431901800007ce901f3a807ceb01800004313010c480600001800006000010c380430d01800007cf501f3d8043090180000430701800007cfb01800004303010c08043010180000600001f4080600001800007d0501f418042f9018000042f7010bd8042f501800007d0d010bc8042f101800007d11010bb807d130180000600001f458042e9018000042e7018000042e5018000042e3018000042e1018000042df01f488042dd018000042db01f49806000018000042d7010b5807d2b01800007d2d01f4b8042d1018000042cf01f4c80600001800007d35010b2807d3701800006000010b18042c501800007d3d01f4f8042c1018000042bf01800007d43018000042bb018000042b9018000042b701f5280600001800007d4d010ac8042b10180000600001f54806000018000042ab010aa8042a9018000042a7010a98042a50180000600001800007d5f0180000429f010a7807d63018000060000180000429901800007d6901f5a807d6b01800004293010a48060000180000600001f5c807d7301800007d7501f5d80428901800004287010a18042850180000428301800007d7f018000060000180000427d01800007d8501f61807d8701800007d89018000042750180000427301f6380427101800007d9101f648060000180000600001f658060000180000426701f6680426501800007d9d01098807d9f0180000425f0109780425d0180000600001f6980425901800007da901f6a80425501800007dad0180000425101800007db101f6c8060000180000424b01f6d8060000180000424701091807dbb01800007dbd01090807dbf0180000423f0108f807dc30180000423b0108e804239018000060000108d80423501800007dcd0108c807dcf01800007dd101800007dd30180000422b0108a807dd701800007dd9010898060000180000422301f77807ddf0180000421f01800007de30180000421b01f798042190180000421701800004215018000060000108480600001800007df101083807df30180000420b018000042090180000420701f7e806000018000042030108080600001800007e010107f807e03018000041fb0107e807e0701800007e090107d8041f501800007e0d01f838041f10180000600001f848041ed0180000600001f85807e1701800007e1901800007e1b018000041e3010788041e101800007e2101f8880600001800007e2501f898041d901800007e29010758041d50180000600001800007e2f01800007e3101f8c8041cd0180000600001f8d8041c9018000041c701f8e8041c5018000041c3018000041c101800007e410106f8041bd018000041bb0180000600001800007e4901f928041b501800007e4d01f938041b1018000041af0106b807e5301800007e550106a807e570180000600001069807e5b018000041a301f9780600001800007e610180000600001800007e6501066807e6701800004197010658060000180000419301064807e6f0180000418f01063807e730180000418b01f9d80600001800007e7901f9e8041850180000600001f9f807e7f01800007e8101fa080417d01800007e8501800007e870180000417701fa2807e8b01800007e8d01fa3806000018000060000105b80416d01800007e950105a807e970180000600001fa680416501800004163010588041610180000600001fa880415d01800007ea501056807ea701800007ea90180000415501800007ead01fab8041510180000414f0105380600001800007eb501800007eb70180000414701fae807ebb01800007ebd0105080414101800007ec101fb08060000180000600001fb1804139018000041370104d80413501800007ecd018000041310180000412f01fb480412d0180000412b01fb5806000018000060000104980412501800004123010488041210180000411f01fb880411d01800007ee5010468041190180000600001fba807eeb01800007eed01044807eef01800007ef101800007ef30180000600001fbd8041090180000410701fbe80600001800007efd0104080410101800007f010103f807f0301800007f0501fc1807f0701800007f0901800007f0b01800006000018000040f101800007f110103b807f13018000040eb018000040e901800007f19010398040e5018000040e30103880600001800007f2101fc8807f23018000040db0103680600001800007f2901fca807f2b018000040d301034807f2f0180000600001fcc807f33018000040cb01032807f37018000040c70180000600001800007f3d01030807f3f01
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem source_eq : sourceValue=packedInput := by decide +kernel
theorem source_word : sourceValue=FR7022Hyperbola.word 22 8000 packedDigit := by
  rw [source_eq,packedInput,build_spec _ (by decide)]
  simp only [Nat.zero_add]
  exact word_pad 22 8000 _ (by decide) (by decide) _
def g := packedColumn 5 sourceValue
theorem g_law : MotorLaw (20000-12000) packedDigit g :=
  packedColumn_law _ 5 sourceValue packedDigit source_word digit_fit
abbrev posSum (t : ℕ) := cumulative 12000 20000 3000000 t packedDigit
end ThetaWidePinned

namespace ThetaWidePinned
open ThetaWindow
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def gw (o n : ℕ) := window 12000 20000 3000000 o n g
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def gt {o n : ℕ} (v : {t : ℕ // t=gw o n}) : Tile posSum o n :=
  verified (D:=12000) (K:=20000) (B:=3000000) (off:=o) (len:=n) (by decide) g_law v
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g0a : Tile posSum 0 8192 := gt (by
  have e : gw 0 8192 = gw 0 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g0b : Tile posSum 8192 8192 := gt (by
  have e : gw 8192 8192 = gw 8192 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g0c : Tile posSum 16384 8192 := gt (by
  have e : gw 16384 8192 = gw 16384 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g0d : Tile posSum 24576 8192 := gt (by
  have e : gw 24576 8192 = gw 24576 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g0 : Tile posSum 0 32768 :=
  join (join g0a g0b) (join g0c g0d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g1a : Tile posSum 32768 8192 := gt (by
  have e : gw 32768 8192 = gw 32768 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g1b : Tile posSum 40960 8192 := gt (by
  have e : gw 40960 8192 = gw 40960 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g1c : Tile posSum 49152 8192 := gt (by
  have e : gw 49152 8192 = gw 49152 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g1d : Tile posSum 57344 8192 := gt (by
  have e : gw 57344 8192 = gw 57344 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g1 : Tile posSum 32768 32768 :=
  join (join g1a g1b) (join g1c g1d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g2a : Tile posSum 65536 8192 := gt (by
  have e : gw 65536 8192 = gw 65536 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g2b : Tile posSum 73728 8192 := gt (by
  have e : gw 73728 8192 = gw 73728 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g2c : Tile posSum 81920 8192 := gt (by
  have e : gw 81920 8192 = gw 81920 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g2d : Tile posSum 90112 8192 := gt (by
  have e : gw 90112 8192 = gw 90112 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g2 : Tile posSum 65536 32768 :=
  join (join g2a g2b) (join g2c g2d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g3a : Tile posSum 98304 8192 := gt (by
  have e : gw 98304 8192 = gw 98304 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g3b : Tile posSum 106496 8192 := gt (by
  have e : gw 106496 8192 = gw 106496 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g3c : Tile posSum 114688 8192 := gt (by
  have e : gw 114688 8192 = gw 114688 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g3d : Tile posSum 122880 8192 := gt (by
  have e : gw 122880 8192 = gw 122880 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g3 : Tile posSum 98304 32768 :=
  join (join g3a g3b) (join g3c g3d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g4a : Tile posSum 131072 8192 := gt (by
  have e : gw 131072 8192 = gw 131072 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g4b : Tile posSum 139264 8192 := gt (by
  have e : gw 139264 8192 = gw 139264 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g4c : Tile posSum 147456 8192 := gt (by
  have e : gw 147456 8192 = gw 147456 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g4d : Tile posSum 155648 8192 := gt (by
  have e : gw 155648 8192 = gw 155648 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g4 : Tile posSum 131072 32768 :=
  join (join g4a g4b) (join g4c g4d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g5a : Tile posSum 163840 8192 := gt (by
  have e : gw 163840 8192 = gw 163840 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g5b : Tile posSum 172032 8192 := gt (by
  have e : gw 172032 8192 = gw 172032 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g5c : Tile posSum 180224 8192 := gt (by
  have e : gw 180224 8192 = gw 180224 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g5d : Tile posSum 188416 8192 := gt (by
  have e : gw 188416 8192 = gw 188416 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g5 : Tile posSum 163840 32768 :=
  join (join g5a g5b) (join g5c g5d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g6a : Tile posSum 196608 8192 := gt (by
  have e : gw 196608 8192 = gw 196608 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g6b : Tile posSum 204800 8192 := gt (by
  have e : gw 204800 8192 = gw 204800 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g6c : Tile posSum 212992 8192 := gt (by
  have e : gw 212992 8192 = gw 212992 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g6d : Tile posSum 221184 8192 := gt (by
  have e : gw 221184 8192 = gw 221184 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g6 : Tile posSum 196608 32768 :=
  join (join g6a g6b) (join g6c g6d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g7a : Tile posSum 229376 8192 := gt (by
  have e : gw 229376 8192 = gw 229376 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g7b : Tile posSum 237568 8192 := gt (by
  have e : gw 237568 8192 = gw 237568 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g7c : Tile posSum 245760 8192 := gt (by
  have e : gw 245760 8192 = gw 245760 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g7d : Tile posSum 253952 8192 := gt (by
  have e : gw 253952 8192 = gw 253952 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g7 : Tile posSum 229376 32768 :=
  join (join g7a g7b) (join g7c g7d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g8a : Tile posSum 262144 8192 := gt (by
  have e : gw 262144 8192 = gw 262144 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g8b : Tile posSum 270336 8192 := gt (by
  have e : gw 270336 8192 = gw 270336 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g8c : Tile posSum 278528 8192 := gt (by
  have e : gw 278528 8192 = gw 278528 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g8d : Tile posSum 286720 8192 := gt (by
  have e : gw 286720 8192 = gw 286720 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g8 : Tile posSum 262144 32768 :=
  join (join g8a g8b) (join g8c g8d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g9a : Tile posSum 294912 8192 := gt (by
  have e : gw 294912 8192 = gw 294912 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g9b : Tile posSum 303104 8192 := gt (by
  have e : gw 303104 8192 = gw 303104 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g9c : Tile posSum 311296 8192 := gt (by
  have e : gw 311296 8192 = gw 311296 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g9d : Tile posSum 319488 8192 := gt (by
  have e : gw 319488 8192 = gw 319488 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g9 : Tile posSum 294912 32768 :=
  join (join g9a g9b) (join g9c g9d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g10a : Tile posSum 327680 8192 := gt (by
  have e : gw 327680 8192 = gw 327680 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g10b : Tile posSum 335872 8192 := gt (by
  have e : gw 335872 8192 = gw 335872 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g10c : Tile posSum 344064 8192 := gt (by
  have e : gw 344064 8192 = gw 344064 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g10d : Tile posSum 352256 8192 := gt (by
  have e : gw 352256 8192 = gw 352256 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g10 : Tile posSum 327680 32768 :=
  join (join g10a g10b) (join g10c g10d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g11a : Tile posSum 360448 8192 := gt (by
  have e : gw 360448 8192 = gw 360448 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g11b : Tile posSum 368640 8192 := gt (by
  have e : gw 368640 8192 = gw 368640 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g11c : Tile posSum 376832 8192 := gt (by
  have e : gw 376832 8192 = gw 376832 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g11d : Tile posSum 385024 8192 := gt (by
  have e : gw 385024 8192 = gw 385024 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g11 : Tile posSum 360448 32768 :=
  join (join g11a g11b) (join g11c g11d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g12a : Tile posSum 393216 8192 := gt (by
  have e : gw 393216 8192 = gw 393216 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g12b : Tile posSum 401408 8192 := gt (by
  have e : gw 401408 8192 = gw 401408 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g12c : Tile posSum 409600 8192 := gt (by
  have e : gw 409600 8192 = gw 409600 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g12d : Tile posSum 417792 8192 := gt (by
  have e : gw 417792 8192 = gw 417792 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g12 : Tile posSum 393216 32768 :=
  join (join g12a g12b) (join g12c g12d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g13a : Tile posSum 425984 8192 := gt (by
  have e : gw 425984 8192 = gw 425984 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g13b : Tile posSum 434176 8192 := gt (by
  have e : gw 434176 8192 = gw 434176 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g13c : Tile posSum 442368 8192 := gt (by
  have e : gw 442368 8192 = gw 442368 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g13d : Tile posSum 450560 8192 := gt (by
  have e : gw 450560 8192 = gw 450560 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g13 : Tile posSum 425984 32768 :=
  join (join g13a g13b) (join g13c g13d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g14a : Tile posSum 458752 8192 := gt (by
  have e : gw 458752 8192 = gw 458752 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g14b : Tile posSum 466944 8192 := gt (by
  have e : gw 466944 8192 = gw 466944 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g14c : Tile posSum 475136 8192 := gt (by
  have e : gw 475136 8192 = gw 475136 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g14d : Tile posSum 483328 8192 := gt (by
  have e : gw 483328 8192 = gw 483328 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g14 : Tile posSum 458752 32768 :=
  join (join g14a g14b) (join g14c g14d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g15a : Tile posSum 491520 8192 := gt (by
  have e : gw 491520 8192 = gw 491520 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g15b : Tile posSum 499712 8192 := gt (by
  have e : gw 499712 8192 = gw 499712 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g15c : Tile posSum 507904 8192 := gt (by
  have e : gw 507904 8192 = gw 507904 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g15d : Tile posSum 516096 8192 := gt (by
  have e : gw 516096 8192 = gw 516096 8192 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g15 : Tile posSum 491520 32768 :=
  join (join g15a g15b) (join g15c g15d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g16a : Tile posSum 524288 7936 := gt (by
  have e : gw 524288 7936 = gw 524288 7936 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g16b : Tile posSum 532224 7936 := gt (by
  have e : gw 532224 7936 = gw 532224 7936 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g16c : Tile posSum 540160 7936 := gt (by
  have e : gw 540160 7936 = gw 540160 7936 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g16d : Tile posSum 548096 7936 := gt (by
  have e : gw 548096 7936 = gw 548096 7936 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g16 : Tile posSum 524288 31744 :=
  join (join g16a g16b) (join g16c g16d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g17a : Tile posSum 556032 7168 := gt (by
  have e : gw 556032 7168 = gw 556032 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g17b : Tile posSum 563200 7168 := gt (by
  have e : gw 563200 7168 = gw 563200 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g17c : Tile posSum 570368 7168 := gt (by
  have e : gw 570368 7168 = gw 570368 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g17d : Tile posSum 577536 7168 := gt (by
  have e : gw 577536 7168 = gw 577536 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g17 : Tile posSum 556032 28672 :=
  join (join g17a g17b) (join g17c g17d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g18a : Tile posSum 584704 7168 := gt (by
  have e : gw 584704 7168 = gw 584704 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g18b : Tile posSum 591872 7168 := gt (by
  have e : gw 591872 7168 = gw 591872 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g18c : Tile posSum 599040 7168 := gt (by
  have e : gw 599040 7168 = gw 599040 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g18d : Tile posSum 606208 7168 := gt (by
  have e : gw 606208 7168 = gw 606208 7168 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g18 : Tile posSum 584704 28672 :=
  join (join g18a g18b) (join g18c g18d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g19a : Tile posSum 613376 6656 := gt (by
  have e : gw 613376 6656 = gw 613376 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g19b : Tile posSum 620032 6656 := gt (by
  have e : gw 620032 6656 = gw 620032 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g19c : Tile posSum 626688 6656 := gt (by
  have e : gw 626688 6656 = gw 626688 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g19d : Tile posSum 633344 6656 := gt (by
  have e : gw 633344 6656 = gw 633344 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g19 : Tile posSum 613376 26624 :=
  join (join g19a g19b) (join g19c g19d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g20a : Tile posSum 640000 6656 := gt (by
  have e : gw 640000 6656 = gw 640000 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g20b : Tile posSum 646656 6656 := gt (by
  have e : gw 646656 6656 = gw 646656 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g20c : Tile posSum 653312 6656 := gt (by
  have e : gw 653312 6656 = gw 653312 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g20d : Tile posSum 659968 6656 := gt (by
  have e : gw 659968 6656 = gw 659968 6656 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g20 : Tile posSum 640000 26624 :=
  join (join g20a g20b) (join g20c g20d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g21a : Tile posSum 666624 6400 := gt (by
  have e : gw 666624 6400 = gw 666624 6400 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g21b : Tile posSum 673024 6400 := gt (by
  have e : gw 673024 6400 = gw 673024 6400 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g21c : Tile posSum 679424 6400 := gt (by
  have e : gw 679424 6400 = gw 679424 6400 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g21d : Tile posSum 685824 6400 := gt (by
  have e : gw 685824 6400 = gw 685824 6400 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g21 : Tile posSum 666624 25600 :=
  join (join g21a g21b) (join g21c g21d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g22a : Tile posSum 692224 6144 := gt (by
  have e : gw 692224 6144 = gw 692224 6144 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g22b : Tile posSum 698368 6144 := gt (by
  have e : gw 698368 6144 = gw 698368 6144 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g22c : Tile posSum 704512 6144 := gt (by
  have e : gw 704512 6144 = gw 704512 6144 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g22d : Tile posSum 710656 6144 := gt (by
  have e : gw 710656 6144 = gw 710656 6144 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g22 : Tile posSum 692224 24576 :=
  join (join g22a g22b) (join g22c g22d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g23a : Tile posSum 716800 5888 := gt (by
  have e : gw 716800 5888 = gw 716800 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g23b : Tile posSum 722688 5888 := gt (by
  have e : gw 722688 5888 = gw 722688 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g23c : Tile posSum 728576 5888 := gt (by
  have e : gw 728576 5888 = gw 728576 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g23d : Tile posSum 734464 5888 := gt (by
  have e : gw 734464 5888 = gw 734464 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g23 : Tile posSum 716800 23552 :=
  join (join g23a g23b) (join g23c g23d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g24a : Tile posSum 740352 5888 := gt (by
  have e : gw 740352 5888 = gw 740352 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g24b : Tile posSum 746240 5888 := gt (by
  have e : gw 746240 5888 = gw 746240 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g24c : Tile posSum 752128 5888 := gt (by
  have e : gw 752128 5888 = gw 752128 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g24d : Tile posSum 758016 5888 := gt (by
  have e : gw 758016 5888 = gw 758016 5888 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g24 : Tile posSum 740352 23552 :=
  join (join g24a g24b) (join g24c g24d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g25a : Tile posSum 763904 5632 := gt (by
  have e : gw 763904 5632 = gw 763904 5632 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g25b : Tile posSum 769536 5632 := gt (by
  have e : gw 769536 5632 = gw 769536 5632 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g25c : Tile posSum 775168 5632 := gt (by
  have e : gw 775168 5632 = gw 775168 5632 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g25d : Tile posSum 780800 5632 := gt (by
  have e : gw 780800 5632 = gw 780800 5632 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g25 : Tile posSum 763904 22528 :=
  join (join g25a g25b) (join g25c g25d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g26a : Tile posSum 786432 5376 := gt (by
  have e : gw 786432 5376 = gw 786432 5376 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g26b : Tile posSum 791808 5376 := gt (by
  have e : gw 791808 5376 = gw 791808 5376 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g26c : Tile posSum 797184 5376 := gt (by
  have e : gw 797184 5376 = gw 797184 5376 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g26d : Tile posSum 802560 5376 := gt (by
  have e : gw 802560 5376 = gw 802560 5376 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g26 : Tile posSum 786432 21504 :=
  join (join g26a g26b) (join g26c g26d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g27a : Tile posSum 807936 5120 := gt (by
  have e : gw 807936 5120 = gw 807936 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g27b : Tile posSum 813056 5120 := gt (by
  have e : gw 813056 5120 = gw 813056 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g27c : Tile posSum 818176 5120 := gt (by
  have e : gw 818176 5120 = gw 818176 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g27d : Tile posSum 823296 5120 := gt (by
  have e : gw 823296 5120 = gw 823296 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g27 : Tile posSum 807936 20480 :=
  join (join g27a g27b) (join g27c g27d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g28a : Tile posSum 828416 5120 := gt (by
  have e : gw 828416 5120 = gw 828416 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g28b : Tile posSum 833536 5120 := gt (by
  have e : gw 833536 5120 = gw 833536 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g28c : Tile posSum 838656 5120 := gt (by
  have e : gw 838656 5120 = gw 838656 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g28d : Tile posSum 843776 5120 := gt (by
  have e : gw 843776 5120 = gw 843776 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g28 : Tile posSum 828416 20480 :=
  join (join g28a g28b) (join g28c g28d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g29a : Tile posSum 848896 5120 := gt (by
  have e : gw 848896 5120 = gw 848896 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g29b : Tile posSum 854016 5120 := gt (by
  have e : gw 854016 5120 = gw 854016 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g29c : Tile posSum 859136 5120 := gt (by
  have e : gw 859136 5120 = gw 859136 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g29d : Tile posSum 864256 5120 := gt (by
  have e : gw 864256 5120 = gw 864256 5120 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g29 : Tile posSum 848896 20480 :=
  join (join g29a g29b) (join g29c g29d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g30a : Tile posSum 869376 4864 := gt (by
  have e : gw 869376 4864 = gw 869376 4864 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g30b : Tile posSum 874240 4864 := gt (by
  have e : gw 874240 4864 = gw 874240 4864 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g30c : Tile posSum 879104 4864 := gt (by
  have e : gw 879104 4864 = gw 879104 4864 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g30d : Tile posSum 883968 4864 := gt (by
  have e : gw 883968 4864 = gw 883968 4864 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g30 : Tile posSum 869376 19456 :=
  join (join g30a g30b) (join g30c g30d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g31a : Tile posSum 888832 4608 := gt (by
  have e : gw 888832 4608 = gw 888832 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g31b : Tile posSum 893440 4608 := gt (by
  have e : gw 893440 4608 = gw 893440 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g31c : Tile posSum 898048 4608 := gt (by
  have e : gw 898048 4608 = gw 898048 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g31d : Tile posSum 902656 4608 := gt (by
  have e : gw 902656 4608 = gw 902656 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g31 : Tile posSum 888832 18432 :=
  join (join g31a g31b) (join g31c g31d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g32a : Tile posSum 907264 4608 := gt (by
  have e : gw 907264 4608 = gw 907264 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g32b : Tile posSum 911872 4608 := gt (by
  have e : gw 911872 4608 = gw 911872 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g32c : Tile posSum 916480 4608 := gt (by
  have e : gw 916480 4608 = gw 916480 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g32d : Tile posSum 921088 4608 := gt (by
  have e : gw 921088 4608 = gw 921088 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g32 : Tile posSum 907264 18432 :=
  join (join g32a g32b) (join g32c g32d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g33a : Tile posSum 925696 4608 := gt (by
  have e : gw 925696 4608 = gw 925696 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g33b : Tile posSum 930304 4608 := gt (by
  have e : gw 930304 4608 = gw 930304 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g33c : Tile posSum 934912 4608 := gt (by
  have e : gw 934912 4608 = gw 934912 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g33d : Tile posSum 939520 4608 := gt (by
  have e : gw 939520 4608 = gw 939520 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g33 : Tile posSum 925696 18432 :=
  join (join g33a g33b) (join g33c g33d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g34a : Tile posSum 944128 4608 := gt (by
  have e : gw 944128 4608 = gw 944128 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g34b : Tile posSum 948736 4608 := gt (by
  have e : gw 948736 4608 = gw 948736 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g34c : Tile posSum 953344 4608 := gt (by
  have e : gw 953344 4608 = gw 953344 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g34d : Tile posSum 957952 4608 := gt (by
  have e : gw 957952 4608 = gw 957952 4608 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g34 : Tile posSum 944128 18432 :=
  join (join g34a g34b) (join g34c g34d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g35a : Tile posSum 962560 4352 := gt (by
  have e : gw 962560 4352 = gw 962560 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g35b : Tile posSum 966912 4352 := gt (by
  have e : gw 966912 4352 = gw 966912 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g35c : Tile posSum 971264 4352 := gt (by
  have e : gw 971264 4352 = gw 971264 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g35d : Tile posSum 975616 4352 := gt (by
  have e : gw 975616 4352 = gw 975616 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g35 : Tile posSum 962560 17408 :=
  join (join g35a g35b) (join g35c g35d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g36a : Tile posSum 979968 4352 := gt (by
  have e : gw 979968 4352 = gw 979968 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g36b : Tile posSum 984320 4352 := gt (by
  have e : gw 984320 4352 = gw 984320 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g36c : Tile posSum 988672 4352 := gt (by
  have e : gw 988672 4352 = gw 988672 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g36d : Tile posSum 993024 4352 := gt (by
  have e : gw 993024 4352 = gw 993024 4352 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g36 : Tile posSum 979968 17408 :=
  join (join g36a g36b) (join g36c g36d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g37a : Tile posSum 997376 4096 := gt (by
  have e : gw 997376 4096 = gw 997376 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g37b : Tile posSum 1001472 4096 := gt (by
  have e : gw 1001472 4096 = gw 1001472 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g37c : Tile posSum 1005568 4096 := gt (by
  have e : gw 1005568 4096 = gw 1005568 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g37d : Tile posSum 1009664 4096 := gt (by
  have e : gw 1009664 4096 = gw 1009664 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g37 : Tile posSum 997376 16384 :=
  join (join g37a g37b) (join g37c g37d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g38a : Tile posSum 1013760 4096 := gt (by
  have e : gw 1013760 4096 = gw 1013760 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g38b : Tile posSum 1017856 4096 := gt (by
  have e : gw 1017856 4096 = gw 1017856 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g38c : Tile posSum 1021952 4096 := gt (by
  have e : gw 1021952 4096 = gw 1021952 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g38d : Tile posSum 1026048 4096 := gt (by
  have e : gw 1026048 4096 = gw 1026048 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g38 : Tile posSum 1013760 16384 :=
  join (join g38a g38b) (join g38c g38d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g39a : Tile posSum 1030144 4096 := gt (by
  have e : gw 1030144 4096 = gw 1030144 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g39b : Tile posSum 1034240 4096 := gt (by
  have e : gw 1034240 4096 = gw 1034240 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g39c : Tile posSum 1038336 4096 := gt (by
  have e : gw 1038336 4096 = gw 1038336 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g39d : Tile posSum 1042432 4096 := gt (by
  have e : gw 1042432 4096 = gw 1042432 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g39 : Tile posSum 1030144 16384 :=
  join (join g39a g39b) (join g39c g39d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g40a : Tile posSum 1046528 4096 := gt (by
  have e : gw 1046528 4096 = gw 1046528 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g40b : Tile posSum 1050624 4096 := gt (by
  have e : gw 1050624 4096 = gw 1050624 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g40c : Tile posSum 1054720 4096 := gt (by
  have e : gw 1054720 4096 = gw 1054720 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g40d : Tile posSum 1058816 4096 := gt (by
  have e : gw 1058816 4096 = gw 1058816 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g40 : Tile posSum 1046528 16384 :=
  join (join g40a g40b) (join g40c g40d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g41a : Tile posSum 1062912 4096 := gt (by
  have e : gw 1062912 4096 = gw 1062912 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g41b : Tile posSum 1067008 4096 := gt (by
  have e : gw 1067008 4096 = gw 1067008 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g41c : Tile posSum 1071104 4096 := gt (by
  have e : gw 1071104 4096 = gw 1071104 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g41d : Tile posSum 1075200 4096 := gt (by
  have e : gw 1075200 4096 = gw 1075200 4096 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g41 : Tile posSum 1062912 16384 :=
  join (join g41a g41b) (join g41c g41d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g42a : Tile posSum 1079296 3840 := gt (by
  have e : gw 1079296 3840 = gw 1079296 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g42b : Tile posSum 1083136 3840 := gt (by
  have e : gw 1083136 3840 = gw 1083136 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g42c : Tile posSum 1086976 3840 := gt (by
  have e : gw 1086976 3840 = gw 1086976 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g42d : Tile posSum 1090816 3840 := gt (by
  have e : gw 1090816 3840 = gw 1090816 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g42 : Tile posSum 1079296 15360 :=
  join (join g42a g42b) (join g42c g42d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g43a : Tile posSum 1094656 3840 := gt (by
  have e : gw 1094656 3840 = gw 1094656 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g43b : Tile posSum 1098496 3840 := gt (by
  have e : gw 1098496 3840 = gw 1098496 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g43c : Tile posSum 1102336 3840 := gt (by
  have e : gw 1102336 3840 = gw 1102336 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g43d : Tile posSum 1106176 3840 := gt (by
  have e : gw 1106176 3840 = gw 1106176 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g43 : Tile posSum 1094656 15360 :=
  join (join g43a g43b) (join g43c g43d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g44a : Tile posSum 1110016 3840 := gt (by
  have e : gw 1110016 3840 = gw 1110016 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g44b : Tile posSum 1113856 3840 := gt (by
  have e : gw 1113856 3840 = gw 1113856 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g44c : Tile posSum 1117696 3840 := gt (by
  have e : gw 1117696 3840 = gw 1117696 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g44d : Tile posSum 1121536 3840 := gt (by
  have e : gw 1121536 3840 = gw 1121536 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g44 : Tile posSum 1110016 15360 :=
  join (join g44a g44b) (join g44c g44d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g45a : Tile posSum 1125376 3840 := gt (by
  have e : gw 1125376 3840 = gw 1125376 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g45b : Tile posSum 1129216 3840 := gt (by
  have e : gw 1129216 3840 = gw 1129216 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g45c : Tile posSum 1133056 3840 := gt (by
  have e : gw 1133056 3840 = gw 1133056 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g45d : Tile posSum 1136896 3840 := gt (by
  have e : gw 1136896 3840 = gw 1136896 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g45 : Tile posSum 1125376 15360 :=
  join (join g45a g45b) (join g45c g45d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g46a : Tile posSum 1140736 3840 := gt (by
  have e : gw 1140736 3840 = gw 1140736 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g46b : Tile posSum 1144576 3840 := gt (by
  have e : gw 1144576 3840 = gw 1144576 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g46c : Tile posSum 1148416 3840 := gt (by
  have e : gw 1148416 3840 = gw 1148416 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g46d : Tile posSum 1152256 3840 := gt (by
  have e : gw 1152256 3840 = gw 1152256 3840 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g46 : Tile posSum 1140736 15360 :=
  join (join g46a g46b) (join g46c g46d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g47a : Tile posSum 1156096 3584 := gt (by
  have e : gw 1156096 3584 = gw 1156096 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g47b : Tile posSum 1159680 3584 := gt (by
  have e : gw 1159680 3584 = gw 1159680 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g47c : Tile posSum 1163264 3584 := gt (by
  have e : gw 1163264 3584 = gw 1163264 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g47d : Tile posSum 1166848 3584 := gt (by
  have e : gw 1166848 3584 = gw 1166848 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g47 : Tile posSum 1156096 14336 :=
  join (join g47a g47b) (join g47c g47d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g48a : Tile posSum 1170432 3584 := gt (by
  have e : gw 1170432 3584 = gw 1170432 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g48b : Tile posSum 1174016 3584 := gt (by
  have e : gw 1174016 3584 = gw 1174016 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g48c : Tile posSum 1177600 3584 := gt (by
  have e : gw 1177600 3584 = gw 1177600 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g48d : Tile posSum 1181184 3584 := gt (by
  have e : gw 1181184 3584 = gw 1181184 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g48 : Tile posSum 1170432 14336 :=
  join (join g48a g48b) (join g48c g48d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g49a : Tile posSum 1184768 3584 := gt (by
  have e : gw 1184768 3584 = gw 1184768 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g49b : Tile posSum 1188352 3584 := gt (by
  have e : gw 1188352 3584 = gw 1188352 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g49c : Tile posSum 1191936 3584 := gt (by
  have e : gw 1191936 3584 = gw 1191936 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g49d : Tile posSum 1195520 3584 := gt (by
  have e : gw 1195520 3584 = gw 1195520 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g49 : Tile posSum 1184768 14336 :=
  join (join g49a g49b) (join g49c g49d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g50a : Tile posSum 1199104 3584 := gt (by
  have e : gw 1199104 3584 = gw 1199104 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g50b : Tile posSum 1202688 3584 := gt (by
  have e : gw 1202688 3584 = gw 1202688 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g50c : Tile posSum 1206272 3584 := gt (by
  have e : gw 1206272 3584 = gw 1206272 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g50d : Tile posSum 1209856 3584 := gt (by
  have e : gw 1209856 3584 = gw 1209856 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g50 : Tile posSum 1199104 14336 :=
  join (join g50a g50b) (join g50c g50d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g51a : Tile posSum 1213440 3584 := gt (by
  have e : gw 1213440 3584 = gw 1213440 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g51b : Tile posSum 1217024 3584 := gt (by
  have e : gw 1217024 3584 = gw 1217024 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g51c : Tile posSum 1220608 3584 := gt (by
  have e : gw 1220608 3584 = gw 1220608 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g51d : Tile posSum 1224192 3584 := gt (by
  have e : gw 1224192 3584 = gw 1224192 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g51 : Tile posSum 1213440 14336 :=
  join (join g51a g51b) (join g51c g51d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g52a : Tile posSum 1227776 3584 := gt (by
  have e : gw 1227776 3584 = gw 1227776 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g52b : Tile posSum 1231360 3584 := gt (by
  have e : gw 1231360 3584 = gw 1231360 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g52c : Tile posSum 1234944 3584 := gt (by
  have e : gw 1234944 3584 = gw 1234944 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g52d : Tile posSum 1238528 3584 := gt (by
  have e : gw 1238528 3584 = gw 1238528 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g52 : Tile posSum 1227776 14336 :=
  join (join g52a g52b) (join g52c g52d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g53a : Tile posSum 1242112 3584 := gt (by
  have e : gw 1242112 3584 = gw 1242112 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g53b : Tile posSum 1245696 3584 := gt (by
  have e : gw 1245696 3584 = gw 1245696 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g53c : Tile posSum 1249280 3584 := gt (by
  have e : gw 1249280 3584 = gw 1249280 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g53d : Tile posSum 1252864 3584 := gt (by
  have e : gw 1252864 3584 = gw 1252864 3584 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g53 : Tile posSum 1242112 14336 :=
  join (join g53a g53b) (join g53c g53d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g54a : Tile posSum 1256448 3328 := gt (by
  have e : gw 1256448 3328 = gw 1256448 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g54b : Tile posSum 1259776 3328 := gt (by
  have e : gw 1259776 3328 = gw 1259776 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g54c : Tile posSum 1263104 3328 := gt (by
  have e : gw 1263104 3328 = gw 1263104 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g54d : Tile posSum 1266432 3328 := gt (by
  have e : gw 1266432 3328 = gw 1266432 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g54 : Tile posSum 1256448 13312 :=
  join (join g54a g54b) (join g54c g54d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g55a : Tile posSum 1269760 3328 := gt (by
  have e : gw 1269760 3328 = gw 1269760 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g55b : Tile posSum 1273088 3328 := gt (by
  have e : gw 1273088 3328 = gw 1273088 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g55c : Tile posSum 1276416 3328 := gt (by
  have e : gw 1276416 3328 = gw 1276416 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g55d : Tile posSum 1279744 3328 := gt (by
  have e : gw 1279744 3328 = gw 1279744 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g55 : Tile posSum 1269760 13312 :=
  join (join g55a g55b) (join g55c g55d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g56a : Tile posSum 1283072 3328 := gt (by
  have e : gw 1283072 3328 = gw 1283072 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g56b : Tile posSum 1286400 3328 := gt (by
  have e : gw 1286400 3328 = gw 1286400 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g56c : Tile posSum 1289728 3328 := gt (by
  have e : gw 1289728 3328 = gw 1289728 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g56d : Tile posSum 1293056 3328 := gt (by
  have e : gw 1293056 3328 = gw 1293056 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g56 : Tile posSum 1283072 13312 :=
  join (join g56a g56b) (join g56c g56d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g57a : Tile posSum 1296384 3328 := gt (by
  have e : gw 1296384 3328 = gw 1296384 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g57b : Tile posSum 1299712 3328 := gt (by
  have e : gw 1299712 3328 = gw 1299712 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g57c : Tile posSum 1303040 3328 := gt (by
  have e : gw 1303040 3328 = gw 1303040 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g57d : Tile posSum 1306368 3328 := gt (by
  have e : gw 1306368 3328 = gw 1306368 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g57 : Tile posSum 1296384 13312 :=
  join (join g57a g57b) (join g57c g57d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g58a : Tile posSum 1309696 3328 := gt (by
  have e : gw 1309696 3328 = gw 1309696 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g58b : Tile posSum 1313024 3328 := gt (by
  have e : gw 1313024 3328 = gw 1313024 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g58c : Tile posSum 1316352 3328 := gt (by
  have e : gw 1316352 3328 = gw 1316352 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g58d : Tile posSum 1319680 3328 := gt (by
  have e : gw 1319680 3328 = gw 1319680 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g58 : Tile posSum 1309696 13312 :=
  join (join g58a g58b) (join g58c g58d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g59a : Tile posSum 1323008 3328 := gt (by
  have e : gw 1323008 3328 = gw 1323008 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g59b : Tile posSum 1326336 3328 := gt (by
  have e : gw 1326336 3328 = gw 1326336 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g59c : Tile posSum 1329664 3328 := gt (by
  have e : gw 1329664 3328 = gw 1329664 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g59d : Tile posSum 1332992 3328 := gt (by
  have e : gw 1332992 3328 = gw 1332992 3328 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g59 : Tile posSum 1323008 13312 :=
  join (join g59a g59b) (join g59c g59d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g60a : Tile posSum 1336320 3072 := gt (by
  have e : gw 1336320 3072 = gw 1336320 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g60b : Tile posSum 1339392 3072 := gt (by
  have e : gw 1339392 3072 = gw 1339392 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g60c : Tile posSum 1342464 3072 := gt (by
  have e : gw 1342464 3072 = gw 1342464 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g60d : Tile posSum 1345536 3072 := gt (by
  have e : gw 1345536 3072 = gw 1345536 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g60 : Tile posSum 1336320 12288 :=
  join (join g60a g60b) (join g60c g60d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g61a : Tile posSum 1348608 3072 := gt (by
  have e : gw 1348608 3072 = gw 1348608 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g61b : Tile posSum 1351680 3072 := gt (by
  have e : gw 1351680 3072 = gw 1351680 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g61c : Tile posSum 1354752 3072 := gt (by
  have e : gw 1354752 3072 = gw 1354752 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g61d : Tile posSum 1357824 3072 := gt (by
  have e : gw 1357824 3072 = gw 1357824 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g61 : Tile posSum 1348608 12288 :=
  join (join g61a g61b) (join g61c g61d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g62a : Tile posSum 1360896 3072 := gt (by
  have e : gw 1360896 3072 = gw 1360896 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g62b : Tile posSum 1363968 3072 := gt (by
  have e : gw 1363968 3072 = gw 1363968 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g62c : Tile posSum 1367040 3072 := gt (by
  have e : gw 1367040 3072 = gw 1367040 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g62d : Tile posSum 1370112 3072 := gt (by
  have e : gw 1370112 3072 = gw 1370112 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g62 : Tile posSum 1360896 12288 :=
  join (join g62a g62b) (join g62c g62d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g63a : Tile posSum 1373184 3072 := gt (by
  have e : gw 1373184 3072 = gw 1373184 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g63b : Tile posSum 1376256 3072 := gt (by
  have e : gw 1376256 3072 = gw 1376256 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g63c : Tile posSum 1379328 3072 := gt (by
  have e : gw 1379328 3072 = gw 1379328 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g63d : Tile posSum 1382400 3072 := gt (by
  have e : gw 1382400 3072 = gw 1382400 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g63 : Tile posSum 1373184 12288 :=
  join (join g63a g63b) (join g63c g63d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g64a : Tile posSum 1385472 3072 := gt (by
  have e : gw 1385472 3072 = gw 1385472 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g64b : Tile posSum 1388544 3072 := gt (by
  have e : gw 1388544 3072 = gw 1388544 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g64c : Tile posSum 1391616 3072 := gt (by
  have e : gw 1391616 3072 = gw 1391616 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g64d : Tile posSum 1394688 3072 := gt (by
  have e : gw 1394688 3072 = gw 1394688 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g64 : Tile posSum 1385472 12288 :=
  join (join g64a g64b) (join g64c g64d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g65a : Tile posSum 1397760 3072 := gt (by
  have e : gw 1397760 3072 = gw 1397760 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g65b : Tile posSum 1400832 3072 := gt (by
  have e : gw 1400832 3072 = gw 1400832 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g65c : Tile posSum 1403904 3072 := gt (by
  have e : gw 1403904 3072 = gw 1403904 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g65d : Tile posSum 1406976 3072 := gt (by
  have e : gw 1406976 3072 = gw 1406976 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g65 : Tile posSum 1397760 12288 :=
  join (join g65a g65b) (join g65c g65d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g66a : Tile posSum 1410048 3072 := gt (by
  have e : gw 1410048 3072 = gw 1410048 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g66b : Tile posSum 1413120 3072 := gt (by
  have e : gw 1413120 3072 = gw 1413120 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g66c : Tile posSum 1416192 3072 := gt (by
  have e : gw 1416192 3072 = gw 1416192 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g66d : Tile posSum 1419264 3072 := gt (by
  have e : gw 1419264 3072 = gw 1419264 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g66 : Tile posSum 1410048 12288 :=
  join (join g66a g66b) (join g66c g66d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g67a : Tile posSum 1422336 3072 := gt (by
  have e : gw 1422336 3072 = gw 1422336 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g67b : Tile posSum 1425408 3072 := gt (by
  have e : gw 1425408 3072 = gw 1425408 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g67c : Tile posSum 1428480 3072 := gt (by
  have e : gw 1428480 3072 = gw 1428480 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g67d : Tile posSum 1431552 3072 := gt (by
  have e : gw 1431552 3072 = gw 1431552 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g67 : Tile posSum 1422336 12288 :=
  join (join g67a g67b) (join g67c g67d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g68a : Tile posSum 1434624 3072 := gt (by
  have e : gw 1434624 3072 = gw 1434624 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g68b : Tile posSum 1437696 3072 := gt (by
  have e : gw 1437696 3072 = gw 1437696 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g68c : Tile posSum 1440768 3072 := gt (by
  have e : gw 1440768 3072 = gw 1440768 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g68d : Tile posSum 1443840 3072 := gt (by
  have e : gw 1443840 3072 = gw 1443840 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g68 : Tile posSum 1434624 12288 :=
  join (join g68a g68b) (join g68c g68d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g69a : Tile posSum 1446912 3072 := gt (by
  have e : gw 1446912 3072 = gw 1446912 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g69b : Tile posSum 1449984 3072 := gt (by
  have e : gw 1449984 3072 = gw 1449984 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g69c : Tile posSum 1453056 3072 := gt (by
  have e : gw 1453056 3072 = gw 1453056 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g69d : Tile posSum 1456128 3072 := gt (by
  have e : gw 1456128 3072 = gw 1456128 3072 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g69 : Tile posSum 1446912 12288 :=
  join (join g69a g69b) (join g69c g69d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g70a : Tile posSum 1459200 2816 := gt (by
  have e : gw 1459200 2816 = gw 1459200 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g70b : Tile posSum 1462016 2816 := gt (by
  have e : gw 1462016 2816 = gw 1462016 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g70c : Tile posSum 1464832 2816 := gt (by
  have e : gw 1464832 2816 = gw 1464832 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g70d : Tile posSum 1467648 2816 := gt (by
  have e : gw 1467648 2816 = gw 1467648 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g70 : Tile posSum 1459200 11264 :=
  join (join g70a g70b) (join g70c g70d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g71a : Tile posSum 1470464 2816 := gt (by
  have e : gw 1470464 2816 = gw 1470464 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g71b : Tile posSum 1473280 2816 := gt (by
  have e : gw 1473280 2816 = gw 1473280 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g71c : Tile posSum 1476096 2816 := gt (by
  have e : gw 1476096 2816 = gw 1476096 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g71d : Tile posSum 1478912 2816 := gt (by
  have e : gw 1478912 2816 = gw 1478912 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g71 : Tile posSum 1470464 11264 :=
  join (join g71a g71b) (join g71c g71d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g72a : Tile posSum 1481728 2816 := gt (by
  have e : gw 1481728 2816 = gw 1481728 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g72b : Tile posSum 1484544 2816 := gt (by
  have e : gw 1484544 2816 = gw 1484544 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g72c : Tile posSum 1487360 2816 := gt (by
  have e : gw 1487360 2816 = gw 1487360 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g72d : Tile posSum 1490176 2816 := gt (by
  have e : gw 1490176 2816 = gw 1490176 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g72 : Tile posSum 1481728 11264 :=
  join (join g72a g72b) (join g72c g72d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g73a : Tile posSum 1492992 2816 := gt (by
  have e : gw 1492992 2816 = gw 1492992 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g73b : Tile posSum 1495808 2816 := gt (by
  have e : gw 1495808 2816 = gw 1495808 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g73c : Tile posSum 1498624 2816 := gt (by
  have e : gw 1498624 2816 = gw 1498624 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g73d : Tile posSum 1501440 2816 := gt (by
  have e : gw 1501440 2816 = gw 1501440 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g73 : Tile posSum 1492992 11264 :=
  join (join g73a g73b) (join g73c g73d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g74a : Tile posSum 1504256 2816 := gt (by
  have e : gw 1504256 2816 = gw 1504256 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g74b : Tile posSum 1507072 2816 := gt (by
  have e : gw 1507072 2816 = gw 1507072 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g74c : Tile posSum 1509888 2816 := gt (by
  have e : gw 1509888 2816 = gw 1509888 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g74d : Tile posSum 1512704 2816 := gt (by
  have e : gw 1512704 2816 = gw 1512704 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g74 : Tile posSum 1504256 11264 :=
  join (join g74a g74b) (join g74c g74d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g75a : Tile posSum 1515520 2816 := gt (by
  have e : gw 1515520 2816 = gw 1515520 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g75b : Tile posSum 1518336 2816 := gt (by
  have e : gw 1518336 2816 = gw 1518336 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g75c : Tile posSum 1521152 2816 := gt (by
  have e : gw 1521152 2816 = gw 1521152 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g75d : Tile posSum 1523968 2816 := gt (by
  have e : gw 1523968 2816 = gw 1523968 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g75 : Tile posSum 1515520 11264 :=
  join (join g75a g75b) (join g75c g75d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g76a : Tile posSum 1526784 2816 := gt (by
  have e : gw 1526784 2816 = gw 1526784 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g76b : Tile posSum 1529600 2816 := gt (by
  have e : gw 1529600 2816 = gw 1529600 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g76c : Tile posSum 1532416 2816 := gt (by
  have e : gw 1532416 2816 = gw 1532416 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g76d : Tile posSum 1535232 2816 := gt (by
  have e : gw 1535232 2816 = gw 1535232 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g76 : Tile posSum 1526784 11264 :=
  join (join g76a g76b) (join g76c g76d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g77a : Tile posSum 1538048 2816 := gt (by
  have e : gw 1538048 2816 = gw 1538048 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g77b : Tile posSum 1540864 2816 := gt (by
  have e : gw 1540864 2816 = gw 1540864 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g77c : Tile posSum 1543680 2816 := gt (by
  have e : gw 1543680 2816 = gw 1543680 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g77d : Tile posSum 1546496 2816 := gt (by
  have e : gw 1546496 2816 = gw 1546496 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g77 : Tile posSum 1538048 11264 :=
  join (join g77a g77b) (join g77c g77d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g78a : Tile posSum 1549312 2816 := gt (by
  have e : gw 1549312 2816 = gw 1549312 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g78b : Tile posSum 1552128 2816 := gt (by
  have e : gw 1552128 2816 = gw 1552128 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g78c : Tile posSum 1554944 2816 := gt (by
  have e : gw 1554944 2816 = gw 1554944 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g78d : Tile posSum 1557760 2816 := gt (by
  have e : gw 1557760 2816 = gw 1557760 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g78 : Tile posSum 1549312 11264 :=
  join (join g78a g78b) (join g78c g78d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g79a : Tile posSum 1560576 2816 := gt (by
  have e : gw 1560576 2816 = gw 1560576 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g79b : Tile posSum 1563392 2816 := gt (by
  have e : gw 1563392 2816 = gw 1563392 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g79c : Tile posSum 1566208 2816 := gt (by
  have e : gw 1566208 2816 = gw 1566208 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g79d : Tile posSum 1569024 2816 := gt (by
  have e : gw 1569024 2816 = gw 1569024 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g79 : Tile posSum 1560576 11264 :=
  join (join g79a g79b) (join g79c g79d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g80a : Tile posSum 1571840 2816 := gt (by
  have e : gw 1571840 2816 = gw 1571840 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g80b : Tile posSum 1574656 2816 := gt (by
  have e : gw 1574656 2816 = gw 1574656 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g80c : Tile posSum 1577472 2816 := gt (by
  have e : gw 1577472 2816 = gw 1577472 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g80d : Tile posSum 1580288 2816 := gt (by
  have e : gw 1580288 2816 = gw 1580288 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g80 : Tile posSum 1571840 11264 :=
  join (join g80a g80b) (join g80c g80d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g81a : Tile posSum 1583104 2816 := gt (by
  have e : gw 1583104 2816 = gw 1583104 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g81b : Tile posSum 1585920 2816 := gt (by
  have e : gw 1585920 2816 = gw 1585920 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g81c : Tile posSum 1588736 2816 := gt (by
  have e : gw 1588736 2816 = gw 1588736 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g81d : Tile posSum 1591552 2816 := gt (by
  have e : gw 1591552 2816 = gw 1591552 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g81 : Tile posSum 1583104 11264 :=
  join (join g81a g81b) (join g81c g81d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g82a : Tile posSum 1594368 2816 := gt (by
  have e : gw 1594368 2816 = gw 1594368 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g82b : Tile posSum 1597184 2816 := gt (by
  have e : gw 1597184 2816 = gw 1597184 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g82c : Tile posSum 1600000 2816 := gt (by
  have e : gw 1600000 2816 = gw 1600000 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g82d : Tile posSum 1602816 2816 := gt (by
  have e : gw 1602816 2816 = gw 1602816 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g82 : Tile posSum 1594368 11264 :=
  join (join g82a g82b) (join g82c g82d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g83a : Tile posSum 1605632 2816 := gt (by
  have e : gw 1605632 2816 = gw 1605632 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g83b : Tile posSum 1608448 2816 := gt (by
  have e : gw 1608448 2816 = gw 1608448 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g83c : Tile posSum 1611264 2816 := gt (by
  have e : gw 1611264 2816 = gw 1611264 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g83d : Tile posSum 1614080 2816 := gt (by
  have e : gw 1614080 2816 = gw 1614080 2816 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g83 : Tile posSum 1605632 11264 :=
  join (join g83a g83b) (join g83c g83d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g84a : Tile posSum 1616896 2560 := gt (by
  have e : gw 1616896 2560 = gw 1616896 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g84b : Tile posSum 1619456 2560 := gt (by
  have e : gw 1619456 2560 = gw 1619456 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g84c : Tile posSum 1622016 2560 := gt (by
  have e : gw 1622016 2560 = gw 1622016 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g84d : Tile posSum 1624576 2560 := gt (by
  have e : gw 1624576 2560 = gw 1624576 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g84 : Tile posSum 1616896 10240 :=
  join (join g84a g84b) (join g84c g84d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g85a : Tile posSum 1627136 2560 := gt (by
  have e : gw 1627136 2560 = gw 1627136 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g85b : Tile posSum 1629696 2560 := gt (by
  have e : gw 1629696 2560 = gw 1629696 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g85c : Tile posSum 1632256 2560 := gt (by
  have e : gw 1632256 2560 = gw 1632256 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g85d : Tile posSum 1634816 2560 := gt (by
  have e : gw 1634816 2560 = gw 1634816 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g85 : Tile posSum 1627136 10240 :=
  join (join g85a g85b) (join g85c g85d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g86a : Tile posSum 1637376 2560 := gt (by
  have e : gw 1637376 2560 = gw 1637376 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g86b : Tile posSum 1639936 2560 := gt (by
  have e : gw 1639936 2560 = gw 1639936 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g86c : Tile posSum 1642496 2560 := gt (by
  have e : gw 1642496 2560 = gw 1642496 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g86d : Tile posSum 1645056 2560 := gt (by
  have e : gw 1645056 2560 = gw 1645056 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g86 : Tile posSum 1637376 10240 :=
  join (join g86a g86b) (join g86c g86d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g87a : Tile posSum 1647616 2560 := gt (by
  have e : gw 1647616 2560 = gw 1647616 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g87b : Tile posSum 1650176 2560 := gt (by
  have e : gw 1650176 2560 = gw 1650176 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g87c : Tile posSum 1652736 2560 := gt (by
  have e : gw 1652736 2560 = gw 1652736 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g87d : Tile posSum 1655296 2560 := gt (by
  have e : gw 1655296 2560 = gw 1655296 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g87 : Tile posSum 1647616 10240 :=
  join (join g87a g87b) (join g87c g87d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g88a : Tile posSum 1657856 2560 := gt (by
  have e : gw 1657856 2560 = gw 1657856 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g88b : Tile posSum 1660416 2560 := gt (by
  have e : gw 1660416 2560 = gw 1660416 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g88c : Tile posSum 1662976 2560 := gt (by
  have e : gw 1662976 2560 = gw 1662976 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g88d : Tile posSum 1665536 2560 := gt (by
  have e : gw 1665536 2560 = gw 1665536 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g88 : Tile posSum 1657856 10240 :=
  join (join g88a g88b) (join g88c g88d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g89a : Tile posSum 1668096 2560 := gt (by
  have e : gw 1668096 2560 = gw 1668096 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g89b : Tile posSum 1670656 2560 := gt (by
  have e : gw 1670656 2560 = gw 1670656 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g89c : Tile posSum 1673216 2560 := gt (by
  have e : gw 1673216 2560 = gw 1673216 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g89d : Tile posSum 1675776 2560 := gt (by
  have e : gw 1675776 2560 = gw 1675776 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g89 : Tile posSum 1668096 10240 :=
  join (join g89a g89b) (join g89c g89d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g90a : Tile posSum 1678336 2560 := gt (by
  have e : gw 1678336 2560 = gw 1678336 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g90b : Tile posSum 1680896 2560 := gt (by
  have e : gw 1680896 2560 = gw 1680896 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g90c : Tile posSum 1683456 2560 := gt (by
  have e : gw 1683456 2560 = gw 1683456 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g90d : Tile posSum 1686016 2560 := gt (by
  have e : gw 1686016 2560 = gw 1686016 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g90 : Tile posSum 1678336 10240 :=
  join (join g90a g90b) (join g90c g90d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g91a : Tile posSum 1688576 2560 := gt (by
  have e : gw 1688576 2560 = gw 1688576 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g91b : Tile posSum 1691136 2560 := gt (by
  have e : gw 1691136 2560 = gw 1691136 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g91c : Tile posSum 1693696 2560 := gt (by
  have e : gw 1693696 2560 = gw 1693696 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g91d : Tile posSum 1696256 2560 := gt (by
  have e : gw 1696256 2560 = gw 1696256 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g91 : Tile posSum 1688576 10240 :=
  join (join g91a g91b) (join g91c g91d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g92a : Tile posSum 1698816 2560 := gt (by
  have e : gw 1698816 2560 = gw 1698816 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g92b : Tile posSum 1701376 2560 := gt (by
  have e : gw 1701376 2560 = gw 1701376 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g92c : Tile posSum 1703936 2560 := gt (by
  have e : gw 1703936 2560 = gw 1703936 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g92d : Tile posSum 1706496 2560 := gt (by
  have e : gw 1706496 2560 = gw 1706496 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g92 : Tile posSum 1698816 10240 :=
  join (join g92a g92b) (join g92c g92d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g93a : Tile posSum 1709056 2560 := gt (by
  have e : gw 1709056 2560 = gw 1709056 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g93b : Tile posSum 1711616 2560 := gt (by
  have e : gw 1711616 2560 = gw 1711616 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g93c : Tile posSum 1714176 2560 := gt (by
  have e : gw 1714176 2560 = gw 1714176 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g93d : Tile posSum 1716736 2560 := gt (by
  have e : gw 1716736 2560 = gw 1716736 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g93 : Tile posSum 1709056 10240 :=
  join (join g93a g93b) (join g93c g93d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g94a : Tile posSum 1719296 2560 := gt (by
  have e : gw 1719296 2560 = gw 1719296 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g94b : Tile posSum 1721856 2560 := gt (by
  have e : gw 1721856 2560 = gw 1721856 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g94c : Tile posSum 1724416 2560 := gt (by
  have e : gw 1724416 2560 = gw 1724416 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g94d : Tile posSum 1726976 2560 := gt (by
  have e : gw 1726976 2560 = gw 1726976 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g94 : Tile posSum 1719296 10240 :=
  join (join g94a g94b) (join g94c g94d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g95a : Tile posSum 1729536 2560 := gt (by
  have e : gw 1729536 2560 = gw 1729536 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g95b : Tile posSum 1732096 2560 := gt (by
  have e : gw 1732096 2560 = gw 1732096 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g95c : Tile posSum 1734656 2560 := gt (by
  have e : gw 1734656 2560 = gw 1734656 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g95d : Tile posSum 1737216 2560 := gt (by
  have e : gw 1737216 2560 = gw 1737216 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g95 : Tile posSum 1729536 10240 :=
  join (join g95a g95b) (join g95c g95d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g96a : Tile posSum 1739776 2560 := gt (by
  have e : gw 1739776 2560 = gw 1739776 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g96b : Tile posSum 1742336 2560 := gt (by
  have e : gw 1742336 2560 = gw 1742336 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g96c : Tile posSum 1744896 2560 := gt (by
  have e : gw 1744896 2560 = gw 1744896 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g96d : Tile posSum 1747456 2560 := gt (by
  have e : gw 1747456 2560 = gw 1747456 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g96 : Tile posSum 1739776 10240 :=
  join (join g96a g96b) (join g96c g96d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g97a : Tile posSum 1750016 2560 := gt (by
  have e : gw 1750016 2560 = gw 1750016 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g97b : Tile posSum 1752576 2560 := gt (by
  have e : gw 1752576 2560 = gw 1752576 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g97c : Tile posSum 1755136 2560 := gt (by
  have e : gw 1755136 2560 = gw 1755136 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g97d : Tile posSum 1757696 2560 := gt (by
  have e : gw 1757696 2560 = gw 1757696 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g97 : Tile posSum 1750016 10240 :=
  join (join g97a g97b) (join g97c g97d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g98a : Tile posSum 1760256 2560 := gt (by
  have e : gw 1760256 2560 = gw 1760256 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g98b : Tile posSum 1762816 2560 := gt (by
  have e : gw 1762816 2560 = gw 1762816 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g98c : Tile posSum 1765376 2560 := gt (by
  have e : gw 1765376 2560 = gw 1765376 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g98d : Tile posSum 1767936 2560 := gt (by
  have e : gw 1767936 2560 = gw 1767936 2560 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g98 : Tile posSum 1760256 10240 :=
  join (join g98a g98b) (join g98c g98d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g99a : Tile posSum 1770496 2304 := gt (by
  have e : gw 1770496 2304 = gw 1770496 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g99b : Tile posSum 1772800 2304 := gt (by
  have e : gw 1772800 2304 = gw 1772800 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g99c : Tile posSum 1775104 2304 := gt (by
  have e : gw 1775104 2304 = gw 1775104 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g99d : Tile posSum 1777408 2304 := gt (by
  have e : gw 1777408 2304 = gw 1777408 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g99 : Tile posSum 1770496 9216 :=
  join (join g99a g99b) (join g99c g99d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g100a : Tile posSum 1779712 2304 := gt (by
  have e : gw 1779712 2304 = gw 1779712 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g100b : Tile posSum 1782016 2304 := gt (by
  have e : gw 1782016 2304 = gw 1782016 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g100c : Tile posSum 1784320 2304 := gt (by
  have e : gw 1784320 2304 = gw 1784320 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g100d : Tile posSum 1786624 2304 := gt (by
  have e : gw 1786624 2304 = gw 1786624 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g100 : Tile posSum 1779712 9216 :=
  join (join g100a g100b) (join g100c g100d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g101a : Tile posSum 1788928 2304 := gt (by
  have e : gw 1788928 2304 = gw 1788928 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g101b : Tile posSum 1791232 2304 := gt (by
  have e : gw 1791232 2304 = gw 1791232 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g101c : Tile posSum 1793536 2304 := gt (by
  have e : gw 1793536 2304 = gw 1793536 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g101d : Tile posSum 1795840 2304 := gt (by
  have e : gw 1795840 2304 = gw 1795840 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g101 : Tile posSum 1788928 9216 :=
  join (join g101a g101b) (join g101c g101d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g102a : Tile posSum 1798144 2304 := gt (by
  have e : gw 1798144 2304 = gw 1798144 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g102b : Tile posSum 1800448 2304 := gt (by
  have e : gw 1800448 2304 = gw 1800448 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g102c : Tile posSum 1802752 2304 := gt (by
  have e : gw 1802752 2304 = gw 1802752 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g102d : Tile posSum 1805056 2304 := gt (by
  have e : gw 1805056 2304 = gw 1805056 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g102 : Tile posSum 1798144 9216 :=
  join (join g102a g102b) (join g102c g102d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g103a : Tile posSum 1807360 2304 := gt (by
  have e : gw 1807360 2304 = gw 1807360 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g103b : Tile posSum 1809664 2304 := gt (by
  have e : gw 1809664 2304 = gw 1809664 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g103c : Tile posSum 1811968 2304 := gt (by
  have e : gw 1811968 2304 = gw 1811968 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g103d : Tile posSum 1814272 2304 := gt (by
  have e : gw 1814272 2304 = gw 1814272 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g103 : Tile posSum 1807360 9216 :=
  join (join g103a g103b) (join g103c g103d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g104a : Tile posSum 1816576 2304 := gt (by
  have e : gw 1816576 2304 = gw 1816576 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g104b : Tile posSum 1818880 2304 := gt (by
  have e : gw 1818880 2304 = gw 1818880 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g104c : Tile posSum 1821184 2304 := gt (by
  have e : gw 1821184 2304 = gw 1821184 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g104d : Tile posSum 1823488 2304 := gt (by
  have e : gw 1823488 2304 = gw 1823488 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g104 : Tile posSum 1816576 9216 :=
  join (join g104a g104b) (join g104c g104d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g105a : Tile posSum 1825792 2304 := gt (by
  have e : gw 1825792 2304 = gw 1825792 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g105b : Tile posSum 1828096 2304 := gt (by
  have e : gw 1828096 2304 = gw 1828096 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g105c : Tile posSum 1830400 2304 := gt (by
  have e : gw 1830400 2304 = gw 1830400 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g105d : Tile posSum 1832704 2304 := gt (by
  have e : gw 1832704 2304 = gw 1832704 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g105 : Tile posSum 1825792 9216 :=
  join (join g105a g105b) (join g105c g105d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g106a : Tile posSum 1835008 2304 := gt (by
  have e : gw 1835008 2304 = gw 1835008 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g106b : Tile posSum 1837312 2304 := gt (by
  have e : gw 1837312 2304 = gw 1837312 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g106c : Tile posSum 1839616 2304 := gt (by
  have e : gw 1839616 2304 = gw 1839616 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g106d : Tile posSum 1841920 2304 := gt (by
  have e : gw 1841920 2304 = gw 1841920 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g106 : Tile posSum 1835008 9216 :=
  join (join g106a g106b) (join g106c g106d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g107a : Tile posSum 1844224 2304 := gt (by
  have e : gw 1844224 2304 = gw 1844224 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g107b : Tile posSum 1846528 2304 := gt (by
  have e : gw 1846528 2304 = gw 1846528 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g107c : Tile posSum 1848832 2304 := gt (by
  have e : gw 1848832 2304 = gw 1848832 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g107d : Tile posSum 1851136 2304 := gt (by
  have e : gw 1851136 2304 = gw 1851136 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g107 : Tile posSum 1844224 9216 :=
  join (join g107a g107b) (join g107c g107d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g108a : Tile posSum 1853440 2304 := gt (by
  have e : gw 1853440 2304 = gw 1853440 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g108b : Tile posSum 1855744 2304 := gt (by
  have e : gw 1855744 2304 = gw 1855744 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g108c : Tile posSum 1858048 2304 := gt (by
  have e : gw 1858048 2304 = gw 1858048 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g108d : Tile posSum 1860352 2304 := gt (by
  have e : gw 1860352 2304 = gw 1860352 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g108 : Tile posSum 1853440 9216 :=
  join (join g108a g108b) (join g108c g108d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g109a : Tile posSum 1862656 2304 := gt (by
  have e : gw 1862656 2304 = gw 1862656 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g109b : Tile posSum 1864960 2304 := gt (by
  have e : gw 1864960 2304 = gw 1864960 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g109c : Tile posSum 1867264 2304 := gt (by
  have e : gw 1867264 2304 = gw 1867264 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g109d : Tile posSum 1869568 2304 := gt (by
  have e : gw 1869568 2304 = gw 1869568 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g109 : Tile posSum 1862656 9216 :=
  join (join g109a g109b) (join g109c g109d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g110a : Tile posSum 1871872 2304 := gt (by
  have e : gw 1871872 2304 = gw 1871872 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g110b : Tile posSum 1874176 2304 := gt (by
  have e : gw 1874176 2304 = gw 1874176 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g110c : Tile posSum 1876480 2304 := gt (by
  have e : gw 1876480 2304 = gw 1876480 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g110d : Tile posSum 1878784 2304 := gt (by
  have e : gw 1878784 2304 = gw 1878784 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g110 : Tile posSum 1871872 9216 :=
  join (join g110a g110b) (join g110c g110d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g111a : Tile posSum 1881088 2304 := gt (by
  have e : gw 1881088 2304 = gw 1881088 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g111b : Tile posSum 1883392 2304 := gt (by
  have e : gw 1883392 2304 = gw 1883392 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g111c : Tile posSum 1885696 2304 := gt (by
  have e : gw 1885696 2304 = gw 1885696 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g111d : Tile posSum 1888000 2304 := gt (by
  have e : gw 1888000 2304 = gw 1888000 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g111 : Tile posSum 1881088 9216 :=
  join (join g111a g111b) (join g111c g111d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g112a : Tile posSum 1890304 2304 := gt (by
  have e : gw 1890304 2304 = gw 1890304 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g112b : Tile posSum 1892608 2304 := gt (by
  have e : gw 1892608 2304 = gw 1892608 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g112c : Tile posSum 1894912 2304 := gt (by
  have e : gw 1894912 2304 = gw 1894912 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g112d : Tile posSum 1897216 2304 := gt (by
  have e : gw 1897216 2304 = gw 1897216 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g112 : Tile posSum 1890304 9216 :=
  join (join g112a g112b) (join g112c g112d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g113a : Tile posSum 1899520 2304 := gt (by
  have e : gw 1899520 2304 = gw 1899520 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g113b : Tile posSum 1901824 2304 := gt (by
  have e : gw 1901824 2304 = gw 1901824 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g113c : Tile posSum 1904128 2304 := gt (by
  have e : gw 1904128 2304 = gw 1904128 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g113d : Tile posSum 1906432 2304 := gt (by
  have e : gw 1906432 2304 = gw 1906432 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g113 : Tile posSum 1899520 9216 :=
  join (join g113a g113b) (join g113c g113d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g114a : Tile posSum 1908736 2304 := gt (by
  have e : gw 1908736 2304 = gw 1908736 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g114b : Tile posSum 1911040 2304 := gt (by
  have e : gw 1911040 2304 = gw 1911040 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g114c : Tile posSum 1913344 2304 := gt (by
  have e : gw 1913344 2304 = gw 1913344 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g114d : Tile posSum 1915648 2304 := gt (by
  have e : gw 1915648 2304 = gw 1915648 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g114 : Tile posSum 1908736 9216 :=
  join (join g114a g114b) (join g114c g114d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g115a : Tile posSum 1917952 2304 := gt (by
  have e : gw 1917952 2304 = gw 1917952 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g115b : Tile posSum 1920256 2304 := gt (by
  have e : gw 1920256 2304 = gw 1920256 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g115c : Tile posSum 1922560 2304 := gt (by
  have e : gw 1922560 2304 = gw 1922560 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g115d : Tile posSum 1924864 2304 := gt (by
  have e : gw 1924864 2304 = gw 1924864 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g115 : Tile posSum 1917952 9216 :=
  join (join g115a g115b) (join g115c g115d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g116a : Tile posSum 1927168 2304 := gt (by
  have e : gw 1927168 2304 = gw 1927168 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g116b : Tile posSum 1929472 2304 := gt (by
  have e : gw 1929472 2304 = gw 1929472 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g116c : Tile posSum 1931776 2304 := gt (by
  have e : gw 1931776 2304 = gw 1931776 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g116d : Tile posSum 1934080 2304 := gt (by
  have e : gw 1934080 2304 = gw 1934080 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g116 : Tile posSum 1927168 9216 :=
  join (join g116a g116b) (join g116c g116d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g117a : Tile posSum 1936384 2304 := gt (by
  have e : gw 1936384 2304 = gw 1936384 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g117b : Tile posSum 1938688 2304 := gt (by
  have e : gw 1938688 2304 = gw 1938688 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g117c : Tile posSum 1940992 2304 := gt (by
  have e : gw 1940992 2304 = gw 1940992 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g117d : Tile posSum 1943296 2304 := gt (by
  have e : gw 1943296 2304 = gw 1943296 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g117 : Tile posSum 1936384 9216 :=
  join (join g117a g117b) (join g117c g117d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g118a : Tile posSum 1945600 2304 := gt (by
  have e : gw 1945600 2304 = gw 1945600 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g118b : Tile posSum 1947904 2304 := gt (by
  have e : gw 1947904 2304 = gw 1947904 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g118c : Tile posSum 1950208 2304 := gt (by
  have e : gw 1950208 2304 = gw 1950208 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g118d : Tile posSum 1952512 2304 := gt (by
  have e : gw 1952512 2304 = gw 1952512 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g118 : Tile posSum 1945600 9216 :=
  join (join g118a g118b) (join g118c g118d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g119a : Tile posSum 1954816 2304 := gt (by
  have e : gw 1954816 2304 = gw 1954816 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g119b : Tile posSum 1957120 2304 := gt (by
  have e : gw 1957120 2304 = gw 1957120 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g119c : Tile posSum 1959424 2304 := gt (by
  have e : gw 1959424 2304 = gw 1959424 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g119d : Tile posSum 1961728 2304 := gt (by
  have e : gw 1961728 2304 = gw 1961728 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g119 : Tile posSum 1954816 9216 :=
  join (join g119a g119b) (join g119c g119d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g120a : Tile posSum 1964032 2304 := gt (by
  have e : gw 1964032 2304 = gw 1964032 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g120b : Tile posSum 1966336 2304 := gt (by
  have e : gw 1966336 2304 = gw 1966336 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g120c : Tile posSum 1968640 2304 := gt (by
  have e : gw 1968640 2304 = gw 1968640 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g120d : Tile posSum 1970944 2304 := gt (by
  have e : gw 1970944 2304 = gw 1970944 2304 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g120 : Tile posSum 1964032 9216 :=
  join (join g120a g120b) (join g120c g120d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g121a : Tile posSum 1973248 2048 := gt (by
  have e : gw 1973248 2048 = gw 1973248 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g121b : Tile posSum 1975296 2048 := gt (by
  have e : gw 1975296 2048 = gw 1975296 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g121c : Tile posSum 1977344 2048 := gt (by
  have e : gw 1977344 2048 = gw 1977344 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g121d : Tile posSum 1979392 2048 := gt (by
  have e : gw 1979392 2048 = gw 1979392 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g121 : Tile posSum 1973248 8192 :=
  join (join g121a g121b) (join g121c g121d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g122a : Tile posSum 1981440 2048 := gt (by
  have e : gw 1981440 2048 = gw 1981440 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g122b : Tile posSum 1983488 2048 := gt (by
  have e : gw 1983488 2048 = gw 1983488 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g122c : Tile posSum 1985536 2048 := gt (by
  have e : gw 1985536 2048 = gw 1985536 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g122d : Tile posSum 1987584 2048 := gt (by
  have e : gw 1987584 2048 = gw 1987584 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g122 : Tile posSum 1981440 8192 :=
  join (join g122a g122b) (join g122c g122d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g123a : Tile posSum 1989632 2048 := gt (by
  have e : gw 1989632 2048 = gw 1989632 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g123b : Tile posSum 1991680 2048 := gt (by
  have e : gw 1991680 2048 = gw 1991680 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g123c : Tile posSum 1993728 2048 := gt (by
  have e : gw 1993728 2048 = gw 1993728 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g123d : Tile posSum 1995776 2048 := gt (by
  have e : gw 1995776 2048 = gw 1995776 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g123 : Tile posSum 1989632 8192 :=
  join (join g123a g123b) (join g123c g123d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g124a : Tile posSum 1997824 2048 := gt (by
  have e : gw 1997824 2048 = gw 1997824 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g124b : Tile posSum 1999872 2048 := gt (by
  have e : gw 1999872 2048 = gw 1999872 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g124c : Tile posSum 2001920 2048 := gt (by
  have e : gw 2001920 2048 = gw 2001920 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g124d : Tile posSum 2003968 2048 := gt (by
  have e : gw 2003968 2048 = gw 2003968 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g124 : Tile posSum 1997824 8192 :=
  join (join g124a g124b) (join g124c g124d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g125a : Tile posSum 2006016 2048 := gt (by
  have e : gw 2006016 2048 = gw 2006016 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g125b : Tile posSum 2008064 2048 := gt (by
  have e : gw 2008064 2048 = gw 2008064 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g125c : Tile posSum 2010112 2048 := gt (by
  have e : gw 2010112 2048 = gw 2010112 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g125d : Tile posSum 2012160 2048 := gt (by
  have e : gw 2012160 2048 = gw 2012160 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g125 : Tile posSum 2006016 8192 :=
  join (join g125a g125b) (join g125c g125d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g126a : Tile posSum 2014208 2048 := gt (by
  have e : gw 2014208 2048 = gw 2014208 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g126b : Tile posSum 2016256 2048 := gt (by
  have e : gw 2016256 2048 = gw 2016256 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g126c : Tile posSum 2018304 2048 := gt (by
  have e : gw 2018304 2048 = gw 2018304 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g126d : Tile posSum 2020352 2048 := gt (by
  have e : gw 2020352 2048 = gw 2020352 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g126 : Tile posSum 2014208 8192 :=
  join (join g126a g126b) (join g126c g126d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g127a : Tile posSum 2022400 2048 := gt (by
  have e : gw 2022400 2048 = gw 2022400 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g127b : Tile posSum 2024448 2048 := gt (by
  have e : gw 2024448 2048 = gw 2024448 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g127c : Tile posSum 2026496 2048 := gt (by
  have e : gw 2026496 2048 = gw 2026496 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g127d : Tile posSum 2028544 2048 := gt (by
  have e : gw 2028544 2048 = gw 2028544 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g127 : Tile posSum 2022400 8192 :=
  join (join g127a g127b) (join g127c g127d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g128a : Tile posSum 2030592 2048 := gt (by
  have e : gw 2030592 2048 = gw 2030592 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g128b : Tile posSum 2032640 2048 := gt (by
  have e : gw 2032640 2048 = gw 2032640 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g128c : Tile posSum 2034688 2048 := gt (by
  have e : gw 2034688 2048 = gw 2034688 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g128d : Tile posSum 2036736 2048 := gt (by
  have e : gw 2036736 2048 = gw 2036736 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g128 : Tile posSum 2030592 8192 :=
  join (join g128a g128b) (join g128c g128d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g129a : Tile posSum 2038784 2048 := gt (by
  have e : gw 2038784 2048 = gw 2038784 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g129b : Tile posSum 2040832 2048 := gt (by
  have e : gw 2040832 2048 = gw 2040832 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g129c : Tile posSum 2042880 2048 := gt (by
  have e : gw 2042880 2048 = gw 2042880 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g129d : Tile posSum 2044928 2048 := gt (by
  have e : gw 2044928 2048 = gw 2044928 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g129 : Tile posSum 2038784 8192 :=
  join (join g129a g129b) (join g129c g129d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g130a : Tile posSum 2046976 2048 := gt (by
  have e : gw 2046976 2048 = gw 2046976 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g130b : Tile posSum 2049024 2048 := gt (by
  have e : gw 2049024 2048 = gw 2049024 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g130c : Tile posSum 2051072 2048 := gt (by
  have e : gw 2051072 2048 = gw 2051072 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g130d : Tile posSum 2053120 2048 := gt (by
  have e : gw 2053120 2048 = gw 2053120 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g130 : Tile posSum 2046976 8192 :=
  join (join g130a g130b) (join g130c g130d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g131a : Tile posSum 2055168 2048 := gt (by
  have e : gw 2055168 2048 = gw 2055168 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g131b : Tile posSum 2057216 2048 := gt (by
  have e : gw 2057216 2048 = gw 2057216 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g131c : Tile posSum 2059264 2048 := gt (by
  have e : gw 2059264 2048 = gw 2059264 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g131d : Tile posSum 2061312 2048 := gt (by
  have e : gw 2061312 2048 = gw 2061312 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g131 : Tile posSum 2055168 8192 :=
  join (join g131a g131b) (join g131c g131d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g132a : Tile posSum 2063360 2048 := gt (by
  have e : gw 2063360 2048 = gw 2063360 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g132b : Tile posSum 2065408 2048 := gt (by
  have e : gw 2065408 2048 = gw 2065408 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g132c : Tile posSum 2067456 2048 := gt (by
  have e : gw 2067456 2048 = gw 2067456 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g132d : Tile posSum 2069504 2048 := gt (by
  have e : gw 2069504 2048 = gw 2069504 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g132 : Tile posSum 2063360 8192 :=
  join (join g132a g132b) (join g132c g132d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g133a : Tile posSum 2071552 2048 := gt (by
  have e : gw 2071552 2048 = gw 2071552 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g133b : Tile posSum 2073600 2048 := gt (by
  have e : gw 2073600 2048 = gw 2073600 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g133c : Tile posSum 2075648 2048 := gt (by
  have e : gw 2075648 2048 = gw 2075648 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g133d : Tile posSum 2077696 2048 := gt (by
  have e : gw 2077696 2048 = gw 2077696 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g133 : Tile posSum 2071552 8192 :=
  join (join g133a g133b) (join g133c g133d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g134a : Tile posSum 2079744 2048 := gt (by
  have e : gw 2079744 2048 = gw 2079744 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g134b : Tile posSum 2081792 2048 := gt (by
  have e : gw 2081792 2048 = gw 2081792 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g134c : Tile posSum 2083840 2048 := gt (by
  have e : gw 2083840 2048 = gw 2083840 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g134d : Tile posSum 2085888 2048 := gt (by
  have e : gw 2085888 2048 = gw 2085888 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g134 : Tile posSum 2079744 8192 :=
  join (join g134a g134b) (join g134c g134d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g135a : Tile posSum 2087936 2048 := gt (by
  have e : gw 2087936 2048 = gw 2087936 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g135b : Tile posSum 2089984 2048 := gt (by
  have e : gw 2089984 2048 = gw 2089984 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g135c : Tile posSum 2092032 2048 := gt (by
  have e : gw 2092032 2048 = gw 2092032 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g135d : Tile posSum 2094080 2048 := gt (by
  have e : gw 2094080 2048 = gw 2094080 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g135 : Tile posSum 2087936 8192 :=
  join (join g135a g135b) (join g135c g135d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g136a : Tile posSum 2096128 2048 := gt (by
  have e : gw 2096128 2048 = gw 2096128 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g136b : Tile posSum 2098176 2048 := gt (by
  have e : gw 2098176 2048 = gw 2098176 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g136c : Tile posSum 2100224 2048 := gt (by
  have e : gw 2100224 2048 = gw 2100224 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g136d : Tile posSum 2102272 2048 := gt (by
  have e : gw 2102272 2048 = gw 2102272 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g136 : Tile posSum 2096128 8192 :=
  join (join g136a g136b) (join g136c g136d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g137a : Tile posSum 2104320 2048 := gt (by
  have e : gw 2104320 2048 = gw 2104320 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g137b : Tile posSum 2106368 2048 := gt (by
  have e : gw 2106368 2048 = gw 2106368 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g137c : Tile posSum 2108416 2048 := gt (by
  have e : gw 2108416 2048 = gw 2108416 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g137d : Tile posSum 2110464 2048 := gt (by
  have e : gw 2110464 2048 = gw 2110464 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g137 : Tile posSum 2104320 8192 :=
  join (join g137a g137b) (join g137c g137d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g138a : Tile posSum 2112512 2048 := gt (by
  have e : gw 2112512 2048 = gw 2112512 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g138b : Tile posSum 2114560 2048 := gt (by
  have e : gw 2114560 2048 = gw 2114560 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g138c : Tile posSum 2116608 2048 := gt (by
  have e : gw 2116608 2048 = gw 2116608 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g138d : Tile posSum 2118656 2048 := gt (by
  have e : gw 2118656 2048 = gw 2118656 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g138 : Tile posSum 2112512 8192 :=
  join (join g138a g138b) (join g138c g138d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g139a : Tile posSum 2120704 2048 := gt (by
  have e : gw 2120704 2048 = gw 2120704 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g139b : Tile posSum 2122752 2048 := gt (by
  have e : gw 2122752 2048 = gw 2122752 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g139c : Tile posSum 2124800 2048 := gt (by
  have e : gw 2124800 2048 = gw 2124800 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g139d : Tile posSum 2126848 2048 := gt (by
  have e : gw 2126848 2048 = gw 2126848 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g139 : Tile posSum 2120704 8192 :=
  join (join g139a g139b) (join g139c g139d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g140a : Tile posSum 2128896 2048 := gt (by
  have e : gw 2128896 2048 = gw 2128896 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g140b : Tile posSum 2130944 2048 := gt (by
  have e : gw 2130944 2048 = gw 2130944 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g140c : Tile posSum 2132992 2048 := gt (by
  have e : gw 2132992 2048 = gw 2132992 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g140d : Tile posSum 2135040 2048 := gt (by
  have e : gw 2135040 2048 = gw 2135040 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g140 : Tile posSum 2128896 8192 :=
  join (join g140a g140b) (join g140c g140d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g141a : Tile posSum 2137088 2048 := gt (by
  have e : gw 2137088 2048 = gw 2137088 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g141b : Tile posSum 2139136 2048 := gt (by
  have e : gw 2139136 2048 = gw 2139136 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g141c : Tile posSum 2141184 2048 := gt (by
  have e : gw 2141184 2048 = gw 2141184 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g141d : Tile posSum 2143232 2048 := gt (by
  have e : gw 2143232 2048 = gw 2143232 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g141 : Tile posSum 2137088 8192 :=
  join (join g141a g141b) (join g141c g141d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g142a : Tile posSum 2145280 2048 := gt (by
  have e : gw 2145280 2048 = gw 2145280 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g142b : Tile posSum 2147328 2048 := gt (by
  have e : gw 2147328 2048 = gw 2147328 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g142c : Tile posSum 2149376 2048 := gt (by
  have e : gw 2149376 2048 = gw 2149376 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g142d : Tile posSum 2151424 2048 := gt (by
  have e : gw 2151424 2048 = gw 2151424 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g142 : Tile posSum 2145280 8192 :=
  join (join g142a g142b) (join g142c g142d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g143a : Tile posSum 2153472 2048 := gt (by
  have e : gw 2153472 2048 = gw 2153472 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g143b : Tile posSum 2155520 2048 := gt (by
  have e : gw 2155520 2048 = gw 2155520 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g143c : Tile posSum 2157568 2048 := gt (by
  have e : gw 2157568 2048 = gw 2157568 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g143d : Tile posSum 2159616 2048 := gt (by
  have e : gw 2159616 2048 = gw 2159616 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g143 : Tile posSum 2153472 8192 :=
  join (join g143a g143b) (join g143c g143d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g144a : Tile posSum 2161664 2048 := gt (by
  have e : gw 2161664 2048 = gw 2161664 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g144b : Tile posSum 2163712 2048 := gt (by
  have e : gw 2163712 2048 = gw 2163712 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g144c : Tile posSum 2165760 2048 := gt (by
  have e : gw 2165760 2048 = gw 2165760 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g144d : Tile posSum 2167808 2048 := gt (by
  have e : gw 2167808 2048 = gw 2167808 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g144 : Tile posSum 2161664 8192 :=
  join (join g144a g144b) (join g144c g144d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g145a : Tile posSum 2169856 2048 := gt (by
  have e : gw 2169856 2048 = gw 2169856 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g145b : Tile posSum 2171904 2048 := gt (by
  have e : gw 2171904 2048 = gw 2171904 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g145c : Tile posSum 2173952 2048 := gt (by
  have e : gw 2173952 2048 = gw 2173952 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g145d : Tile posSum 2176000 2048 := gt (by
  have e : gw 2176000 2048 = gw 2176000 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g145 : Tile posSum 2169856 8192 :=
  join (join g145a g145b) (join g145c g145d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g146a : Tile posSum 2178048 2048 := gt (by
  have e : gw 2178048 2048 = gw 2178048 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g146b : Tile posSum 2180096 2048 := gt (by
  have e : gw 2180096 2048 = gw 2180096 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g146c : Tile posSum 2182144 2048 := gt (by
  have e : gw 2182144 2048 = gw 2182144 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g146d : Tile posSum 2184192 2048 := gt (by
  have e : gw 2184192 2048 = gw 2184192 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g146 : Tile posSum 2178048 8192 :=
  join (join g146a g146b) (join g146c g146d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g147a : Tile posSum 2186240 2048 := gt (by
  have e : gw 2186240 2048 = gw 2186240 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g147b : Tile posSum 2188288 2048 := gt (by
  have e : gw 2188288 2048 = gw 2188288 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g147c : Tile posSum 2190336 2048 := gt (by
  have e : gw 2190336 2048 = gw 2190336 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g147d : Tile posSum 2192384 2048 := gt (by
  have e : gw 2192384 2048 = gw 2192384 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g147 : Tile posSum 2186240 8192 :=
  join (join g147a g147b) (join g147c g147d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g148a : Tile posSum 2194432 2048 := gt (by
  have e : gw 2194432 2048 = gw 2194432 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g148b : Tile posSum 2196480 2048 := gt (by
  have e : gw 2196480 2048 = gw 2196480 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g148c : Tile posSum 2198528 2048 := gt (by
  have e : gw 2198528 2048 = gw 2198528 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g148d : Tile posSum 2200576 2048 := gt (by
  have e : gw 2200576 2048 = gw 2200576 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g148 : Tile posSum 2194432 8192 :=
  join (join g148a g148b) (join g148c g148d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g149a : Tile posSum 2202624 2048 := gt (by
  have e : gw 2202624 2048 = gw 2202624 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g149b : Tile posSum 2204672 2048 := gt (by
  have e : gw 2204672 2048 = gw 2204672 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g149c : Tile posSum 2206720 2048 := gt (by
  have e : gw 2206720 2048 = gw 2206720 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g149d : Tile posSum 2208768 2048 := gt (by
  have e : gw 2208768 2048 = gw 2208768 2048 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g149 : Tile posSum 2202624 8192 :=
  join (join g149a g149b) (join g149c g149d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g150a : Tile posSum 2210816 1792 := gt (by
  have e : gw 2210816 1792 = gw 2210816 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g150b : Tile posSum 2212608 1792 := gt (by
  have e : gw 2212608 1792 = gw 2212608 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g150c : Tile posSum 2214400 1792 := gt (by
  have e : gw 2214400 1792 = gw 2214400 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g150d : Tile posSum 2216192 1792 := gt (by
  have e : gw 2216192 1792 = gw 2216192 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g150 : Tile posSum 2210816 7168 :=
  join (join g150a g150b) (join g150c g150d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g151a : Tile posSum 2217984 1792 := gt (by
  have e : gw 2217984 1792 = gw 2217984 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g151b : Tile posSum 2219776 1792 := gt (by
  have e : gw 2219776 1792 = gw 2219776 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g151c : Tile posSum 2221568 1792 := gt (by
  have e : gw 2221568 1792 = gw 2221568 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g151d : Tile posSum 2223360 1792 := gt (by
  have e : gw 2223360 1792 = gw 2223360 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g151 : Tile posSum 2217984 7168 :=
  join (join g151a g151b) (join g151c g151d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g152a : Tile posSum 2225152 1792 := gt (by
  have e : gw 2225152 1792 = gw 2225152 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g152b : Tile posSum 2226944 1792 := gt (by
  have e : gw 2226944 1792 = gw 2226944 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g152c : Tile posSum 2228736 1792 := gt (by
  have e : gw 2228736 1792 = gw 2228736 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g152d : Tile posSum 2230528 1792 := gt (by
  have e : gw 2230528 1792 = gw 2230528 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g152 : Tile posSum 2225152 7168 :=
  join (join g152a g152b) (join g152c g152d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g153a : Tile posSum 2232320 1792 := gt (by
  have e : gw 2232320 1792 = gw 2232320 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g153b : Tile posSum 2234112 1792 := gt (by
  have e : gw 2234112 1792 = gw 2234112 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g153c : Tile posSum 2235904 1792 := gt (by
  have e : gw 2235904 1792 = gw 2235904 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g153d : Tile posSum 2237696 1792 := gt (by
  have e : gw 2237696 1792 = gw 2237696 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g153 : Tile posSum 2232320 7168 :=
  join (join g153a g153b) (join g153c g153d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g154a : Tile posSum 2239488 1792 := gt (by
  have e : gw 2239488 1792 = gw 2239488 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g154b : Tile posSum 2241280 1792 := gt (by
  have e : gw 2241280 1792 = gw 2241280 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g154c : Tile posSum 2243072 1792 := gt (by
  have e : gw 2243072 1792 = gw 2243072 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g154d : Tile posSum 2244864 1792 := gt (by
  have e : gw 2244864 1792 = gw 2244864 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g154 : Tile posSum 2239488 7168 :=
  join (join g154a g154b) (join g154c g154d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g155a : Tile posSum 2246656 1792 := gt (by
  have e : gw 2246656 1792 = gw 2246656 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g155b : Tile posSum 2248448 1792 := gt (by
  have e : gw 2248448 1792 = gw 2248448 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g155c : Tile posSum 2250240 1792 := gt (by
  have e : gw 2250240 1792 = gw 2250240 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g155d : Tile posSum 2252032 1792 := gt (by
  have e : gw 2252032 1792 = gw 2252032 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g155 : Tile posSum 2246656 7168 :=
  join (join g155a g155b) (join g155c g155d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g156a : Tile posSum 2253824 1792 := gt (by
  have e : gw 2253824 1792 = gw 2253824 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g156b : Tile posSum 2255616 1792 := gt (by
  have e : gw 2255616 1792 = gw 2255616 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g156c : Tile posSum 2257408 1792 := gt (by
  have e : gw 2257408 1792 = gw 2257408 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g156d : Tile posSum 2259200 1792 := gt (by
  have e : gw 2259200 1792 = gw 2259200 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g156 : Tile posSum 2253824 7168 :=
  join (join g156a g156b) (join g156c g156d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g157a : Tile posSum 2260992 1792 := gt (by
  have e : gw 2260992 1792 = gw 2260992 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g157b : Tile posSum 2262784 1792 := gt (by
  have e : gw 2262784 1792 = gw 2262784 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g157c : Tile posSum 2264576 1792 := gt (by
  have e : gw 2264576 1792 = gw 2264576 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g157d : Tile posSum 2266368 1792 := gt (by
  have e : gw 2266368 1792 = gw 2266368 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g157 : Tile posSum 2260992 7168 :=
  join (join g157a g157b) (join g157c g157d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g158a : Tile posSum 2268160 1792 := gt (by
  have e : gw 2268160 1792 = gw 2268160 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g158b : Tile posSum 2269952 1792 := gt (by
  have e : gw 2269952 1792 = gw 2269952 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g158c : Tile posSum 2271744 1792 := gt (by
  have e : gw 2271744 1792 = gw 2271744 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g158d : Tile posSum 2273536 1792 := gt (by
  have e : gw 2273536 1792 = gw 2273536 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g158 : Tile posSum 2268160 7168 :=
  join (join g158a g158b) (join g158c g158d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g159a : Tile posSum 2275328 1792 := gt (by
  have e : gw 2275328 1792 = gw 2275328 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g159b : Tile posSum 2277120 1792 := gt (by
  have e : gw 2277120 1792 = gw 2277120 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g159c : Tile posSum 2278912 1792 := gt (by
  have e : gw 2278912 1792 = gw 2278912 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g159d : Tile posSum 2280704 1792 := gt (by
  have e : gw 2280704 1792 = gw 2280704 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g159 : Tile posSum 2275328 7168 :=
  join (join g159a g159b) (join g159c g159d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g160a : Tile posSum 2282496 1792 := gt (by
  have e : gw 2282496 1792 = gw 2282496 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g160b : Tile posSum 2284288 1792 := gt (by
  have e : gw 2284288 1792 = gw 2284288 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g160c : Tile posSum 2286080 1792 := gt (by
  have e : gw 2286080 1792 = gw 2286080 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g160d : Tile posSum 2287872 1792 := gt (by
  have e : gw 2287872 1792 = gw 2287872 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g160 : Tile posSum 2282496 7168 :=
  join (join g160a g160b) (join g160c g160d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g161a : Tile posSum 2289664 1792 := gt (by
  have e : gw 2289664 1792 = gw 2289664 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g161b : Tile posSum 2291456 1792 := gt (by
  have e : gw 2291456 1792 = gw 2291456 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g161c : Tile posSum 2293248 1792 := gt (by
  have e : gw 2293248 1792 = gw 2293248 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g161d : Tile posSum 2295040 1792 := gt (by
  have e : gw 2295040 1792 = gw 2295040 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g161 : Tile posSum 2289664 7168 :=
  join (join g161a g161b) (join g161c g161d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g162a : Tile posSum 2296832 1792 := gt (by
  have e : gw 2296832 1792 = gw 2296832 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g162b : Tile posSum 2298624 1792 := gt (by
  have e : gw 2298624 1792 = gw 2298624 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g162c : Tile posSum 2300416 1792 := gt (by
  have e : gw 2300416 1792 = gw 2300416 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g162d : Tile posSum 2302208 1792 := gt (by
  have e : gw 2302208 1792 = gw 2302208 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g162 : Tile posSum 2296832 7168 :=
  join (join g162a g162b) (join g162c g162d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g163a : Tile posSum 2304000 1792 := gt (by
  have e : gw 2304000 1792 = gw 2304000 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g163b : Tile posSum 2305792 1792 := gt (by
  have e : gw 2305792 1792 = gw 2305792 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g163c : Tile posSum 2307584 1792 := gt (by
  have e : gw 2307584 1792 = gw 2307584 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g163d : Tile posSum 2309376 1792 := gt (by
  have e : gw 2309376 1792 = gw 2309376 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g163 : Tile posSum 2304000 7168 :=
  join (join g163a g163b) (join g163c g163d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g164a : Tile posSum 2311168 1792 := gt (by
  have e : gw 2311168 1792 = gw 2311168 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g164b : Tile posSum 2312960 1792 := gt (by
  have e : gw 2312960 1792 = gw 2312960 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g164c : Tile posSum 2314752 1792 := gt (by
  have e : gw 2314752 1792 = gw 2314752 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g164d : Tile posSum 2316544 1792 := gt (by
  have e : gw 2316544 1792 = gw 2316544 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g164 : Tile posSum 2311168 7168 :=
  join (join g164a g164b) (join g164c g164d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g165a : Tile posSum 2318336 1792 := gt (by
  have e : gw 2318336 1792 = gw 2318336 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g165b : Tile posSum 2320128 1792 := gt (by
  have e : gw 2320128 1792 = gw 2320128 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g165c : Tile posSum 2321920 1792 := gt (by
  have e : gw 2321920 1792 = gw 2321920 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g165d : Tile posSum 2323712 1792 := gt (by
  have e : gw 2323712 1792 = gw 2323712 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g165 : Tile posSum 2318336 7168 :=
  join (join g165a g165b) (join g165c g165d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g166a : Tile posSum 2325504 1792 := gt (by
  have e : gw 2325504 1792 = gw 2325504 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g166b : Tile posSum 2327296 1792 := gt (by
  have e : gw 2327296 1792 = gw 2327296 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g166c : Tile posSum 2329088 1792 := gt (by
  have e : gw 2329088 1792 = gw 2329088 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g166d : Tile posSum 2330880 1792 := gt (by
  have e : gw 2330880 1792 = gw 2330880 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g166 : Tile posSum 2325504 7168 :=
  join (join g166a g166b) (join g166c g166d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g167a : Tile posSum 2332672 1792 := gt (by
  have e : gw 2332672 1792 = gw 2332672 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g167b : Tile posSum 2334464 1792 := gt (by
  have e : gw 2334464 1792 = gw 2334464 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g167c : Tile posSum 2336256 1792 := gt (by
  have e : gw 2336256 1792 = gw 2336256 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g167d : Tile posSum 2338048 1792 := gt (by
  have e : gw 2338048 1792 = gw 2338048 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g167 : Tile posSum 2332672 7168 :=
  join (join g167a g167b) (join g167c g167d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g168a : Tile posSum 2339840 1792 := gt (by
  have e : gw 2339840 1792 = gw 2339840 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g168b : Tile posSum 2341632 1792 := gt (by
  have e : gw 2341632 1792 = gw 2341632 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g168c : Tile posSum 2343424 1792 := gt (by
  have e : gw 2343424 1792 = gw 2343424 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g168d : Tile posSum 2345216 1792 := gt (by
  have e : gw 2345216 1792 = gw 2345216 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g168 : Tile posSum 2339840 7168 :=
  join (join g168a g168b) (join g168c g168d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g169a : Tile posSum 2347008 1792 := gt (by
  have e : gw 2347008 1792 = gw 2347008 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g169b : Tile posSum 2348800 1792 := gt (by
  have e : gw 2348800 1792 = gw 2348800 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g169c : Tile posSum 2350592 1792 := gt (by
  have e : gw 2350592 1792 = gw 2350592 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g169d : Tile posSum 2352384 1792 := gt (by
  have e : gw 2352384 1792 = gw 2352384 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g169 : Tile posSum 2347008 7168 :=
  join (join g169a g169b) (join g169c g169d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g170a : Tile posSum 2354176 1792 := gt (by
  have e : gw 2354176 1792 = gw 2354176 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g170b : Tile posSum 2355968 1792 := gt (by
  have e : gw 2355968 1792 = gw 2355968 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g170c : Tile posSum 2357760 1792 := gt (by
  have e : gw 2357760 1792 = gw 2357760 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g170d : Tile posSum 2359552 1792 := gt (by
  have e : gw 2359552 1792 = gw 2359552 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g170 : Tile posSum 2354176 7168 :=
  join (join g170a g170b) (join g170c g170d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g171a : Tile posSum 2361344 1792 := gt (by
  have e : gw 2361344 1792 = gw 2361344 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g171b : Tile posSum 2363136 1792 := gt (by
  have e : gw 2363136 1792 = gw 2363136 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g171c : Tile posSum 2364928 1792 := gt (by
  have e : gw 2364928 1792 = gw 2364928 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g171d : Tile posSum 2366720 1792 := gt (by
  have e : gw 2366720 1792 = gw 2366720 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g171 : Tile posSum 2361344 7168 :=
  join (join g171a g171b) (join g171c g171d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g172a : Tile posSum 2368512 1792 := gt (by
  have e : gw 2368512 1792 = gw 2368512 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g172b : Tile posSum 2370304 1792 := gt (by
  have e : gw 2370304 1792 = gw 2370304 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g172c : Tile posSum 2372096 1792 := gt (by
  have e : gw 2372096 1792 = gw 2372096 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g172d : Tile posSum 2373888 1792 := gt (by
  have e : gw 2373888 1792 = gw 2373888 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g172 : Tile posSum 2368512 7168 :=
  join (join g172a g172b) (join g172c g172d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g173a : Tile posSum 2375680 1792 := gt (by
  have e : gw 2375680 1792 = gw 2375680 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g173b : Tile posSum 2377472 1792 := gt (by
  have e : gw 2377472 1792 = gw 2377472 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g173c : Tile posSum 2379264 1792 := gt (by
  have e : gw 2379264 1792 = gw 2379264 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g173d : Tile posSum 2381056 1792 := gt (by
  have e : gw 2381056 1792 = gw 2381056 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g173 : Tile posSum 2375680 7168 :=
  join (join g173a g173b) (join g173c g173d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g174a : Tile posSum 2382848 1792 := gt (by
  have e : gw 2382848 1792 = gw 2382848 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g174b : Tile posSum 2384640 1792 := gt (by
  have e : gw 2384640 1792 = gw 2384640 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g174c : Tile posSum 2386432 1792 := gt (by
  have e : gw 2386432 1792 = gw 2386432 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g174d : Tile posSum 2388224 1792 := gt (by
  have e : gw 2388224 1792 = gw 2388224 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g174 : Tile posSum 2382848 7168 :=
  join (join g174a g174b) (join g174c g174d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g175a : Tile posSum 2390016 1792 := gt (by
  have e : gw 2390016 1792 = gw 2390016 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g175b : Tile posSum 2391808 1792 := gt (by
  have e : gw 2391808 1792 = gw 2391808 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g175c : Tile posSum 2393600 1792 := gt (by
  have e : gw 2393600 1792 = gw 2393600 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g175d : Tile posSum 2395392 1792 := gt (by
  have e : gw 2395392 1792 = gw 2395392 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g175 : Tile posSum 2390016 7168 :=
  join (join g175a g175b) (join g175c g175d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g176a : Tile posSum 2397184 1792 := gt (by
  have e : gw 2397184 1792 = gw 2397184 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g176b : Tile posSum 2398976 1792 := gt (by
  have e : gw 2398976 1792 = gw 2398976 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g176c : Tile posSum 2400768 1792 := gt (by
  have e : gw 2400768 1792 = gw 2400768 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g176d : Tile posSum 2402560 1792 := gt (by
  have e : gw 2402560 1792 = gw 2402560 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g176 : Tile posSum 2397184 7168 :=
  join (join g176a g176b) (join g176c g176d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g177a : Tile posSum 2404352 1792 := gt (by
  have e : gw 2404352 1792 = gw 2404352 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g177b : Tile posSum 2406144 1792 := gt (by
  have e : gw 2406144 1792 = gw 2406144 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g177c : Tile posSum 2407936 1792 := gt (by
  have e : gw 2407936 1792 = gw 2407936 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g177d : Tile posSum 2409728 1792 := gt (by
  have e : gw 2409728 1792 = gw 2409728 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g177 : Tile posSum 2404352 7168 :=
  join (join g177a g177b) (join g177c g177d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g178a : Tile posSum 2411520 1792 := gt (by
  have e : gw 2411520 1792 = gw 2411520 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g178b : Tile posSum 2413312 1792 := gt (by
  have e : gw 2413312 1792 = gw 2413312 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g178c : Tile posSum 2415104 1792 := gt (by
  have e : gw 2415104 1792 = gw 2415104 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g178d : Tile posSum 2416896 1792 := gt (by
  have e : gw 2416896 1792 = gw 2416896 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g178 : Tile posSum 2411520 7168 :=
  join (join g178a g178b) (join g178c g178d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g179a : Tile posSum 2418688 1792 := gt (by
  have e : gw 2418688 1792 = gw 2418688 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g179b : Tile posSum 2420480 1792 := gt (by
  have e : gw 2420480 1792 = gw 2420480 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g179c : Tile posSum 2422272 1792 := gt (by
  have e : gw 2422272 1792 = gw 2422272 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g179d : Tile posSum 2424064 1792 := gt (by
  have e : gw 2424064 1792 = gw 2424064 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g179 : Tile posSum 2418688 7168 :=
  join (join g179a g179b) (join g179c g179d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g180a : Tile posSum 2425856 1792 := gt (by
  have e : gw 2425856 1792 = gw 2425856 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g180b : Tile posSum 2427648 1792 := gt (by
  have e : gw 2427648 1792 = gw 2427648 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g180c : Tile posSum 2429440 1792 := gt (by
  have e : gw 2429440 1792 = gw 2429440 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g180d : Tile posSum 2431232 1792 := gt (by
  have e : gw 2431232 1792 = gw 2431232 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g180 : Tile posSum 2425856 7168 :=
  join (join g180a g180b) (join g180c g180d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g181a : Tile posSum 2433024 1792 := gt (by
  have e : gw 2433024 1792 = gw 2433024 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g181b : Tile posSum 2434816 1792 := gt (by
  have e : gw 2434816 1792 = gw 2434816 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g181c : Tile posSum 2436608 1792 := gt (by
  have e : gw 2436608 1792 = gw 2436608 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g181d : Tile posSum 2438400 1792 := gt (by
  have e : gw 2438400 1792 = gw 2438400 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g181 : Tile posSum 2433024 7168 :=
  join (join g181a g181b) (join g181c g181d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g182a : Tile posSum 2440192 1792 := gt (by
  have e : gw 2440192 1792 = gw 2440192 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g182b : Tile posSum 2441984 1792 := gt (by
  have e : gw 2441984 1792 = gw 2441984 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g182c : Tile posSum 2443776 1792 := gt (by
  have e : gw 2443776 1792 = gw 2443776 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g182d : Tile posSum 2445568 1792 := gt (by
  have e : gw 2445568 1792 = gw 2445568 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g182 : Tile posSum 2440192 7168 :=
  join (join g182a g182b) (join g182c g182d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g183a : Tile posSum 2447360 1792 := gt (by
  have e : gw 2447360 1792 = gw 2447360 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g183b : Tile posSum 2449152 1792 := gt (by
  have e : gw 2449152 1792 = gw 2449152 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g183c : Tile posSum 2450944 1792 := gt (by
  have e : gw 2450944 1792 = gw 2450944 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g183d : Tile posSum 2452736 1792 := gt (by
  have e : gw 2452736 1792 = gw 2452736 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g183 : Tile posSum 2447360 7168 :=
  join (join g183a g183b) (join g183c g183d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g184a : Tile posSum 2454528 1792 := gt (by
  have e : gw 2454528 1792 = gw 2454528 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g184b : Tile posSum 2456320 1792 := gt (by
  have e : gw 2456320 1792 = gw 2456320 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g184c : Tile posSum 2458112 1792 := gt (by
  have e : gw 2458112 1792 = gw 2458112 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g184d : Tile posSum 2459904 1792 := gt (by
  have e : gw 2459904 1792 = gw 2459904 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g184 : Tile posSum 2454528 7168 :=
  join (join g184a g184b) (join g184c g184d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g185a : Tile posSum 2461696 1792 := gt (by
  have e : gw 2461696 1792 = gw 2461696 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g185b : Tile posSum 2463488 1792 := gt (by
  have e : gw 2463488 1792 = gw 2463488 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g185c : Tile posSum 2465280 1792 := gt (by
  have e : gw 2465280 1792 = gw 2465280 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g185d : Tile posSum 2467072 1792 := gt (by
  have e : gw 2467072 1792 = gw 2467072 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g185 : Tile posSum 2461696 7168 :=
  join (join g185a g185b) (join g185c g185d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g186a : Tile posSum 2468864 1792 := gt (by
  have e : gw 2468864 1792 = gw 2468864 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g186b : Tile posSum 2470656 1792 := gt (by
  have e : gw 2470656 1792 = gw 2470656 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g186c : Tile posSum 2472448 1792 := gt (by
  have e : gw 2472448 1792 = gw 2472448 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g186d : Tile posSum 2474240 1792 := gt (by
  have e : gw 2474240 1792 = gw 2474240 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g186 : Tile posSum 2468864 7168 :=
  join (join g186a g186b) (join g186c g186d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g187a : Tile posSum 2476032 1792 := gt (by
  have e : gw 2476032 1792 = gw 2476032 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g187b : Tile posSum 2477824 1792 := gt (by
  have e : gw 2477824 1792 = gw 2477824 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g187c : Tile posSum 2479616 1792 := gt (by
  have e : gw 2479616 1792 = gw 2479616 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g187d : Tile posSum 2481408 1792 := gt (by
  have e : gw 2481408 1792 = gw 2481408 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g187 : Tile posSum 2476032 7168 :=
  join (join g187a g187b) (join g187c g187d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g188a : Tile posSum 2483200 1792 := gt (by
  have e : gw 2483200 1792 = gw 2483200 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g188b : Tile posSum 2484992 1792 := gt (by
  have e : gw 2484992 1792 = gw 2484992 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g188c : Tile posSum 2486784 1792 := gt (by
  have e : gw 2486784 1792 = gw 2486784 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g188d : Tile posSum 2488576 1792 := gt (by
  have e : gw 2488576 1792 = gw 2488576 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g188 : Tile posSum 2483200 7168 :=
  join (join g188a g188b) (join g188c g188d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g189a : Tile posSum 2490368 1792 := gt (by
  have e : gw 2490368 1792 = gw 2490368 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g189b : Tile posSum 2492160 1792 := gt (by
  have e : gw 2492160 1792 = gw 2492160 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g189c : Tile posSum 2493952 1792 := gt (by
  have e : gw 2493952 1792 = gw 2493952 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g189d : Tile posSum 2495744 1792 := gt (by
  have e : gw 2495744 1792 = gw 2495744 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g189 : Tile posSum 2490368 7168 :=
  join (join g189a g189b) (join g189c g189d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g190a : Tile posSum 2497536 1792 := gt (by
  have e : gw 2497536 1792 = gw 2497536 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g190b : Tile posSum 2499328 1792 := gt (by
  have e : gw 2499328 1792 = gw 2499328 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g190c : Tile posSum 2501120 1792 := gt (by
  have e : gw 2501120 1792 = gw 2501120 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g190d : Tile posSum 2502912 1792 := gt (by
  have e : gw 2502912 1792 = gw 2502912 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g190 : Tile posSum 2497536 7168 :=
  join (join g190a g190b) (join g190c g190d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g191a : Tile posSum 2504704 1792 := gt (by
  have e : gw 2504704 1792 = gw 2504704 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g191b : Tile posSum 2506496 1792 := gt (by
  have e : gw 2506496 1792 = gw 2506496 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g191c : Tile posSum 2508288 1792 := gt (by
  have e : gw 2508288 1792 = gw 2508288 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g191d : Tile posSum 2510080 1792 := gt (by
  have e : gw 2510080 1792 = gw 2510080 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g191 : Tile posSum 2504704 7168 :=
  join (join g191a g191b) (join g191c g191d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g192a : Tile posSum 2511872 1792 := gt (by
  have e : gw 2511872 1792 = gw 2511872 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g192b : Tile posSum 2513664 1792 := gt (by
  have e : gw 2513664 1792 = gw 2513664 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g192c : Tile posSum 2515456 1792 := gt (by
  have e : gw 2515456 1792 = gw 2515456 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g192d : Tile posSum 2517248 1792 := gt (by
  have e : gw 2517248 1792 = gw 2517248 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g192 : Tile posSum 2511872 7168 :=
  join (join g192a g192b) (join g192c g192d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g193a : Tile posSum 2519040 1792 := gt (by
  have e : gw 2519040 1792 = gw 2519040 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g193b : Tile posSum 2520832 1792 := gt (by
  have e : gw 2520832 1792 = gw 2520832 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g193c : Tile posSum 2522624 1792 := gt (by
  have e : gw 2522624 1792 = gw 2522624 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g193d : Tile posSum 2524416 1792 := gt (by
  have e : gw 2524416 1792 = gw 2524416 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g193 : Tile posSum 2519040 7168 :=
  join (join g193a g193b) (join g193c g193d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g194a : Tile posSum 2526208 1792 := gt (by
  have e : gw 2526208 1792 = gw 2526208 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g194b : Tile posSum 2528000 1792 := gt (by
  have e : gw 2528000 1792 = gw 2528000 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g194c : Tile posSum 2529792 1792 := gt (by
  have e : gw 2529792 1792 = gw 2529792 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g194d : Tile posSum 2531584 1792 := gt (by
  have e : gw 2531584 1792 = gw 2531584 1792 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g194 : Tile posSum 2526208 7168 :=
  join (join g194a g194b) (join g194c g194d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g195a : Tile posSum 2533376 1536 := gt (by
  have e : gw 2533376 1536 = gw 2533376 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g195b : Tile posSum 2534912 1536 := gt (by
  have e : gw 2534912 1536 = gw 2534912 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g195c : Tile posSum 2536448 1536 := gt (by
  have e : gw 2536448 1536 = gw 2536448 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g195d : Tile posSum 2537984 1536 := gt (by
  have e : gw 2537984 1536 = gw 2537984 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g195 : Tile posSum 2533376 6144 :=
  join (join g195a g195b) (join g195c g195d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g196a : Tile posSum 2539520 1536 := gt (by
  have e : gw 2539520 1536 = gw 2539520 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g196b : Tile posSum 2541056 1536 := gt (by
  have e : gw 2541056 1536 = gw 2541056 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g196c : Tile posSum 2542592 1536 := gt (by
  have e : gw 2542592 1536 = gw 2542592 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g196d : Tile posSum 2544128 1536 := gt (by
  have e : gw 2544128 1536 = gw 2544128 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g196 : Tile posSum 2539520 6144 :=
  join (join g196a g196b) (join g196c g196d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g197a : Tile posSum 2545664 1536 := gt (by
  have e : gw 2545664 1536 = gw 2545664 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g197b : Tile posSum 2547200 1536 := gt (by
  have e : gw 2547200 1536 = gw 2547200 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g197c : Tile posSum 2548736 1536 := gt (by
  have e : gw 2548736 1536 = gw 2548736 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g197d : Tile posSum 2550272 1536 := gt (by
  have e : gw 2550272 1536 = gw 2550272 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g197 : Tile posSum 2545664 6144 :=
  join (join g197a g197b) (join g197c g197d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g198a : Tile posSum 2551808 1536 := gt (by
  have e : gw 2551808 1536 = gw 2551808 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g198b : Tile posSum 2553344 1536 := gt (by
  have e : gw 2553344 1536 = gw 2553344 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g198c : Tile posSum 2554880 1536 := gt (by
  have e : gw 2554880 1536 = gw 2554880 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g198d : Tile posSum 2556416 1536 := gt (by
  have e : gw 2556416 1536 = gw 2556416 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g198 : Tile posSum 2551808 6144 :=
  join (join g198a g198b) (join g198c g198d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g199a : Tile posSum 2557952 1536 := gt (by
  have e : gw 2557952 1536 = gw 2557952 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g199b : Tile posSum 2559488 1536 := gt (by
  have e : gw 2559488 1536 = gw 2559488 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g199c : Tile posSum 2561024 1536 := gt (by
  have e : gw 2561024 1536 = gw 2561024 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g199d : Tile posSum 2562560 1536 := gt (by
  have e : gw 2562560 1536 = gw 2562560 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g199 : Tile posSum 2557952 6144 :=
  join (join g199a g199b) (join g199c g199d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g200a : Tile posSum 2564096 1536 := gt (by
  have e : gw 2564096 1536 = gw 2564096 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g200b : Tile posSum 2565632 1536 := gt (by
  have e : gw 2565632 1536 = gw 2565632 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g200c : Tile posSum 2567168 1536 := gt (by
  have e : gw 2567168 1536 = gw 2567168 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g200d : Tile posSum 2568704 1536 := gt (by
  have e : gw 2568704 1536 = gw 2568704 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g200 : Tile posSum 2564096 6144 :=
  join (join g200a g200b) (join g200c g200d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g201a : Tile posSum 2570240 1536 := gt (by
  have e : gw 2570240 1536 = gw 2570240 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g201b : Tile posSum 2571776 1536 := gt (by
  have e : gw 2571776 1536 = gw 2571776 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g201c : Tile posSum 2573312 1536 := gt (by
  have e : gw 2573312 1536 = gw 2573312 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g201d : Tile posSum 2574848 1536 := gt (by
  have e : gw 2574848 1536 = gw 2574848 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g201 : Tile posSum 2570240 6144 :=
  join (join g201a g201b) (join g201c g201d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g202a : Tile posSum 2576384 1536 := gt (by
  have e : gw 2576384 1536 = gw 2576384 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g202b : Tile posSum 2577920 1536 := gt (by
  have e : gw 2577920 1536 = gw 2577920 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g202c : Tile posSum 2579456 1536 := gt (by
  have e : gw 2579456 1536 = gw 2579456 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g202d : Tile posSum 2580992 1536 := gt (by
  have e : gw 2580992 1536 = gw 2580992 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g202 : Tile posSum 2576384 6144 :=
  join (join g202a g202b) (join g202c g202d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g203a : Tile posSum 2582528 1536 := gt (by
  have e : gw 2582528 1536 = gw 2582528 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g203b : Tile posSum 2584064 1536 := gt (by
  have e : gw 2584064 1536 = gw 2584064 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g203c : Tile posSum 2585600 1536 := gt (by
  have e : gw 2585600 1536 = gw 2585600 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g203d : Tile posSum 2587136 1536 := gt (by
  have e : gw 2587136 1536 = gw 2587136 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g203 : Tile posSum 2582528 6144 :=
  join (join g203a g203b) (join g203c g203d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g204a : Tile posSum 2588672 1536 := gt (by
  have e : gw 2588672 1536 = gw 2588672 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g204b : Tile posSum 2590208 1536 := gt (by
  have e : gw 2590208 1536 = gw 2590208 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g204c : Tile posSum 2591744 1536 := gt (by
  have e : gw 2591744 1536 = gw 2591744 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g204d : Tile posSum 2593280 1536 := gt (by
  have e : gw 2593280 1536 = gw 2593280 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g204 : Tile posSum 2588672 6144 :=
  join (join g204a g204b) (join g204c g204d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g205a : Tile posSum 2594816 1536 := gt (by
  have e : gw 2594816 1536 = gw 2594816 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g205b : Tile posSum 2596352 1536 := gt (by
  have e : gw 2596352 1536 = gw 2596352 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g205c : Tile posSum 2597888 1536 := gt (by
  have e : gw 2597888 1536 = gw 2597888 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g205d : Tile posSum 2599424 1536 := gt (by
  have e : gw 2599424 1536 = gw 2599424 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g205 : Tile posSum 2594816 6144 :=
  join (join g205a g205b) (join g205c g205d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g206a : Tile posSum 2600960 1536 := gt (by
  have e : gw 2600960 1536 = gw 2600960 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g206b : Tile posSum 2602496 1536 := gt (by
  have e : gw 2602496 1536 = gw 2602496 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g206c : Tile posSum 2604032 1536 := gt (by
  have e : gw 2604032 1536 = gw 2604032 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g206d : Tile posSum 2605568 1536 := gt (by
  have e : gw 2605568 1536 = gw 2605568 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g206 : Tile posSum 2600960 6144 :=
  join (join g206a g206b) (join g206c g206d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g207a : Tile posSum 2607104 1536 := gt (by
  have e : gw 2607104 1536 = gw 2607104 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g207b : Tile posSum 2608640 1536 := gt (by
  have e : gw 2608640 1536 = gw 2608640 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g207c : Tile posSum 2610176 1536 := gt (by
  have e : gw 2610176 1536 = gw 2610176 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g207d : Tile posSum 2611712 1536 := gt (by
  have e : gw 2611712 1536 = gw 2611712 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g207 : Tile posSum 2607104 6144 :=
  join (join g207a g207b) (join g207c g207d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g208a : Tile posSum 2613248 1536 := gt (by
  have e : gw 2613248 1536 = gw 2613248 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g208b : Tile posSum 2614784 1536 := gt (by
  have e : gw 2614784 1536 = gw 2614784 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g208c : Tile posSum 2616320 1536 := gt (by
  have e : gw 2616320 1536 = gw 2616320 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g208d : Tile posSum 2617856 1536 := gt (by
  have e : gw 2617856 1536 = gw 2617856 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g208 : Tile posSum 2613248 6144 :=
  join (join g208a g208b) (join g208c g208d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g209a : Tile posSum 2619392 1536 := gt (by
  have e : gw 2619392 1536 = gw 2619392 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g209b : Tile posSum 2620928 1536 := gt (by
  have e : gw 2620928 1536 = gw 2620928 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g209c : Tile posSum 2622464 1536 := gt (by
  have e : gw 2622464 1536 = gw 2622464 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g209d : Tile posSum 2624000 1536 := gt (by
  have e : gw 2624000 1536 = gw 2624000 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g209 : Tile posSum 2619392 6144 :=
  join (join g209a g209b) (join g209c g209d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g210a : Tile posSum 2625536 1536 := gt (by
  have e : gw 2625536 1536 = gw 2625536 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g210b : Tile posSum 2627072 1536 := gt (by
  have e : gw 2627072 1536 = gw 2627072 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g210c : Tile posSum 2628608 1536 := gt (by
  have e : gw 2628608 1536 = gw 2628608 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g210d : Tile posSum 2630144 1536 := gt (by
  have e : gw 2630144 1536 = gw 2630144 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g210 : Tile posSum 2625536 6144 :=
  join (join g210a g210b) (join g210c g210d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g211a : Tile posSum 2631680 1536 := gt (by
  have e : gw 2631680 1536 = gw 2631680 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g211b : Tile posSum 2633216 1536 := gt (by
  have e : gw 2633216 1536 = gw 2633216 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g211c : Tile posSum 2634752 1536 := gt (by
  have e : gw 2634752 1536 = gw 2634752 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g211d : Tile posSum 2636288 1536 := gt (by
  have e : gw 2636288 1536 = gw 2636288 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g211 : Tile posSum 2631680 6144 :=
  join (join g211a g211b) (join g211c g211d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g212a : Tile posSum 2637824 1536 := gt (by
  have e : gw 2637824 1536 = gw 2637824 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g212b : Tile posSum 2639360 1536 := gt (by
  have e : gw 2639360 1536 = gw 2639360 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g212c : Tile posSum 2640896 1536 := gt (by
  have e : gw 2640896 1536 = gw 2640896 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g212d : Tile posSum 2642432 1536 := gt (by
  have e : gw 2642432 1536 = gw 2642432 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g212 : Tile posSum 2637824 6144 :=
  join (join g212a g212b) (join g212c g212d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g213a : Tile posSum 2643968 1536 := gt (by
  have e : gw 2643968 1536 = gw 2643968 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g213b : Tile posSum 2645504 1536 := gt (by
  have e : gw 2645504 1536 = gw 2645504 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g213c : Tile posSum 2647040 1536 := gt (by
  have e : gw 2647040 1536 = gw 2647040 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g213d : Tile posSum 2648576 1536 := gt (by
  have e : gw 2648576 1536 = gw 2648576 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g213 : Tile posSum 2643968 6144 :=
  join (join g213a g213b) (join g213c g213d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g214a : Tile posSum 2650112 1536 := gt (by
  have e : gw 2650112 1536 = gw 2650112 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g214b : Tile posSum 2651648 1536 := gt (by
  have e : gw 2651648 1536 = gw 2651648 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g214c : Tile posSum 2653184 1536 := gt (by
  have e : gw 2653184 1536 = gw 2653184 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g214d : Tile posSum 2654720 1536 := gt (by
  have e : gw 2654720 1536 = gw 2654720 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g214 : Tile posSum 2650112 6144 :=
  join (join g214a g214b) (join g214c g214d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g215a : Tile posSum 2656256 1536 := gt (by
  have e : gw 2656256 1536 = gw 2656256 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g215b : Tile posSum 2657792 1536 := gt (by
  have e : gw 2657792 1536 = gw 2657792 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g215c : Tile posSum 2659328 1536 := gt (by
  have e : gw 2659328 1536 = gw 2659328 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g215d : Tile posSum 2660864 1536 := gt (by
  have e : gw 2660864 1536 = gw 2660864 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g215 : Tile posSum 2656256 6144 :=
  join (join g215a g215b) (join g215c g215d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g216a : Tile posSum 2662400 1536 := gt (by
  have e : gw 2662400 1536 = gw 2662400 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g216b : Tile posSum 2663936 1536 := gt (by
  have e : gw 2663936 1536 = gw 2663936 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g216c : Tile posSum 2665472 1536 := gt (by
  have e : gw 2665472 1536 = gw 2665472 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g216d : Tile posSum 2667008 1536 := gt (by
  have e : gw 2667008 1536 = gw 2667008 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g216 : Tile posSum 2662400 6144 :=
  join (join g216a g216b) (join g216c g216d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g217a : Tile posSum 2668544 1536 := gt (by
  have e : gw 2668544 1536 = gw 2668544 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g217b : Tile posSum 2670080 1536 := gt (by
  have e : gw 2670080 1536 = gw 2670080 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g217c : Tile posSum 2671616 1536 := gt (by
  have e : gw 2671616 1536 = gw 2671616 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g217d : Tile posSum 2673152 1536 := gt (by
  have e : gw 2673152 1536 = gw 2673152 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g217 : Tile posSum 2668544 6144 :=
  join (join g217a g217b) (join g217c g217d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g218a : Tile posSum 2674688 1536 := gt (by
  have e : gw 2674688 1536 = gw 2674688 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g218b : Tile posSum 2676224 1536 := gt (by
  have e : gw 2676224 1536 = gw 2676224 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g218c : Tile posSum 2677760 1536 := gt (by
  have e : gw 2677760 1536 = gw 2677760 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g218d : Tile posSum 2679296 1536 := gt (by
  have e : gw 2679296 1536 = gw 2679296 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g218 : Tile posSum 2674688 6144 :=
  join (join g218a g218b) (join g218c g218d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g219a : Tile posSum 2680832 1536 := gt (by
  have e : gw 2680832 1536 = gw 2680832 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g219b : Tile posSum 2682368 1536 := gt (by
  have e : gw 2682368 1536 = gw 2682368 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g219c : Tile posSum 2683904 1536 := gt (by
  have e : gw 2683904 1536 = gw 2683904 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g219d : Tile posSum 2685440 1536 := gt (by
  have e : gw 2685440 1536 = gw 2685440 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g219 : Tile posSum 2680832 6144 :=
  join (join g219a g219b) (join g219c g219d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g220a : Tile posSum 2686976 1536 := gt (by
  have e : gw 2686976 1536 = gw 2686976 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g220b : Tile posSum 2688512 1536 := gt (by
  have e : gw 2688512 1536 = gw 2688512 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g220c : Tile posSum 2690048 1536 := gt (by
  have e : gw 2690048 1536 = gw 2690048 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g220d : Tile posSum 2691584 1536 := gt (by
  have e : gw 2691584 1536 = gw 2691584 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g220 : Tile posSum 2686976 6144 :=
  join (join g220a g220b) (join g220c g220d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g221a : Tile posSum 2693120 1536 := gt (by
  have e : gw 2693120 1536 = gw 2693120 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g221b : Tile posSum 2694656 1536 := gt (by
  have e : gw 2694656 1536 = gw 2694656 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g221c : Tile posSum 2696192 1536 := gt (by
  have e : gw 2696192 1536 = gw 2696192 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g221d : Tile posSum 2697728 1536 := gt (by
  have e : gw 2697728 1536 = gw 2697728 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g221 : Tile posSum 2693120 6144 :=
  join (join g221a g221b) (join g221c g221d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g222a : Tile posSum 2699264 1536 := gt (by
  have e : gw 2699264 1536 = gw 2699264 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g222b : Tile posSum 2700800 1536 := gt (by
  have e : gw 2700800 1536 = gw 2700800 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g222c : Tile posSum 2702336 1536 := gt (by
  have e : gw 2702336 1536 = gw 2702336 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g222d : Tile posSum 2703872 1536 := gt (by
  have e : gw 2703872 1536 = gw 2703872 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g222 : Tile posSum 2699264 6144 :=
  join (join g222a g222b) (join g222c g222d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g223a : Tile posSum 2705408 1536 := gt (by
  have e : gw 2705408 1536 = gw 2705408 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g223b : Tile posSum 2706944 1536 := gt (by
  have e : gw 2706944 1536 = gw 2706944 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g223c : Tile posSum 2708480 1536 := gt (by
  have e : gw 2708480 1536 = gw 2708480 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g223d : Tile posSum 2710016 1536 := gt (by
  have e : gw 2710016 1536 = gw 2710016 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g223 : Tile posSum 2705408 6144 :=
  join (join g223a g223b) (join g223c g223d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g224a : Tile posSum 2711552 1536 := gt (by
  have e : gw 2711552 1536 = gw 2711552 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g224b : Tile posSum 2713088 1536 := gt (by
  have e : gw 2713088 1536 = gw 2713088 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g224c : Tile posSum 2714624 1536 := gt (by
  have e : gw 2714624 1536 = gw 2714624 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g224d : Tile posSum 2716160 1536 := gt (by
  have e : gw 2716160 1536 = gw 2716160 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g224 : Tile posSum 2711552 6144 :=
  join (join g224a g224b) (join g224c g224d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g225a : Tile posSum 2717696 1536 := gt (by
  have e : gw 2717696 1536 = gw 2717696 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g225b : Tile posSum 2719232 1536 := gt (by
  have e : gw 2719232 1536 = gw 2719232 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g225c : Tile posSum 2720768 1536 := gt (by
  have e : gw 2720768 1536 = gw 2720768 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g225d : Tile posSum 2722304 1536 := gt (by
  have e : gw 2722304 1536 = gw 2722304 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g225 : Tile posSum 2717696 6144 :=
  join (join g225a g225b) (join g225c g225d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g226a : Tile posSum 2723840 1536 := gt (by
  have e : gw 2723840 1536 = gw 2723840 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g226b : Tile posSum 2725376 1536 := gt (by
  have e : gw 2725376 1536 = gw 2725376 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g226c : Tile posSum 2726912 1536 := gt (by
  have e : gw 2726912 1536 = gw 2726912 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g226d : Tile posSum 2728448 1536 := gt (by
  have e : gw 2728448 1536 = gw 2728448 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g226 : Tile posSum 2723840 6144 :=
  join (join g226a g226b) (join g226c g226d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g227a : Tile posSum 2729984 1536 := gt (by
  have e : gw 2729984 1536 = gw 2729984 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g227b : Tile posSum 2731520 1536 := gt (by
  have e : gw 2731520 1536 = gw 2731520 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g227c : Tile posSum 2733056 1536 := gt (by
  have e : gw 2733056 1536 = gw 2733056 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g227d : Tile posSum 2734592 1536 := gt (by
  have e : gw 2734592 1536 = gw 2734592 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g227 : Tile posSum 2729984 6144 :=
  join (join g227a g227b) (join g227c g227d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g228a : Tile posSum 2736128 1536 := gt (by
  have e : gw 2736128 1536 = gw 2736128 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g228b : Tile posSum 2737664 1536 := gt (by
  have e : gw 2737664 1536 = gw 2737664 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g228c : Tile posSum 2739200 1536 := gt (by
  have e : gw 2739200 1536 = gw 2739200 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g228d : Tile posSum 2740736 1536 := gt (by
  have e : gw 2740736 1536 = gw 2740736 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g228 : Tile posSum 2736128 6144 :=
  join (join g228a g228b) (join g228c g228d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g229a : Tile posSum 2742272 1536 := gt (by
  have e : gw 2742272 1536 = gw 2742272 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g229b : Tile posSum 2743808 1536 := gt (by
  have e : gw 2743808 1536 = gw 2743808 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g229c : Tile posSum 2745344 1536 := gt (by
  have e : gw 2745344 1536 = gw 2745344 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g229d : Tile posSum 2746880 1536 := gt (by
  have e : gw 2746880 1536 = gw 2746880 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g229 : Tile posSum 2742272 6144 :=
  join (join g229a g229b) (join g229c g229d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g230a : Tile posSum 2748416 1536 := gt (by
  have e : gw 2748416 1536 = gw 2748416 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g230b : Tile posSum 2749952 1536 := gt (by
  have e : gw 2749952 1536 = gw 2749952 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g230c : Tile posSum 2751488 1536 := gt (by
  have e : gw 2751488 1536 = gw 2751488 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g230d : Tile posSum 2753024 1536 := gt (by
  have e : gw 2753024 1536 = gw 2753024 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g230 : Tile posSum 2748416 6144 :=
  join (join g230a g230b) (join g230c g230d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g231a : Tile posSum 2754560 1536 := gt (by
  have e : gw 2754560 1536 = gw 2754560 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g231b : Tile posSum 2756096 1536 := gt (by
  have e : gw 2756096 1536 = gw 2756096 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g231c : Tile posSum 2757632 1536 := gt (by
  have e : gw 2757632 1536 = gw 2757632 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g231d : Tile posSum 2759168 1536 := gt (by
  have e : gw 2759168 1536 = gw 2759168 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g231 : Tile posSum 2754560 6144 :=
  join (join g231a g231b) (join g231c g231d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g232a : Tile posSum 2760704 1536 := gt (by
  have e : gw 2760704 1536 = gw 2760704 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g232b : Tile posSum 2762240 1536 := gt (by
  have e : gw 2762240 1536 = gw 2762240 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g232c : Tile posSum 2763776 1536 := gt (by
  have e : gw 2763776 1536 = gw 2763776 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g232d : Tile posSum 2765312 1536 := gt (by
  have e : gw 2765312 1536 = gw 2765312 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g232 : Tile posSum 2760704 6144 :=
  join (join g232a g232b) (join g232c g232d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g233a : Tile posSum 2766848 1536 := gt (by
  have e : gw 2766848 1536 = gw 2766848 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g233b : Tile posSum 2768384 1536 := gt (by
  have e : gw 2768384 1536 = gw 2768384 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g233c : Tile posSum 2769920 1536 := gt (by
  have e : gw 2769920 1536 = gw 2769920 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g233d : Tile posSum 2771456 1536 := gt (by
  have e : gw 2771456 1536 = gw 2771456 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g233 : Tile posSum 2766848 6144 :=
  join (join g233a g233b) (join g233c g233d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g234a : Tile posSum 2772992 1536 := gt (by
  have e : gw 2772992 1536 = gw 2772992 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g234b : Tile posSum 2774528 1536 := gt (by
  have e : gw 2774528 1536 = gw 2774528 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g234c : Tile posSum 2776064 1536 := gt (by
  have e : gw 2776064 1536 = gw 2776064 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g234d : Tile posSum 2777600 1536 := gt (by
  have e : gw 2777600 1536 = gw 2777600 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g234 : Tile posSum 2772992 6144 :=
  join (join g234a g234b) (join g234c g234d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g235a : Tile posSum 2779136 1536 := gt (by
  have e : gw 2779136 1536 = gw 2779136 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g235b : Tile posSum 2780672 1536 := gt (by
  have e : gw 2780672 1536 = gw 2780672 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g235c : Tile posSum 2782208 1536 := gt (by
  have e : gw 2782208 1536 = gw 2782208 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g235d : Tile posSum 2783744 1536 := gt (by
  have e : gw 2783744 1536 = gw 2783744 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g235 : Tile posSum 2779136 6144 :=
  join (join g235a g235b) (join g235c g235d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g236a : Tile posSum 2785280 1536 := gt (by
  have e : gw 2785280 1536 = gw 2785280 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g236b : Tile posSum 2786816 1536 := gt (by
  have e : gw 2786816 1536 = gw 2786816 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g236c : Tile posSum 2788352 1536 := gt (by
  have e : gw 2788352 1536 = gw 2788352 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g236d : Tile posSum 2789888 1536 := gt (by
  have e : gw 2789888 1536 = gw 2789888 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g236 : Tile posSum 2785280 6144 :=
  join (join g236a g236b) (join g236c g236d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g237a : Tile posSum 2791424 1536 := gt (by
  have e : gw 2791424 1536 = gw 2791424 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g237b : Tile posSum 2792960 1536 := gt (by
  have e : gw 2792960 1536 = gw 2792960 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g237c : Tile posSum 2794496 1536 := gt (by
  have e : gw 2794496 1536 = gw 2794496 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g237d : Tile posSum 2796032 1536 := gt (by
  have e : gw 2796032 1536 = gw 2796032 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g237 : Tile posSum 2791424 6144 :=
  join (join g237a g237b) (join g237c g237d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g238a : Tile posSum 2797568 1536 := gt (by
  have e : gw 2797568 1536 = gw 2797568 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g238b : Tile posSum 2799104 1536 := gt (by
  have e : gw 2799104 1536 = gw 2799104 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g238c : Tile posSum 2800640 1536 := gt (by
  have e : gw 2800640 1536 = gw 2800640 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g238d : Tile posSum 2802176 1536 := gt (by
  have e : gw 2802176 1536 = gw 2802176 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g238 : Tile posSum 2797568 6144 :=
  join (join g238a g238b) (join g238c g238d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g239a : Tile posSum 2803712 1536 := gt (by
  have e : gw 2803712 1536 = gw 2803712 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g239b : Tile posSum 2805248 1536 := gt (by
  have e : gw 2805248 1536 = gw 2805248 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g239c : Tile posSum 2806784 1536 := gt (by
  have e : gw 2806784 1536 = gw 2806784 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g239d : Tile posSum 2808320 1536 := gt (by
  have e : gw 2808320 1536 = gw 2808320 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g239 : Tile posSum 2803712 6144 :=
  join (join g239a g239b) (join g239c g239d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g240a : Tile posSum 2809856 1536 := gt (by
  have e : gw 2809856 1536 = gw 2809856 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g240b : Tile posSum 2811392 1536 := gt (by
  have e : gw 2811392 1536 = gw 2811392 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g240c : Tile posSum 2812928 1536 := gt (by
  have e : gw 2812928 1536 = gw 2812928 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g240d : Tile posSum 2814464 1536 := gt (by
  have e : gw 2814464 1536 = gw 2814464 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g240 : Tile posSum 2809856 6144 :=
  join (join g240a g240b) (join g240c g240d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g241a : Tile posSum 2816000 1536 := gt (by
  have e : gw 2816000 1536 = gw 2816000 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g241b : Tile posSum 2817536 1536 := gt (by
  have e : gw 2817536 1536 = gw 2817536 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g241c : Tile posSum 2819072 1536 := gt (by
  have e : gw 2819072 1536 = gw 2819072 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g241d : Tile posSum 2820608 1536 := gt (by
  have e : gw 2820608 1536 = gw 2820608 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g241 : Tile posSum 2816000 6144 :=
  join (join g241a g241b) (join g241c g241d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g242a : Tile posSum 2822144 1536 := gt (by
  have e : gw 2822144 1536 = gw 2822144 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g242b : Tile posSum 2823680 1536 := gt (by
  have e : gw 2823680 1536 = gw 2823680 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g242c : Tile posSum 2825216 1536 := gt (by
  have e : gw 2825216 1536 = gw 2825216 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g242d : Tile posSum 2826752 1536 := gt (by
  have e : gw 2826752 1536 = gw 2826752 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g242 : Tile posSum 2822144 6144 :=
  join (join g242a g242b) (join g242c g242d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g243a : Tile posSum 2828288 1536 := gt (by
  have e : gw 2828288 1536 = gw 2828288 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g243b : Tile posSum 2829824 1536 := gt (by
  have e : gw 2829824 1536 = gw 2829824 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g243c : Tile posSum 2831360 1536 := gt (by
  have e : gw 2831360 1536 = gw 2831360 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g243d : Tile posSum 2832896 1536 := gt (by
  have e : gw 2832896 1536 = gw 2832896 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g243 : Tile posSum 2828288 6144 :=
  join (join g243a g243b) (join g243c g243d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g244a : Tile posSum 2834432 1536 := gt (by
  have e : gw 2834432 1536 = gw 2834432 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g244b : Tile posSum 2835968 1536 := gt (by
  have e : gw 2835968 1536 = gw 2835968 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g244c : Tile posSum 2837504 1536 := gt (by
  have e : gw 2837504 1536 = gw 2837504 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g244d : Tile posSum 2839040 1536 := gt (by
  have e : gw 2839040 1536 = gw 2839040 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g244 : Tile posSum 2834432 6144 :=
  join (join g244a g244b) (join g244c g244d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g245a : Tile posSum 2840576 1536 := gt (by
  have e : gw 2840576 1536 = gw 2840576 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g245b : Tile posSum 2842112 1536 := gt (by
  have e : gw 2842112 1536 = gw 2842112 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g245c : Tile posSum 2843648 1536 := gt (by
  have e : gw 2843648 1536 = gw 2843648 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g245d : Tile posSum 2845184 1536 := gt (by
  have e : gw 2845184 1536 = gw 2845184 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g245 : Tile posSum 2840576 6144 :=
  join (join g245a g245b) (join g245c g245d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g246a : Tile posSum 2846720 1536 := gt (by
  have e : gw 2846720 1536 = gw 2846720 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g246b : Tile posSum 2848256 1536 := gt (by
  have e : gw 2848256 1536 = gw 2848256 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g246c : Tile posSum 2849792 1536 := gt (by
  have e : gw 2849792 1536 = gw 2849792 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g246d : Tile posSum 2851328 1536 := gt (by
  have e : gw 2851328 1536 = gw 2851328 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g246 : Tile posSum 2846720 6144 :=
  join (join g246a g246b) (join g246c g246d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g247a : Tile posSum 2852864 1536 := gt (by
  have e : gw 2852864 1536 = gw 2852864 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g247b : Tile posSum 2854400 1536 := gt (by
  have e : gw 2854400 1536 = gw 2854400 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g247c : Tile posSum 2855936 1536 := gt (by
  have e : gw 2855936 1536 = gw 2855936 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g247d : Tile posSum 2857472 1536 := gt (by
  have e : gw 2857472 1536 = gw 2857472 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g247 : Tile posSum 2852864 6144 :=
  join (join g247a g247b) (join g247c g247d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g248a : Tile posSum 2859008 1536 := gt (by
  have e : gw 2859008 1536 = gw 2859008 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g248b : Tile posSum 2860544 1536 := gt (by
  have e : gw 2860544 1536 = gw 2860544 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g248c : Tile posSum 2862080 1536 := gt (by
  have e : gw 2862080 1536 = gw 2862080 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g248d : Tile posSum 2863616 1536 := gt (by
  have e : gw 2863616 1536 = gw 2863616 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g248 : Tile posSum 2859008 6144 :=
  join (join g248a g248b) (join g248c g248d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g249a : Tile posSum 2865152 1536 := gt (by
  have e : gw 2865152 1536 = gw 2865152 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g249b : Tile posSum 2866688 1536 := gt (by
  have e : gw 2866688 1536 = gw 2866688 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g249c : Tile posSum 2868224 1536 := gt (by
  have e : gw 2868224 1536 = gw 2868224 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g249d : Tile posSum 2869760 1536 := gt (by
  have e : gw 2869760 1536 = gw 2869760 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g249 : Tile posSum 2865152 6144 :=
  join (join g249a g249b) (join g249c g249d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g250a : Tile posSum 2871296 1536 := gt (by
  have e : gw 2871296 1536 = gw 2871296 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g250b : Tile posSum 2872832 1536 := gt (by
  have e : gw 2872832 1536 = gw 2872832 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g250c : Tile posSum 2874368 1536 := gt (by
  have e : gw 2874368 1536 = gw 2874368 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g250d : Tile posSum 2875904 1536 := gt (by
  have e : gw 2875904 1536 = gw 2875904 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g250 : Tile posSum 2871296 6144 :=
  join (join g250a g250b) (join g250c g250d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g251a : Tile posSum 2877440 1536 := gt (by
  have e : gw 2877440 1536 = gw 2877440 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g251b : Tile posSum 2878976 1536 := gt (by
  have e : gw 2878976 1536 = gw 2878976 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g251c : Tile posSum 2880512 1536 := gt (by
  have e : gw 2880512 1536 = gw 2880512 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g251d : Tile posSum 2882048 1536 := gt (by
  have e : gw 2882048 1536 = gw 2882048 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g251 : Tile posSum 2877440 6144 :=
  join (join g251a g251b) (join g251c g251d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g252a : Tile posSum 2883584 1536 := gt (by
  have e : gw 2883584 1536 = gw 2883584 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g252b : Tile posSum 2885120 1536 := gt (by
  have e : gw 2885120 1536 = gw 2885120 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g252c : Tile posSum 2886656 1536 := gt (by
  have e : gw 2886656 1536 = gw 2886656 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g252d : Tile posSum 2888192 1536 := gt (by
  have e : gw 2888192 1536 = gw 2888192 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g252 : Tile posSum 2883584 6144 :=
  join (join g252a g252b) (join g252c g252d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g253a : Tile posSum 2889728 1536 := gt (by
  have e : gw 2889728 1536 = gw 2889728 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g253b : Tile posSum 2891264 1536 := gt (by
  have e : gw 2891264 1536 = gw 2891264 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g253c : Tile posSum 2892800 1536 := gt (by
  have e : gw 2892800 1536 = gw 2892800 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g253d : Tile posSum 2894336 1536 := gt (by
  have e : gw 2894336 1536 = gw 2894336 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g253 : Tile posSum 2889728 6144 :=
  join (join g253a g253b) (join g253c g253d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g254a : Tile posSum 2895872 1536 := gt (by
  have e : gw 2895872 1536 = gw 2895872 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g254b : Tile posSum 2897408 1536 := gt (by
  have e : gw 2897408 1536 = gw 2897408 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g254c : Tile posSum 2898944 1536 := gt (by
  have e : gw 2898944 1536 = gw 2898944 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g254d : Tile posSum 2900480 1536 := gt (by
  have e : gw 2900480 1536 = gw 2900480 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g254 : Tile posSum 2895872 6144 :=
  join (join g254a g254b) (join g254c g254d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g255a : Tile posSum 2902016 1536 := gt (by
  have e : gw 2902016 1536 = gw 2902016 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g255b : Tile posSum 2903552 1536 := gt (by
  have e : gw 2903552 1536 = gw 2903552 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g255c : Tile posSum 2905088 1536 := gt (by
  have e : gw 2905088 1536 = gw 2905088 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g255d : Tile posSum 2906624 1536 := gt (by
  have e : gw 2906624 1536 = gw 2906624 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g255 : Tile posSum 2902016 6144 :=
  join (join g255a g255b) (join g255c g255d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g256a : Tile posSum 2908160 1536 := gt (by
  have e : gw 2908160 1536 = gw 2908160 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g256b : Tile posSum 2909696 1536 := gt (by
  have e : gw 2909696 1536 = gw 2909696 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g256c : Tile posSum 2911232 1536 := gt (by
  have e : gw 2911232 1536 = gw 2911232 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g256d : Tile posSum 2912768 1536 := gt (by
  have e : gw 2912768 1536 = gw 2912768 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g256 : Tile posSum 2908160 6144 :=
  join (join g256a g256b) (join g256c g256d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g257a : Tile posSum 2914304 1536 := gt (by
  have e : gw 2914304 1536 = gw 2914304 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g257b : Tile posSum 2915840 1536 := gt (by
  have e : gw 2915840 1536 = gw 2915840 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g257c : Tile posSum 2917376 1536 := gt (by
  have e : gw 2917376 1536 = gw 2917376 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g257d : Tile posSum 2918912 1536 := gt (by
  have e : gw 2918912 1536 = gw 2918912 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g257 : Tile posSum 2914304 6144 :=
  join (join g257a g257b) (join g257c g257d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g258a : Tile posSum 2920448 1536 := gt (by
  have e : gw 2920448 1536 = gw 2920448 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g258b : Tile posSum 2921984 1536 := gt (by
  have e : gw 2921984 1536 = gw 2921984 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g258c : Tile posSum 2923520 1536 := gt (by
  have e : gw 2923520 1536 = gw 2923520 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g258d : Tile posSum 2925056 1536 := gt (by
  have e : gw 2925056 1536 = gw 2925056 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g258 : Tile posSum 2920448 6144 :=
  join (join g258a g258b) (join g258c g258d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g259a : Tile posSum 2926592 1536 := gt (by
  have e : gw 2926592 1536 = gw 2926592 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g259b : Tile posSum 2928128 1536 := gt (by
  have e : gw 2928128 1536 = gw 2928128 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g259c : Tile posSum 2929664 1536 := gt (by
  have e : gw 2929664 1536 = gw 2929664 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g259d : Tile posSum 2931200 1536 := gt (by
  have e : gw 2931200 1536 = gw 2931200 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g259 : Tile posSum 2926592 6144 :=
  join (join g259a g259b) (join g259c g259d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g260a : Tile posSum 2932736 1536 := gt (by
  have e : gw 2932736 1536 = gw 2932736 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g260b : Tile posSum 2934272 1536 := gt (by
  have e : gw 2934272 1536 = gw 2934272 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g260c : Tile posSum 2935808 1536 := gt (by
  have e : gw 2935808 1536 = gw 2935808 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g260d : Tile posSum 2937344 1536 := gt (by
  have e : gw 2937344 1536 = gw 2937344 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g260 : Tile posSum 2932736 6144 :=
  join (join g260a g260b) (join g260c g260d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g261a : Tile posSum 2938880 1536 := gt (by
  have e : gw 2938880 1536 = gw 2938880 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g261b : Tile posSum 2940416 1536 := gt (by
  have e : gw 2940416 1536 = gw 2940416 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g261c : Tile posSum 2941952 1536 := gt (by
  have e : gw 2941952 1536 = gw 2941952 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g261d : Tile posSum 2943488 1536 := gt (by
  have e : gw 2943488 1536 = gw 2943488 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g261 : Tile posSum 2938880 6144 :=
  join (join g261a g261b) (join g261c g261d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g262a : Tile posSum 2945024 1536 := gt (by
  have e : gw 2945024 1536 = gw 2945024 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g262b : Tile posSum 2946560 1536 := gt (by
  have e : gw 2946560 1536 = gw 2946560 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g262c : Tile posSum 2948096 1536 := gt (by
  have e : gw 2948096 1536 = gw 2948096 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g262d : Tile posSum 2949632 1536 := gt (by
  have e : gw 2949632 1536 = gw 2949632 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g262 : Tile posSum 2945024 6144 :=
  join (join g262a g262b) (join g262c g262d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g263a : Tile posSum 2951168 1536 := gt (by
  have e : gw 2951168 1536 = gw 2951168 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g263b : Tile posSum 2952704 1536 := gt (by
  have e : gw 2952704 1536 = gw 2952704 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g263c : Tile posSum 2954240 1536 := gt (by
  have e : gw 2954240 1536 = gw 2954240 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g263d : Tile posSum 2955776 1536 := gt (by
  have e : gw 2955776 1536 = gw 2955776 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g263 : Tile posSum 2951168 6144 :=
  join (join g263a g263b) (join g263c g263d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g264a : Tile posSum 2957312 1280 := gt (by
  have e : gw 2957312 1280 = gw 2957312 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g264b : Tile posSum 2958592 1280 := gt (by
  have e : gw 2958592 1280 = gw 2958592 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g264c : Tile posSum 2959872 1280 := gt (by
  have e : gw 2959872 1280 = gw 2959872 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g264d : Tile posSum 2961152 1280 := gt (by
  have e : gw 2961152 1280 = gw 2961152 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g264 : Tile posSum 2957312 5120 :=
  join (join g264a g264b) (join g264c g264d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g265a : Tile posSum 2962432 1536 := gt (by
  have e : gw 2962432 1536 = gw 2962432 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g265b : Tile posSum 2963968 1536 := gt (by
  have e : gw 2963968 1536 = gw 2963968 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g265c : Tile posSum 2965504 1536 := gt (by
  have e : gw 2965504 1536 = gw 2965504 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g265d : Tile posSum 2967040 1536 := gt (by
  have e : gw 2967040 1536 = gw 2967040 1536 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g265 : Tile posSum 2962432 6144 :=
  join (join g265a g265b) (join g265c g265d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g266a : Tile posSum 2968576 1280 := gt (by
  have e : gw 2968576 1280 = gw 2968576 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g266b : Tile posSum 2969856 1280 := gt (by
  have e : gw 2969856 1280 = gw 2969856 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g266c : Tile posSum 2971136 1280 := gt (by
  have e : gw 2971136 1280 = gw 2971136 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g266d : Tile posSum 2972416 1280 := gt (by
  have e : gw 2972416 1280 = gw 2972416 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g266 : Tile posSum 2968576 5120 :=
  join (join g266a g266b) (join g266c g266d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g267a : Tile posSum 2973696 1280 := gt (by
  have e : gw 2973696 1280 = gw 2973696 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g267b : Tile posSum 2974976 1280 := gt (by
  have e : gw 2974976 1280 = gw 2974976 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g267c : Tile posSum 2976256 1280 := gt (by
  have e : gw 2976256 1280 = gw 2976256 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g267d : Tile posSum 2977536 1280 := gt (by
  have e : gw 2977536 1280 = gw 2977536 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g267 : Tile posSum 2973696 5120 :=
  join (join g267a g267b) (join g267c g267d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g268a : Tile posSum 2978816 1280 := gt (by
  have e : gw 2978816 1280 = gw 2978816 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g268b : Tile posSum 2980096 1280 := gt (by
  have e : gw 2980096 1280 = gw 2980096 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g268c : Tile posSum 2981376 1280 := gt (by
  have e : gw 2981376 1280 = gw 2981376 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g268d : Tile posSum 2982656 1280 := gt (by
  have e : gw 2982656 1280 = gw 2982656 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g268 : Tile posSum 2978816 5120 :=
  join (join g268a g268b) (join g268c g268d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g269a : Tile posSum 2983936 1280 := gt (by
  have e : gw 2983936 1280 = gw 2983936 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g269b : Tile posSum 2985216 1280 := gt (by
  have e : gw 2985216 1280 = gw 2985216 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g269c : Tile posSum 2986496 1280 := gt (by
  have e : gw 2986496 1280 = gw 2986496 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g269d : Tile posSum 2987776 1280 := gt (by
  have e : gw 2987776 1280 = gw 2987776 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g269 : Tile posSum 2983936 5120 :=
  join (join g269a g269b) (join g269c g269d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g270a : Tile posSum 2989056 1280 := gt (by
  have e : gw 2989056 1280 = gw 2989056 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g270b : Tile posSum 2990336 1280 := gt (by
  have e : gw 2990336 1280 = gw 2990336 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g270c : Tile posSum 2991616 1280 := gt (by
  have e : gw 2991616 1280 = gw 2991616 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g270d : Tile posSum 2992896 1280 := gt (by
  have e : gw 2992896 1280 = gw 2992896 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g270 : Tile posSum 2989056 5120 :=
  join (join g270a g270b) (join g270c g270d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g271a : Tile posSum 2994176 1280 := gt (by
  have e : gw 2994176 1280 = gw 2994176 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g271b : Tile posSum 2995456 1280 := gt (by
  have e : gw 2995456 1280 = gw 2995456 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g271c : Tile posSum 2996736 1280 := gt (by
  have e : gw 2996736 1280 = gw 2996736 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g271d : Tile posSum 2998016 1280 := gt (by
  have e : gw 2998016 1280 = gw 2998016 1280 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g271 : Tile posSum 2994176 5120 :=
  join (join g271a g271b) (join g271c g271d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g272a : Tile posSum 2999296 176 := gt (by
  have e : gw 2999296 176 = gw 2999296 176 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g272b : Tile posSum 2999472 176 := gt (by
  have e : gw 2999472 176 = gw 2999472 176 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g272c : Tile posSum 2999648 176 := gt (by
  have e : gw 2999648 176 = gw 2999648 176 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def g272d : Tile posSum 2999824 176 := gt (by
  have e : gw 2999824 176 = gw 2999824 176 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩)
noncomputable def g272 : Tile posSum 2999296 704 :=
  join (join g272a g272b) (join g272c g272d)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def tape_g : Tile posSum 0 3000000 := (join (join (join (join (join (join (join (join g0 g1) (join g2 g3)) (join (join g4 g5) (join g6 g7))) (join (join (join g8 g9) (join g10 g11)) (join (join g12 g13) (join g14 (join g15 g16))))) (join (join (join (join g17 g18) (join g19 g20)) (join (join g21 g22) (join g23 g24))) (join (join (join g25 g26) (join g27 g28)) (join (join g29 g30) (join g31 (join g32 g33)))))) (join (join (join (join (join g34 g35) (join g36 g37)) (join (join g38 g39) (join g40 g41))) (join (join (join g42 g43) (join g44 g45)) (join (join g46 g47) (join g48 (join g49 g50))))) (join (join (join (join g51 g52) (join g53 g54)) (join (join g55 g56) (join g57 g58))) (join (join (join g59 g60) (join g61 g62)) (join (join g63 g64) (join g65 (join g66 g67))))))) (join (join (join (join (join (join g68 g69) (join g70 g71)) (join (join g72 g73) (join g74 g75))) (join (join (join g76 g77) (join g78 g79)) (join (join g80 g81) (join g82 (join g83 g84))))) (join (join (join (join g85 g86) (join g87 g88)) (join (join g89 g90) (join g91 g92))) (join (join (join g93 g94) (join g95 g96)) (join (join g97 g98) (join g99 (join g100 g101)))))) (join (join (join (join (join g102 g103) (join g104 g105)) (join (join g106 g107) (join g108 g109))) (join (join (join g110 g111) (join g112 g113)) (join (join g114 g115) (join g116 (join g117 g118))))) (join (join (join (join g119 g120) (join g121 g122)) (join (join g123 g124) (join g125 g126))) (join (join (join g127 g128) (join g129 g130)) (join (join g131 g132) (join g133 (join g134 g135)))))))) (join (join (join (join (join (join (join g136 g137) (join g138 g139)) (join (join g140 g141) (join g142 g143))) (join (join (join g144 g145) (join g146 g147)) (join (join g148 g149) (join g150 (join g151 g152))))) (join (join (join (join g153 g154) (join g155 g156)) (join (join g157 g158) (join g159 g160))) (join (join (join g161 g162) (join g163 g164)) (join (join g165 g166) (join g167 (join g168 g169)))))) (join (join (join (join (join g170 g171) (join g172 g173)) (join (join g174 g175) (join g176 g177))) (join (join (join g178 g179) (join g180 g181)) (join (join g182 g183) (join g184 (join g185 g186))))) (join (join (join (join g187 g188) (join g189 g190)) (join (join g191 g192) (join g193 g194))) (join (join (join g195 g196) (join g197 g198)) (join (join g199 g200) (join g201 (join g202 g203))))))) (join (join (join (join (join (join g204 g205) (join g206 g207)) (join (join g208 g209) (join g210 g211))) (join (join (join g212 g213) (join g214 g215)) (join (join g216 g217) (join g218 (join g219 g220))))) (join (join (join (join g221 g222) (join g223 g224)) (join (join g225 g226) (join g227 g228))) (join (join (join g229 g230) (join g231 g232)) (join (join g233 g234) (join g235 (join g236 g237)))))) (join (join (join (join (join g238 g239) (join g240 g241)) (join (join g242 g243) (join g244 g245))) (join (join (join g246 g247) (join g248 g249)) (join (join g250 g251) (join g252 (join g253 g254))))) (join (join (join (join g255 g256) (join g257 g258)) (join (join g259 g260) (join g261 (join g262 g263)))) (join (join (join g264 g265) (join g266 g267)) (join (join g268 g269) (join g270 (join g271 g272)))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
noncomputable def pinned_g : {v : ℕ // v=tape_g.value} := by
  have e : tape_g.value=tape_g.value:=rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
end ThetaWidePinned

namespace ThetaWidePinned
open Finset ThetaWindow
noncomputable def packed : ℕ := pinned_g.1
theorem packed_spec : (packed:ℤ) = ∑ d∈Ioc 0 (3000000/(12000+1)),
    ∑ k∈Ioc 12000 (min 20000 (3000000/d)), (256*(coeff k+8192)+1)*(2^64:ℤ)^(d*k-1) := by
  change (pinned_g.1:ℤ)=_
  rw [pinned_g.2,tile_value 12000 20000 3000000 packedDigit tape_g]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro k hk
  have h : 12001+(k-(12000+1))=k := by have := (mem_Ioc.mp hk).1; omega
  rw [digit_cast,h]
end ThetaWidePinned

namespace ThetaWidePinned
open Finset FR7022Hyperbola ThetaWide
private def indices (d i : ℕ) : Finset ℕ :=
  (Ioc 12000 (min 20000 (3000000/d))).filter (fun k => d*k=i+1)
private def lane (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ d ∈ Ioc 0 (3000000/(12000+1)), ∑ k ∈ indices d i, f k
private theorem repack (f : ℕ → ℕ) :
    (word 64 3000000 (lane f) : ℤ) =
      ∑ d ∈ Ioc 0 (3000000/(12000+1)), ∑ k ∈ Ioc 12000 (min 20000 (3000000/d)),
        (f k : ℤ)*(2^64:ℤ)^(d*k-1) := by
  rw [word_cast _ _ (by decide)]
  simp only [lane, Nat.cast_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  simp_rw [indices, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  have dh := (mem_Ioc.mp hd).1
  obtain ⟨kl,ku⟩ := mem_Ioc.mp hk
  have pos := Nat.mul_pos dh (show 0<k by omega)
  have top : d*k ≤ 3000000 := by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le dh).mp (ku.trans (min_le_right _ _))
  have range_mem : d*k-1 ∈ range 3000000 := mem_range.mpr (by omega)
  have iff_index (i : ℕ) : d*k=i+1 ↔ d*k-1=i := by omega
  simp_rw [iff_index]
  rw [Finset.sum_eq_single_of_mem (d*k-1) range_mem (fun i _ ne => ite_eq_right (Ne.symm ne))]
  rw [ite_eq_left rfl, ←pow_mul, mul_comm]
private theorem lane_bound (f : ℕ → ℕ) (m : ℕ) (h : ∀ k, f k ≤ m) (i : ℕ) :
    lane f i ≤ 249*m := by
  unfold lane
  calc
    _ ≤ ∑ d ∈ Ioc 0 (3000000/(12000+1)), m := by
      apply sum_le_sum
      intro d hd
      have dp := (mem_Ioc.mp hd).1
      have one : (indices d i).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        exact Nat.eq_of_mul_eq_mul_left dp ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
      calc
        _ ≤ ∑ _k ∈ indices d i, m := sum_le_sum fun k _ => h k
        _ = (indices d i).card*m := by simp
        _ ≤ 1*m := Nat.mul_le_mul_right m one
        _ = m := Nat.one_mul _
    _ = _ := by simp
private noncomputable def biasedCoeff (k : ℕ) := (coeff k+8192).toNat
private theorem biased_int (k : ℕ) : (biasedCoeff k : ℤ) = coeff k+8192 := by
  apply Int.toNat_of_nonneg
  have := (abs_le.mp (coeff_le k)).1
  omega
private theorem biased_le (k : ℕ) : biasedCoeff k ≤ 16192 := by
  have h := (abs_le.mp (coeff_le k)).2
  exact_mod_cast (show (biasedCoeff k:ℤ) ≤ 16192 by rw [biased_int]; omega)
private theorem lane_add (i : ℕ) :
    lane (fun k => 256*biasedCoeff k+1) i =
      lane (fun _ => 1) i + 256*lane biasedCoeff i := by
  simp only [lane, mul_sum, ←sum_add_distrib, Nat.add_comm]
private theorem melt_mask (n : ℕ) (g u : ℕ → ℕ)
    (hg : ∀ i, g i ≤ 249*16192) (hu : ∀ i, u i ≤ 249) :
    word 64 n (fun i => u i+256*g i) &&& word 64 n (fun _ => 255) = word 64 n u := by
  let h := fun i => u i+256*g i
  have hf (i : ℕ) (_ : i<n) : h i < 2^64 := by dsimp [h]; have := hg i; have := hu i; omega
  have uf (i : ℕ) (_ : i<n) : u i < 2^64 := by have := hu i; omega
  have mf (i : ℕ) (_ : i<n) : (255:ℕ) < 2^64 := by decide
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  by_cases hj : j<64*n
  · let i := j/64
    let b := j % 64
    have hi : i<n := (Nat.div_lt_iff_lt_mul (by decide : 0<64)).mpr (by simpa [Nat.mul_comm] using hj)
    have hb : b<64 := Nat.mod_lt _ (by decide)
    have rep : 64*i+b=j := Nat.div_add_mod _ _
    change ((word 64 n h).testBit j && _) = _
    rw [←rep,word_bit (by decide) h hf i b hi hb, word_bit (by decide) _ mf i b hi hb,
      word_bit (by decide) u uf i b hi hb]
    have hm : (h i &&& 255) = u i := by
      rw [show (255:ℕ)=2^8-1 by decide, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [h]
      have := hu i
      omega
    exact (Nat.testBit_and _ _ _).symm.trans (congrArg (fun z : ℕ => z.testBit b) hm)
  · have big : (2:ℕ)^(64*n) ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((word_small (by decide) h hf).trans_le big),
      Nat.testBit_lt_two_pow ((word_small (by decide) u uf).trans_le big)]
    rfl
private theorem packed_word : packed =
    word 64 3000000 (fun i => lane (fun _ => 1) i + 256*lane biasedCoeff i) := by
  simp_rw [←lane_add]
  apply Int.ofNat_inj.mp
  rw [packed_spec,repack]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,biased_int]
private noncomputable def unitMask : ℕ := 255*ThetaWide.unit 64 22 3000000
private theorem unitMask_spec : unitMask = word 64 3000000 (fun _ => 255) := by
  rw [unitMask, unit_eq _ (by decide) _ _ (by decide), word_const]
noncomputable def extra : ℕ := packed &&& unitMask
private theorem extra_word : extra = word 64 3000000 (lane (fun _ => 1)) := by
  rw [extra,packed_word,unitMask_spec]
  exact melt_mask _ _ _ (lane_bound biasedCoeff 16192 biased_le)
    (fun i => by simpa using lane_bound (fun _ => 1) 1 (fun _ => le_rfl) i)
theorem extra_spec : (extra:ℤ)=∑d∈Ioc 0 (3000000/(12000+1)),
    ∑k∈Ioc 12000 (min 20000 (3000000/d)),(2^64:ℤ)^(d*k-1) := by
  rw [extra_word,repack]
  simp
noncomputable def base : ℤ := ((packed:ℤ)-(extra:ℤ))/256-8192*(extra:ℤ)
theorem base_spec : base=∑d∈Ioc 0 (3000000/(12000+1)),
    ∑k∈Ioc 12000 (min 20000 (3000000/d)),coeff k*(2^64:ℤ)^(d*k-1) := by
  let S := ∑d∈Ioc 0 (3000000/(12000+1)), ∑k∈Ioc 12000 (min 20000 (3000000/d)),coeff k*(2^64:ℤ)^(d*k-1)
  have eq : (packed:ℤ) = 256*(S+8192*(extra:ℤ))+(extra:ℤ) := by
    dsimp [S]
    rw [packed_spec,extra_spec]
    simp only [mul_add,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro k _
    ring
  change ((packed:ℤ)-(extra:ℤ))/256-8192*(extra:ℤ)=S
  rw [eq,add_sub_cancel_right,Int.mul_ediv_cancel_left _ (by decide)]
  ring
end ThetaWidePinned

/- Rational modular combination and Newton inversion adapt CATLILIZHOU PR 2645 and nanzhiyan1 PR 2649, Apache-2.0. -/
namespace FR7022Rational
structure Poly where
  d : Int
  a : Int
  e : Int
def clip (m : Nat) : Int → Int
  | .ofNat a => Int.ofNat (a &&& m)
  | .negSucc a => -Int.ofNat ((a+1) &&& m)
def withInt {α : Type} (x : Int) (f : Int → α) : α :=
  match x with
  | .ofNat n => withNat n (fun a => f (.ofNat a))
  | .negSucc n => withNat n (fun a => f (.negSucc a))
def inv (d : Int) (w : Nat) : Nat → Int
  | 0 => 1
  | h+1 =>
    let m : Int := Int.ofNat (1 <<< (min w (2^(h+1))))
    withInt (inv d w h) (fun v => (v*(2-(d % m)*v)) % m)
theorem withInt_eq {α} (x : Int) (f : Int → α) : withInt x f = f x := by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl
theorem clip_spec (w : Nat) (x : Int) : clip (2^w-1) x ≡ x [ZMOD (2:ℤ)^w] := by
  cases x with
  | ofNat n =>
    simpa [clip,Nat.and_two_pow_sub_one_eq_mod,Int.natCast_emod] using (Int.mod_modEq (n:ℤ) (2^w))
  | negSucc n =>
    change -((↑((n+1) &&& (2^w-1)):ℤ)) ≡ -((↑(n+1):ℤ)) [ZMOD (2:ℤ)^w]
    apply Int.neg_modEq_neg.mpr
    simpa [Nat.and_two_pow_sub_one_eq_mod,Int.natCast_emod] using (Int.mod_modEq (↑(n+1):ℤ) (2^w))
def Represents (w : ℕ) (v : Poly) (x y : ℤ) : Prop :=
  v.d*x ≡ v.a [ZMOD (2:ℤ)^w] ∧ v.d*y ≡ v.e [ZMOD (2:ℤ)^w] ∧ v.d ≡ 1 [ZMOD 2]
theorem lift_inv (M L d v : ℤ) (hd : M ∣ L*L) (h : d*v ≡ 1 [ZMOD L]) :
    d*((v*(2-(d % M)*v)) % M) ≡ 1 [ZMOD M] := by
  have h1 := Int.modEq_iff_dvd.mp h
  have h2 := hd.trans (mul_dvd_mul h1 h1)
  have restore : d*(v*(2-d*v)) ≡ 1 [ZMOD M] := by
    apply Int.modEq_iff_dvd.mpr
    convert h2 using 1 <;> ring
  calc
    _ ≡ d*(v*(2-(d % M)*v)) [ZMOD M] := (Int.mod_modEq _ _).mul_left _
    _ ≡ d*(v*(2-d*v)) [ZMOD M] :=
      (((Int.ModEq.refl 2).sub ((Int.mod_modEq d M).mul_right v)).mul_left v).mul_left d
    _ ≡ 1 [ZMOD M] := restore
theorem inv_spec (d : Int) (w h : Nat) (hw : 0 < w) (hd : d ≡ 1 [ZMOD 2]) :
    d*inv d w h ≡ 1 [ZMOD (2:ℤ)^(min w (2^h))] := by
  induction h with
  | zero => simpa [inv,min_eq_right (show 1 ≤ w by omega)] using hd
  | succ h ih =>
    have he : min w (2^(h+1)) ≤ min w (2^h)+min w (2^h) := by rw [pow_succ]; omega
    have dv : (2:ℤ)^(min w (2^(h+1))) ∣ (2:ℤ)^(min w (2^h)) * 2^(min w (2^h)) := by
      rw [←pow_add]
      exact pow_dvd_pow _ he
    simp only [inv,withInt_eq,Nat.shiftLeft_eq,one_mul,Int.ofNat_eq_natCast,Nat.cast_pow,Nat.cast_ofNat]
    exact lift_inv _ _ _ _ dv ih
end FR7022Rational

namespace ThetaKernel
open Finset FR7022Rational
noncomputable section

def leafSum (z : ℤ) (B k : ℕ) : ℤ := z^(k-1) * ∑ j ∈ range (B/k), (z^k)^j

theorem leafSum_filter (z : ℤ) (B k : ℕ) (hk : 0<k) :
    leafSum z B k = ∑ j ∈ Icc 1 B, if k∣j then z^(j-1) else 0 := by
  rw [←sum_filter]
  have hs : ((Icc 1 B).filter (k∣·)) = (range (B/k)).image (fun i => k*(i+1)) := by
    ext j
    constructor
    · intro hj
      obtain ⟨hja,hjd⟩ := mem_filter.mp hj
      obtain ⟨t,rfl⟩ := hjd
      obtain ⟨hj1,hjB⟩ := mem_Icc.mp hja
      cases t with
      | zero => simp at hj1
      | succ t =>
        exact mem_image.mpr ⟨t,mem_range.mpr ((Nat.le_div_iff_mul_le hk).mpr (by simpa [mul_comm] using hjB)),rfl⟩
    · rintro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hk (by omega),by simpa [mul_comm] using (Nat.le_div_iff_mul_le hk).mp (mem_range.mp hi)⟩,dvd_mul_right _ _⟩
  rw [hs,sum_image (fun i _ j _ he => by have h := Nat.eq_of_mul_eq_mul_left hk he; omega)]
  unfold leafSum; rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [←pow_mul,←pow_add]
  congr 1; rw [Nat.mul_add]; omega

theorem leaf_relation (w B k : ℕ) (hk : 0<k) :
    let z := (2:ℤ)^w
    (1-z^k)*leafSum z B k ≡ z^(k-1) [ZMOD (2:ℤ)^(w*B)] := by
  intro z
  have hpow : B≤(k-1)+k*(B/k) := by
    have hm := Nat.mod_lt B hk
    have he := Nat.mod_add_div B k
    omega
  have hd : z^B ∣ z^((k-1)+k*(B/k)) := pow_dvd_pow z hpow
  rw [Int.modEq_iff_dvd]
  have he : z^(k-1)-(1-z^k)*leafSum z B k=z^((k-1)+k*(B/k)) := by
    rw [pow_add,pow_mul,leafSum]
    have hh := geom_sum_mul (z^k) (B/k)
    linear_combination z^(k-1)*hh
  rw [he]
  simpa [z,pow_mul] using hd

def divisorEval (w B K : ℕ) (f : ℕ→ℤ) : ℤ :=
  ∑ j ∈ Icc 1 B,(∑ k ∈ Icc 1 K,if k∣j then f k else 0)*((2:ℤ)^w)^(j-1)

theorem eval_fibers (w B K : ℕ) (f : ℕ→ℤ) :
    divisorEval w B K f = ∑ k ∈ Icc 1 K,f k*leafSum ((2:ℤ)^w) B k := by
  unfold divisorEval
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [leafSum_filter _ _ _ (mem_Icc.mp hk).1,mul_sum]
  apply sum_congr rfl
  intro j hj
  by_cases h : k∣j <;> simp [h]

def leaf (w B : ℕ) (f g : ℕ→ℤ) (k : ℕ) : Poly :=
  if f k=0 ∧ g k=0 then ⟨1,0,0⟩ else
    ⟨1-((1:ℤ)<<<(w*k)),(f k)<<<(w*(k-1)),(g k)<<<(w*(k-1))⟩

theorem represents_leaf (w B : ℕ) (hw : 0<w) (f g : ℕ→ℤ) (k : ℕ) (hk : 0<k) :
    Represents (w*B) (leaf w B f g k)
       (f k*leafSum ((2:ℤ)^w) B k) (g k*leafSum ((2:ℤ)^w) B k) := by
  unfold leaf
  split_ifs with hh
  · simp [Represents,hh.1,hh.2]
  · simp only [Represents,Int.shiftLeft_eq,one_mul,pow_mul]
    have hl := leaf_relation w B k hk
    change _ ≡ _ [ZMOD _] at hl
    refine ⟨?_,?_,?_⟩
    · simpa only [mul_left_comm,pow_mul] using hl.mul_left (f k)
    · simpa only [mul_left_comm,pow_mul] using hl.mul_left (g k)
    · have he : ((2:ℤ)^w)^k ≡ 0 [ZMOD 2] := Int.modEq_zero_iff_dvd.mpr
          (dvd_trans (dvd_pow_self _ (by omega : w≠0)) (dvd_pow_self _ (by omega : k≠0)))
      simpa using (Int.ModEq.refl 1).sub he

def walk (f : ℕ→ℤ) : ℕ→ℕ→ℤ
  | 0,k => f k
  | h+1,k => walk f h k + walk f h (k+2^h)

theorem walk_sum (f : ℕ→ℤ) (h k : ℕ) : walk f h k=∑ j∈range (2^h),f (k+j) := by
  induction h generalizing k with
  | zero => simp [walk]
  | succ h ih =>
    rw [walk,ih,ih,pow_succ,Nat.mul_two,sum_range_add]
    simp only [Nat.add_assoc]

end
end ThetaKernel

namespace ThetaKernel
open Finset FR7022Lane GoldbachCoefficientPrefix

theorem divisorEval_eq (w B K : ℕ) (f : ℕ→ℤ) :
    divisorEval w B K f = eval ((2:ℤ)^w) B (fun i=>divisorWeight (Icc 1 K) f (i+1)) := by
  rw [divisorEval,eval_eq_sum]
  have hs : Icc 1 B=Ico 1 (B+1) := by ext i; simp
  rw [hs,sum_Ico_eq_sum_range,Nat.add_sub_cancel]
  apply sum_congr rfl
  intro i hi
  simp only [divisorWeight,add_comm 1 i,Nat.add_sub_cancel]
  rw [mul_comm]

theorem leaf_multiples (w B : ℕ) (f : ℕ→ℤ) (k : ℕ) (hk : 0<k) :
    f k*leafSum ((2:ℤ)^w) B k =
    ∑ d∈Ioc 0 (B/k),f k*((2:ℤ)^w)^(d*k-1) := by
  rw [←Ico_add_one_add_one_eq_Ioc,sum_Ico_eq_sum_range,Nat.zero_add,Nat.add_sub_cancel]
  unfold leafSum
  rw [←mul_assoc,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_assoc,←pow_mul ((2:ℤ)^w) k i,←pow_add]
  congr 2
  rw [Nat.add_mul,one_mul,Nat.mul_comm i k]
  omega

theorem word_split (w B K D : ℕ) (hDK : D≤K) (f : ℕ→ℤ) :
    divisorEval w B K f = divisorEval w B D f +
    ∑ d∈Ioc 0 (B/(D+1)),∑ k∈Ioc D (min K (B/d)),f k*((2:ℤ)^w)^(d*k-1) := by
  rw [eval_fibers,eval_fibers]
  have hU : Icc 1 K = Icc 1 D ∪ Ioc D K := by ext k; simp; omega
  have hdis : Disjoint (Icc 1 D) (Ioc D K) := by
    apply disjoint_left.mpr; simp only [mem_Icc,mem_Ioc]; omega
  rw [hU,sum_union hdis]
  congr 1
  calc
    _ = ∑ k∈Ioc D K,∑ d∈Ioc 0 (B/k),f k*((2:ℤ)^w)^(d*k-1) :=
      sum_congr rfl fun k h=>leaf_multiples _ _ _ _ (by have := (mem_Ioc.mp h).1; omega)
    _ = _ := by
      apply sum_comm'
      intro k d
      simp only [mem_Ioc,le_min_iff]
      constructor
      · rintro ⟨⟨hk,hK⟩,hd,hB⟩
        have hk' : 0<k := by omega
        have hprod := (Nat.le_div_iff_mul_le hk').mp hB
        exact ⟨⟨hk,hK,(Nat.le_div_iff_mul_le hd).mpr ((Nat.mul_comm _ _).trans_le hprod)⟩,
          hd,(Nat.le_div_iff_mul_le (Nat.succ_pos D)).mpr ((Nat.mul_le_mul_left d hk).trans hprod)⟩
      · rintro ⟨⟨hk,hK,hB⟩,hd,_⟩
        have hk' : 0<k := by omega
        exact ⟨⟨hk,hK⟩,hd,(Nat.le_div_iff_mul_le hk').mpr
          ((Nat.mul_comm _ _).trans_le ((Nat.le_div_iff_mul_le hd).mp hB))⟩

end ThetaKernel

namespace ThetaKernel
open Finset FR7022Lane FR7022Flat FR7022Hyperbola

def ones (w B : ℕ) : ℤ := (((1:ℤ)<<<(w*B))-1)/(((1:ℤ)<<<w)-1)

theorem ones_spec (w B : ℕ) (hw : 0<w) :
    ones w B = eval ((2:ℤ)^w) B (fun _=>1) := by
  rw [ones,Int.shiftLeft_eq,Int.shiftLeft_eq,one_mul,one_mul,pow_mul,eval_eq_sum]
  simp only [mul_one]
  rw [←geom_sum_mul]
  apply Int.mul_ediv_cancel
  have hp := one_lt_pow₀ (by decide : (1:ℤ)<2) hw.ne'
  omega

def padded (B C : ℕ) (a : ℕ→ℤ) (i : ℕ) : ℕ := if i<B then ((C:ℤ)+a i).toNat else 0

theorem padded_eq (w B N C : ℕ) (hw : 0<w) (hN : B≤N)
    (a : ℕ→ℤ) (ha : ∀ i<B, -(C:ℤ)≤a i) :
    (word w N (padded B C a):ℤ) = (C:ℤ)*ones w B+eval ((2:ℤ)^w) B a := by
  rw [word,pack_int]
  simp only [show w-1+1=w by omega,Nat.cast_pow,Nat.cast_ofNat,ones_spec w B hw,
    eval_eq_sum,mul_one,mul_sum,←sum_add_distrib]
  calc
    ∑ i ∈ range N, (2^w:ℤ)^i*(padded B C a i:ℤ) =
      ∑ i ∈ range B, (2^w:ℤ)^i*(padded B C a i:ℤ) := by
        symm
        apply sum_subset (range_mono hN)
        intro i hi hn
        simp [padded,mem_range.mpr.mt hn]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have hl := ha i (mem_range.mp hi)
      rw [padded,if_pos (mem_range.mp hi),Int.toNat_of_nonneg (by omega)]
      ring

def widen (iw ow B depth C : ℕ) (raw : ℤ) : ℤ :=
  let biased := ((raw+C*ones iw B) % ((1:ℤ)<<<(iw*B))).toNat
  (expand iw ow depth biased 1 : ℤ)-C*ones ow B

theorem widen_spec (iw ow B depth C : ℕ) (raw : ℤ) (a : ℕ→ℤ)
    (hi : 0 < iw) (ho : iw≤ow) (hN : B≤2^depth)
    (hlo : ∀ i<B,-(C:ℤ)≤a i) (hhi : ∀ i<B,(C:ℤ)+a i < (2:ℤ)^iw)
    (hr : raw ≡ eval ((2:ℤ)^iw) B a [ZMOD (2:ℤ)^(iw*B)]) :
    widen iw ow B depth C raw = eval ((2:ℤ)^ow) B a := by
  let v := padded B C a
  have hv (i : ℕ) : v i < 2^iw := by
    dsimp [v,padded]
    split_ifs with hb
    · have hl := hlo i hb
      have hh := hhi i hb
      exact_mod_cast (show (((C:ℤ)+a i).toNat:ℤ)<(2:ℤ)^iw by rwa [Int.toNat_of_nonneg (by omega)])
    · positivity
  have hs : word iw B v<2^(iw*B) := word_small hi _ (fun i _=>hv i)
  have hp := padded_eq iw B B C hi le_rfl a hlo
  have hp' := padded_eq iw B (2^depth) C hi hN a hlo
  have hb : ((raw+C*ones iw B) % ((1:ℤ)<<<(iw*B))).toNat = word iw (2^depth) v := by
    rw [Int.shiftLeft_eq,one_mul]
    have eq := hr.add_left ((C:ℤ)*ones iw B)
    rw [←hp,add_comm] at eq
    change _ % _ = _ % _ at eq
    have hposs : (0:ℤ)≤(word iw B v:ℤ) := by positivity
    have hc : (word iw B v:ℤ) < (2:ℤ)^(iw*B) := by exact_mod_cast hs
    rw [Int.emod_eq_of_lt hposs hc] at eq
    rw [eq,Int.toNat_natCast]
    exact_mod_cast hp.trans hp'.symm
  rw [widen,hb,expand_word (@split_lanes) iw ow hi ho v hv,padded_eq ow B (2^depth) C (hi.trans_le ho) hN a hlo]
  ring
end ThetaKernel

namespace ThetaKernel
open Finset FR7022Lane GoldbachCoefficientPrefix ThetaScalar

def signCut (D k : ℕ) : ℤ := if k≤D then signs k else 0

theorem sign_small (k : ℕ) : |signs k|≤1 := by
  unfold signs
  split <;> norm_num

theorem sign_column_bound (D j : ℕ) :
    |divisorWeight (Icc 1 D) signs j|≤(D:ℤ) := by
  unfold divisorWeight
  calc
    _ ≤ ∑ k∈Icc 1 D,|if k∣j then signs k else (0:ℤ)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _k∈Icc 1 D,(1:ℤ) := sum_le_sum (fun k _=>by split_ifs <;> simp [sign_small])
    _ = D := by simp

theorem sign_cut_weight (D K j : ℕ) (hD : D≤K) :
    divisorWeight (Icc 1 K) (signCut D) j = divisorWeight (Icc 1 D) signs j := by
  have hS : Icc 1 D⊆Icc 1 K := Icc_subset_Icc_right hD
  unfold divisorWeight
  calc
    _ = ∑ k∈Icc 1 D,if k∣j then signCut D k else 0 := by
      symm; apply sum_subset hS
      intro k hK hn
      have hd : ¬k≤D := fun h=> hn (mem_Icc.mpr ⟨(mem_Icc.mp hK).1,h⟩)
      simp [signCut,hd]
    _ = _ := sum_congr rfl (fun k hk=>by simp [signCut,(mem_Icc.mp hk).2])

theorem low_scaled (D B : ℕ) (hD : D≤12000) :
    divisorEval 64 B D (fun k=>signs k*(min 8000 (20000-k):ℕ)) =
    8000*divisorEval 64 B D signs := by
  rw [eval_fibers,eval_fibers,mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk' := (mem_Icc.mp hk).2
  rw [min_eq_left (by omega : 8000≤20000-k)]
  push_cast
  ring
end ThetaKernel

namespace ThetaKernel
open Finset FR7022Rational

def boundAt (w B h k : ℕ) (v : ℤ) : ℤ :=
  if 2^h*(k+2^h)≤B then v else clip ((1<<<(w*B))-1) v

theorem boundAt_spec (w B h k : ℕ) (v : ℤ) : boundAt w B h k v ≡ v [ZMOD (2:ℤ)^(w*B)] := by
  unfold boundAt
  split_ifs
  · rfl
  · simpa [Nat.shiftLeft_eq] using clip_spec (w*B) v

def fastColumn {α : Type} (w B D : ℕ) (f : ℕ→ℤ) : ℕ→ℕ→(ℤ→ℤ→α)→α
  | 0,k,C => if k>D then C 1 0 else
    withInt (f k) fun c => if c=0 then C 1 0 else
      withInt (1-((1:ℤ)<<<(w*k))) fun d => withInt (c<<<(w*(k-1))) (C d)
  | h+1,k,C => if k>D then C 1 0 else
    fastColumn w B D f h k fun d a => fastColumn w B D f h (k+2^h) fun g b =>
      withInt (boundAt w B (h+1) k (d*g)) fun u =>
        withInt (boundAt w B (h+1) k (a*g+b*d)) (C u)

def fastPair (w B D h : ℕ) (f : ℕ→ℤ) := fastColumn w B D f h 1 Prod.mk

def fastRaw (w B : ℕ) (p : ℤ×ℤ) : ℤ :=
  let bits := w*B
  withNat (1<<<bits) fun M =>
    withInt (inv p.1 bits ((bits-1).log2+1)) fun v => (p.2*v) % (M:ℤ)

end ThetaKernel

namespace ThetaKernel
open Finset FR7022Rational

def foldValue (w B D : ℕ) (f : ℕ→ℤ) (h k : ℕ) :=
  walk (fun j=>(if j≤D then f j else 0)*leafSum ((2:ℤ)^w) B j) h k

theorem fold_zero (w B D : ℕ) (f : ℕ→ℤ) (h k : ℕ) (hk : D<k) :
    foldValue w B D f h k=0 := by
  rw [foldValue,walk_sum]
  apply sum_eq_zero
  intro i hi
  simp [show ¬k+i≤D by omega]

theorem fast_ind {α : Type} (w B D : ℕ) (hw : 0<w) (hB : 0<B) (f : ℕ→ℤ)
    (h k : ℕ) (hk : 0<k) (C : ℤ→ℤ→α) (P : α→Prop)
    (good : ∀ d a, d*foldValue w B D f h k ≡ a [ZMOD (2:ℤ)^(w*B)] →
      d ≡ 1 [ZMOD 2] → P (C d a)) : P (fastColumn w B D f h k C) := by
  induction h generalizing k C with
  | zero =>
    unfold fastColumn
    by_cases hD : D<k
    · rw [ite_eq_left hD]
      apply good <;> simp [fold_zero _ _ _ _ _ _ hD]
    · rw [ite_eq_right hD,withInt_eq]
      have hkD : k≤D := by omega
      have eqv : foldValue w B D f 0 k = f k*leafSum ((2:ℤ)^w) B k := by simp [foldValue,walk,hkD]
      have H := represents_leaf w B hw f (fun _=>0) k hk
      split_ifs with hz
      · apply good <;> simp [eqv,hz]
      · rw [withInt_eq,withInt_eq]
        apply good
        · simpa [eqv,leaf,hz] using H.1
        · simpa [leaf,hz] using H.2.2
  | succ h ih =>
    rw [fastColumn]
    by_cases hD : D<k
    · rw [ite_eq_left hD]
      apply good <;> simp [fold_zero _ _ _ _ _ _ hD]
    · rw [ite_eq_right hD]
      apply ih k hk
      intro d a hx hd
      apply ih (k+2^h) (Nat.add_pos_left hk _)
      intro g b hy hg
      rw [withInt_eq,withInt_eq]
      apply good
      · let x := foldValue w B D f h k
        let y := foldValue w B D f h (k+2^h)
        change boundAt w B (h+1) k (d*g)*(x+y) ≡ boundAt w B (h+1) k (a*g+b*d) [ZMOD _]
        calc
          _ ≡ (d*g)*(x+y) [ZMOD (2:ℤ)^(w*B)] := (boundAt_spec _ _ _ _ _).mul_right _
          _ = (d*x)*g+(g*y)*d := by ring
          _ ≡ a*g+b*d [ZMOD (2:ℤ)^(w*B)] := (hx.mul_right _).add (hy.mul_right _)
          _ ≡ _ [ZMOD (2:ℤ)^(w*B)] := (boundAt_spec _ _ _ _ _).symm
      · have hh : (2:ℤ) ∣ 2^(w*B) := dvd_pow_self _ (Nat.mul_pos hw hB).ne'
        exact ((boundAt_spec _ _ _ _ _).of_dvd hh).trans (by simpa using hd.mul hg)

theorem fastRaw_spec (w B : ℕ) (p : ℤ×ℤ) (x : ℤ) (hw : 0<w) (hB : 0<B)
    (hp : p.1*x ≡ p.2 [ZMOD (2:ℤ)^(w*B)]) (hodd : p.1 ≡ 1 [ZMOD 2]) :
    fastRaw w B p ≡ x [ZMOD (2:ℤ)^(w*B)] := by
  have hh : w*B≤2^((w*B-1).log2+1) := by have h := Nat.lt_log2_self (n:=w*B-1); omega
  have hi := inv_spec p.1 (w*B) ((w*B-1).log2+1) (Nat.mul_pos hw hB) hodd
  rw [min_eq_left hh] at hi
  simp only [fastRaw,withNat_eq,withInt_eq,Nat.shiftLeft_eq,one_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (Int.mod_modEq _ _).trans
  calc
    _ ≡ (p.1*x)*inv p.1 (w*B) ((w*B-1).log2+1) [ZMOD (2:ℤ)^(w*B)] := hp.symm.mul_right _
    _ = (p.1*inv p.1 (w*B) ((w*B-1).log2+1))*x := by ring
    _ ≡ x [ZMOD (2:ℤ)^(w*B)] := by simpa using hi.mul_right x
end ThetaKernel

namespace ThetaKernel
open FR7022Rational

def RepresentsPair (m : ℕ) (v : ℤ×ℤ) (x : ℤ) : Prop :=
  v.1*x ≡ v.2 [ZMOD (2:ℤ)^m] ∧ v.1 ≡ 1 [ZMOD 2]

def pairDo (w B h k : ℕ) (l r : ℤ×ℤ) : ℤ×ℤ :=
  (boundAt w B h k (l.1*r.1),boundAt w B h k (l.2*r.1+r.2*l.1))

theorem pairDo_good (w B h k : ℕ) (hw : 0<w) (hB : 0<B) (l r : ℤ×ℤ) (x y : ℤ)
    (hl : RepresentsPair (w*B) l x) (hr : RepresentsPair (w*B) r y) :
    RepresentsPair (w*B) (pairDo w B h k l r) (x+y) := by
  constructor
  · change boundAt w B h k (l.1*r.1)*(x+y) ≡ boundAt w B h k (l.2*r.1+r.2*l.1) [ZMOD _]
    calc
      _ ≡ (l.1*r.1)*(x+y) [ZMOD (2:ℤ)^(w*B)] := (boundAt_spec _ _ _ _ _).mul_right _
      _ = (l.1*x)*r.1+(r.1*y)*l.1 := by ring
      _ ≡ l.2*r.1+r.2*l.1 [ZMOD (2:ℤ)^(w*B)] := (hl.1.mul_right _).add (hr.1.mul_right _)
      _ ≡ _ [ZMOD (2:ℤ)^(w*B)] := (boundAt_spec _ _ _ _ _).symm
  · have hh : (2:ℤ)∣2^(w*B) := dvd_pow_self _ (Nat.mul_pos hw hB).ne'
    exact ((boundAt_spec _ _ _ _ _).of_dvd hh).trans (by simpa using hl.2.mul hr.2)

structure Piece (h k : ℕ) where
  data : ℤ×ℤ
  spec : RepresentsPair (15*3000000) data (foldValue 15 3000000 12000 ThetaScalar.signs h k)

def pieceLeaf (h k : ℕ) (hk : 0<k)
    (p : {p : ℤ×ℤ // p=fastColumn 15 3000000 12000 ThetaScalar.signs h k Prod.mk}) : Piece h k where
  data := p.1
  spec := by
    rw [p.2]
    exact fast_ind 15 3000000 12000 (by decide) (by decide) ThetaScalar.signs h k hk Prod.mk
      (fun v:ℤ×ℤ => RepresentsPair (15*3000000) v (foldValue 15 3000000 12000 ThetaScalar.signs h k))
      (fun _ _ h1 h2 => ⟨h1,h2⟩)

def pieceJoin (h k : ℕ) (l : Piece h k) (r : Piece h (k+2^h))
    (p : {p:ℤ×ℤ // p=pairDo 15 3000000 (h+1) k l.data r.data}) : Piece (h+1) k where
  data := p.1
  spec := by
    rw [p.2]
    exact pairDo_good _ _ _ _ (by decide) (by decide) _ _ _ _ l.spec r.spec

def pieceZero (h k : ℕ) (hk : 12000<k) : Piece h k where
  data := (1,0)
  spec := by simp [RepresentsPair,fold_zero _ _ _ _ _ _ hk]

theorem whole_fold : foldValue 15 3000000 12000 ThetaScalar.signs 14 1
    = divisorEval 15 3000000 12000 ThetaScalar.signs := by
  have eqCut : divisorEval 15 3000000 (2^14) (signCut 12000)=divisorEval 15 3000000 12000 ThetaScalar.signs := by
    rw [divisorEval_eq,divisorEval_eq]; simp_rw [sign_cut_weight 12000 (2^14) _ (by decide)]
  rw [←eqCut,foldValue,walk_sum,eval_fibers]
  have hS : Finset.Icc 1 (2^14)=Finset.Ico 1 (2^14+1) := by ext i; simp; omega
  rw [hS,Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel]
  rfl
end ThetaKernel

namespace ThetaKernel
open FR7022Hyperbola FR7022Flat

def chunkSpread (iw ow tip : ℕ) : ℕ→ℕ→ℕ
  | 0,z=>z
  | h+1,z=> if z=0 then 0 else if h+1≤tip then expand iw ow (h+1) z 1 else
    let half := 2^h
    chunkSpread iw ow tip h (z &&& (ThetaWide.powBit (iw*half)-1))+
      (chunkSpread iw ow tip h (z >>> (iw*half)) <<< (ow*half))

theorem chunkSpread_eq (iw ow tip h z : ℕ) (hi : 0 < iw) (ho : iw≤ow) :
    chunkSpread iw ow tip h z=ThetaWide.spread iw ow tip h z := by
  induction h generalizing z with
  | zero => rfl
  | succ h ih =>
    rw [chunkSpread]
    by_cases hz : z=0
    · rw [ite_eq_left hz,hz]
      have e := ThetaWide.spread_eq iw ow tip hi ho (fun _=>0)
        (fun _=>Nat.two_pow_pos _) (h+1)
      simpa only [ThetaWide.word_zeros] using e.symm
    · rw [ite_eq_right hz,ThetaWide.spread]
      split_ifs
      · rfl
      · simp only [ih]

theorem chunkSpread_small (iw ow tip h z : ℕ) (hi : 0 < iw) (ho : iw≤ow)
    (hz : z<2^(iw*2^h)) :
    chunkSpread iw ow tip h z = expand iw ow h z 1 := by
  let f := fun i=>slice iw z i 1
  have hf (i : ℕ) : f i<2^iw := by
    dsimp [f,slice]
    simp only [Nat.mul_one,Nat.shiftLeft_eq,Nat.one_mul]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
  have hr := word_of_slots (u:=iw) (N:=2^h) (table:=z) hi hz f (fun i _=>hf i) (fun _ _=>rfl)
  rw [chunkSpread_eq iw ow tip h z hi ho,hr,ThetaWide.spread_eq iw ow tip hi ho f hf h,
    expand_word (@split_lanes) iw ow hi ho f hf h]

def biasedRaw (iw B C : ℕ) (raw : ℤ) : ℕ := ((raw+C*ones iw B) % ((1:ℤ)<<<(iw*B))).toNat

theorem biasedRaw_bound (iw B h C : ℕ) (raw : ℤ) (hB : B≤2^h) :
    biasedRaw iw B C raw<2^(iw*2^h) := by
  let M := (2:ℤ)^(iw*B)
  have hm : 0<M := by dsimp [M]; positivity
  have hl := Int.emod_nonneg (raw+C*ones iw B) hm.ne'
  have hu := Int.emod_lt_of_pos (raw+C*ones iw B) hm
  have hcut : biasedRaw iw B C raw < 2^(iw*B) := by
    rw [biasedRaw,Int.shiftLeft_eq,one_mul]
    exact_mod_cast (show (((raw+C*ones iw B) % M).toNat:ℤ) < (2:ℤ)^(iw*B) by
      rw [Int.toNat_of_nonneg hl]; exact hu)
  exact hcut.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left iw hB))

theorem widenChunks_eq (iw ow tip B depth C : ℕ) (raw : ℤ)
    (hi : 0 < iw) (ho : iw≤ow) (hB : B≤2^depth) :
    (chunkSpread iw ow tip depth (biasedRaw iw B C raw):ℤ)-C*ones ow B = widen iw ow B depth C raw := by
  rw [chunkSpread_small _ _ _ _ _ hi ho (biasedRaw_bound _ _ _ _ _ hB)]
  rfl
end ThetaKernel

namespace ThetaKernel
open FR7022Rational

def wLeft (p z : ℕ) := z &&& (ThetaWide.powBit (15*2^p)-1)
def wRight (p z : ℕ) := z >>> (15*2^p)
def wJoin (p l r : ℕ) := l+(r<<<(64*2^p))

theorem chunk_zero (h : ℕ) : chunkSpread 15 64 13 h 0=0 := by
  cases h <;> simp [chunkSpread]

theorem chunk_step (p z : ℕ) (hp : 13<p+1) :
    chunkSpread 15 64 13 (p+1) z =
      wJoin p (chunkSpread 15 64 13 p (wLeft p z)) (chunkSpread 15 64 13 p (wRight p z)) := by
  rw [chunkSpread]
  by_cases hz : z=0
  · simp [hz,wLeft,wRight,wJoin,chunk_zero]
  · simp [hz,not_le.mpr hp,wLeft,wRight,wJoin]

structure WidePiece (d z : ℕ) where
  val : ℕ
  spec : val = chunkSpread 15 64 13 d z

def wideJoin (p z : ℕ) (hp : 13<p+1) (l : WidePiece p (wLeft p z)) (r : WidePiece p (wRight p z)) :
    WidePiece (p+1) z where
  val := wJoin p l.val r.val
  spec := by rw [l.spec,r.spec,chunk_step p z hp]

theorem finishWide {raw : ℤ} {b : ℕ} (hb : b=biasedRaw 15 3000000 12000 raw)
    (v : WidePiece 22 b) :
    (v.val:ℤ)-12000*ones 64 3000000=widen 15 64 3000000 22 12000 raw := by
  rw [v.spec,hb]
  exact widenChunks_eq 15 64 13 3000000 22 12000 raw (by decide) (by decide) (by decide)

def finishNewton (w B : ℕ) (p : ℤ×ℤ) (v : ℤ) : ℤ :=
  (p.2*v) % ((1<<<(w*B):ℕ):ℤ)

theorem finishNewton_eq (w B : ℕ) (p : ℤ×ℤ) (v : ℤ)
    (hv : v=inv p.1 (w*B) ((w*B-1).log2+1)) :
    finishNewton w B p v=fastRaw w B p := by
  rw [hv]
  simp only [finishNewton,fastRaw,withInt_eq,withNat_eq]
end ThetaKernel

namespace ThetaKernel
open FR7022Lane GoldbachCoefficientPrefix
theorem pinnedLow_spec (p : Piece 14 1) (ur wr : ℤ)
    (hraw : ur=fastRaw 15 3000000 p.data) (hwide : wr=widen 15 64 3000000 22 12000 ur) :
    wr=divisorEval 64 3000000 12000 ThetaScalar.signs := by
  rw [hwide,divisorEval_eq]
  apply widen_spec _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · intro i _
    exact (abs_le.mp (sign_column_bound 12000 (i+1))).1
  · intro i _
    have hd := (abs_le.mp (sign_column_bound 12000 (i+1))).2
    norm_num at hd ⊢
    omega
  · have H := p.spec
    rw [whole_fold] at H
    have H' := fastRaw_spec 15 3000000 p.data _ (by decide) (by decide) H.1 H.2
    rw [←hraw,divisorEval_eq] at H'
    exact H'
end ThetaKernel

namespace ThetaKernel

/- The low columns are evaluated in blocks of 512.  Materializing three levels of the product tree bounds the amount of intermediate arithmetic stored in the compiled proof. -/

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_1 : Piece 9 1 := pieceLeaf 9 1 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 1 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 1 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_513 : Piece 9 513 := pieceLeaf 9 513 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 513 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 513 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_1 : Piece 10 1 := pieceJoin 9 1 p_9_1 p_9_513 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_1025 : Piece 9 1025 := pieceLeaf 9 1025 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 1025 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 1025 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_1537 : Piece 9 1537 := pieceLeaf 9 1537 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 1537 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 1537 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_1025 : Piece 10 1025 := pieceJoin 9 1025 p_9_1025 p_9_1537 ⟨_, rfl⟩

noncomputable def p_11_1 : Piece 11 1 := pieceJoin 10 1 p_10_1 p_10_1025 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_2049 : Piece 9 2049 := pieceLeaf 9 2049 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 2049 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 2049 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_2561 : Piece 9 2561 := pieceLeaf 9 2561 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 2561 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 2561 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_2049 : Piece 10 2049 := pieceJoin 9 2049 p_9_2049 p_9_2561 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_3073 : Piece 9 3073 := pieceLeaf 9 3073 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 3073 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 3073 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_3585 : Piece 9 3585 := pieceLeaf 9 3585 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 3585 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 3585 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_3073 : Piece 10 3073 := pieceJoin 9 3073 p_9_3073 p_9_3585 ⟨_, rfl⟩

noncomputable def p_11_2049 : Piece 11 2049 := pieceJoin 10 2049 p_10_2049 p_10_3073 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_12_1 : Piece 12 1 := pieceJoin 11 1 p_11_1 p_11_2049 (by
  have e : pairDo 15 3000000 12 1 p_11_1.data p_11_2049.data = pairDo 15 3000000 12 1 p_11_1.data p_11_2049.data := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_4097 : Piece 9 4097 := pieceLeaf 9 4097 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 4097 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 4097 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_4609 : Piece 9 4609 := pieceLeaf 9 4609 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 4609 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 4609 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_4097 : Piece 10 4097 := pieceJoin 9 4097 p_9_4097 p_9_4609 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_5121 : Piece 9 5121 := pieceLeaf 9 5121 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 5121 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 5121 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_5633 : Piece 9 5633 := pieceLeaf 9 5633 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 5633 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 5633 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_5121 : Piece 10 5121 := pieceJoin 9 5121 p_9_5121 p_9_5633 ⟨_, rfl⟩

noncomputable def p_11_4097 : Piece 11 4097 := pieceJoin 10 4097 p_10_4097 p_10_5121 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_6145 : Piece 9 6145 := pieceLeaf 9 6145 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 6145 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 6145 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_6657 : Piece 9 6657 := pieceLeaf 9 6657 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 6657 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 6657 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_6145 : Piece 10 6145 := pieceJoin 9 6145 p_9_6145 p_9_6657 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_7169 : Piece 9 7169 := pieceLeaf 9 7169 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 7169 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 7169 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_7681 : Piece 9 7681 := pieceLeaf 9 7681 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 7681 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 7681 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_7169 : Piece 10 7169 := pieceJoin 9 7169 p_9_7169 p_9_7681 ⟨_, rfl⟩

noncomputable def p_11_6145 : Piece 11 6145 := pieceJoin 10 6145 p_10_6145 p_10_7169 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_12_4097 : Piece 12 4097 := pieceJoin 11 4097 p_11_4097 p_11_6145 (by
  have e : pairDo 15 3000000 12 4097 p_11_4097.data p_11_6145.data = pairDo 15 3000000 12 4097 p_11_4097.data p_11_6145.data := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_13_1 : Piece 13 1 := pieceJoin 12 1 p_12_1 p_12_4097 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_8193 : Piece 9 8193 := pieceLeaf 9 8193 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 8193 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 8193 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_8705 : Piece 9 8705 := pieceLeaf 9 8705 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 8705 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 8705 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_8193 : Piece 10 8193 := pieceJoin 9 8193 p_9_8193 p_9_8705 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_9217 : Piece 9 9217 := pieceLeaf 9 9217 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 9217 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 9217 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_9729 : Piece 9 9729 := pieceLeaf 9 9729 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 9729 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 9729 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_9217 : Piece 10 9217 := pieceJoin 9 9217 p_9_9217 p_9_9729 ⟨_, rfl⟩

noncomputable def p_11_8193 : Piece 11 8193 := pieceJoin 10 8193 p_10_8193 p_10_9217 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_10241 : Piece 9 10241 := pieceLeaf 9 10241 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 10241 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 10241 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_10753 : Piece 9 10753 := pieceLeaf 9 10753 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 10753 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 10753 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_10241 : Piece 10 10241 := pieceJoin 9 10241 p_9_10241 p_9_10753 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_11265 : Piece 9 11265 := pieceLeaf 9 11265 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 11265 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 11265 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_9_11777 : Piece 9 11777 := pieceLeaf 9 11777 (by decide) (by
  have e : fastColumn 15 3000000 12000 ThetaScalar.signs 9 11777 Prod.mk = fastColumn 15 3000000 12000 ThetaScalar.signs 9 11777 Prod.mk := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_10_11265 : Piece 10 11265 := pieceJoin 9 11265 p_9_11265 p_9_11777 ⟨_, rfl⟩

noncomputable def p_11_10241 : Piece 11 10241 := pieceJoin 10 10241 p_10_10241 p_10_11265 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_12_8193 : Piece 12 8193 := pieceJoin 11 8193 p_11_8193 p_11_10241 (by
  have e : pairDo 15 3000000 12 8193 p_11_8193.data p_11_10241.data = pairDo 15 3000000 12 8193 p_11_8193.data p_11_10241.data := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

noncomputable def p_12_12289 : Piece 12 12289 := pieceZero 12 12289 (by decide)

noncomputable def p_13_8193 : Piece 13 8193 := pieceJoin 12 8193 p_12_8193 p_12_12289 ⟨_, rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def p_14_1 : Piece 14 1 := pieceJoin 13 1 p_13_1 p_13_8193 (by
  have e : pairDo 15 3000000 14 1 p_13_1.data p_13_8193.data = pairDo 15 3000000 14 1 p_13_1.data p_13_8193.data := rfl
  conv at e => lhs; reduce
  exact ⟨_, e⟩)

end ThetaKernel

namespace ThetaKernel
open FR7022Rational
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def lowInverse : {v:ℤ // v=inv p_14_1.data.1 (15*3000000) (((15*3000000:ℕ)-1).log2+1)} := by
  have e : inv p_14_1.data.1 (15*3000000) (((15*3000000:ℕ)-1).log2+1)=inv p_14_1.data.1 (15*3000000) (((15*3000000:ℕ)-1).log2+1) := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def lowRaw : {v:ℤ // v=fastRaw 15 3000000 p_14_1.data} := by
  have e : finishNewton 15 3000000 p_14_1.data lowInverse.1=finishNewton 15 3000000 p_14_1.data lowInverse.1 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e.trans (finishNewton_eq _ _ _ _ lowInverse.2)⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def lowBiased : {v:ℕ // v=biasedRaw 15 3000000 12000 lowRaw.1} := by
  have e : biasedRaw 15 3000000 12000 lowRaw.1=biasedRaw 15 3000000 12000 lowRaw.1 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLIn : ℕ := wLeft 21 lowBiased.1
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLIn : ℕ := wLeft 20 spAllLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLLIn : ℕ := wLeft 19 spAllLLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLLLIn : ℕ := wLeft 18 spAllLLLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLLL : WidePiece 18 spAllLLLLIn := by
  have e : chunkSpread 15 64 13 18 spAllLLLLIn=chunkSpread 15 64 13 18 spAllLLLLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLLRIn : ℕ := wRight 18 spAllLLLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLLR : WidePiece 18 spAllLLLRIn := by
  have e : chunkSpread 15 64 13 18 spAllLLLRIn=chunkSpread 15 64 13 18 spAllLLLRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLL : WidePiece 19 spAllLLLIn :=
  wideJoin 18 spAllLLLIn (by decide) spAllLLLL spAllLLLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLRIn : ℕ := wRight 19 spAllLLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLRLIn : ℕ := wLeft 18 spAllLLRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLRL : WidePiece 18 spAllLLRLIn := by
  have e : chunkSpread 15 64 13 18 spAllLLRLIn=chunkSpread 15 64 13 18 spAllLLRLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLRRIn : ℕ := wRight 18 spAllLLRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLRR : WidePiece 18 spAllLLRRIn := by
  have e : chunkSpread 15 64 13 18 spAllLLRRIn=chunkSpread 15 64 13 18 spAllLLRRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLLR : WidePiece 19 spAllLLRIn :=
  wideJoin 18 spAllLLRIn (by decide) spAllLLRL spAllLLRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLL : WidePiece 20 spAllLLIn :=
  wideJoin 19 spAllLLIn (by decide) spAllLLL spAllLLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRIn : ℕ := wRight 20 spAllLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRLIn : ℕ := wLeft 19 spAllLRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRLLIn : ℕ := wLeft 18 spAllLRLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRLL : WidePiece 18 spAllLRLLIn := by
  have e : chunkSpread 15 64 13 18 spAllLRLLIn=chunkSpread 15 64 13 18 spAllLRLLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRLRIn : ℕ := wRight 18 spAllLRLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRLR : WidePiece 18 spAllLRLRIn := by
  have e : chunkSpread 15 64 13 18 spAllLRLRIn=chunkSpread 15 64 13 18 spAllLRLRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRL : WidePiece 19 spAllLRLIn :=
  wideJoin 18 spAllLRLIn (by decide) spAllLRLL spAllLRLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRRIn : ℕ := wRight 19 spAllLRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRRLIn : ℕ := wLeft 18 spAllLRRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRRL : WidePiece 18 spAllLRRLIn := by
  have e : chunkSpread 15 64 13 18 spAllLRRLIn=chunkSpread 15 64 13 18 spAllLRRLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRRRIn : ℕ := wRight 18 spAllLRRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRRR : WidePiece 18 spAllLRRRIn := by
  have e : chunkSpread 15 64 13 18 spAllLRRRIn=chunkSpread 15 64 13 18 spAllLRRRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLRR : WidePiece 19 spAllLRRIn :=
  wideJoin 18 spAllLRRIn (by decide) spAllLRRL spAllLRRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllLR : WidePiece 20 spAllLRIn :=
  wideJoin 19 spAllLRIn (by decide) spAllLRL spAllLRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllL : WidePiece 21 spAllLIn :=
  wideJoin 20 spAllLIn (by decide) spAllLL spAllLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRIn : ℕ := wRight 21 lowBiased.1
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLIn : ℕ := wLeft 20 spAllRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLLIn : ℕ := wLeft 19 spAllRLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLLLIn : ℕ := wLeft 18 spAllRLLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLLL : WidePiece 18 spAllRLLLIn := by
  have e : chunkSpread 15 64 13 18 spAllRLLLIn=chunkSpread 15 64 13 18 spAllRLLLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLLRIn : ℕ := wRight 18 spAllRLLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLLR : WidePiece 18 spAllRLLRIn := by
  have e : chunkSpread 15 64 13 18 spAllRLLRIn=chunkSpread 15 64 13 18 spAllRLLRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLL : WidePiece 19 spAllRLLIn :=
  wideJoin 18 spAllRLLIn (by decide) spAllRLLL spAllRLLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLRIn : ℕ := wRight 19 spAllRLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLRLIn : ℕ := wLeft 18 spAllRLRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLRL : WidePiece 18 spAllRLRLIn := by
  have e : chunkSpread 15 64 13 18 spAllRLRLIn=chunkSpread 15 64 13 18 spAllRLRLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLRRIn : ℕ := wRight 18 spAllRLRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLRR : WidePiece 18 spAllRLRRIn := by
  have e : chunkSpread 15 64 13 18 spAllRLRRIn=chunkSpread 15 64 13 18 spAllRLRRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRLR : WidePiece 19 spAllRLRIn :=
  wideJoin 18 spAllRLRIn (by decide) spAllRLRL spAllRLRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRL : WidePiece 20 spAllRLIn :=
  wideJoin 19 spAllRLIn (by decide) spAllRLL spAllRLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRIn : ℕ := wRight 20 spAllRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRLIn : ℕ := wLeft 19 spAllRRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRLLIn : ℕ := wLeft 18 spAllRRLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRLL : WidePiece 18 spAllRRLLIn := by
  have e : chunkSpread 15 64 13 18 spAllRRLLIn=chunkSpread 15 64 13 18 spAllRRLLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRLRIn : ℕ := wRight 18 spAllRRLIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRLR : WidePiece 18 spAllRRLRIn := by
  have e : chunkSpread 15 64 13 18 spAllRRLRIn=chunkSpread 15 64 13 18 spAllRRLRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRL : WidePiece 19 spAllRRLIn :=
  wideJoin 18 spAllRRLIn (by decide) spAllRRLL spAllRRLR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRRIn : ℕ := wRight 19 spAllRRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRRLIn : ℕ := wLeft 18 spAllRRRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRRL : WidePiece 18 spAllRRRLIn := by
  have e : chunkSpread 15 64 13 18 spAllRRRLIn=chunkSpread 15 64 13 18 spAllRRRLIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRRRIn : ℕ := wRight 18 spAllRRRIn
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRRR : WidePiece 18 spAllRRRRIn := by
  have e : chunkSpread 15 64 13 18 spAllRRRRIn=chunkSpread 15 64 13 18 spAllRRRRIn := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRRR : WidePiece 19 spAllRRRIn :=
  wideJoin 18 spAllRRRIn (by decide) spAllRRRL spAllRRRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllRR : WidePiece 20 spAllRRIn :=
  wideJoin 19 spAllRRIn (by decide) spAllRRL spAllRRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAllR : WidePiece 21 spAllRIn :=
  wideJoin 20 spAllRIn (by decide) spAllRL spAllRR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def spAll : WidePiece 22 lowBiased.1 :=
  wideJoin 21 lowBiased.1 (by decide) spAllL spAllR
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def lowSigned : {v:ℤ // v=widen 15 64 3000000 22 12000 lowRaw.1} := by
  have e : (spAll.val:ℤ)-12000*ones 64 3000000=(spAll.val:ℤ)-12000*ones 64 3000000 := rfl
  conv at e => lhs; reduce
  exact ⟨_,e.trans (finishWide lowBiased.2 spAll)⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lowSigned_spec : lowSigned.1=divisorEval 64 3000000 12000 ThetaScalar.signs :=
  pinnedLow_spec p_14_1 _ _ lowRaw.2 lowSigned.2
end ThetaKernel

namespace ThetaKernel
open Finset FR7022Lane GoldbachCoefficientPrefix

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
def trueBase (k : ℕ) := ThetaScalar.base 20000 12000 ThetaScalar.signs k

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem join_base (lo hi : ℤ)
    (hl : lo=divisorEval 64 3000000 12000 ThetaScalar.signs)
    (hh : hi=∑ d∈Ioc 0 (3000000/(12000+1)),∑ k∈Ioc 12000 (min 20000 (3000000/d)),
      trueBase k*(2^64:ℤ)^(d*k-1)) :
    eval (2^64:ℤ) 3000000 (fun i=> divisorWeight (Icc 1 20000) trueBase (i+1)) =
      8000*lo+hi := by
  calc
    _ = divisorEval 64 3000000 20000 trueBase := (divisorEval_eq _ _ _ _).symm
    _ = _ := word_split 64 3000000 20000 12000 (by decide) trueBase
    _ = 8000*lo+hi := congrArg₂ (·+·) ((low_scaled 12000 3000000 le_rfl).trans (congrArg (8000*·) hl.symm)) hh.symm

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem join_extra (hi : ℤ)
    (hh : hi=∑ d∈Ioc 0 (3000000/(12000+1)),∑ k∈Ioc 12000 (min 20000 (3000000/d)),
      (2^64:ℤ)^(d*k-1)) :
    eval (2^64:ℤ) 3000000 (fun i=>divisorWeight (Icc 1 20000) (ThetaScalar.bump 12000) (i+1))=hi := by
  have split := word_split 64 3000000 20000 12000 (by decide) (ThetaScalar.bump 12000)
  refine (divisorEval_eq 64 3000000 20000 (ThetaScalar.bump 12000)).symm.trans (split.trans (?_ : _=hi))
  rw [hh,eval_fibers]
  have hzero : (∑ k∈Icc 1 12000,ThetaScalar.bump 12000 k * leafSum ((2:ℤ)^64) 3000000 k)=0 := by
    apply sum_eq_zero
    intro k hk
    simp [ThetaScalar.bump,not_lt.mpr (mem_Icc.mp hk).2]
  rw [hzero,zero_add]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro k hk
  simp [ThetaScalar.bump,(mem_Ioc.mp hk).1]
end ThetaKernel

namespace ThetaKernelPinned
open Finset FR7022Lane FR7022Verified GoldbachCoefficientPrefix

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def total : {w:ℤ // w=8000*ThetaKernel.lowSigned.1+ThetaWidePinned.base} := by
  have e : 8000*ThetaKernel.lowSigned.1+ThetaWidePinned.base=8000*ThetaKernel.lowSigned.1+ThetaWidePinned.base := rfl
  conv at e => lhs; reduce
  exact ⟨_,e⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def baseWord : ℤ := total.1
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
noncomputable def extraWord : ℤ := ThetaWidePinned.extra

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem baseWord_spec :
    eval A 3000000 (fun i=>divisorWeight (Icc 1 20000) (ThetaScalar.base 20000 12000 ThetaScalar.signs) (i+1))=baseWord :=
  (ThetaKernel.join_base _ _ ThetaKernel.lowSigned_spec ThetaWidePinned.base_spec).trans total.2.symm

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem extraWord_spec :
    eval A 3000000 (fun i=>divisorWeight (Icc 1 20000) (ThetaScalar.bump 12000) (i+1))=extraWord :=
  ThetaKernel.join_extra _ ThetaWidePinned.extra_spec
end ThetaKernelPinned



namespace ThetaScalar
set_option maxHeartbeats 0 in
theorem divSum1 : dsum 20000 12000 1 signs = (4281304145076787,5108089574692989,-79958254650350,-79958081042863,49283394601,49283406745,77821729,8000) := by
  rw [←dfold_eq 1 15 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum2 : dsum 20000 12000 2 signs = (-12549655431424577,2553961459568697,79864359017244,79864410502413,24640978528,24640984502,25945892,4000) := by
  rw [←dfold_eq 2 14 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum3 : dsum 20000 12000 3 signs = (-6461599496754333,1702252098663229,39928483707406,39928525296298,16423538698,16423542743,19451966,2666) := by
  rw [←dfold_eq 3 13 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum5 : dsum 20000 12000 5 signs = (-3701372002774826,1021484599383041,19956430942674,19956457919585,9855528879,9855531301,12977555,1600) := by
  rw [←dfold_eq 5 12 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum6 : dsum 20000 12000 6 signs = (107510711969313498,851042745164313,-38842504418530,-38842492155566,8211050752,8211052748,6482344,1333) := by
  rw [←dfold_eq 6 12 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum7 : dsum 20000 12000 7 signs = (-1678633926969797,729750878133992,13311666230385,13311686079789,7040781439,7040783179,9724220,1143) := by
  rw [←dfold_eq 7 12 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum10 : dsum 20000 12000 10 signs = (71341378971286202,510658994135961,-19232815748819,-19232807816378,4927045810,4927046990,4330430,800) := by
  rw [←dfold_eq 10 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum11 : dsum 20000 12000 11 signs = (2763970798281170,464886960315351,8020900213840,8020913189495,4485217136,4485218245,6497474,728) := by
  rw [←dfold_eq 11 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum13 : dsum 20000 12000 13 signs = (-5051289488310160,392609510669251,6613470959031,6613482063409,3788020366,3788021296,5567846,615) := by
  rw [←dfold_eq 13 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum14 : dsum 20000 12000 14 signs = (58436518343856699,364542147416668,-12705465432933,-12705459616622,3517196343,3517197207,3245526,571) := by
  rw [←dfold_eq 14 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum15 : dsum 20000 12000 15 signs = (44507337324493562,340217179729128,-9522018115428,-9522011625093,3282567998,3282568800,3245310,533) := by
  rw [←dfold_eq 15 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum17 : dsum 20000 12000 17 signs = (-2925841072630086,300819048978535,4970187796631,4970196096519,2902246647,2902247366,4326235,471) := by
  rw [←dfold_eq 17 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum19 : dsum 20000 12000 19 signs = (-6706706552013316,268855556261623,4374954957645,4374962340384,2593904654,2593905290,3890947,421) := by
  rw [←dfold_eq 19 11 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum21 : dsum 20000 12000 21 signs = (36976538635185988,243250258152099,-6270287509211,-6270282756894,2346926867,2346927449,2427134,381) := by
  rw [←dfold_eq 21 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum22 : dsum 20000 12000 22 signs = (45845555308791067,232360046833220,-7508183624204,-7508179824920,2241888858,2241889401,2169916,364) := by
  rw [←dfold_eq 22 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum23 : dsum 20000 12000 23 signs = (-8518207765655292,222264765764393,3549880267598,3549886439462,2144367612,2144368141,3248290,348) := by
  rw [←dfold_eq 23 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum26 : dsum 20000 12000 26 signs = (41052793597576918,196637990026424,-6224010233074,-6224006992295,1897204101,1897204555,1858154,308) := by
  rw [←dfold_eq 26 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum29 : dsum 20000 12000 29 signs = (1932506931917724,176313457490700,2872676444241,2872681228624,1701002998,1701003420,2592322,276) := by
  rw [←dfold_eq 29 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum30 : dsum 20000 12000 30 signs = (-209952459272046372,169775402380080,7694687568760,7694689462827,1638090495,1638090887,1080960,266) := by
  rw [←dfold_eq 30 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum31 : dsum 20000 12000 31 signs = (-3144022741763577,164615865807615,2632670973521,2632675415515,1588354973,1588355368,2430413,258) := by
  rw [←dfold_eq 31 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum33 : dsum 20000 12000 33 signs = (32512467738811472,155128857376688,-3655230783963,-3655227669550,1496721849,1496722224,1624435,243) := by
  rw [←dfold_eq 33 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum34 : dsum 20000 12000 34 signs = (37560792745455056,150742967478783,-4594216974578,-4594214550539,1454318988,1454319338,1443296,236) := by
  rw [←dfold_eq 34 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum35 : dsum 20000 12000 35 signs = (25891363170515218,146283599402657,-3057765520727,-3057762438627,1411287955,1411288296,1614295,229) := by
  rw [←dfold_eq 35 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum37 : dsum 20000 12000 37 signs = (975916125754695,137894283207281,2231191152181,2231194907774,1330446470,1330446791,2047981,216) := by
  rw [←dfold_eq 37 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum38 : dsum 20000 12000 38 signs = (33226609998131332,134761152977187,-4083595932251,-4083593800665,1300147431,1300147741,1297628,211) := by
  rw [←dfold_eq 38 10 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum39 : dsum 20000 12000 39 signs = (25347893202629565,130980856858261,-3060338508221,-3060335826215,1263631176,1263631488,1393621,205) := by
  rw [←dfold_eq 39 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum41 : dsum 20000 12000 41 signs = (937941196173010,124591539531886,2008037720353,2008041103387,1201990571,1201990860,1850333,195) := by
  rw [←dfold_eq 41 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum42 : dsum 20000 12000 42 signs = (-164738262546440043,121958420554037,4855376007433,4855377389395,1176657815,1176658109,809382,191) := by
  rw [←dfold_eq 42 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum43 : dsum 20000 12000 43 signs = (525775483951425,118630107684563,1908289496339,1908292607030,1144692429,1144692700,1764709,186) := by
  rw [←dfold_eq 43 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum46 : dsum 20000 12000 46 signs = (29626844079804323,111215802219461,-3313618058073,-3313616263182,1072903394,1072903655,1079012,174) := by
  rw [←dfold_eq 46 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum47 : dsum 20000 12000 47 signs = (-1935266263307528,108519602177823,1718458452008,1718461322480,1047039596,1047039861,1616058,170) := by
  rw [←dfold_eq 47 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum51 : dsum 20000 12000 51 signs = (22782525695513357,100161792733891,-2253003313366,-2253001458966,966456100,966456343,1076452,157) := by
  rw [←dfold_eq 51 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum53 : dsum 20000 12000 53 signs = (-3201672779010837,96382095089192,1506408701702,1506411314643,929937835,929938072,1443334,151) := by
  rw [←dfold_eq 53 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum55 : dsum 20000 12000 55 signs = (21557062222411235,92544131825259,-1772340429599,-1772338464482,892922828,892923048,1091255,145) := by
  rw [←dfold_eq 55 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum57 : dsum 20000 12000 57 signs = (21038659608123312,89451658277563,-1994571983981,-1994570289843,862982652,862982862,969894,140) := by
  rw [←dfold_eq 57 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum58 : dsum 20000 12000 58 signs = (30793779151798417,88240181382321,-2527079767039,-2527078384390,851221358,851221563,868898,138) := by
  rw [←dfold_eq 58 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum59 : dsum 20000 12000 59 signs = (-3035279970722753,86247024571063,1349574592405,1349576944744,832079677,832079871,1304962,135) := by
  rw [←dfold_eq 59 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum61 : dsum 20000 12000 61 signs = (-1014367370766632,83741792318483,1322727088680,1322729417984,807852889,807853088,1262442,131) := by
  rw [←dfold_eq 61 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum62 : dsum 20000 12000 62 signs = (27319952620490514,82391114768101,-2370946792978,-2370945504453,794895120,794895314,813142,129) := by
  rw [←dfold_eq 62 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum65 : dsum 20000 12000 65 signs = (17680043535543638,78588436982262,-1476986801317,-1476985097881,758178082,758178263,933280,123) := by
  rw [←dfold_eq 65 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum66 : dsum 20000 12000 66 signs = (-123605026007537442,77897749137423,2637680109366,2637681007684,751555514,751555697,542708,122) := by
  rw [←dfold_eq 66 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum67 : dsum 20000 12000 67 signs = (-1357182109225416,75909537217160,1197611282298,1197613305038,732463773,732463950,1150166,119) := by
  rw [←dfold_eq 67 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum69 : dsum 20000 12000 69 signs = (16240351398947107,74199537770486,-1638607990402,-1638606471925,715749112,715749291,814638,116) := by
  rw [←dfold_eq 69 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum70 : dsum 20000 12000 70 signs = (-103442092395976556,72808265290979,2193142455509,2193143357652,702447558,702447729,544830,114) := by
  rw [←dfold_eq 70 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum71 : dsum 20000 12000 71 signs = (-4533646114354070,71447689620931,1096848630860,1096850647823,689411204,689411375,1085179,112) := by
  rw [←dfold_eq 71 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum73 : dsum 20000 12000 73 signs = (-5529436367506691,69642475193867,1055349579761,1055351509168,671880475,671880640,1055791,109) := by
  rw [←dfold_eq 73 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum74 : dsum 20000 12000 74 signs = (29671463015794930,68863930819508,-1904797573331,-1904796487499,664505404,664505559,681210,108) := by
  rw [←dfold_eq 74 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum77 : dsum 20000 12000 77 signs = (18279045808164412,66507774880004,-1141411439906,-1141409916433,641567839,641567996,821077,104) := by
  rw [←dfold_eq 77 9 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum78 : dsum 20000 12000 78 signs = (-114186117442909537,65823969555879,2076306011197,2076306788737,635012116,635012269,465438,103) := by
  rw [←dfold_eq 78 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum79 : dsum 20000 12000 79 signs = (-7510267402997257,65161649508259,950363929409,950365735648,628642124,628642279,976545,102) := by
  rw [←dfold_eq 79 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum82 : dsum 20000 12000 82 signs = (29590784481144845,61962228709694,-1684115318320,-1684114335541,597798764,597798905,614978,97) := by
  rw [←dfold_eq 82 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum83 : dsum 20000 12000 83 signs = (-9458791529285230,61378229744134,881286304872,881287983312,592106161,592106302,931326,96) := by
  rw [←dfold_eq 83 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum85 : dsum 20000 12000 85 signs = (17560351157174733,59930572548143,-1063481601312,-1063480439278,578309615,578309767,720905,94) := by
  rw [←dfold_eq 85 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum86 : dsum 20000 12000 86 signs = (29293587039362357,59398169007869,-1591832379240,-1591831491032,573063302,573063440,586170,93) := by
  rw [←dfold_eq 86 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum87 : dsum 20000 12000 87 signs = (18075701762556504,58882494211493,-1234540870881,-1234539869363,567961388,567961527,651749,92) := by
  rw [←dfold_eq 87 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum89 : dsum 20000 12000 89 signs = (-7564519546984808,57562924899821,832808780892,832810268491,555272676,555272813,867691,90) := by
  rw [←dfold_eq 89 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum91 : dsum 20000 12000 91 signs = (14417878093814549,56301520458128,-956200163982,-956198941658,543086864,543086998,697258,88) := by
  rw [←dfold_eq 91 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum93 : dsum 20000 12000 93 signs = (17127132078067213,54761122696573,-1149280777769,-1149279732871,528495440,528495564,610490,86) := by
  rw [←dfold_eq 93 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum94 : dsum 20000 12000 94 signs = (27001045874458540,54342976956902,-1449344824232,-1449344003684,524237341,524237474,536618,85) := by
  rw [←dfold_eq 94 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum95 : dsum 20000 12000 95 signs = (15593273234791455,53604387528206,-944668947459,-944667842068,517215052,517215181,645590,84) := by
  rw [←dfold_eq 95 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum97 : dsum 20000 12000 97 signs = (-6092976798210678,52995618726219,771253389623,771254846229,511300979,511301110,796771,83) := by
  rw [←dfold_eq 97 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum101 : dsum 20000 12000 101 signs = (-7575239820789799,51076656417557,722772200469,722773592415,492786364,492786486,766601,80) := by
  rw [←dfold_eq 101 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum102 : dsum 20000 12000 102 signs = (-98468214539029974,50413937147661,1415588235557,1415588767894,486420284,486420402,357680,79) := by
  rw [←dfold_eq 102 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum103 : dsum 20000 12000 103 signs = (-7548909200820668,49761060340637,706885922041,706887271275,480139276,480139389,751825,78) := by
  rw [←dfold_eq 103 8 (by decide)]
  apply eqVec_spec; decide +kernel

set_option maxHeartbeats 0 in
theorem divSum105 : dsum 20000 12000 105 signs = (-60076995215074485,48483365865193,1002232050985,1002232852388,467819827,467819941,408460,76) := by
  rw [←dfold_eq 105 8 (by decide)]
  apply eqVec_spec; decide +kernel
end ThetaScalar
namespace ThetaScalar
theorem price2 : PriceRow 20000 12000 2 1 6488 94623 signs (-6590) (-6589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (16830959576501364,2554128115124292,-159822613667594,-159822491545276,24642416073,24642422243,51875837,4000)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price4 : PriceRow 20000 12000 4 2 6488 47312 signs (-6590) (-6589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (16830959576501364,2554128115124292,-159822613667594,-159822491545276,24642416073,24642422243,51875837,4000)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price6 : PriceRow 20000 12000 6 2 4889 301025 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price8 : PriceRow 20000 12000 8 4 6488 23656 signs (-6590) (-6589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (16830959576501364,2554128115124292,-159822613667594,-159822491545276,24642416073,24642422243,51875837,4000)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price10 : PriceRow 20000 12000 10 4 5422 127307 signs (-44964) (-44963) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (91873710550562392,2043302509877212,-199011860359087,-199011757281239,19713933004,19713937932,43228712,3200)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(10,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum10]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price12 : PriceRow 20000 12000 12 4 4889 150513 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price14 : PriceRow 20000 12000 14 6 5690 75590 signs (-35153) (-35152) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (76946111847327860,2188919384406968,-185839745330912,-185839637241687,21118830977,21118836271,45397143,3428)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(7,-1),(14,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum7,divSum14]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price16 : PriceRow 20000 12000 16 8 6488 11828 signs (-6590) (-6589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (16830959576501364,2554128115124292,-159822613667594,-159822491545276,24642416073,24642422243,51875837,4000)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price18 : PriceRow 20000 12000 18 6 4889 100342 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price20 : PriceRow 20000 12000 20 8 5422 63654 signs (-44964) (-44963) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (91873710550562392,2043302509877212,-199011860359087,-199011757281239,19713933004,19713937932,43228712,3200)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(10,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum10]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price22 : PriceRow 20000 12000 22 10 5956 39992 signs (-25807) (-25806) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (59912544087011261,2321601201642161,-175351697505638,-175351584559691,22399087795,22399093399,47548279,3636)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(11,-1),(22,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum11,divSum22]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price24 : PriceRow 20000 12000 24 8 4889 75257 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price26 : PriceRow 20000 12000 26 12 6034 31807 signs (-26689) (-26688) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (62935042662388442,2358156594481465,-172660094859699,-172659980600980,22751599808,22751605502,48166145,3693)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(13,-1),(26,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum13,divSum26]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price28 : PriceRow 20000 12000 28 12 5690 37795 signs (-35153) (-35152) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (76946111847327860,2188919384406968,-185839745330912,-185839637241687,21118830977,21118836271,45397143,3428)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(7,-1),(14,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum7,divSum14]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price30 : PriceRow 20000 12000 30 8 4144 233099 signs (-337831) (-337830) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (460305818613170157,1362534933727344,-294999554169211,-294999475821023,13145922561,13145925850,32423440,2134)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(5,-1),(6,1),(10,1),(15,1),(30,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum5,divSum6,divSum10,divSum15,divSum30]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price32 : PriceRow 20000 12000 32 16 6488 5914 signs (-6590) (-6589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (16830959576501364,2554128115124292,-159822613667594,-159822491545276,24642416073,24642422243,51875837,4000)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price34 : PriceRow 20000 12000 34 16 6136 22094 signs (-23843) (-23842) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (57317593394586506,2404052033624540,-169387018438803,-169386902192334,23194488414,23194494215,48992898,3765)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(17,-1),(34,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum17,divSum34]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price36 : PriceRow 20000 12000 36 12 4889 50171 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price38 : PriceRow 20000 12000 38 18 6172 19803 signs (-23456) (-23455) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (56764276126646012,2420033711839856,-168281164557490,-168281047686325,23348658850,23348664694,49282518,3790)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(19,-1),(38,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum19,divSum38]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price40 : PriceRow 20000 12000 40 16 5422 31827 signs (-44964) (-44963) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (91873710550562392,2043302509877212,-199011860359087,-199011757281239,19713933004,19713937932,43228712,3200)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(10,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum10]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price42 : PriceRow 20000 12000 42 12 4333 141527 signs (-269111) (-269110) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (392633224495021722,1459001868506114,-275736396973492,-275736314839840,14076612083,14076615616,34045273,2285)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1),(7,-1),(14,1),(21,1),(42,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6,divSum7,divSum14,divSum21,divSum42]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price44 : PriceRow 20000 12000 44 20 5956 19996 signs (-25807) (-25806) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (59912544087011261,2321601201642161,-175351697505638,-175351584559691,22399087795,22399093399,47548279,3636)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(11,-1),(22,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum11,divSum22]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price46 : PriceRow 20000 12000 46 22 6225 15310 signs (-22503) (-22502) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (54976011421960979,2443079151579360,-166686111993265,-166685994247920,23570951855,23570957757,49706559,3826)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(23,-1),(46,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum23,divSum46]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price48 : PriceRow 20000 12000 48 16 4889 37629 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price50 : PriceRow 20000 12000 50 20 5422 25462 signs (-44964) (-44963) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (91873710550562392,2043302509877212,-199011860359087,-199011757281239,19713933004,19713937932,43228712,3200)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(10,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum10]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price52 : PriceRow 20000 12000 52 24 6034 15904 signs (-26689) (-26688) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (62935042662388442,2358156594481465,-172660094859699,-172659980600980,22751599808,22751605502,48166145,3693)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(13,-1),(26,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum13,divSum26]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price53 : PriceRow 20000 12000 53 52 9549 420 signs (-1494) (-1493) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (7482976924087624,5011707479603797,-81464663352052,-81464492357506,48353456766,48353468673,76378395,7849)
  · rw [divide_sum signs (by decide) [(1,1),(53,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum53]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price54 : PriceRow 20000 12000 54 18 4889 33448 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price55 : PriceRow 20000 12000 55 40 7435 7707 signs (-7209) (-7208) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (26775767571981678,3714262146819856,-109707926236463,-109707790616425,35835571414,35835580247,59437955,5817)
  · rw [divide_sum signs (by decide) [(1,1),(5,-1),(11,-1),(55,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum5,divSum11,divSum55]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price56 : PriceRow 20000 12000 56 24 5690 18898 signs (-35153) (-35152) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (76946111847327860,2188919384406968,-185839745330912,-185839637241687,21118830977,21118836271,45397143,3428)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(7,-1),(14,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum7,divSum14]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price57 : PriceRow 20000 12000 57 36 6939 8595 signs (-11930) (-11929) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (38488269801967748,3226433578045700,-126256265299382,-126256138969388,31128933901,31128941574,55448710,5053)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(19,-1),(57,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum19,divSum57]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price58 : PriceRow 20000 12000 58 28 6278 11036 signs (-18529) (-18528) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (45692231796382057,2466054839015913,-165222369878874,-165222251158290,23792634433,23792640386,50152413,3862)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(29,-1),(58,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum29,divSum58]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price59 : PriceRow 20000 12000 59 58 9567 235 signs (-1457) (-1456) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (7316584115799540,5021842550121926,-81307829242755,-81307657987607,48451314924,48451326874,76516767,7865)
  · rw [divide_sum signs (by decide) [(1,1),(59,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum59]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price60 : PriceRow 20000 12000 60 16 4144 116550 signs (-337831) (-337830) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (460305818613170157,1362534933727344,-294999554169211,-294999475821023,13145922561,13145925850,32423440,2134)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(5,-1),(6,1),(10,1),(15,1),(30,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum5,divSum6,divSum10,divSum15,divSum30]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price61 : PriceRow 20000 12000 61 60 9571 294 signs (-1055) (-1054) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (5295671515843419,5024347782374506,-81280981739030,-81280810460847,48475541712,48475553657,76559287,7869)
  · rw [divide_sum signs (by decide) [(1,1),(61,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum61]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price62 : PriceRow 20000 12000 62 30 6292 10266 signs (-19134) (-19133) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (47294934938755455,2471903364084778,-164826231434093,-164826112465244,23848956220,23848962189,50258566,3871)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(31,-1),(62,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum31,divSum62]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price63 : PriceRow 20000 12000 63 36 6394 10885 signs (-16921) (-16920) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (49398076203986905,2919336856047867,-139468692097352,-139468575175844,28166001331,28166008272,51072677,4572)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(7,-1),(21,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum7,divSum21]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price64 : PriceRow 20000 12000 64 32 6488 2958 signs (-6590) (-6589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (16830959576501364,2554128115124292,-159822613667594,-159822491545276,24642416073,24642422243,51875837,4000)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price65 : PriceRow 20000 12000 65 48 7533 6157 signs (-8142) (-8141) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (30714009171705411,3772583901622959,-108005143353372,-108005006123738,36398023438,36398032411,60209608,5908)
  · rw [divide_sum signs (by decide) [(1,1),(5,-1),(13,-1),(65,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum5,divSum13,divSum65]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price66 : PriceRow 20000 12000 66 20 4523 75867 signs (-213232) (-213231) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (330002349299428006,1547622956382510,-260415596524903,-260415510688789,14931766184,14931769931,35660384,2424)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1),(11,-1),(22,1),(33,1),(66,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6,divSum11,divSum22,divSum33,divSum66]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price67 : PriceRow 20000 12000 67 66 9586 383 signs (-1121) (-1120) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (5638486254302203,5032180037475829,-81155865932648,-81155694347901,48550930828,48550942795,76671563,7881)
  · rw [divide_sum signs (by decide) [(1,1),(67,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum67]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price68 : PriceRow 20000 12000 68 32 6136 11047 signs (-23843) (-23842) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (57317593394586506,2404052033624540,-169387018438803,-169386902192334,23194488414,23194494215,48992898,3765)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(17,-1),(34,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum17,divSum34]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price69 : PriceRow 20000 12000 69 44 6999 6693 signs (-10898) (-10897) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (35501462806433519,3257772248035853,-125075226615756,-125075099250548,31431237403,31431245152,55936111,5102)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(23,-1),(69,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum23,divSum69]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price70 : PriceRow 20000 12000 70 24 4783 60595 signs (-160612) (-160611) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (281322318387880662,1751569113271566,-230279899998641,-230279808773929,16899188305,16899192527,37819483,2743)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(7,-1),(10,1),(14,1),(35,1),(70,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum7,divSum10,divSum14,divSum35,divSum70]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price71 : PriceRow 20000 12000 71 70 9594 509 signs (-1751) (-1750) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (8814950259430857,5036641885072058,-81055103281210,-81054931690686,48593983397,48593995370,76736550,7888)
  · rw [divide_sum signs (by decide) [(1,1),(71,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum71]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price72 : PriceRow 20000 12000 72 24 4889 25086 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price73 : PriceRow 20000 12000 73 72 9598 520 signs (-1948) (-1947) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (9810740512583478,5038447099499122,-81013604230111,-81013432552031,48611514126,48611526105,76765938,7891)
  · rw [divide_sum signs (by decide) [(1,1),(73,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum73]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price74 : PriceRow 20000 12000 74 36 6323 7895 signs (-18320) (-18319) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (45526506466541599,2485097762736519,-163958602393106,-163958482940549,23976475007,23976481011,50509066,3892)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(37,-1),(74,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum37,divSum74]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price75 : PriceRow 20000 12000 75 40 6092 11026 signs (-21638) (-21637) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (58951612969099508,2724570056375847,-149365187415858,-149365075883839,26286895022,26286901501,48637518,4267)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(5,-1),(15,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum5,divSum15]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price76 : PriceRow 20000 12000 76 36 6172 9902 signs (-23456) (-23455) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (56764276126646012,2420033711839856,-168281164557490,-168281047686325,23348658850,23348664694,49282518,3790)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(19,-1),(38,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum19,divSum38]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price77 : PriceRow 20000 12000 77 60 7807 4451 signs (-5396) (-5395) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (21475013081929826,3979959511123650,-102432232534481,-102432090228580,38398963865,38398973317,62421112,6233)
  · rw [divide_sum signs (by decide) [(1,1),(7,-1),(11,-1),(77,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum7,divSum11,divSum77]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price78 : PriceRow 20000 12000 78 24 4578 60789 signs (-201286) (-201285) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (316441364773995375,1572104128284931,-256567727505053,-256567640667796,15167730922,15167734726,36124706,2462)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1),(13,-1),(26,1),(39,1),(78,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6,divSum13,divSum26,divSum39,divSum78]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price79 : PriceRow 20000 12000 79 78 9608 545 signs (-2339) (-2338) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (11791571548074044,5042927925184730,-80908618579759,-80908446778511,48654752477,48654764466,76845184,7898)
  · rw [divide_sum signs (by decide) [(1,1),(79,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum79]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price80 : PriceRow 20000 12000 80 32 5422 15914 signs (-44964) (-44963) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (91873710550562392,2043302509877212,-199011860359087,-199011757281239,19713933004,19713937932,43228712,3200)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(10,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum10]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price81 : PriceRow 20000 12000 81 54 7299 1506 signs (-3155) (-3154) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (10742903641831120,3405837476029760,-119886738357756,-119886606339161,32859855903,32859864002,58369763,5334)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price82 : PriceRow 20000 12000 82 40 6339 7094 signs (-18256) (-18255) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (45483802861473199,2491498804302100,-163514766706267,-163514646984204,24038224266,24038230288,50640482,3902)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(41,-1),(82,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum41,divSum82]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price83 : PriceRow 20000 12000 83 82 9614 558 signs (-2723) (-2722) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (13740095674362017,5046711344948855,-80839540955222,-80839369026175,48691288440,48691300443,76890403,7904)
  · rw [divide_sum signs (by decide) [(1,1),(83,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum83]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price84 : PriceRow 20000 12000 84 24 4333 70764 signs (-269111) (-269110) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (392633224495021722,1459001868506114,-275736396973492,-275736314839840,14076612083,14076615616,34045273,2285)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1),(7,-1),(14,1),(21,1),(42,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6,divSum7,divSum14,divSum21,divSum42]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price85 : PriceRow 20000 12000 85 64 7661 3992 signs (-7403) (-7402) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (28468868377656432,3845716498879556,-105948354990967,-105948215498245,37103928690,37103937845,61238844,6023)
  · rw [divide_sum signs (by decide) [(1,1),(5,-1),(17,-1),(85,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum5,divSum17,divSum85]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price86 : PriceRow 20000 12000 86 42 6347 6831 signs (-18277) (-18276) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (45598771131912296,2494896176447598,-163322735543173,-163322615643338,24070786946,24070792983,50697298,3907)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(43,-1),(86,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum43,divSum86]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price87 : PriceRow 20000 12000 87 56 7059 4668 signs (-8177) (-8176) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (26886098472469900,3288406512750553,-123993955672878,-123993827437148,31726814293,31726822109,56429190,5150)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(29,-1),(87,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum29,divSum87]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price88 : PriceRow 20000 12000 88 40 5956 9998 signs (-25807) (-25806) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (59912544087011261,2321601201642161,-175351697505638,-175351584559691,22399087795,22399093399,47548279,3636)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(11,-1),(22,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum11,divSum22]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price89 : PriceRow 20000 12000 89 88 9622 553 signs (-2346) (-2345) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (11845823692061595,5050526649793168,-80791063431242,-80790891311354,48728121925,48728133932,76954038,7910)
  · rw [divide_sum signs (by decide) [(1,1),(89,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum89]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price90 : PriceRow 20000 12000 90 24 4144 77700 signs (-337831) (-337830) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (460305818613170157,1362534933727344,-294999554169211,-294999475821023,13145922561,13145925850,32423440,2134)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(5,-1),(6,1),(10,1),(15,1),(30,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum5,divSum6,divSum10,divSum15,divSum30]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price91 : PriceRow 20000 12000 91 72 7909 3617 signs (-6292) (-6291) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (25429105654171293,4042030706347874,-100839592003748,-100839448127719,38997679660,38997689268,63226921,6330)
  · rw [divide_sum signs (by decide) [(1,1),(7,-1),(13,-1),(91,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum7,divSum13,divSum91]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price92 : PriceRow 20000 12000 92 44 6225 7655 signs (-22503) (-22502) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (54976011421960979,2443079151579360,-166686111993265,-166685994247920,23570951855,23570957757,49706559,3826)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(23,-1),(46,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum23,divSum46]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price93 : PriceRow 20000 12000 93 60 7075 4333 signs (-9410) (-9409) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (31014058461661910,3295982732918718,-123668690109046,-123668561487547,31799996370,31800004198,56549840,5162)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(31,-1),(93,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum31,divSum93]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price94 : PriceRow 20000 12000 94 46 6359 6172 signs (-18308) (-18307) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (45767271714267432,2499951489903371,-162990416943834,-162990296871440,24119613818,24119619856,50796397,3915)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(47,-1),(94,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum47,divSum94]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price95 : PriceRow 20000 12000 95 72 7706 3846 signs (-7823) (-7822) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (30282655934656384,3871353806576531,-105234309498128,-105234169144900,37351176120,37351185335,61598817,6063)
  · rw [divide_sum signs (by decide) [(1,1),(5,-1),(19,-1),(95,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum5,divSum19,divSum95]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price96 : PriceRow 20000 12000 96 32 4889 18815 signs (-76812) (-76811) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (130803271042569195,1702918761625376,-238593601793530,-238593508997140,16429928127,16429932248,38906215,2667)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price97 : PriceRow 20000 12000 97 96 9631 505 signs (-2053) (-2052) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (10374280943287465,5055093955966770,-80729508039973,-80729335889092,48772093622,48772105635,77024958,7917)
  · rw [divide_sum signs (by decide) [(1,1),(97,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum97]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price98 : PriceRow 20000 12000 98 42 5690 10799 signs (-35153) (-35152) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (76946111847327860,2188919384406968,-185839745330912,-185839637241687,21118830977,21118836271,45397143,3428)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(7,-1),(14,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum7,divSum14]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price99 : PriceRow 20000 12000 99 60 6696 5884 signs (-13079) (-13078) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (40491400582361422,3096079373091097,-131562869355559,-131562747198206,29871360616,29871367981,53496724,4849)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(11,-1),(33,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum11,divSum33]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price100 : PriceRow 20000 12000 100 40 5422 12731 signs (-44964) (-44963) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (91873710550562392,2043302509877212,-199011860359087,-199011757281239,19713933004,19713937932,43228712,3200)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(5,-1),(10,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum5,divSum10]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price101 : PriceRow 20000 12000 101 100 9635 592 signs (-2345) (-2344) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (11856543965866586,5057012918275432,-80681026850819,-80680854635278,48790608237,48790620259,77055128,7920)
  · rw [divide_sum signs (by decide) [(1,1),(101,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum101]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price102 : PriceRow 20000 12000 102 32 4651 43018 signs (-182543) (-182542) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (292540645095197668,1602590535711854,-251826598113662,-251826509871058,15462036284,15462040161,36742048,2510)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(3,-1),(6,1),(17,-1),(34,1),(51,1),(102,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum3,divSum6,divSum17,divSum34,divSum51,divSum102]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price103 : PriceRow 20000 12000 103 102 9637 637 signs (-2339) (-2338) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (11830213345897455,5058328514352352,-80665140572391,-80664968314138,48803255325,48803267356,77069904,7922)
  · rw [divide_sum signs (by decide) [(1,1),(103,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum103]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price104 : PriceRow 20000 12000 104 48 6034 7952 signs (-26689) (-26688) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (62935042662388442,2358156594481465,-172660094859699,-172659980600980,22751599808,22751605502,48166145,3693)
  · rw [divide_sum signs (by decide) [(1,1),(2,-1),(13,-1),(26,1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum2,divSum13,divSum26]
    apply eqVec_spec; decide +kernel
  · decide +kernel
theorem price105 : PriceRow 20000 12000 105 48 5355 26410 signs (-78590) (-78589) := by
  apply price_of_values _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (183575143916844996,2335869669931418,-173007138727166,-173007040011537,22536508578,22536514126,42546267,3658)
  · rw [divide_sum signs (by decide) [(1,1),(3,-1),(5,-1),(7,-1),(15,1),(21,1),(35,1),(105,-1)] (by decide +kernel)]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,divSum1,divSum3,divSum5,divSum7,divSum15,divSum21,divSum35,divSum105]
    apply eqVec_spec; decide +kernel
  · decide +kernel
end ThetaScalar

namespace SmallModulusSteps
open FR7022NextRows ThetaScalar
private theorem ready2 : Ready q2 := certified q2 1 6488 94623 (by unfold rateOK; decide +kernel) ThetaScalar.price2 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready4 : Ready q4 := certified q4 2 6488 47312 (by unfold rateOK; decide +kernel) ThetaScalar.price4 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready6 : Ready q6 := certified q6 2 4889 301025 (by unfold rateOK; decide +kernel) ThetaScalar.price6 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready8 : Ready q8 := certified q8 4 6488 23656 (by unfold rateOK; decide +kernel) ThetaScalar.price8 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready10 : Ready q10 := certified q10 4 5422 127307 (by unfold rateOK; decide +kernel) ThetaScalar.price10 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready12 : Ready q12 := certified q12 4 4889 150513 (by unfold rateOK; decide +kernel) ThetaScalar.price12 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready14 : Ready q14 := certified q14 6 5690 75590 (by unfold rateOK; decide +kernel) ThetaScalar.price14 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready16 : Ready q16 := certified q16 8 6488 11828 (by unfold rateOK; decide +kernel) ThetaScalar.price16 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready18 : Ready q18 := certified q18 6 4889 100342 (by unfold rateOK; decide +kernel) ThetaScalar.price18 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready20 : Ready q20 := certified q20 8 5422 63654 (by unfold rateOK; decide +kernel) ThetaScalar.price20 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready22 : Ready q22 := certified q22 10 5956 39992 (by unfold rateOK; decide +kernel) ThetaScalar.price22 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready24 : Ready q24 := certified q24 8 4889 75257 (by unfold rateOK; decide +kernel) ThetaScalar.price24 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready26 : Ready q26 := certified q26 12 6034 31807 (by unfold rateOK; decide +kernel) ThetaScalar.price26 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready28 : Ready q28 := certified q28 12 5690 37795 (by unfold rateOK; decide +kernel) ThetaScalar.price28 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready30 : Ready q30 := certified q30 8 4144 233099 (by unfold rateOK; decide +kernel) ThetaScalar.price30 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready32 : Ready q32 := certified q32 16 6488 5914 (by unfold rateOK; decide +kernel) ThetaScalar.price32 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready34 : Ready q34 := certified q34 16 6136 22094 (by unfold rateOK; decide +kernel) ThetaScalar.price34 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready36 : Ready q36 := certified q36 12 4889 50171 (by unfold rateOK; decide +kernel) ThetaScalar.price36 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready38 : Ready q38 := certified q38 18 6172 19803 (by unfold rateOK; decide +kernel) ThetaScalar.price38 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready40 : Ready q40 := certified q40 16 5422 31827 (by unfold rateOK; decide +kernel) ThetaScalar.price40 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready42 : Ready q42 := certified q42 12 4333 141527 (by unfold rateOK; decide +kernel) ThetaScalar.price42 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready44 : Ready q44 := certified q44 20 5956 19996 (by unfold rateOK; decide +kernel) ThetaScalar.price44 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready46 : Ready q46 := certified q46 22 6225 15310 (by unfold rateOK; decide +kernel) ThetaScalar.price46 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready48 : Ready q48 := certified q48 16 4889 37629 (by unfold rateOK; decide +kernel) ThetaScalar.price48 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready50 : Ready q50 := certified q50 20 5422 25462 (by unfold rateOK; decide +kernel) ThetaScalar.price50 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready52 : Ready q52 := certified q52 24 6034 15904 (by unfold rateOK; decide +kernel) ThetaScalar.price52 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready53 : Ready q53 := certified q53 52 9549 420 (by unfold rateOK; decide +kernel) ThetaScalar.price53 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready54 : Ready q54 := certified q54 18 4889 33448 (by unfold rateOK; decide +kernel) ThetaScalar.price54 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready55 : Ready q55 := certified q55 40 7435 7707 (by unfold rateOK; decide +kernel) ThetaScalar.price55 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready56 : Ready q56 := certified q56 24 5690 18898 (by unfold rateOK; decide +kernel) ThetaScalar.price56 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready57 : Ready q57 := certified q57 36 6939 8595 (by unfold rateOK; decide +kernel) ThetaScalar.price57 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready58 : Ready q58 := certified q58 28 6278 11036 (by unfold rateOK; decide +kernel) ThetaScalar.price58 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready59 : Ready q59 := certified q59 58 9567 235 (by unfold rateOK; decide +kernel) ThetaScalar.price59 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready60 : Ready q60 := certified q60 16 4144 116550 (by unfold rateOK; decide +kernel) ThetaScalar.price60 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready61 : Ready q61 := certified q61 60 9571 294 (by unfold rateOK; decide +kernel) ThetaScalar.price61 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready62 : Ready q62 := certified q62 30 6292 10266 (by unfold rateOK; decide +kernel) ThetaScalar.price62 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready63 : Ready q63 := certified q63 36 6394 10885 (by unfold rateOK; decide +kernel) ThetaScalar.price63 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready64 : Ready q64 := certified q64 32 6488 2958 (by unfold rateOK; decide +kernel) ThetaScalar.price64 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready65 : Ready q65 := certified q65 48 7533 6157 (by unfold rateOK; decide +kernel) ThetaScalar.price65 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready66 : Ready q66 := certified q66 20 4523 75867 (by unfold rateOK; decide +kernel) ThetaScalar.price66 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready67 : Ready q67 := certified q67 66 9586 383 (by unfold rateOK; decide +kernel) ThetaScalar.price67 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready68 : Ready q68 := certified q68 32 6136 11047 (by unfold rateOK; decide +kernel) ThetaScalar.price68 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready69 : Ready q69 := certified q69 44 6999 6693 (by unfold rateOK; decide +kernel) ThetaScalar.price69 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready70 : Ready q70 := certified q70 24 4783 60595 (by unfold rateOK; decide +kernel) ThetaScalar.price70 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready71 : Ready q71 := certified q71 70 9594 509 (by unfold rateOK; decide +kernel) ThetaScalar.price71 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready72 : Ready q72 := certified q72 24 4889 25086 (by unfold rateOK; decide +kernel) ThetaScalar.price72 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready73 : Ready q73 := certified q73 72 9598 520 (by unfold rateOK; decide +kernel) ThetaScalar.price73 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready74 : Ready q74 := certified q74 36 6323 7895 (by unfold rateOK; decide +kernel) ThetaScalar.price74 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready75 : Ready q75 := certified q75 40 6092 11026 (by unfold rateOK; decide +kernel) ThetaScalar.price75 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready76 : Ready q76 := certified q76 36 6172 9902 (by unfold rateOK; decide +kernel) ThetaScalar.price76 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready77 : Ready q77 := certified q77 60 7807 4451 (by unfold rateOK; decide +kernel) ThetaScalar.price77 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready78 : Ready q78 := certified q78 24 4578 60789 (by unfold rateOK; decide +kernel) ThetaScalar.price78 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready79 : Ready q79 := certified q79 78 9608 545 (by unfold rateOK; decide +kernel) ThetaScalar.price79 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready80 : Ready q80 := certified q80 32 5422 15914 (by unfold rateOK; decide +kernel) ThetaScalar.price80 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready81 : Ready q81 := certified q81 54 7299 1506 (by unfold rateOK; decide +kernel) ThetaScalar.price81 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready82 : Ready q82 := certified q82 40 6339 7094 (by unfold rateOK; decide +kernel) ThetaScalar.price82 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready83 : Ready q83 := certified q83 82 9614 558 (by unfold rateOK; decide +kernel) ThetaScalar.price83 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready84 : Ready q84 := certified q84 24 4333 70764 (by unfold rateOK; decide +kernel) ThetaScalar.price84 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready85 : Ready q85 := certified q85 64 7661 3992 (by unfold rateOK; decide +kernel) ThetaScalar.price85 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready86 : Ready q86 := certified q86 42 6347 6831 (by unfold rateOK; decide +kernel) ThetaScalar.price86 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready87 : Ready q87 := certified q87 56 7059 4668 (by unfold rateOK; decide +kernel) ThetaScalar.price87 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready88 : Ready q88 := certified q88 40 5956 9998 (by unfold rateOK; decide +kernel) ThetaScalar.price88 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready89 : Ready q89 := certified q89 88 9622 553 (by unfold rateOK; decide +kernel) ThetaScalar.price89 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready90 : Ready q90 := certified q90 24 4144 77700 (by unfold rateOK; decide +kernel) ThetaScalar.price90 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready91 : Ready q91 := certified q91 72 7909 3617 (by unfold rateOK; decide +kernel) ThetaScalar.price91 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready92 : Ready q92 := certified q92 44 6225 7655 (by unfold rateOK; decide +kernel) ThetaScalar.price92 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready93 : Ready q93 := certified q93 60 7075 4333 (by unfold rateOK; decide +kernel) ThetaScalar.price93 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready94 : Ready q94 := certified q94 46 6359 6172 (by unfold rateOK; decide +kernel) ThetaScalar.price94 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready95 : Ready q95 := certified q95 72 7706 3846 (by unfold rateOK; decide +kernel) ThetaScalar.price95 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready96 : Ready q96 := certified q96 32 4889 18815 (by unfold rateOK; decide +kernel) ThetaScalar.price96 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready97 : Ready q97 := certified q97 96 9631 505 (by unfold rateOK; decide +kernel) ThetaScalar.price97 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready98 : Ready q98 := certified q98 42 5690 10799 (by unfold rateOK; decide +kernel) ThetaScalar.price98 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready99 : Ready q99 := certified q99 60 6696 5884 (by unfold rateOK; decide +kernel) ThetaScalar.price99 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready100 : Ready q100 := certified q100 40 5422 12731 (by unfold rateOK; decide +kernel) ThetaScalar.price100 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready101 : Ready q101 := certified q101 100 9635 592 (by unfold rateOK; decide +kernel) ThetaScalar.price101 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready102 : Ready q102 := certified q102 32 4651 43018 (by unfold rateOK; decide +kernel) ThetaScalar.price102 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready103 : Ready q103 := certified q103 102 9637 637 (by unfold rateOK; decide +kernel) ThetaScalar.price103 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready104 : Ready q104 := certified q104 48 6034 7952 (by unfold rateOK; decide +kernel) ThetaScalar.price104 (by unfold SmallModulusPack.capCheck; decide +kernel)
private theorem ready105 : Ready q105 := certified q105 48 5355 26410 (by unfold rateOK; decide +kernel) ThetaScalar.price105 (by unfold SmallModulusPack.capCheck; decide +kernel)
theorem data_ready : allReady FR7022NextRows.rows := ⟨ready2,ready4,ready6,ready8,ready10,ready12,ready14,ready16,ready18,ready20,ready22,ready24,ready26,ready28,ready30,ready32,ready34,ready36,ready38,ready40,ready42,ready44,ready46,ready48,ready50,ready52,ready53,ready54,ready55,ready56,ready57,ready58,ready59,ready60,ready61,ready62,ready63,ready64,ready65,ready66,ready67,ready68,ready69,ready70,ready71,ready72,ready73,ready74,ready75,ready76,ready77,ready78,ready79,ready80,ready81,ready82,ready83,ready84,ready85,ready86,ready87,ready88,ready89,ready90,ready91,ready92,ready93,ready94,ready95,ready96,ready97,ready98,ready99,ready100,ready101,ready102,ready103,ready104,ready105,True.intro⟩
end SmallModulusSteps

namespace FR7022NextRows

/- Each modulus has its own checked numerical assertion. Elaborate them in order so that the temporary integers can be released between assertions. -/
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_checks : rows.all (check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord)=true := by
  have kernel_q2 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q2 =true := by decide +kernel
  have kernel_q4 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q4 =true := by decide +kernel
  have kernel_q6 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q6 =true := by decide +kernel
  have kernel_q8 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q8 =true := by decide +kernel
  have kernel_q10 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q10 =true := by decide +kernel
  have kernel_q12 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q12 =true := by decide +kernel
  have kernel_q14 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q14 =true := by decide +kernel
  have kernel_q16 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q16 =true := by decide +kernel
  have kernel_q18 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q18 =true := by decide +kernel
  have kernel_q20 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q20 =true := by decide +kernel
  have kernel_q22 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q22 =true := by decide +kernel
  have kernel_q24 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q24 =true := by decide +kernel
  have kernel_q26 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q26 =true := by decide +kernel
  have kernel_q28 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q28 =true := by decide +kernel
  have kernel_q30 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q30 =true := by decide +kernel
  have kernel_q32 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q32 =true := by decide +kernel
  have kernel_q34 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q34 =true := by decide +kernel
  have kernel_q36 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q36 =true := by decide +kernel
  have kernel_q38 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q38 =true := by decide +kernel
  have kernel_q40 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q40 =true := by decide +kernel
  have kernel_q42 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q42 =true := by decide +kernel
  have kernel_q44 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q44 =true := by decide +kernel
  have kernel_q46 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q46 =true := by decide +kernel
  have kernel_q48 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q48 =true := by decide +kernel
  have kernel_q50 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q50 =true := by decide +kernel
  have kernel_q52 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q52 =true := by decide +kernel
  have kernel_q53 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q53 =true := by decide +kernel
  have kernel_q54 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q54 =true := by decide +kernel
  have kernel_q55 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q55 =true := by decide +kernel
  have kernel_q56 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q56 =true := by decide +kernel
  have kernel_q57 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q57 =true := by decide +kernel
  have kernel_q58 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q58 =true := by decide +kernel
  have kernel_q59 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q59 =true := by decide +kernel
  have kernel_q60 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q60 =true := by decide +kernel
  have kernel_q61 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q61 =true := by decide +kernel
  have kernel_q62 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q62 =true := by decide +kernel
  have kernel_q63 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q63 =true := by decide +kernel
  have kernel_q64 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q64 =true := by decide +kernel
  have kernel_q65 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q65 =true := by decide +kernel
  have kernel_q66 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q66 =true := by decide +kernel
  have kernel_q67 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q67 =true := by decide +kernel
  have kernel_q68 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q68 =true := by decide +kernel
  have kernel_q69 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q69 =true := by decide +kernel
  have kernel_q70 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q70 =true := by decide +kernel
  have kernel_q71 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q71 =true := by decide +kernel
  have kernel_q72 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q72 =true := by decide +kernel
  have kernel_q73 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q73 =true := by decide +kernel
  have kernel_q74 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q74 =true := by decide +kernel
  have kernel_q75 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q75 =true := by decide +kernel
  have kernel_q76 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q76 =true := by decide +kernel
  have kernel_q77 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q77 =true := by decide +kernel
  have kernel_q78 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q78 =true := by decide +kernel
  have kernel_q79 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q79 =true := by decide +kernel
  have kernel_q80 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q80 =true := by decide +kernel
  have kernel_q81 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q81 =true := by decide +kernel
  have kernel_q82 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q82 =true := by decide +kernel
  have kernel_q83 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q83 =true := by decide +kernel
  have kernel_q84 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q84 =true := by decide +kernel
  have kernel_q85 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q85 =true := by decide +kernel
  have kernel_q86 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q86 =true := by decide +kernel
  have kernel_q87 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q87 =true := by decide +kernel
  have kernel_q88 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q88 =true := by decide +kernel
  have kernel_q89 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q89 =true := by decide +kernel
  have kernel_q90 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q90 =true := by decide +kernel
  have kernel_q91 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q91 =true := by decide +kernel
  have kernel_q92 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q92 =true := by decide +kernel
  have kernel_q93 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q93 =true := by decide +kernel
  have kernel_q94 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q94 =true := by decide +kernel
  have kernel_q95 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q95 =true := by decide +kernel
  have kernel_q96 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q96 =true := by decide +kernel
  have kernel_q97 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q97 =true := by decide +kernel
  have kernel_q98 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q98 =true := by decide +kernel
  have kernel_q99 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q99 =true := by decide +kernel
  have kernel_q100 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q100 =true := by decide +kernel
  have kernel_q101 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q101 =true := by decide +kernel
  have kernel_q102 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q102 =true := by decide +kernel
  have kernel_q103 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q103 =true := by decide +kernel
  have kernel_q104 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q104 =true := by decide +kernel
  have kernel_q105 : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord q105 =true := by decide +kernel
  simp only [rows,List.all_cons,List.all_nil,Bool.true_and,kernel_q2,kernel_q4,kernel_q6,kernel_q8,kernel_q10,kernel_q12,kernel_q14,kernel_q16,kernel_q18,kernel_q20,kernel_q22,kernel_q24,kernel_q26,kernel_q28,kernel_q30,kernel_q32,kernel_q34,kernel_q36,kernel_q38,kernel_q40,kernel_q42,kernel_q44,kernel_q46,kernel_q48,kernel_q50,kernel_q52,kernel_q53,kernel_q54,kernel_q55,kernel_q56,kernel_q57,kernel_q58,kernel_q59,kernel_q60,kernel_q61,kernel_q62,kernel_q63,kernel_q64,kernel_q65,kernel_q66,kernel_q67,kernel_q68,kernel_q69,kernel_q70,kernel_q71,kernel_q72,kernel_q73,kernel_q74,kernel_q75,kernel_q76,kernel_q77,kernel_q78,kernel_q79,kernel_q80,kernel_q81,kernel_q82,kernel_q83,kernel_q84,kernel_q85,kernel_q86,kernel_q87,kernel_q88,kernel_q89,kernel_q90,kernel_q91,kernel_q92,kernel_q93,kernel_q94,kernel_q95,kernel_q96,kernel_q97,kernel_q98,kernel_q99,kernel_q100,kernel_q101,kernel_q102,kernel_q103,kernel_q104,kernel_q105]
set_option maxHeartbeats 0 in
theorem row_checked (r : Row) (hr : r∈rows) : check 3000000 8000000 ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord r=true :=
  (List.all_eq_true.mp all_checks) r hr
end FR7022NextRows

theorem PEqualNP.Outside.L_goldbach_fixed_ap_theta_half_budget : ∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), (if k.Prime then ArithmeticFunction.vonMangoldt k else 0)) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/200 :=
  SmallModulusSteps.theta_certificate ThetaKernelPinned.baseWord ThetaKernelPinned.extraWord
    ThetaKernelPinned.baseWord_spec ThetaKernelPinned.extraWord_spec
    SmallModulusSteps.data_ready FR7022NextRows.row_checked
