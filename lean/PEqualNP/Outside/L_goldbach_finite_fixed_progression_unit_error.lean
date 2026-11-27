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
  have extfun (B : ℤ) (m : ℕ) (f g : ℕ → ℤ) (h : ∀ i<m, f i = g i) : eval B m f = eval B m g := by
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
namespace FR7022Steps
open Finset Real
end FR7022Steps
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
private theorem log_budget (n : ℕ) (hn : 10^16≤n) : Real.log (n:ℝ) ≤ (n:ℝ)/2500 := by
  have h0 := Nat.cast_nonneg (α:=ℝ) n
  have hs : (5000:ℝ) ≤ Real.sqrt n := by
    apply (Real.le_sqrt (by norm_num) h0).mpr
    exact_mod_cast (le_trans (by decide : (5000:ℕ)^2 ≤ 10^16) hn)
  have hlog := Real.log_le_rpow_div (ε:=1/2) h0 (by norm_num)
  rw [←Real.sqrt_eq_rpow] at hlog
  nlinarith only [hlog,Real.sq_sqrt h0,mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n:ℝ))]
theorem reduce_all (n : ℕ) (hn : 10^16≤n)
    (input : ∀ q a : ℕ, 1≤q → q≤105 → (Even q ∨ 51<q) → a.Coprime q →
        |psi q a n - (n:ℝ)/q.totient| ≤ (96/10000:ℝ)*n) :
    ∀ q a : ℕ, 1≤q → q≤105 → a.Coprime q →
      |psi q a n - (n:ℝ)/q.totient| ≤ (n:ℝ)/100 := by
  intro q a hq hQ ha
  by_cases active : Even q ∨ 51<q
  · have h := input q a hq hQ active ha
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have ho : Odd q := (Nat.even_or_odd q).resolve_left (fun he => active (Or.inl he))
  have small : q≤51 := by exact le_of_not_gt (fun hl => active (Or.inr hl))
  have liftBound := input (2*q) (oddLift q a) (by omega) (by omega)
    (Or.inl ⟨q,by omega⟩) (lift_data ho ha).2.2
  rw [Nat.totient_two_mul_of_odd ho] at liftBound
  have near := odd_lift_error q a n ho ha (by omega)
  have triangle := abs_sub_le (psi q a n) (psi (2*q) (oddLift q a) n) ((n:ℝ)/q.totient)
  linarith only [triangle,near,log_budget n hn,liftBound]
end FR7022OddModuli
namespace FR7022TwoStageBridge
open Finset Real ArithmeticFunction
structure Row (q N last : ℕ) (C ε : ℝ) where
  support : Finset ℕ
  A : ArithmeticFunction ℝ
  support_spec : ∀ k ∉ support, A k = 0
  support_bounds : ∀ k ∈ support, 0 < k ∧ k ≤ N
  units : ∀ k ∈ support, k.Coprime q
  zero_slope : ∑ k ∈ support, A k/k = 0
  jumps : Finset ℕ
  w : ℕ → ℝ
  nonneg : ∀ t ∈ jumps, 0 ≤ w t
  jump_bounds : ∀ t ∈ jumps, 0 < t ∧ t ≤ last
  envelope : ∀ r u : ℕ, 0 < u → r.Coprime q →
    |FR7022ProgressionTail.G support A q r u - (if r % q=1 % q then (1:ℝ) else 0)| ≤
      ∑ t ∈ jumps, if t ≤ u then w t else 0
  budget : C*(∑ t ∈ jumps, w t/t) +
    |-(∑ k ∈ support, A k * Real.log k / k)/(q:ℝ) - 1/(q.totient:ℝ)| +
    91*(∑ k ∈ support, |A k|)/N ≤ ε
theorem Row.bound {q N last : ℕ} {C ε : ℝ} (row : Row q N last C ε)
    (hC : 0≤C) (hN : 0<N) (n a : ℕ) (hq : 0<q) (ha : a.Coprime q)
    (hn : N≤n) (hu : (n:ℝ) < exp (exp (19/5)))
    (hy : ∀ t ∈ row.jumps, Chebyshev.psi (n/t : ℕ) ≤ C*(↑(n/t):ℝ)) :
    |FR7022OddModuli.psi q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)*ε :=
  FR7022Dirichlet.bound_of_steps C ε hC N hN n q a hq ha hn hu
    row.support row.A row.support_spec row.support_bounds row.units row.zero_slope
    row.jumps row.w row.nonneg (fun t ht => (row.jump_bounds t ht).1) hy row.envelope row.budget
theorem base_psi (x : ℝ) (hx : 360000 ≤ x) : Chebyshev.psi x ≤ (31/20)*x := by
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
  have hl : Real.log x = 2*Real.log (√x) := by simpa [sq] using (Real.log_pow (√x) 2)
  have hl' : Real.log x ≤ (20/600)*√x := by linarith
  have h4 : Real.log 4 ≤ 7/5 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hpsi := Chebyshev.psi_le (show 1 ≤ x by linarith)
  have a := mul_le_mul_of_nonneg_left hl' hs0.le
  have b := mul_le_mul_of_nonneg_right h4 hx0.le
  nlinarith only [hpsi,a,b,sq,hx0]
theorem first_cutoff {n t : ℕ} (hn : 10^10 ≤ n) (ht : 0<t) (hmax : t≤24576) :
    360000 ≤ n/t := (Nat.le_div_iff_mul_le ht).mpr (by omega)
theorem second_cutoff {n t : ℕ} (hn : 10^16 ≤ n) (ht : 0<t) (hmax : t≤368640) :
    10^10 ≤ n/t := (Nat.le_div_iff_mul_le ht).mpr (by omega)
theorem ordinary_of_first (first : Row 1 (10^10) 24576 (31/20) (1/25)) (n : ℕ)
    (hn : 10^10≤n) (hu : (n:ℝ)<exp (exp (19/5))) :
    Chebyshev.psi n ≤ (26/25)*(n:ℝ) := by
  have z := first.bound (by norm_num) (by decide) n 0 (by decide) (by decide) hn hu
    (fun t ht => base_psi _ (by exact_mod_cast (first_cutoff hn (first.jump_bounds t ht).1 (first.jump_bounds t ht).2)))
  have same : FR7022OddModuli.psi 1 0 n = Chebyshev.psi n := by
    simp [FR7022OddModuli.psi,Chebyshev.psi_eq_sum_Icc,Nat.range_succ_eq_Icc_zero,Nat.mod_one]
  rw [same,Nat.totient_one, Nat.cast_one,div_one,abs_le] at z
  linarith [z.2]
theorem frozen_of_two_stages (first : Row 1 (10^10) 24576 (31/20) (1/25))
    (second : ∀ q : ℕ, 1≤q → q≤105 → Even q ∨ 51<q →
      Row q (10^16) 368640 (26/25) (96/10000)) :
    ∀ q a n : ℕ, 1≤q → q≤105 → a.Coprime q → 10^16≤n →
      (n:ℝ)<exp (exp (19/5)) →
      |(∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), vonMangoldt k) -
       (n:ℝ)/q.totient| ≤ (n:ℝ)/100 := by
  intro q a n hq hQ ha hn hu
  apply FR7022OddModuli.reduce_all n hn _ q a hq hQ ha
  intro m r hm hM active hr
  let row := second m hm hM active
  have e := row.bound (by norm_num) (by decide) n r (by omega) hr hn hu (fun t ht =>
    ordinary_of_first first (n/t) (second_cutoff hn (row.jump_bounds t ht).1
      (row.jump_bounds t ht).2)
      (lt_of_le_of_lt (by exact_mod_cast Nat.div_le_self n t) hu))
  simpa only [mul_comm] using e
end FR7022TwoStageBridge
namespace FR7022ProgressionTail
open Finset
noncomputable def affineCoeff (base extra : ℕ → ℤ) (d alpha : ℝ) (k : ℕ) : ℝ :=
  (base k + alpha * extra k) / d
def endpointWeight (base extra : ℕ → ℤ) (u v : ℤ) (k : ℕ) : ℤ :=
  v * base k + u * extra k
theorem affine_G_mono (S : Finset ℕ) (base extra : ℕ → ℤ) (d a b : ℝ)
    (hd : 0 < d) (he : ∀ k ∈ S, 0 ≤ extra k) (hab : a ≤ b) (q h t : ℕ) :
    G S (affineCoeff base extra d a) q h t ≤ G S (affineCoeff base extra d b) q h t := by
  unfold G
  apply sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ hd.le
  exact add_le_add_right (mul_le_mul_of_nonneg_right hab (by exact_mod_cast he k hk)) _
private theorem sum_real_div (S : Finset ℕ) (f : ℕ → ℝ) (d : ℝ) :
    (∑ k ∈ S, f k) / d = ∑ k ∈ S, f k / d := by
  simp only [div_eq_mul_inv, sum_mul]
theorem G_endpoint_scaled (S : Finset ℕ) (base extra : ℕ → ℤ) (d : ℝ) (u v : ℤ)
    (hv : 0 < v) (q h t : ℕ) :
    G S (affineCoeff base extra d ((u:ℝ)/v)) q h t =
    G S (fun k => ((endpointWeight base extra u v k:ℤ):ℝ)) q h t / (d*v) := by
  have hv' : (v:ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  unfold G
  rw [sum_real_div]
  apply sum_congr rfl
  intro k _
  unfold affineCoeff endpointWeight
  push_cast
  by_cases hd : d=0
  · simp [hd]
  · field_simp
theorem affine_G_from_prefixes (S : Finset ℕ) (base extra : ℕ → ℤ)
    (d alpha L U : ℝ) (ul vl uu vu Plo Phi : ℤ)
    (hqlo : 0 < vl) (hqup : 0 < vu) (hd : 0 < d)
    (he : ∀ k ∈ S, 0 ≤ extra k)
    (hal : (ul:ℝ)/vl ≤ alpha) (hau : alpha ≤ (uu:ℝ)/vu)
    (q h t : ℕ)
    (hPlo : G S (fun k => ((endpointWeight base extra ul vl k:ℤ):ℝ)) q h t = Plo)
    (hPhi : G S (fun k => ((endpointWeight base extra uu vu k:ℤ):ℝ)) q h t = Phi)
    (hlo : L * (d*vl) ≤ Plo) (hhi : (Phi:ℝ) ≤ U * (d*vu)) :
    L ≤ G S (affineCoeff base extra d alpha) q h t ∧
      G S (affineCoeff base extra d alpha) q h t ≤ U := by
  have vlpos : (0:ℝ) < vl := by exact_mod_cast hqlo
  have vupos : (0:ℝ) < vu := by exact_mod_cast hqup
  have left := affine_G_mono S base extra d _ _ hd he hal q h t
  have right := affine_G_mono S base extra d _ _ hd he hau q h t
  rw [G_endpoint_scaled S base extra d ul vl hqlo, hPlo] at left
  rw [G_endpoint_scaled S base extra d uu vu hqup, hPhi] at right
  exact ⟨((le_div_iff₀ (mul_pos hd vlpos)).mpr hlo).trans left,
    right.trans ((div_le_iff₀ (mul_pos hd vupos)).mpr hhi)⟩
noncomputable def harmonicCoeff (S : Finset ℕ) (w : ℕ → ℤ) : ℝ :=
  ∑ k ∈ S, (w k:ℝ)/k
theorem affine_cancel_iff (S : Finset ℕ) (base extra : ℕ → ℤ) (d alpha : ℝ)
    (hd : d ≠ 0) (hw : harmonicCoeff S extra ≠ 0) :
    (∑ k ∈ S, affineCoeff base extra d alpha k / k) = 0 ↔
      alpha = -harmonicCoeff S base / harmonicCoeff S extra := by
  have hsum : (∑ k ∈ S, affineCoeff base extra d alpha k / k) =
      (harmonicCoeff S base + alpha * harmonicCoeff S extra) / d := by
    unfold harmonicCoeff
    rw [mul_sum, ←sum_add_distrib, sum_real_div]
    apply sum_congr rfl
    intro k _
    unfold affineCoeff
    ring
  rw [hsum, div_eq_zero_iff]
  constructor
  · intro ha
    have hs : harmonicCoeff S base + alpha * harmonicCoeff S extra = 0 := ha.resolve_right hd
    exact (eq_div_iff hw).mpr (by linarith)
  · intro ha
    exact Or.inl (by linarith [(eq_div_iff hw).mp ha])
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
def harmonicInteger (S : Finset ℕ) (w : ℕ → ℤ) (B : ℕ) : ℤ :=
  ∑ k ∈ S, w k * ((B/k:ℕ):ℤ)
theorem harmonic_as_integer (S : Finset ℕ) (w : ℕ → ℤ) (B : ℕ) (hB : 0 < B)
    (hk : ∀ k ∈ S, 0 < k ∧ k ∣ B) :
    harmonicCoeff S w = (harmonicInteger S w B:ℝ) / B := by
  have hBp : (B:ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  unfold harmonicCoeff harmonicInteger
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [sum_real_div]
  apply sum_congr rfl
  intro k hks
  have hs := hk k hks
  have hkp : (k:ℝ) ≠ 0 := by exact_mod_cast hs.1.ne'
  have he : ((B/k:ℕ):ℝ) = (B:ℝ)/k := (eq_div_iff hkp).mpr (by exact_mod_cast Nat.div_mul_cancel hs.2)
  rw [he]
  apply (eq_div_iff hBp).mpr
  ring
theorem affine_cancel_iff_integer_ratio (S : Finset ℕ) (base extra : ℕ → ℤ)
    (B : ℕ) (hB : 0 < B) (hk : ∀ k ∈ S, 0 < k ∧ k ∣ B)
    (d alpha : ℝ) (hd : d ≠ 0) (he : 0 < harmonicInteger S extra B) :
    (∑ k ∈ S, affineCoeff base extra d alpha k / k) = 0 ↔
      alpha = -(harmonicInteger S base B:ℝ) / (harmonicInteger S extra B:ℝ) := by
  have hBp : (B:ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hE : (harmonicInteger S extra B:ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hw : harmonicCoeff S extra ≠ 0 := by
    rw [harmonic_as_integer S extra B hB hk]
    exact div_ne_zero hE hBp
  rw [affine_cancel_iff S base extra d alpha hd hw,
      harmonic_as_integer S base B hB hk, harmonic_as_integer S extra B hB hk]
  have hr : -((harmonicInteger S base B:ℝ) / B) / ((harmonicInteger S extra B:ℝ) / B) =
      -(harmonicInteger S base B:ℝ)/(harmonicInteger S extra B:ℝ) := by field_simp
  rw [hr]
theorem cancellation_bracket_of_integers (S : Finset ℕ) (base extra : ℕ → ℤ)
    (B : ℕ) (hB : 0 < B) (hk : ∀ k ∈ S, 0 < k ∧ k ∣ B)
    (d alpha : ℝ) (hd : d ≠ 0) (he : 0 < harmonicInteger S extra B)
    (hcancel : (∑ k ∈ S, affineCoeff base extra d alpha k/k) = 0)
    (ul vl uu vu : ℤ) (hlv : 0 < vl) (huv : 0 < vu)
    (hl : ul * harmonicInteger S extra B ≤ -harmonicInteger S base B * vl)
    (hu : -harmonicInteger S base B * vu ≤ uu * harmonicInteger S extra B) :
    (ul:ℝ)/vl ≤ alpha ∧ alpha ≤ (uu:ℝ)/vu := by
  have hE : 0 < (harmonicInteger S extra B:ℝ) := by exact_mod_cast he
  have hvl : (0:ℝ) < vl := by exact_mod_cast hlv
  have hvu : (0:ℝ) < vu := by exact_mod_cast huv
  rw [(affine_cancel_iff_integer_ratio S base extra B hB hk d alpha hd he).mp hcancel]
  exact ⟨(div_le_div_iff₀ hvl hE).mpr (by exact_mod_cast hl),
         (div_le_div_iff₀ hE hvu).mpr (by exact_mod_cast hu)⟩
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
def endpointMass (S : Finset ℕ) (base extra : ℕ → ℤ) (lo hi v : ℤ) : ℤ :=
  ∑ k ∈ S, max |endpointWeight base extra lo v k| |endpointWeight base extra hi v k|
theorem affine_l1_le_endpointMass (S : Finset ℕ) (base extra : ℕ → ℤ)
    (he : ∀ k ∈ S, 0 ≤ extra k) (d alpha : ℝ) (hd : 0 < d) (lo hi v : ℤ) (hv : 0 < v)
    (hal : (lo:ℝ)/v ≤ alpha) (hau : alpha ≤ (hi:ℝ)/v) :
    (∑ k ∈ S, |affineCoeff base extra d alpha k|) ≤
    (endpointMass S base extra lo hi v:ℝ) / (d*v) := by
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hp := mul_pos hd hv'
  unfold endpointMass
  simp only [Int.cast_sum, Int.cast_max, Int.cast_abs]
  rw [sum_real_div]
  apply sum_le_sum
  intro k hks
  have hek : (0:ℝ) ≤ extra k := by exact_mod_cast he k hks
  have hh (u : ℤ) : affineCoeff base extra d ((u:ℝ)/v) k =
      (endpointWeight base extra u v k:ℝ)/(d*v) := by
    unfold affineCoeff endpointWeight
    push_cast
    field_simp
  have mono (x y : ℝ) (hxy : x ≤ y) :
      affineCoeff base extra d x k ≤ affineCoeff base extra d y k :=
    div_le_div_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right hxy hek) _) hd.le
  have lb := mono _ _ hal
  have ub := mono _ _ hau
  rw [hh lo] at lb
  rw [hh hi] at ub
  let a : ℝ := endpointWeight base extra lo v k
  let b : ℝ := endpointWeight base extra hi v k
  change a/(d*v) ≤ _ at lb
  change _ ≤ b/(d*v) at ub
  change _ ≤ max |a| |b| / (d*v)
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply le_trans _ lb
    apply div_le_div_of_nonneg_right _ hp.le
    exact (neg_le_neg (le_max_left |a| |b|)).trans (neg_abs_le a)
  · apply ub.trans
    exact div_le_div_of_nonneg_right ((le_abs_self b).trans (le_max_right |a| |b|)) hp.le
end FR7022ProgressionTail
namespace FR7022OrdinaryStage
open Finset FR7022ProgressionTail
def positiveBits : ℕ := 0x2088644e26422ca240c0e6440a0c488006a08cc6a22c0cc84a2602480a660c8ec6a284a84082000e24c0480020a4a824648686c6a0c0acc262222642a44468e0200842a8884ec4620824480428c6ca8422ec8880440a48628028042ee66e040a860042c806e0620cc88400e8e42422468840ce0460c442
def negativeBits : ℕ := 0xc668200888cc244aa2400aa6000846ce04a60284c422206a480e82480886220080c6242ac68ee40880ea6c6ca48424a0a280820440a40248c4888844aa2820ccee42c0646a0228864c0a62a02080462c800246e22a4868842c2e8c00800aac46864a824a00e0c80066ae20208c2cc28208e20e08a28ac
def coefficientSign (k : ℕ) : ℤ :=
  if positiveBits.testBit k then 1 else if negativeBits.testBit k then -1 else 0
def support : Finset ℕ := (Icc 1 950).filter fun k => k.Coprime 1
def baseCoeff (k : ℕ) : ℤ := coefficientSign k * (if k ≤ 350 then 600 else ((950-k:ℕ):ℤ))
def extraCoeff (k : ℕ) : ℤ := if 350 < k then 1 else 0
def commonMultiple : ℕ := 0xac32c9e17a813c927e3ee822b7e7003eb4365faa68b8a96c459cefeeed30648b39ada3e9a9b4e43dec655d72af0cde7940e72a70eb6aeb26a610678a7a5890d5edac5af3c3c6d21ff6e84a44d43971b85cdf0519df5e30bd724ccf01cdb3e37e37e3c707a4f941323265c49d54bd0cbfbc6e36022c8d47b9f653377aeedbd92355eda7dd29395d7a07db9d568f5bd245fd032dc7c35c6c5c2a82034860edee4e35b8b775d3bcc6e91a600
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem supported_divisors : ∀ k ∈ support, 0 < k ∧ k ∣ commonMultiple := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem slope_pos : 0 < harmonicInteger support extraCoeff commonMultiple := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem endpoint_comparisons :
    (-202:ℤ) * harmonicInteger support extraCoeff commonMultiple ≤
        -harmonicInteger support baseCoeff commonMultiple * 1000 ∧
    -harmonicInteger support baseCoeff commonMultiple * 1000 ≤
        (-201:ℤ) * harmonicInteger support extraCoeff commonMultiple := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem endpoint_mass_value : endpointMass support baseCoeff extraCoeff (-202) (-201) 1000 =
      237714451 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
noncomputable def alpha : ℝ :=
  -(harmonicInteger support baseCoeff commonMultiple:ℝ) / (harmonicInteger support extraCoeff commonMultiple:ℝ)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem exact_cancellation : (∑ k ∈ support, affineCoeff baseCoeff extraCoeff 600 alpha k / k)=0 := by
  apply (affine_cancel_iff_integer_ratio support baseCoeff extraCoeff commonMultiple
    (by decide) supported_divisors 600 alpha (by norm_num) slope_pos).mpr
  rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem actual_bracket : (-202:ℝ)/1000 ≤ alpha ∧ alpha ≤ (-201:ℝ)/1000 := by
  simpa using cancellation_bracket_of_integers support baseCoeff extraCoeff commonMultiple
    (by decide) supported_divisors 600 alpha (by norm_num) slope_pos exact_cancellation
    (-202) 1000 (-201) 1000 (by decide) (by decide) endpoint_comparisons.1 endpoint_comparisons.2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem actual_rounding_budget : 91*(∑ k ∈ support, |affineCoeff baseCoeff extraCoeff 600 alpha k|)/
      (10:ℝ)^10 ≤ 3605336/(10:ℝ)^12 := by
  have hm := affine_l1_le_endpointMass support baseCoeff extraCoeff
    (fun k _ => by unfold extraCoeff; split <;> omega) 600 alpha (by norm_num)
    (-202) (-201) 1000 (by decide) actual_bracket.1 actual_bracket.2
  rw [endpoint_mass_value] at hm
  norm_num at hm ⊢
  linarith
end FR7022OrdinaryStage
namespace FR7022SignedLog
open Finset
theorem from_power (k P b : ℕ) (hk : 0 < k)
    (hl : 2^b ≤ k^P) (hu : k^P < 2^(b+1)) :
    (b:ℝ)*6931471803 ≤ (P*10000000000:ℕ)*Real.log k ∧
    (P*10000000000:ℕ)*Real.log k ≤ ((b+1:ℕ):ℝ)*6931471808 := by
  have x : (2:ℝ)^b ≤ (k:ℝ)^P := by exact_mod_cast hl
  have y : (k:ℝ)^P ≤ (2:ℝ)^(b+1) := by exact_mod_cast hu.le
  have l := Real.log_le_log (by positivity : 0<(2:ℝ)^b) x
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have h := Real.log_le_log (by positivity : 0<(k:ℝ)^P) y
  simp only [Real.log_pow, Nat.cast_add,Nat.cast_one] at l h
  have w := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg b)
  have z := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (show (0:ℝ)≤b+1 by positivity)
  push_cast
  constructor <;> linarith only [l,h,w,z]
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
theorem scaled (S : Finset ℕ) (B : ℕ) (C : ℕ → ℝ)
    (cl ch ll lh : ℕ → ℤ) (D W : ℝ)
    (hk : ∀ k ∈ S, 0 < k ∧ k ∣ B)
    (hc : ∀ k ∈ S, (cl k:ℝ) ≤ D*C k ∧ D*C k ≤ ch k)
    (hl : ∀ k ∈ S, (ll k:ℝ) ≤ W*Real.log k ∧ W*Real.log k ≤ lh k)
    (hW : 0 ≤ W) :
    ((∑ k ∈ S, signedLow (cl k) (ll k) (lh k) * ↑(B/k):ℤ):ℝ) ≤
        (D*W*B)*(∑ k ∈ S, C k*Real.log k/k) ∧
    (D*W*B)*(∑ k ∈ S, C k*Real.log k/k) ≤
        ((∑ k ∈ S, signedHigh (ch k) (ll k) (lh k) * ↑(B/k):ℤ):ℝ) := by
  push_cast
  rw [mul_sum]
  have one (k : ℕ) (h : k ∈ S) :
      (signedLow (cl k) (ll k) (lh k):ℝ) * (↑(B/k):ℝ) ≤ (D*W*B)*(C k*Real.log k/k) ∧
      (D*W*B)*(C k*Real.log k/k) ≤ (signedHigh (ch k) (ll k) (lh k):ℝ) * (↑(B/k):ℝ) := by
    have hp : (0:ℝ)<k := by exact_mod_cast (hk k h).1
    have hn : 0 ≤ W*Real.log k := mul_nonneg hW (Real.log_nonneg (by exact_mod_cast (hk k h).1))
    have L := (signed_bounds (cl k) _ _ _ (hl k h)).1
    have U := (signed_bounds (ch k) _ _ _ (hl k h)).2
    have c1 := L.trans (mul_le_mul_of_nonneg_right (hc k h).1 hn)
    have c2 := (mul_le_mul_of_nonneg_right (hc k h).2 hn).trans U
    have eqn : (D*W*B)*(C k*Real.log k/k) = (D*C k)*(W*Real.log k)*(↑(B/k):ℝ) := by
      rw [Nat.cast_div (hk k h).2 hp.ne']
      ring
    rw [eqn]
    exact ⟨mul_le_mul_of_nonneg_right c1 (Nat.cast_nonneg _),mul_le_mul_of_nonneg_right c2 (Nat.cast_nonneg _)⟩
  exact ⟨sum_le_sum (fun k h => (one k h).1),sum_le_sum (fun k h => (one k h).2)⟩
end FR7022SignedLog
namespace FR7022OrdinaryStage
open Finset FR7022ProgressionTail FR7022SignedLog
def logCodes : ℕ := 0x9e449e3e9e389e329e2b9e259e1f9e199e129e0c9e069dff9df99df39ded9de69de09dda9dd39dcd9dc79dc09dba9db39dad9da79da09d9a9d939d8d9d879d809d7a9d739d6d9d669d609d599d539d4d9d469d409d399d339d2c9d259d1f9d189d129d0b9d059cfe9cf89cf19cea9ce49cdd9cd79cd09cc99cc39cbc9cb59caf9ca89ca19c9b9c949c8d9c879c809c799c739c6c9c659c5e9c589c519c4a9c439c3c9c369c2f9c289c219c1a9c149c0d9c069bff9bf89bf19bea9be39bdd9bd69bcf9bc89bc19bba9bb39bac9ba59b9e9b979b909b899b829b7b9b749b6d9b669b5f9b589b519b4a9b439b3c9b359b2d9b269b1f9b189b119b0a9b039afb9af49aed9ae69adf9ad79ad09ac99ac29abb9ab39aac9aa59a9d9a969a8f9a889a809a799a729a6a9a639a5b9a549a4d9a459a3e9a379a2f9a289a209a199a119a0a9a0299fb99f399ec99e499dd99d599ce99c699bf99b799b099a899a09999999199899982997a9973996b9963995c9954994c9944993d9935992d9925991e9916990e990698fe98f798ef98e798df98d798cf98c798c098b898b098a898a0989898909888988098789870986898609858985098489840983898309828981f9817980f980797ff97f797ef97e697de97d697ce97c597bd97b597ad97a4979c9794978b9783977b9772976a976297599751974997409738972f9727971e9716970d970596fc96f496eb96e396da96d196c996c096b896af96a6969e9695968c9684967b9672966a96619658964f9646963e9635962c9623961a96119609960095f795ee95e595dc95d395ca95c195b895af95a6959d9594958b9582957995709566955d9554954b95429539952f9526951d9514950a950194f894ee94e594dc94d294c994c094b694ad94a3949a94919487947e9474946b94619457944e9444943b94319427941e9414940a940193f793ed93e493da93d093c693bc93b393a9939f9395938b93819377936d93639359934f9345933b93319327931d9313930992ff92f592eb92e092d692cc92c292b892ad92a39299928e9284927a926f9265925a92509246923b92319226921c9211920691fc91f191e791dc91d191c791bc91b191a7919c91919186917b91719166915b91509145913a912f91249119910e910390f890ed90e290d790cc90c190b590aa909f90949088907d90729066905b905090449039902d90229017900b90008ff48fe88fdd8fd18fc68fba8fae8fa28f978f8b8f7f8f738f688f5c8f508f448f388f2c8f208f148f088efc8ef08ee48ed88ecc8ebf8eb38ea78e9b8e8e8e828e768e698e5d8e518e448e388e2b8e1f8e128e068df98ded8de08dd38dc78dba8dad8da08d938d878d7a8d6d8d608d538d468d398d2c8d1f8d128d058cf88cea8cdd8cd08cc38cb58ca88c9b8c8d8c808c738c658c588c4a8c3c8c2f8c218c148c068bf88bea8bdd8bcf8bc18bb38ba58b978b898b7b8b6d8b5f8b518b438b358b268b188b0a8afb8aed8adf8ad08ac28ab38aa58a968a888a798a6a8a5b8a4d8a3e8a2f8a208a118a0289f389e489d589c689b789a889998989897a896b895c894c893d892d891e890e88fe88ef88df88cf88c088b088a08890888088708860885088408830881f880f87ff87ef87de87ce87bd87ad879c878b877b876a87598749873887278716870586f486e386d186c086af869e868c867b866a86588646863586238611860085ee85dc85ca85b885a6859485828570855d854b853985268514850184ee84dc84c984b684a38491847e846b845784448431841e840a83f783e483d083bc83a983958381836d835983458331831d830982f582e082cc82b882a3828e827a82658250823b8226821181fc81e781d181bc81a78191817b81668150813a8124810e80f880e280cc80b5809f80888072805b8044802d801780007fe87fd17fba7fa27f8b7f737f5c7f447f2c7f147efc7ee47ecc7eb37e9b7e827e697e517e387e1f7e067ded7dd37dba7da07d877d6d7d537d397d1f7d057cea7cd07cb57c9b7c807c657c4a7c2f7c147bf87bdd7bc17ba57b897b6d7b517b357b187afb7adf7ac27aa57a887a6a7a4d7a2f7a1179f379d579b77999797a795c793d791e78fe78df78c078a0788078607840781f77ff77de77bd779c777b77597738771676f476d176af768c766a76467623760075dc75b875947570754b7526750174dc74b67491746b7444741e73f773d073a9738173597331730972e072b8728e7265723b721171e771bc71917166713a710e70e270b57088705b702d70006fd16fa26f736f446f146ee46eb36e826e516e1f6ded6dba6d876d536d1f6cea6cb56c806c4a6c146bdd6ba56b6d6b356afb6ac26a886a4d6a1169d56999695c691e68df68a06860681f67de679c6759671666d1668c6646660065b86570652664dc6491644463f763a96359630962b86265621161bc6166610e60b5605b60005fa25f445ee45e825e1f5dba5d535cea5c805c145ba55b355ac25a4d59d5595c58df586057de575956d1564655b85526549153f7535952b85211516650b550004f444e824dba4cea4c144b354a4d495c486047594646452643f742b8416640003e823cea3b35395c3759352632b830002cea295c25262000195c100000000000
def bitCode (k : ℕ) := (logCodes >>> (16*k)) % 65536
def wl (k : ℕ) : ℤ := 1000*baseCoeff k - 202*extraCoeff k
def wh (k : ℕ) : ℤ := 1000*baseCoeff k - 201*extraCoeff k
def ll (k : ℕ) : ℤ := (bitCode k:ℤ)*6931471803
def lh (k : ℕ) : ℤ := if k=1 then 0 else ((bitCode k : ℤ)+1)*6931471808
def momentL : ℤ := ∑ k ∈ support, signedLow (wl k) (ll k) (lh k) * ↑(commonMultiple/k)
def momentU : ℤ := ∑ k ∈ support, signedHigh (wh k) (ll k) (lh k) * ↑(commonMultiple/k)
def normDen : ℤ := 600000*4096*10000000000*1*(commonMultiple:ℤ)
theorem code_facts : ∀ k ∈ support, 2^(bitCode k) ≤ k^4096 ∧ k^4096 < 2^(bitCode k + 1) := by decide +kernel
theorem main_integers :
    1000*(1*momentU+normDen) ≤ 1*normDen ∧
    -(1*normDen) ≤ 1000*(1*momentL+normDen) := by decide +kernel
private theorem finish_main (M b L U : ℝ) (hb : 0 < b)
    (e : L ≤ (600000*40960000000000*b)*M ∧ (600000*40960000000000*b)*M ≤ U)
    (h1 : 1000*(1*U+(600000*40960000000000*1)*b) ≤ 1*((600000*40960000000000*1)*b))
    (h2 : -(1*((600000*40960000000000*1)*b)) ≤ 1000*(1*L+(600000*40960000000000*1)*b)) :
    |(-M)/1-1/1| ≤ 1/1000 := by
  rw [abs_le]
  constructor
  · by_contra! z
    nlinarith only [h1,e.2,mul_lt_mul_of_pos_right z hb]
  · by_contra! z
    nlinarith only [h2,e.1,mul_lt_mul_of_pos_right z hb]
set_option maxRecDepth 8192 in
theorem actual_main_budget :
    |-(∑ k ∈ support, affineCoeff baseCoeff extraCoeff 600 alpha k * Real.log k/k)/
        (1:ℝ) - 1/1| ≤ 1/1000 := by
  have hb : (0:ℝ)<commonMultiple := by exact_mod_cast (show 0 < commonMultiple by decide)
  have hweights (k : ℕ) : (wl k:ℝ) ≤ 600000*affineCoeff baseCoeff extraCoeff 600 alpha k ∧
      600000*affineCoeff baseCoeff extraCoeff 600 alpha k ≤ wh k := by
    have hx : 0 ≤ (extraCoeff k:ℝ) := by unfold extraCoeff; split <;> norm_num
    have a := mul_le_mul_of_nonneg_right actual_bracket.1 hx
    have b := mul_le_mul_of_nonneg_right actual_bracket.2 hx
    unfold wl wh affineCoeff
    push_cast
    constructor <;> linarith only [a,b]
  have hlogs (k : ℕ) (hk : k ∈ support) :
      (ll k:ℝ) ≤ (40960000000000:ℝ)*Real.log k ∧ (40960000000000:ℝ)*Real.log k ≤ lh k := by
    have e := from_power k 4096 (bitCode k) (supported_divisors k hk).1 (code_facts k hk).1 (code_facts k hk).2
    by_cases h : k=1
    · subst k
      have b1 : bitCode 1 = 0 := by decide +kernel
      simp [ll,lh,b1]
    · simpa [ll, lh, h] using e
  have e := scaled support commonMultiple (affineCoeff baseCoeff extraCoeff 600 alpha)
    wl wh ll lh 600000 40960000000000 supported_divisors (fun k _ => hweights k) hlogs (by norm_num)
  let M := ∑ k ∈ support, affineCoeff baseCoeff extraCoeff 600 alpha k * Real.log k/k
  change (momentL:ℝ) ≤ (600000*40960000000000*commonMultiple)*M ∧
    (600000*40960000000000*commonMultiple)*M ≤ (momentU:ℝ) at e
  have h1 : (1000:ℝ)*(1*(momentU:ℝ)+(normDen:ℝ)) ≤ 1*(normDen:ℝ) := by exact_mod_cast main_integers.1
  have h2 : -((1:ℝ)*(normDen:ℝ)) ≤ 1000*(1*(momentL:ℝ)+(normDen:ℝ)) := by exact_mod_cast main_integers.2
  have nd : (normDen:ℝ) = 600000*4096*10000000000*1*(commonMultiple:ℝ) := by norm_num [normDen]
  rw [nd] at h1 h2
  have denEq : (600000*40960000000000*1 : ℝ) = 600000*4096*10000000000*1 := by norm_num
  rw [← denEq] at h1 h2
  exact finish_main M _ _ _ hb e h1 h2
end FR7022OrdinaryStage
namespace FR7022ProgressionTail
open Finset
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
      exact (Nat.lt_irrefl C) ((lt_count_iff hq (t/k) r C).mpr hh)
    exact ((Nat.div_lt_iff_lt_mul hk).mp hn).le
  have upper : (R+C*q)*k ≤ t+q*k := by
    cases hz : C with
    | zero => simpa using (Nat.mul_le_mul_right k hR).trans (Nat.le_add_left (q*k) t)
    | succ j =>
      have hj : j < countTerms (t/k) q r := by change j<C; omega
      have hh := (Nat.le_div_iff_mul_le hk).mp ((lt_count_iff hq (t/k) r j).mp hj)
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
namespace FR7022OrdinaryStage
open Finset FR7022ProgressionTail
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sum_wl : ∑ k ∈ support, wl k = -1126200 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sum_wh : ∑ k ∈ support, wh k = -1125600 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem actual_weight_sides (k : ℕ) :
    (wl k:ℝ) ≤ 600000 * affineCoeff baseCoeff extraCoeff 600 alpha k ∧
    600000 * affineCoeff baseCoeff extraCoeff 600 alpha k ≤ (wh k:ℝ) := by
  have hn : 0 ≤ (extraCoeff k:ℝ) := by unfold extraCoeff; split <;> norm_num
  have a := mul_le_mul_of_nonneg_right actual_bracket.1 hn
  have b := mul_le_mul_of_nonneg_right actual_bracket.2 hn
  unfold wl wh affineCoeff
  push_cast
  constructor <;> linarith only [a,b]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem actual_infinite_tail (r t : ℕ) :
    |G support (affineCoeff baseCoeff extraCoeff 600 alpha) 1 r t - 1|
      ≤ 118894426/600000 := by
  let A := affineCoeff baseCoeff extraCoeff 600 alpha
  have sl : (-1126200:ℝ) ≤ 600000 * ∑ k ∈ support, A k := by
    rw [mul_sum]
    have n : (∑ k ∈ support, (wl k:ℝ)) = -1126200 := by exact_mod_cast sum_wl
    rw [←n]
    exact sum_le_sum fun k _ => (actual_weight_sides k).1
  have su : 600000 * ∑ k ∈ support, A k ≤ (-1125600:ℝ) := by
    rw [mul_sum]
    have n : (∑ k ∈ support, (wh k:ℝ)) = -1125600 := by exact_mod_cast sum_wh
    rw [←n]
    exact sum_le_sum fun k _ => (actual_weight_sides k).2
  have mass := affine_l1_le_endpointMass support baseCoeff extraCoeff
    (fun k _ => by unfold extraCoeff; split <;> omega) 600 alpha (by norm_num)
    (-202) (-201) 1000 (by decide) actual_bracket.1 actual_bracket.2
  rw [endpoint_mass_value] at mass
  change (∑ k ∈ support, |A k|) ≤ _ at mass
  have h := centered_tail_bound support A 1 r t (fun _ => 0) (by decide)
    (fun k hk => (supported_divisors k hk).1) (fun k _ => Nat.coprime_one_right k)
    (fun k _ => by simp [Nat.ModEq,Nat.mod_one]) exact_cancellation 1
  have rc : residueCenter 1 0 = (-1/2:ℝ) := by norm_num [residueCenter,firstResidue]
  simp only [rc] at h
  rw [←sum_mul] at h
  have bound : |(∑ k ∈ support, A k)*(-1/2)-1| ≤ 74400/1200000 := by
    rw [abs_le]
    constructor <;> linarith only [sl,su]
  change |G support A 1 r t-1| ≤ _
  norm_num at mass
  linarith only [h,bound,mass]
end FR7022OrdinaryStage
namespace FR7022BlockJumps
open Finset
def thresholds (m : ℕ) (b : ℕ → ℕ) := (range m).image b
noncomputable def mass (m : ℕ) (b : ℕ → ℕ) (M : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ (range m).filter (fun i => b i = t), (M (i+1) - M i)
theorem nonneg (m : ℕ) (b : ℕ → ℕ) (M : ℕ → ℝ) (hm : Monotone M) (t : ℕ) :
    0 ≤ mass m b M t := by
  unfold mass
  exact sum_nonneg fun i _ => sub_nonneg.mpr (hm (Nat.le_succ i))
end FR7022BlockJumps
namespace FR7022BlockJumps
open Finset
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
end FR7022BlockJumps
namespace FR7022First
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def sign (k : Nat) : Int := if (0x2088644e26422ca240c0e6440a0c488006a08cc6a22c0cc84a2602480a660c8ec6a284a84082000e24c0480020a4a824648686c6a0c0acc262222642a44468e0200842a8884ec4620824480428c6ca8422ec8880440a48628028042ee66e040a860042c806e0620cc88400e8e42422468840ce0460c442:Nat).testBit k then 1 else if (0xc668200888cc244aa2400aa6000846ce04a60284c422206a480e82480886220080c6242ac68ee40880ea6c6ca48424a0a280820440a40248c4888844aa2820ccee42c0646a0228864c0a62a02080462c800246e22a4868842c2e8c00800aac46864a824a00e0c80066ae20208c2cc28208e20e08a28ac:Nat).testBit k then -1 else 0
def base (k : Nat) : Int := sign k * (min 600 (950-k):Nat)
def extra (k : Nat) : Int := if 350<k ∧ k≤950 then 1 else 0
def coeff (alpha : Int) (k : Nat) : Int := 1000*base k+alpha*extra k
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def envelope (t : Nat) : Nat :=
  if 1398≤t then 8014170 else
  if 1096≤t then 6116577 else
  if 1063≤t then 4293788 else
  if 913≤t then 4145602 else
  if 675≤t then 3244067 else
  if 655≤t then 3225685 else
  if 636≤t then 2288896 else
  if 581≤t then 2045884 else
  if 564≤t then 1793046 else
  if 547≤t then 1770208 else
  if 531≤t then 1357592 else
  if 431≤t then 702307 else
  if 406≤t then 194534 else
  if 394≤t then 151696 else
  if 383≤t then 64161 else
  if 372≤t then 58171 else
  if 361≤t then 31980 else
  if 351≤t then 8191 else
  0
def radix : Int := 2^48
def bias : Int := 2^47
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def bitsum : Nat → Nat → (Nat → Int) → Int
  | 0, s, f => f s
  | d+1, s, f => bitsum d s f + bitsum d (s+2^d) f
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def allRange : Nat → Nat → (Nat → Bool) → Bool
  | 0, s, f => f s
  | d+1,s,f => allRange d s f && allRange d (s+2^d) f
def scalar (alpha : Int) (t : Nat) : Int := bitsum 10 1 (fun k => coeff alpha k * (t/k:Nat))-600000
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def geo (start n k : Nat) : Int :=
  let r := (k-start % k) % k
  let m := if r<n then (n-1-r)/k+1 else 0
  if m=0 then 0 else if m=1 then radix^r else radix^r*((radix^(k*m)-1)/(radix^k-1))
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def deltaWord (alpha : Int) (start : Nat) : Int :=
  bitsum 10 1 (fun k => let z:=coeff alpha k; if z=0 then 0 else z*geo start 4096 k)
def raw (word : Nat) : Int := (word:Int)-bias*((radix^4096-1)/(radix-1))
def laneValue (word i : Nat) : Int := (((word >>> (48*i)) &&& (2^48-1):Nat):Int)-bias
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def boundOK (s word : Nat) : Bool :=
  allRange 12 0 (fun i => decide ((laneValue word i).natAbs ≤ envelope (s+1+i)))
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
def proposedWord (alpha : Int) (s : Nat) : Nat :=
  let D := scalar alpha s + deltaWord alpha (s+1)
  let Q := (D*(radix^(1*4096)-1)/(radix^1-1)) % radix^4096
  ((Q + bias * ((radix^4096-1)/(radix-1))) % radix^4096).toNat
def w0L : Nat := proposedWord (-202) 0
theorem c0L : proposedWord (-202) 0 = w0L := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e0L : boundOK 0 w0L = true := by decide +kernel
def w0U : Nat := proposedWord (-201) 0
theorem c0U : proposedWord (-201) 0 = w0U := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e0U : boundOK 0 w0U = true := by decide +kernel
def w1L : Nat := proposedWord (-202) 4096
theorem c1L : proposedWord (-202) 4096 = w1L := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e1L : boundOK 4096 w1L = true := by decide +kernel
def w1U : Nat := proposedWord (-201) 4096
theorem c1U : proposedWord (-201) 4096 = w1U := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e1U : boundOK 4096 w1U = true := by decide +kernel
def w2L : Nat := proposedWord (-202) 8192
theorem c2L : proposedWord (-202) 8192 = w2L := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e2L : boundOK 8192 w2L = true := by decide +kernel
def w2U : Nat := proposedWord (-201) 8192
theorem c2U : proposedWord (-201) 8192 = w2U := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e2U : boundOK 8192 w2U = true := by decide +kernel
def w3L : Nat := proposedWord (-202) 12288
theorem c3L : proposedWord (-202) 12288 = w3L := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e3L : boundOK 12288 w3L = true := by decide +kernel
def w3U : Nat := proposedWord (-201) 12288
theorem c3U : proposedWord (-201) 12288 = w3U := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e3U : boundOK 12288 w3U = true := by decide +kernel
def w4L : Nat := proposedWord (-202) 16384
theorem c4L : proposedWord (-202) 16384 = w4L := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e4L : boundOK 16384 w4L = true := by decide +kernel
def w4U : Nat := proposedWord (-201) 16384
theorem c4U : proposedWord (-201) 16384 = w4U := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e4U : boundOK 16384 w4U = true := by decide +kernel
def w5L : Nat := proposedWord (-202) 20480
theorem c5L : proposedWord (-202) 20480 = w5L := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e5L : boundOK 20480 w5L = true := by decide +kernel
def w5U : Nat := proposedWord (-201) 20480
theorem c5U : proposedWord (-201) 20480 = w5U := rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem e5U : boundOK 20480 w5U = true := by decide +kernel
end FR7022First
namespace FR7022First
open Finset FR7022Lane
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem bitsum_spec (d a : ℕ) (f : ℕ → ℤ) :
    bitsum d a f = ∑ i ∈ range (2^d), f (a+i) := by
  induction d generalizing a with
  | zero => simp [bitsum]
  | succ d ih => rw [bitsum,ih,ih,pow_succ,Nat.mul_two,sum_range_add]; simp [Nat.add_assoc]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem support_sum (f : ℕ → ℤ) :
    ∑ k ∈ Ico 1 1025, f k = bitsum 10 1 f := by
  rw [sum_Ico_eq_sum_range,bitsum_spec]; rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem allRange_sound (d s : ℕ) (f : ℕ → Bool) (h : allRange d s f = true) :
    ∀ i, s ≤ i → i < s+2^d → f i = true := by
  induction d generalizing s with
  | zero =>
    intro i hi hu; simp only [pow_zero] at hu
    have : i=s := by omega
    exact this ▸ h
  | succ d ih =>
    rw [allRange,Bool.and_eq_true] at h
    intro i hi hu
    rw [pow_succ] at hu
    by_cases hh : i<s+2^d
    · exact ih s h.1 i hi hh
    · exact ih (s+2^d) h.2 i (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem coef_abs (a : ℤ) (ha : a=-202 ∨ a=-201) (k : ℕ) : |coeff a k| ≤ 601000 := by
  have m : min 600 (950-k) ≤ 600 := min_le_left _ _
  unfold coeff base sign extra
  split_ifs <;> rcases ha with rfl | rfl <;> rw [abs_le] <;> omega
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem block_valid (a : ℤ) (ha : a=-202 ∨ a=-201) (s word : ℕ) (hs : s≤20480)
    (hc : proposedWord a s = word) (he : boundOK s word = true) (i : ℕ) (hi : i<4096) :
    |primePrefix (Ico 1 1025) (coeff a) 600000 (s+1+i)| ≤ (envelope (s+1+i):ℤ) := by
  let f := fun j => primePrefix (Ico 1 1025) (coeff a) 600000 (s+1+j)
  let D := scalar a s + deltaWord a (s+1)
  have hp (t : ℕ) : primePrefix (Ico 1 1025) (coeff a) 600000 t = scalar a t := by
    rw [primePrefix, support_sum]; rfl
  have hD : ∑ k ∈ Ico 1 1025, coeff a k * divisorWord radix (s+1) 4096 k = deltaWord a (s+1) := by
    rw [support_sum]
    unfold deltaWord
    congr 1
    funext k
    dsimp only
    split_ifs with h
    · simp [h]
    · rfl
  have modf : eval radix 4096 f ≡ prefixWord radix 1 4096 4096 D [ZMOD radix^4096] := by
    have h := prefix_mod_eval (Ico 1 1025) (coeff a) 600000 radix s 4096 (by decide) (by decide)
      (fun k h => (mem_Ico.mp h).1)
    rw [hp,hD] at h; exact h
  have sh (j : ℕ) (hj : j<4096) : |f j| < ((2^47:ℕ):ℤ) := by
    have ht : s+1+j ≤ 24576 := by omega
    let t := s+1+j
    have bound : ∑ k ∈ Ico 1 1025, |coeff a k * (t/k:ℕ)| ≤
        ∑ _k ∈ Ico 1 1025, (601000*24576:ℤ) := by
      apply sum_le_sum; intro k _
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤((t/k:ℕ):ℤ))]
      have u : t/k ≤ 24576 := (Nat.div_le_self _ _).trans ht
      apply mul_le_mul (coef_abs a ha k) (by exact_mod_cast u) (by positivity) (by decide)
    have u := Finset.abs_sum_le_sum_abs (fun k => coeff a k * ((t/k:ℕ):ℤ)) (Ico 1 1025)
    have hu := u.trans bound
    norm_num [Nat.card_Ico] at hu
    have hv := abs_sub (∑ k ∈ Ico 1 1025, coeff a k * (t/k:ℕ)) (600000:ℤ)
    change |(∑ k ∈ Ico 1 1025, coeff a k * (t/k:ℕ)) - 600000| < _
    norm_num at hv ⊢
    linarith
  have dg := decode_signed 47 4096 f (prefixWord radix 1 4096 4096 D) modf sh i hi
  change f i = (digit 48 (proposedWord a s) i:ℤ) - bias at dg
  rw [hc] at dg
  have h := allRange_sound 12 0 _ he i (by omega) hi
  change decide ((laneValue word i).natAbs ≤ envelope (s+1+i)) = true at h
  have hn := of_decide_eq_true h
  have H : |laneValue word i| ≤ (envelope (s+1+i):ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast hn
  rw [laneValue,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow] at H
  change |f i| ≤ _
  rw [dg]; exact H
end FR7022First
namespace FR7022First
open Finset FR7022Lane
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem finite_bounds (t : ℕ) (ht : 1≤t) (hu : t≤24575) (a : ℤ) (ha : a=(-202) ∨ a=(-201)) :
    |(∑ k ∈ Ico 1 1025, coeff a k * ((t/k:ℕ):ℤ))-600000| ≤ (envelope t:ℤ) := by
  by_cases h0 : t ≤ 4096
  · have h : 0+1+(t-(0+1))=t := by omega
    rcases ha with rfl | rfl
    · have v := block_valid (-202) (by decide) 0 w0L (by decide) c0L e0L (t-(0+1)) (by omega)
      simpa only [h,primePrefix] using v
    · have v := block_valid (-201) (by decide) 0 w0U (by decide) c0U e0U (t-(0+1)) (by omega)
      simpa only [h,primePrefix] using v
  by_cases h1 : t ≤ 8192
  · have h : 4096+1+(t-(4096+1))=t := by omega
    rcases ha with rfl | rfl
    · have v := block_valid (-202) (by decide) 4096 w1L (by decide) c1L e1L (t-(4096+1)) (by omega)
      simpa only [h,primePrefix] using v
    · have v := block_valid (-201) (by decide) 4096 w1U (by decide) c1U e1U (t-(4096+1)) (by omega)
      simpa only [h,primePrefix] using v
  by_cases h2 : t ≤ 12288
  · have h : 8192+1+(t-(8192+1))=t := by omega
    rcases ha with rfl | rfl
    · have v := block_valid (-202) (by decide) 8192 w2L (by decide) c2L e2L (t-(8192+1)) (by omega)
      simpa only [h,primePrefix] using v
    · have v := block_valid (-201) (by decide) 8192 w2U (by decide) c2U e2U (t-(8192+1)) (by omega)
      simpa only [h,primePrefix] using v
  by_cases h3 : t ≤ 16384
  · have h : 12288+1+(t-(12288+1))=t := by omega
    rcases ha with rfl | rfl
    · have v := block_valid (-202) (by decide) 12288 w3L (by decide) c3L e3L (t-(12288+1)) (by omega)
      simpa only [h,primePrefix] using v
    · have v := block_valid (-201) (by decide) 12288 w3U (by decide) c3U e3U (t-(12288+1)) (by omega)
      simpa only [h,primePrefix] using v
  by_cases h4 : t ≤ 20480
  · have h : 16384+1+(t-(16384+1))=t := by omega
    rcases ha with rfl | rfl
    · have v := block_valid (-202) (by decide) 16384 w4L (by decide) c4L e4L (t-(16384+1)) (by omega)
      simpa only [h,primePrefix] using v
    · have v := block_valid (-201) (by decide) 16384 w4U (by decide) c4U e4U (t-(16384+1)) (by omega)
      simpa only [h,primePrefix] using v
  have h : 20480+1+(t-(20480+1))=t := by omega
  rcases ha with rfl | rfl
  · have v := block_valid (-202) (by decide) 20480 w5L (by decide) c5L e5L (t-(20480+1)) (by omega)
    simpa only [h,primePrefix] using v
  · have v := block_valid (-201) (by decide) 20480 w5U (by decide) c5U e5U (t-(20480+1)) (by omega)
    simpa only [h,primePrefix] using v
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem finite_pair (t : ℕ) (ht : 0<t) (hu : t≤24575) :
    |(∑ k ∈ Icc 1 1024, coeff (-202) k * ((t/k:ℕ):ℤ))-600000| ≤ (envelope t:ℤ) ∧
    |(∑ k ∈ Icc 1 1024, coeff (-201) k * ((t/k:ℕ):ℤ))-600000| ≤ (envelope t:ℤ) := by
  have h : Icc 1 1024 = Ico 1 1025 := by ext k; simp only [mem_Icc,mem_Ico]; omega
  rw [h]
  exact ⟨finite_bounds t ht hu _ (Or.inl rfl),finite_bounds t ht hu _ (Or.inr rfl)⟩
end FR7022First
namespace FR7022FirstJumps
open Finset
def T : Finset ℕ := {351,361,372,383,394,406,431,531,547,564,581,636,655,675,913,1063,1096,1398,24576}
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def delta : ℕ → ℕ
  | 351 => 8191
  | 361 => 23789
  | 372 => 26191
  | 383 => 5990
  | 394 => 87535
  | 406 => 42838
  | 431 => 507773
  | 531 => 655285
  | 547 => 412616
  | 564 => 22838
  | 581 => 252838
  | 636 => 243012
  | 655 => 936789
  | 675 => 18382
  | 913 => 901535
  | 1063 => 148186
  | 1096 => 1822789
  | 1398 => 1897593
  | 24576 => 110880256
  | _ => 0
def level (u : ℕ) := ∑ t ∈ T, if t ≤ u then delta t else 0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
noncomputable def w (t : ℕ) : ℝ := (delta t:ℝ)/600000
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem bounds : ∀ t ∈ T, 0<t ∧ t≤24576 ∧ (t=24576 ∨ t≤1398) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem early : ∀ u ∈ Icc 0 1398, level u = FR7022First.envelope u := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem finite_prefix (u : ℕ) (hu : u≤24575) : level u = FR7022First.envelope u := by
  by_cases low : u≤1398
  · exact early u (mem_Icc.mpr ⟨Nat.zero_le _,low⟩)
  have en : FR7022First.envelope u = 8014170 := by
    simp [FR7022First.envelope, show 1398≤u by omega]
  rw [en, ← show level 1398 = 8014170 by decide +kernel]
  unfold level
  apply sum_congr rfl
  intro t ht
  rcases (bounds t ht).2.2 with eq | small
  · subst t
    simp [show ¬24576≤u by omega]
  · simp [small,show t≤u by omega]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem tail_prefix (u : ℕ) (hu : 24576≤u) : level u = 118894426 := by
  have h : level u = ∑ t ∈ T, delta t := by
    unfold level
    apply sum_congr rfl
    intro t ht
    simp [(bounds t ht).2.1.trans hu]
  exact h.trans (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem paid (u : ℕ) :
    ∑ t ∈ T, (if t≤u then w t else 0) = (level u : ℝ)/600000 := by
  unfold level
  rw [Nat.cast_sum,div_eq_mul_inv,sum_mul]
  apply sum_congr rfl
  intro t _
  by_cases ht:t≤u <;> simp [ht,w,div_eq_mul_inv]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem covers {err : ℕ → ℝ}
    (finite : ∀ u, 0<u → u≤24575 → err u ≤ (FR7022First.envelope u:ℝ)/600000)
    (infinite : ∀ u, err u ≤ 118894426/600000) (u : ℕ) (hu : 0<u) :
    err u ≤ ∑ t ∈ T, if t≤u then w t else 0 := by
  rw [paid]
  by_cases h:u≤24575
  · rw [finite_prefix u h]; exact finite u hu h
  · rw [tail_prefix u (by omega)]; exact infinite u
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem jump_cost : ∑ t ∈ T, w t/t ≤ 24406248245/1000000000000 := by
  have numeric : ∑ t ∈ T, FR7022BlockJumps.ceilRatio (delta t * 1000000000000) (600000*t) =
      24406248245 := by decide +kernel
  calc
    _ ≤ ∑ t ∈ T, ((FR7022BlockJumps.ceilRatio (delta t*1000000000000) (600000*t):ℕ):ℝ)/1000000000000 :=
      sum_le_sum fun t ht => FR7022BlockJumps.per_jump_cost (delta t) 1000000000000 600000 t
        (by decide) (by decide) (bounds t ht).1
    _ = _ := by
      have casted : (∑ t ∈ T, (FR7022BlockJumps.ceilRatio (delta t*1000000000000) (600000*t):ℝ)) =
          24406248245 := by exact_mod_cast numeric
      simp only [div_eq_mul_inv, ←sum_mul,casted]
end FR7022FirstJumps
namespace FR7022OrdinaryStage
open Finset FR7022ProgressionTail
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def endpointSum (v : ℤ) (t : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 1024, FR7022First.coeff v k * (t/k:ℕ)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem weights_agree : ∀ k ∈ support,
    endpointWeight baseCoeff extraCoeff (-202) 1000 k = FR7022First.coeff (-202) k ∧
    endpointWeight baseCoeff extraCoeff (-201) 1000 k = FR7022First.coeff (-201) k := by
  intro k hk
  have hm : k ∈ Icc 1 950 := (mem_filter.mp hk).1
  have ku := (mem_Icc.mp hm).2
  have hs : coefficientSign k = FR7022First.sign k := rfl
  have hb : baseCoeff k = FR7022First.base k := by
    by_cases e : k ≤ 350
    · rw [baseCoeff, FR7022First.base, hs, if_pos e, min_eq_left (show 600 ≤ 950-k by omega)]
      exact congrArg (fun z : ℤ => FR7022First.sign k * z) (by decide : (600:ℤ) = ((600:ℕ):ℤ))
    · rw [baseCoeff, FR7022First.base, hs, if_neg e, min_eq_right (show 950-k ≤ 600 by omega)]
  have he : extraCoeff k = FR7022First.extra k := by
    simp [extraCoeff, FR7022First.extra, ku]
  constructor <;> simp only [endpointWeight, FR7022First.coeff, hb, he]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem outside_extra : ∀ k ∈ Icc 1 1024, k ∉ support →
    FR7022First.coeff (-202) k = 0 ∧ FR7022First.coeff (-201) k = 0 := by
  intro k hk hn
  have hlarge : ¬ k ≤ 950 := by
    intro h
    exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hk).1,h⟩,by simp⟩)
  have hz : 950-k = 0 := by omega
  simp [FR7022First.coeff, FR7022First.base, FR7022First.extra, hlarge, hz]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem endpoint_as_integer (r t : ℕ) (v : ℤ) (hv : v= -202 ∨ v= -201) :
    G support (fun k => ((endpointWeight baseCoeff extraCoeff v 1000 k:ℤ):ℝ)) 1 r t = endpointSum v t := by
  have incl : support ⊆ Icc 1 1024 := by
    intro k hk
    have hm : k ∈ Icc 1 950 := (mem_filter.mp hk).1
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans (by decide)⟩
  have cnt (k : ℕ) : count 1 r t k = t/k := by simp [count,Nat.mod_one]
  unfold G endpointSum
  push_cast
  simp_rw [cnt]
  calc
    _ = ∑ k ∈ support, (FR7022First.coeff v k:ℝ) * (↑(t/k):ℝ) := by
      apply sum_congr rfl
      intro k hk
      rcases hv with rfl | rfl
      · rw [(weights_agree k hk).1]
      · rw [(weights_agree k hk).2]
    _ = _ := by
      apply sum_subset incl
      intro k hk hnot
      rcases hv with rfl | rfl
      · simp [(outside_extra k hk hnot).1]
      · simp [(outside_extra k hk hnot).2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem actual_finite (f : ∀ u : ℕ, 0<u → u≤24575 →
    |endpointSum (-202) u - 600000| ≤ FR7022First.envelope u ∧
    |endpointSum (-201) u - 600000| ≤ FR7022First.envelope u)
    (r t : ℕ) (ht : 0<t) (hmax : t≤24575) :
    |G support (affineCoeff baseCoeff extraCoeff 600 alpha) 1 r t - 1| ≤
      (FR7022First.envelope t:ℝ)/600000 := by
  let b : ℝ := (FR7022First.envelope t:ℝ)/600000
  have ee := f t ht hmax
  have lo : -(FR7022First.envelope t:ℝ) ≤ (endpointSum (-202) t:ℝ)-600000 := by
    exact_mod_cast (abs_le.mp ee.1).1
  have hi : (endpointSum (-201) t:ℝ)-600000 ≤ (FR7022First.envelope t:ℝ) := by
    exact_mod_cast (abs_le.mp ee.2).2
  have br := affine_G_from_prefixes support baseCoeff extraCoeff 600 alpha (1-b) (1+b)
    (-202) 1000 (-201) 1000 (endpointSum (-202) t) (endpointSum (-201) t)
    (by decide) (by decide) (by norm_num)
    (fun k _ => by dsimp [extraCoeff]; split <;> omega)
    actual_bracket.1 actual_bracket.2 1 r t (endpoint_as_integer r t _ (Or.inl rfl))
    (endpoint_as_integer r t _ (Or.inr rfl))
    (by dsimp [b]; push_cast; linarith only [lo])
    (by dsimp [b]; push_cast; linarith only [hi])
  change |_-1| ≤ b
  rw [abs_le]
  constructor <;> linarith [br.1,br.2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem actual_he (f : ∀ u : ℕ, 0<u → u≤24575 →
    |endpointSum (-202) u - 600000| ≤ FR7022First.envelope u ∧
    |endpointSum (-201) u - 600000| ≤ FR7022First.envelope u)
    (r u : ℕ) (hu : 0<u) :
    |G support (affineCoeff baseCoeff extraCoeff 600 alpha) 1 r u - (if r % 1=1 % 1 then (1:ℝ) else 0)| ≤
      ∑ t ∈ FR7022FirstJumps.T, if t≤u then FR7022FirstJumps.w t else 0 := by
  simp only [Nat.mod_one, ite_true]
  exact FR7022FirstJumps.covers (fun t ht hb => actual_finite f r t ht hb)
    (fun t => actual_infinite_tail r t) u hu
end FR7022OrdinaryStage
namespace FR7022OrdinaryStage
open Finset FR7022ProgressionTail
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
noncomputable def firstArithmetic : ArithmeticFunction ℝ :=
  ⟨fun k => if k∈support then affineCoeff baseCoeff extraCoeff 600 alpha k else 0,
   by simp [support]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem realized_first_row
    (f : ∀ u : ℕ, 0<u → u≤24575 →
      |endpointSum (-202) u - 600000| ≤ FR7022First.envelope u ∧
      |endpointSum (-201) u - 600000| ≤ FR7022First.envelope u) :
    Nonempty (FR7022TwoStageBridge.Row 1 (10^10) 24576 (31/20) (1/25)) := by
  let A := affineCoeff baseCoeff extraCoeff 600 alpha
  have agree : ∀ k ∈ support, firstArithmetic k = A k := by
    intro k hk
    change (if k∈support then A k else 0) = A k
    simp [hk]
  have eqMoment : (∑ k ∈ support, firstArithmetic k * Real.log k / k) =
      ∑ k ∈ support, A k * Real.log k / k :=
    sum_congr rfl fun k hk => by rw [agree k hk]
  have eqMass : (∑ k ∈ support, |firstArithmetic k|) = ∑ k ∈ support, |A k| :=
    sum_congr rfl fun k hk => by rw [agree k hk]
  refine ⟨⟨support, firstArithmetic, ?_, ?_, (fun k _ => Nat.coprime_one_right k),
    ?_, FR7022FirstJumps.T, FR7022FirstJumps.w, ?_, ?_, ?_, ?_⟩⟩
  · intro k hk
    change (if k∈support then A k else 0) = 0
    simp [hk]
  · intro k hk
    have z := mem_Icc.mp (mem_filter.mp hk).1
    omega
  · calc
      (∑ k ∈ support, firstArithmetic k / k) = ∑ k ∈ support, A k / k := by
        apply sum_congr rfl
        intro k hk
        rw [agree k hk]
      _ = 0 := exact_cancellation
  · intro t _
    unfold FR7022FirstJumps.w
    positivity
  · intro t ht
    exact ⟨(FR7022FirstJumps.bounds t ht).1,(FR7022FirstJumps.bounds t ht).2.1⟩
  · intro r u hu _
    have gg : G support firstArithmetic 1 r u = G support A 1 r u := by
      unfold G
      exact sum_congr rfl fun k hk => by rw [agree k hk]
    rw [gg]
    exact actual_he f r u hu
  · rw [eqMoment,eqMass]
    have ma := actual_main_budget
    have lg := actual_rounding_budget
    have jc := FR7022FirstJumps.jump_cost
    dsimp only [A]
    norm_num only [Nat.totient_one,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,div_one] at *
    linarith only [ma,lg,jc]
end FR7022OrdinaryStage
namespace FR7022OrdinaryStage
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem first_row : Nonempty (FR7022TwoStageBridge.Row 1 (10^10) 24576 (31/20) (1/25)) :=
  realized_first_row (fun u ht hu => FR7022First.finite_pair u ht hu)
end FR7022OrdinaryStage
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
  have aux (x : ℕ) (hx : x<modN n) : ∀ d q, prefixPacked (modN n-1) d q x < modN n := by
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
namespace FR7022TwoStage
structure Certificate where
  q : Nat
  k0 : Nat
  k1 : Nat
  B : Nat
  alphaLo : Int
  alphaHi : Int
  scale : Nat
  globalMax : Nat
  mainCost : Nat
  finiteCost : Nat
  tailCost : Nat
  logCost : Nat
  total : Nat
  blocks : Array (Nat × Nat × Nat)
def ceilDiv (x y : Nat) : Nat := (x+y-1)/y
structure Packed where
  params : Certificate
  blockCount : Nat
  rises : List (Nat × Nat)
def jumpList : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | n+1, word => (word % 524288, (word >>> 19) % 536870912) :: jumpList n (word >>> 48)
def q2 : Packed := ⟨⟨2,2508,3800,368639,(-7755),(-7754),1292000,827749213,489359981,6317662722,1645039694,12,8770570506,#[]⟩,166,jumpList 21 0x458ad009cc0058a5200a1a003517000a6a00713c500abd0296f9a00bc501a8da080c23024714480c840107d930107f0172b47012a701a1de901af3014618e82067001725f0216a0030e79825c902283bd02d6f006990d83857019085e84a4c000c1b005c24006f0f007246006ad2908dba0018897116db028228f2bdd7⟩
def q4 : Packed := ⟨⟨4,2508,3800,368639,(-7755),(-7754),1292000,829901044,244679991,6730509879,1654287709,12,8964869495,#[]⟩,166,jumpList 17 0x340b4809cc002d8a200a1a005680c80a6a00017b300abd0079b3400b1201410ef00bc501982e380c2301b18db00c8400b8e718107f02e15ab812170276dc0012a7009db700147301d9250015be016ea648189400d5f918216a011fe4282c0f025b71409b6d⟩
def q6 : Packed := ⟨⟨6,2508,3800,368639,(-66375),(-66374),1292000,623821183,1287324896,6637725472,1214288205,9,9453419130,#[]⟩,166,jumpList 20 0x78589809cc0094fca00a1a0018a4980abd00eb04100b1202497eb80b6a008c94480bc5004824c00c23011953880c840021dfe00ce800dd83080d4f006db5f00db90235d7780e26016c17080e9700df3888238802c3783825c9012b83403be9003e67a0854500d2d7309b6d0080400a35d903f8114a7ff5⟩
def q8 : Packed := ⟨⟨8,2508,3800,368639,(-7755),(-7754),1292000,831677042,122339996,7389324137,1642416650,12,9515350427,#[]⟩,166,jumpList 20 0x20721809cc002ae2480a1a0033b3b00a6a00221ca00abd00810df00b120073de700b6a0119c0f80bc500adb6a00c230220e6380c8400cdf2100fff009db700107f004a0f80118b04500100121701d9250012a700f8b93018940073f2b025c9000b86e0282e029f1938296f04e4e8382aba013777502c0f⟩
def q10 : Packed := ⟨⟨10,2508,3800,368639,(-39646),(-39645),1292000,695689325,543983752,6378665671,1369006115,10,8601562420,#[]⟩,166,jumpList 21 0x34250009cc005ebf400a1a003709e00a6a0006b2e00abd00b874200b1200fca0900b6a010a9d500bc5020530700c2300f4e2d00c84004680f00d4f009b61600db9001b1510118b013b6e0012a7013b6e00171e03b24a0017d6009db7001894007048381af3007b30f8296f009b05902aba0006c180517a04f58490a54a⟩
def q12 : Packed := ⟨⟨12,2508,3800,368639,(-66375),(-66374),1292000,624451905,643662448,6259076610,1226582310,9,8428747734,#[]⟩,166,jumpList 25 0x49324809cc00557ad00a1a000f36880a6a007a64080abd004598680b12011a88200b6a005b14680bc500a8fdb80c2300fc90400c84011a93d80ce8001b3ca80d4f0067c6680db9005841c00e26006c89280e97004c0cc011030263e488118b0012f77813d50276dc0014730276dc0015160075c2d0683401615aa89b6d00cc1f89063701728cb293f400198b136686006629553708⟩
def q14 : Packed := ⟨⟨14,2508,3800,368639,(-30917),(-30916),1292000,728604911,330425856,7260544935,1429268630,11,9367831975,#[]⟩,166,jumpList 24 0x23d68809cc0048d3480a1a009066480abd00976db00b120003c6280b6a00220c480bc5010932b00c2300bb8a800c8401b7bf980ce8000941d00d4f0003ffb80f0b008156580f8301123cc00fff02025640107f0021648012a7007c5280133c01d925001473031493001516009db700166b01d92500171e013b6e0017d6009db700189401dd1be085450240d6209227⟩
def q16 : Packed := ⟨⟨16,2508,3800,368639,(-7755),(-7754),1292000,840051166,61169998,7265893841,1649659262,12,9333345238,#[]⟩,166,jumpList 26 0x18c0b809cc00194d080a1a003238600a6a001ebad00abd002886000b1200ac6be00b6a00cdf8680bc5001166100c2300c25ee80c840003d8b00ce8008a84500db9016523d00e97007a7e980f0b015ea6680fff001106981217013b6e0012a7009db700133c02c327401bca0276dc001ca80164c8181d8d02317b50216a027608702275032ee0a02388013e2ce024a40122201025c90064203026f7⟩
def q18 : Packed := ⟨⟨18,2508,3800,368639,(-66375),(-66374),1292000,631212556,429108299,6897623316,1227327983,9,8879057659,#[]⟩,166,jumpList 25 0x3cc69809cc003de7a80a1a001f6ee00a6a003b99d00abd005aed580b1200b7de500b6a007124d80bc5002f1a980c2300871dd80c84005724980ce8009746900d4f005325280e2602af2a100e970276dc000fff009db7001103013b6e0013d5013b6e00147301d925001516009db700171e013b6e00238800cce52036a203415bd83857004b6f1861fd0033810116db0173f2c53708⟩
def q20 : Packed := ⟨⟨20,2508,3800,368639,(-39646),(-39645),1292000,695390182,271991876,5519970941,1366185915,10,7433595017,#[]⟩,166,jumpList 25 0x21270009cc002d47d00a1a005064c00a6a0010f5d00abd006b1b180b12007764080b6a00baa1600bc501a1dff00c2300d2f7300c84006881500d4f00cef5300fff00db5130118b00bfd0d01217009db70012a7009db700133c007b9d3015be0038c5e8166b008735e8189400b438181958009db7001af30155464043c00033d4384a4c0507bb904f02027e18e0517a00e43420a54a⟩
def q22 : Packed := ⟨⟨22,2508,3800,368639,(-26539),(-26538),1292000,774481405,175196072,6994983493,1512292983,11,9022763619,#[]⟩,166,jumpList 31 0x207d6009cc00258d080a1a000218200a6a004f1ee00abd00931d200b12004048c80b6a002d1e880bc500b87a100c2300bfbc380c8400dd46b80ce800576be00d4f000c67880db900241ae80e26008dbe200e97016367280f0b009db7000f830121ac20118b009db70012170019c1e015be013b5f9817d6031493001894004785f81d8d0025a0a0216a02dfde502275019cd9f023880079652026f7013cb0782d6f01ddc8983a19022e63303be9002f39003dc801cffae03fb6⟩
def q24 : Packed := ⟨⟨24,2508,3800,368639,(-66375),(-66374),1292000,623272774,321831224,5883463489,1226652896,9,7716352274,#[]⟩,166,jumpList 25 0x26836009cc00449e680a1a00205d280a6a002834f80abd004907500b1200bb70600b6a0047f1f80bc500e747080c2300d4d4600c840064d8680ce8003452880e26014ef9e80e97010e8200107f013b6e0011030276dc00118b0123fe001473013b6e00151600e213002aba004ca5183a1900909a683fb60101448041b300a5d13843c001464b40480c0123793293f40008be4abdd7⟩
def q26 : Packed := ⟨⟨26,2508,3800,368639,(-23789),(-23788),1292000,790940620,140409223,7360631554,1544678812,11,9401932015,#[]⟩,166,jumpList 34 0x1642f809cc002c99b80a1a001ba1f80a6a005fa0380abd000be2b80b120053fa480b6a00d4b0f80bc5009da9d00c23001e63880c8400ec33080ce8007c4ff80d4f00cfbc500e26008c7c000fff026310d0107f009db7001103009db70012a701d9250013d5009db70014730276dc001516013b6e00166b009db7001af30039955025c90015e240282e01e9aee0296f012570402aba009306402c0f009db7002d6f013b6e002eda0137abe030500090b48031d20143134043c000a4fee1288d0083406131d1007f77f9453a⟩
def q28 : Packed := ⟨⟨28,2508,3800,368639,(-30917),(-30916),1292000,743243127,165212928,6561190048,1448021674,11,8494793130,#[]⟩,166,jumpList 40 0x18df3809cc002499d00a1a000014e00a6a005416100abd005c43d00b120026e3c80b6a00d691b80bc50037fd600c2300c866200c84007910380ce8008faff80e26000de2b80f830005fb400fff0103d950107f01232a98118b0184ed181217013b6e0012a7006970b01516013b6e00166b013b6e00171e01d9250017d6000787c026f70022faf0282e0060df88296f015f68f82aba0318b4502c0f009db7002d6f00fe008031d2008aed20336000611e2036a2009bef603857013386a03a1900426fe03be90021cea06b75004572e07246010011087986005761d07d52004c14a8813c0005d72096b80034f8f4f708⟩
def q30 : Packed := ⟨⟨30,2508,3800,368639,(-244808),(-244807),1292000,527472658,868766948,5574897161,1016677589,8,7724004696,#[]⟩,166,jumpList 24 0x5dec8009cc00609c000a1a003df7000a6a004d14000abd00bc0a400b1200c418c00b6a010b43800bc500a99b800c2300752a000c84003803000ce8016a74800d4f003f6e000db9013729800e2600d286400e97009db7000fff008f11001a22009db7002c0f021583d83dc8014e912045de00593040595a012ac6d85c2400766f20a54a00a33a50f69103f394c1e52a⟩
def q32 : Packed := ⟨⟨32,2508,3800,368639,(-7755),(-7754),1292000,842074106,30584999,6537698059,1662860297,12,8559165702,#[]⟩,166,jumpList 35 0x1063c809cc0018d7b00a1a0038eac80a6a004a5c300b1200264c500b6a00525af00bc5000aa7080c2300bc7aa00c840064ec180ce800429f780d4f004295d80db900a612e00e26014408e00e97013b6e000f0b009db7000f83010cd018107f009db700110300cc54e8118b009db70012a7009db700133c01cf39901d8d0091a8f01e7900d788e81f6c0003c9602067010bcb98216a0066b0f022750101910023880097ea6024a40220b4b025c902732a5026f700574740296f00054e10e7db01e4db80ef19002fb5599362004863e19ffd⟩
def q34 : Packed := ⟨⟨34,2508,3800,368639,(-20568),(-20567),1292000,802117403,95415675,6317240784,1580040390,12,8308588108,#[]⟩,166,jumpList 35 0x110dc009cc00234b800a1a000236c00a6a0031f8500abd001b93f00b120064cb400b6a006961400bc50057bb800c23005d85c00c840039b4000ce801619a000d4f010725c00db9001296b00f0b00dac4100f8301d92500107f00236270121701180b90133c0276dc0013d5009a86701894009a8e901ca8004bf5402067013b6e00216a008732c02388009dda8024a4000282c025c900dbb50026f702911000336002e56b4034fb003506c075d800c78280798600ca8840afc7000cb5996fd1001295a9ba630003e3c45708005fec047708⟩
def q36 : Packed := ⟨⟨36,2508,3800,368639,(-66375),(-66374),1292000,636857398,214554150,5968229744,1240504698,9,7711637979,#[]⟩,166,jumpList 28 0x25db6809cc002120780a1a000c8af00a6a002ec4a80abd00338f380b120041faa00b6a00a3f4a80bc50015d1f00c23007284680c8400733fe80ce8002f41a80d4f00d503400e97009db7000f0b01d925000fff009db700107f009db700110300ff9d80118b01d925001217009db70015160276dc00171e009db70017d602457130385701970f103a190131b5f03dc80029b200480c0023cff84a4c013b2909288d01829372ea63⟩
def q38 : Packed := ⟨⟨38,2508,3800,368639,(-20306),(-20305),1292000,809418603,82100273,6767319301,1592375351,12,8776182724,#[]⟩,166,jumpList 38 0xfb32009cc001fef600a1a001566500a6a004378a80abd0031c5580b6a009392b00bc50051fbe00c23006260f00c84008f43600ce8008450700d4f000998a00db90039ed100e26009bad500e97001bdc100f0b0081daf00f83013b6e000fff009db700107f0062e0801217002961c012a7009db70013d5009db700151601d9250015be014ce2c0166b009db700171e0276dc0017d6013b6e001894013b6e00195801d394202d6f009db7002eda009db7003050009db47031d201c8bd603360001c7ad034fb00a0833036a200c66c1092270020dd40baef00495908c6cc000933034c25⟩
def q40 : Packed := ⟨⟨40,2508,3800,368639,(-39646),(-39645),1292000,707921653,135995938,6392026309,1375821819,10,8214558002,#[]⟩,166,jumpList 32 0x15a46009cc0020a0e00a1a002b01200a6a0023b9300abd007830400b12007558600b6a00939e600bc500a726600c23001366d00c84017a24c00e9700f0adf00f0b009db7000fff009db700107f013b6e001103009db700118b009db7001217013b6e00133c009db70014730276dc001516009db70015be00a246b82388012cde3024a400c9ab0825c9008a504826f7006d0d58282e003c87b04f02001352a0517a034e4e00813c005b8b90854500fa4ed0896f0069a0608dba026096c916db⟩
def q42 : Packed := ⟨⟨42,2508,3800,368639,(-196244),(-196243),1292000,558727541,530496086,5373864603,1082796861,8,7245424017,#[]⟩,166,jumpList 29 0x37b94009cc003e50c00a1a003141000a6a0078aa400abd008d2c400b12003509c00b6a002b65000bc5006f6ae00c2300e781400c84003509c00ce8003102800d4f007454800db9014c94400e2600adfae00e97002961c00fff0031704013d5009db7001473009db700151600ebbc58171e0276dc0017d6009db700216a008aa0503dc800c59a283fb600ad21d845de0156f498480c00ab9308517a013b6e005405019dc9e8650c01d925006834⟩
def q44 : Packed := ⟨⟨44,2508,3800,368639,(-26539),(-26538),1292000,776154653,87598036,6458734832,1518241530,11,8383653464,#[]⟩,166,jumpList 36 0x12ee3009cc001ea6300a1a0003f8d80a6a004951480abd00637f300b12000e7ac00bc5005fe6900c23006d62700c84006bacf00ce8013d36c80d4f00802ee80e26013a52600e97006b54080f83003262f8107f009db700118b009db7001217009db700133c003f0448147300fc69b81516013b6e0015be013b6e00166b009db700171e009db70017d6008098d81f6c00fc69e82275014747b0238800011bb024a400405c10282e01a4bac8296f014a85082aba00083e982c0f009db7002d6f008eed18385703b81328480c01df91484a4c00033d584c9e⟩
def q46 : Packed := ⟨⟨46,2508,3800,368639,(-20021),(-20020),1292000,813646341,66151888,6493960702,1589748941,12,8473209929,#[]⟩,166,jumpList 35 0xdcc9009cc002329500a1a000e04000a6a00238d780abd003a1c500b120071c6500b6a0030b6100bc50050f0100c2300b910500c840064f4680ce800034db80d4f0018c9980db9009aca700e260093f4f80e97013b6e000f0b009db7000f83009db7000fff009db700107f013b6e00118b013b6e0012a7009db7001af301d925001bca013b6e001ca8030c47501d8d013ab3d01e79009db7001f6c005505c03050005c935041b300405f404a4c009db7004c9e01689d1854050133a968896f00d728e0a04803664088a54a00695968aa74⟩
def q48 : Packed := ⟨⟨48,2508,3800,368639,(-66375),(-66374),1292000,635777709,160915612,5250689464,1225623697,9,6896281309,#[]⟩,166,jumpList 35 0x1c2af009cc001bec700a1a001fa9780a6a001643380abd002a34b00b120077a4e80b6a001610700bc500b30bf00c2300ca7bf00c840037d8e00d4f002766b80e26014abf180e97009db7000f0b013b6e000f83009db7001103013b6e00118b00040740166b009db700171e009db70017d6013b6e00195800c92508282e009db700296f00254238385700b3a5783a19009e13903dc801a06d783fb6024e58e841b3000f8c78480c00b48ac09b6d0065e5f0a048018ace50a54a01481830baef019931e8c0c600f7dd20c6cc00faa02c3708⟩
def q50 : Packed := ⟨⟨50,2508,3800,368639,(-39646),(-39645),1292000,704017950,108796751,5624618498,1373639821,10,7386985413,#[]⟩,166,jumpList 35 0x1277e009cc00269c200a1a000f56700a6a00507ae00abd0004d6f00b12007519e00b6a003397b00bc500706b500c230084f8600c840050d8a00ce8007505b00d4f006235500e97009db7000f0b013b6e000f83013b6e00107f009db7001103009db700118b001d8a80147301937ed015be002b2b68171e00728b9817d6013b6e001894009db7001a22009db7001af301f1d8981d8d00b021d843c0012554104f02003e9430517a00625128650c010be8d8813c01d593b88545006e5e108dba009af97096b800c1f4e8c0c6022dc660c6cc⟩
def q52 : Packed := ⟨⟨52,2508,3800,368639,(-23789),(-23788),1292000,791617031,70204612,6525892929,1554573894,11,8473890119,#[]⟩,166,jumpList 36 0xed75009cc001788a80a1a002fec100a6a0024b7a80abd002ccb900b12004368100b6a008dcb500bc5005352900c23005d1d280c84007c4ff80ce8007681280d4f00e403680e26005a50480f83009db7000fff007fcec01217009db70012a7013b6e0013d5009db700147301d925001516009db70015be009db700166b009db700171e009db70017d6006f46b81af3013b6e001bca01d356401d8d01c7b6e01e790011f8601f6c00185160206700dc59103050009db70031d201bffdc834fb0116a92836a2016c5aa83857004089d9d67700bd6222bdd7⟩
def q53 : Packed := ⟨⟨53,2508,3800,368639,(-2575),(-2574),1292000,1242343172,9571879,5744270410,2485389454,18,8568418156,#[]⟩,166,jumpList 50 0xa3c6009cc0014ed100a1a002073e00a6a002373d00abd0021f0e00b12003932f80b6a0088ede80bc50003f9f80c230059dcb00c840062b3f80ce800fe22980db9000050780e26004114f00e970062af400f0b0044c7100fff013b6e00107f0079cae8121700bbf84812a7002050b013d5010c6e1014730030924815be004e6330166b00005078171e0000507817d6000888d81958007a9fb81a22005ec3601bca008c78281ca8000050781d8d0093f7b01e790124be301f6c00c248b82067005fee982275019344b8238800f1793024a40059e9f825c90061032826f7008b3260282e012f827036a200bd7cb03857014199e03a1901862bb03be900507f103dc80077f99041b3009d162043c000fd41f0480c0041a9b0595a008a52505c240173b8f187290278b1899362⟩
def q54 : Packed := ⟨⟨54,2508,3800,368639,(-66375),(-66374),1292000,637820823,143036100,5925729652,1232152483,9,7587233530,#[]⟩,166,jumpList 32 0x197b7009cc002026780a1a003782f00a6a002892b80abd006e71700b12002621b80b6a00967b700bc500b0d9700c2300624ff80c840051e8c00e26009f97780e97008bd0f80f0b01d925000fff013b6e001103009db7001217009db70013d5009db7001473013b6e0015160080c8c017d600023280216a009db7002275013b6e0023880114476031d20026f4d036a2023fc29038570131d1203a19003aab903be900cef1204a4c02151ca04c9e002199a04f02022eea10517a015710705c24⟩
def q55 : Packed := ⟨⟨55,2508,3800,368639,(-8472),(-8471),1292000,965910078,32567058,5225675199,1905491290,14,7448980221,#[]⟩,166,jumpList 43 0xb394009cc0014cf400a1a001ee9680a6a00232dd80abd0036ae400b120035f4080b6a0068aab80bc500356da80c2300b8d2500c84005dc1080d4f00110ae00db900fe6da00e97013ee2b80fff009a4248118b000374b812a70001b75013d5009cae48147300b2f6501516009cae4815be009cae48166b000534a817d6001020a01958000532d81af3007fa0c81bca00104550206701aa9408216a00fe66d0227500e861802d6f009e56103050021a94d031d20118ab003a19012875583be90064221045de00186e785f0501b7218061fd0242e6c0650c001dc5806834011238806b75006108406ed0005c1290896f016b1f788dba015a578096b8017a77b0a048⟩
def q56 : Packed := ⟨⟨56,2508,3800,368639,(-30917),(-30916),1292000,751085062,82606464,5940372984,1451764122,11,7770429066,#[]⟩,166,jumpList 38 0x1094d009cc001440e80a1a000ec2a80a6a004b2cd00abd002fd7680b12004149900b6a00266e900bc50051c6e80c2300a0bf100c84006687680ce801054d480db9000e62500e2600892d700f83005594e0107f009db7001103007551981217009db70012a700c61c681473013b6e001516013b6e00166b013b6e00171e013b6e0017d6009db70018940063b3a0227500ab6840238800e92a2024a401201b4025c90196e18026f70020a5604c9e012e0f685405024eecd85c24023aa12075d802e48260798600b04ce07d52001d75b0ef19007a9ef116db00b95fe9288d009db70131d1⟩
def q57 : Packed := ⟨⟨57,2508,3800,368639,(-9818),(-9817),1292000,913739528,36025026,5587916351,1791548645,13,7710668635,#[]⟩,166,jumpList 46 0xb6e2009cc0017a8d00a1a0014e8700a6a001568300abd000cc5a00b12004b10480b6a0041d6b80bc5002b50100c230094e5100c840064baf80ce8007172b00d4f00fa2ab00db9008d47b00e260004ce300f0b009db7000f83006bbd680fff009db700107f009db70012a7007c7a7015be01a86a90166b00d7cc50171e01311bf017d600f3a15018940081ce102388009db70024a4009d345026f7011023902d6f001ab0603050003b9d50336000a01ca034fb0140394036a2000132d038570011f1b03fb600128df0480c00817e904a4c00822050683401d6bf706b7500212e107d5201f8a0a0813c0381fb80854500510570896f00e7ddf08dba000623009227018032e0afc7000132d0b545010404e10637⟩
def q58 : Packed := ⟨⟨58,2508,3800,368639,(-19182),(-19181),1292000,822602792,49619624,6092725911,1610810290,12,8061297286,#[]⟩,166,jumpList 40 0xe72e009cc001b5db00a1a000e3fd00a6a00191fc00abd00626ee00b12000d92700b6a00738bc00bc5004a70d80c23005642700c840072a8080ce80076d1a00d4f00b8e1900e26005dc0780e97013b6e000f0b009db7000f8300904eb81217009db70012a7009db70013d5000f813015be01395518166b009db700171e0086cca01f6c010a5af8206700e644e0216a01063ab0227501f737e0238801910ba024a400451d3025c90147316026f70061256033600122cb3034fb004fe0e036a200722e203857019d1bb03a19010f6840540500d173706834006d49506ed00041bd90724601a2e98075d80061c2f1d677⟩
def q59 : Packed := ⟨⟨59,2508,3800,368639,(-1599),(-1598),1292000,1245814316,8033541,5775653500,2487050497,18,8601245716,#[]⟩,166,jumpList 52 0xb34e009cc00152ad00a1a001356100a6a00389de00abd001a2c100b12001a70080b6a004a9bf00bc5006796b80c23001a25b00c8400d23ab00ce80018f9b80d4f0020c5380db900b791e00e26009d85100e97009db7000f0b0104c870107f009db700118b00990f801473013b0a2015160012309017d60122ee181958004b93481a22011564901af300ad2b801ca80001a2d01d8d00830e401f6c007c7050206700753c90216a0073cc002388005139d024a40159ba7025c90060da20282e00005eb031d2013abf60336000ad64803be9005f50203dc8002cfb2041b3009795104a4c0160afb04c9e01625940517a003b3ab05405008c67f056a5009ecb105f0500400050650c00eb2e106834000063f06b75000532e86ed001159c88724600418c2885450354d4b8896f005133708dba00b8212b3291⟩
def q60 : Packed := ⟨⟨60,2508,3800,368639,(-244808),(-244807),1292000,537615706,434383474,5414864345,1029528849,8,7136552404,#[]⟩,166,jumpList 31 0x44500009cc002ce6000a1a003571800a6a003feb000abd003ff1000b12005899800b6a00c5b5000bc5005874400c2300f418000c84008508800ce8004317800d4f0094d5000e26001de2400e97009db7000f0b0123c5801217009db70012a7009db7001473009db70015be009db700166b013b6e001958013b6e001a22009497f041b300aa0b4043c000753c1045de00cec8684c9e013b6e004f0200694590517a00259f085405022d110056a5028ebd00595a01c5e9e9f453⟩
def q61 : Packed := ⟨⟨61,2508,3800,368639,(-1402),(-1401),1292000,1247092080,7156376,5341463373,2493213105,18,8155219932,#[]⟩,166,jumpList 45 0x9fc6009cc0011fe500a1a002197b00a6a00230ef00abd003a0e780b1200455c300b6a0019f3b80bc50082a3b00c2300598cf80c8400373fb80ce800c68a800d4f00426c900e2600a108f00e9700a60c400f0b00dfc1400f83013b6e00118b009db70012170044c0301473008346501516008104c0171e00f39a7817d6009d8b38189400b433301958004736d02067009db700216a00309b8825c900d98db026f700b1e2d83a19000057a03be9010503403fb600002bd041b300a1d36045de00e131e8480c003820a84a4c014d8b604c9e002ba9806834030700706b75007b7cf0813c00420a188545003583b8896f0109ee808dba03c7d5a8ef19009db700f691013bdd790e6800487cb116db⟩
def q62 : Packed := ⟨⟨62,2508,3800,368639,(-18701),(-18700),1292000,818801299,45746828,5730728221,1585767163,12,7654902040,#[]⟩,166,jumpList 40 0xed1d009cc00195aa80a1a001c87280a6a002418a80abd0020cce80b120072ead00b6a0044cfa80bc50015fc380c84007419f80ce800ad2e680d4f00819a280db901005b980e2600dde3c80f0b010d0b000fff007269f8107f009db7001103009db7001217009db70012a7009db7001473009db70015160017d7201af300d7f1401ca800e6aa001e79006059a025c9002bb9c0296f00c037802aba01d478282c0f013b6e002d6f009d30a830500133562831d200024868336000b3bb203fb60006cf5861fd010e1e20650c035cb1a06b7500a247d06ed0001d8bc09b6d01d839c0ef1901da8048fe450340ffb45708⟩
def q63 : Packed := ⟨⟨63,2508,3800,368639,(-15964),(-15963),1292000,835931445,47928363,5214717967,1646376765,12,7183466897,#[]⟩,166,jumpList 42 0xe460009cc001135200a1a000fbe200a6a002ad6800abd0029dda00b1200224c200b6a007081d00bc500616e900c84007126800ce80076e4600d4f004f23e00e26009991a80e9700855cb80f0b013b6e000f83009db7000fff009db700107f009db7001103009db700118b0009076013d50012ab001473011f3a2015160027ca6015be00704aa0171e004f2aa01ca80001f2e01d8d00ecb1802275013b6e002388009db70024a4013b6e0025c901d9250026f700b376e05f0500eb39a061fd010340406834010ec280813c0042ce00d36a00dfce20e0d500071b70e7db001b82d0ef19006c2af8f69100d671b27ff5002f7e9293f402caeefb3291⟩
def q64 : Packed := ⟨⟨64,2508,3800,368639,(-7755),(-7754),1292000,843668766,15292500,5605426683,1655260633,12,7566407321,#[]⟩,166,jumpList 42 0xbe73009cc001286580a1a002496380a6a001d06f80abd000d64280b12002c03a00b6a0060fc700bc5000b71d80c23008ecad80c8400333d580ce80033a6880d4f003e1f180db9003662300e260135c3380e97009db7000f0b010e29e00f83009db7000fff0033e1401103009db7001217009db700133c009db700171e006a33801958009db7001a22009db7001bca00949f301e790097cbb01f6c00a76bb0206701a9a118216a006663182275015dd9d025c90105a07026f700a3a260282e009db700296f00c090203050000f13203360006744803dc800495cc041b3011ad2406834004d74d09b6d042026c0aa74013a7bb0afc700f01e891f91⟩
def q65 : Packed := ⟨⟨65,2508,3800,368639,(-8288),(-8287),1292000,981433074,26601577,5670217854,1953917828,14,7955702701,#[]⟩,166,jumpList 42 0xc27c009cc001297000a1a0019ffe00a6a001e39200abd002899000b12003987c00b6a004141800bc50050b9400c2300b940400c84000103000ce800e8dbc00d4f008157c00db9000103000e260135d9800e97009db7000f0b009db7000f8300610bc0118b000c858013d5008c4b401473009eba00151600a7ac4015be010a4540166b005db2c0171e005768301894014054581958009044781af3010f8140216a00d8968022750043d1c023880001030024a401339ac02d6f0235d4c02eda000206003050004229c845de006ed0384f0201188d80517a0011a54075d80051b3c07d520239e140896f00ab20408dba0035a9c09b6d01a91140a048⟩
def q66 : Packed := ⟨⟨66,2508,3800,368639,(-158537),(-158536),1292000,585779829,286361842,5680007778,1127157704,9,7365813953,#[]⟩,166,jumpList 31 0x30789009cc002358080a1a003818880a6a00346f080abd00224f900b12004c9a880b6a0054a9080bc500739c100c23006f84080c84008f32900ce801224d200e2600181d080e97013b6e000f0b0057d5881217013b6e00133c013b6e0013d5009db70014730100b9201bca013b6e001ca8013b6e001d8d0071a5c02388009db70024a4013b6e0025c900730e38336000405a483a19012071803be900d2fe803dc8024819003fb6001946c06b75013b6e006ed00276dc007246⟩
def q67 : Packed := ⟨⟨67,2508,3800,368639,(-1451),(-1450),1292000,1248246534,5189857,5189514085,2493086114,18,7995094082,#[]⟩,166,jumpList 52 0xa3df009cc00162fa00a1a001ba7b00a6a002183b00abd002c0fe00b120038f0980b6a004979700bc5002009980c2300606c700c84001072900ce8007439200d4f010156200db90094f0200e260095eab80f0b009db7000f83009db7000fff003eacb812a7009db700133c009655f013d5000f343014730085fa70151600a08200189400002d581958003e38501bca013b9b581ca80004def01d8d00002d581e79003749302067009de458216a016f2cf022750043ed1823880079b7f02d6f00005ab02eda004aa3d8305000625c283857013bc8b03a19014625e03be9022cce483dc8001c10703fb60096114841b3003795c843c000005ab045de002d36c85f05005213188545001339e0896f01a262408dba00eec820922700ea6018fe4501f955d1063701e509c116db018ea3ead3c5009e4b645708⟩
def q68 : Packed := ⟨⟨68,2508,3800,368639,(-20568),(-20567),1292000,808794442,47707838,5610566107,1562752628,12,7507959335,#[]⟩,166,jumpList 36 0xe8b0009cc0013b9000a1a000d02400a6a003034680abd001de4100b1200494e080b6a003c20c00bc500513f000c230014c4c00c84002fad400ce80075de000d4f0104a3000db90036c6000e97013b6e000f0b009db7000f83013b6e000fff009db700107f009db7001103009db700118b013b6e0013d500c37cd81ca8002bca6020670138eb48216a00717190282e01d6a248296f014107502aba0104af30480c00b3fc084a4c013eb5904c9e00cce3084f0200feef88517a026de740854500cb4380896f01cf5e51288d03e31a3a7ff501ec4a7bbab5⟩
def q69 : Packed := ⟨⟨69,2508,3800,368639,(-10761),(-10760),1292000,914280290,28944114,4940220826,1811321493,13,7050548139,#[]⟩,166,jumpList 46 0xc455009cc0012c5080a1a0012e4480a6a0015fde00abd00165e400b1200258e000b6a002bcb480bc50032d8500c23003b0d880c840066a1c80ce800a1af500d4f000150480db9009367100e26009a83080e97009db7000f0b0004e2000fff005362e8107f009db7001103011072d8118b00b23368147300a21408166b00015048171e0035c7b01a22011bffd01af3002d79501bca009f07481ca801dad3081d8d009db7001e79009db7001f6c003654d031d2013f7fa8336000ae04f036a2006831f03a1900095cb85405006b954061fd00a825e8650c000f6098683400773a806b75011d6cc06ed0009db700724600d2553075d800c47990798600585f08896f008beb609b6d01414cc0a54a026d9be0b545⟩
def q70 : Packed := ⟨⟨70,2508,3800,368639,(-118734),(-118733),1292000,624989462,228283501,5021974971,1222074527,9,6722094988,#[]⟩,166,jumpList 38 0x25e62009cc001ff3300a1a00287eb00a6a002ab1300abd0064eb700b1200483bb00b6a000e7e700bc5002b0ef00c23005487a00c84002588600ce800844ab00d4f008cd6300db9002588600e26000e7e700e97009db7000f0b009db7000f83009db7000fff00007050107f013b6e001103009db7001217009db700133c01030ce017d6009db7001894009db7001a220127faf02067011a7030216a006daac825c9006b78983be9013b6e003dc8009db700480c013b6e004a4c010169e85405008787d8595a002c02b05c24005d43005f05000ce1f0650c00bbdde8798601a044a07d52⟩
def q71 : Packed := ⟨⟨71,2508,3800,368639,(-1631),(-1630),1292000,1251683511,4505840,5520781747,2495378709,18,8341312733,#[]⟩,166,jumpList 49 0x9bbe009cc0014e4880a1a001ed5580a6a001894d00abd001de6400b12002c24f80b6a005bd4300bc5002b4a380c23004984b00c840084c4780ce80048a1080d4f0016eae00db9008e80500e26009d84100e97009db7000f0b0091a1400f8300758dc0118b010114801217009db70012a7009db700133c0003f39013d500181eb0171e01910bd017d600a5c8f01958013b3b101a2200216a601af30094a6601bca004f20e02067010c3bd0216a009d84102275005d2f50238800e8b418385700992d384c9e00a0d4a04f02004ca5a8517a01982fb85f050109e1f061fd01b577a075d8007382b0798601a3ba887d52005d9ee8813c01307658854500398ac0afc7013c39e0b545008dc648baef0017e5f8c6cc02f36080cd0200421270d36a006640245708⟩
def q72 : Packed := ⟨⟨72,2508,3800,368639,(-66375),(-66374),1292000,638728073,107277075,4987913029,1237496862,9,6581703371,#[]⟩,166,jumpList 40 0x193cf009cc0019cd780a1a001355380a6a001b82f80abd003076400b1200447f280b6a004e89780bc5001875b80c23004021f80c84003d91b80ce800f7e4f00d4f008783680e2600a3fc780e97000f61800fff005a5500107f00436200110300f80c00118b013b6e001217007c06001516009db700166b007cd1b017d6013b6e0018940085f850216a009db70026f7013b6e00296f009db7002aba009db7002eda001f18f0336000b52ed03a1900fb06a03dc8009db7003fb600eda42045de00a5dbd8480c00fab798517a013b6e0054050074f7307246017f74207986001d0ba9e52a00e049f9f453013134f3f74e⟩
def q73 : Packed := ⟨⟨73,2508,3800,368639,(-1674),(-1673),1292000,1244424365,4261449,5269178949,2493793907,18,8077753238,#[]⟩,166,jumpList 44 0x9906009cc00137c880a1a001bfe780a6a001b98700abd0032f9c00b1200263f780b6a00107df80bc5003e52b80c230019d6300c8400b1d0700ce8002971b80d4f00a84c400e26009db7000f0b009db7000f8300ea40c0107f008468101217009db70012a7009deb50133c00e3d53813d5012986781473001a68381516007ebfd817d600f33f101894000034501958001cda901bca013ba2501ca8013abd601d8d00116a901e79001cb4902d6f006c0a50336001a004a03857009db7003a19013a34503be900a5669041b30023702043c0005f9098517a01b0f908a54a01c36788aa740115ca30afc703368500c6cc000515b0cd02011089f8ef19001ccea93b5f002b7c6164ac⟩
def q74 : Packed := ⟨⟨74,2508,3800,368639,(-19191),(-19190),1292000,826842271,38374934,5878411288,1625769965,12,7842723450,#[]⟩,166,jumpList 37 0xb40f809cc0018b4700a1a001e0d780a6a000985800abd002ee3000b1200415da80b6a001543780bc50050d5780c23003b9df00c8400874e680ce800570dc00d4f005ebff80db900916eb00e26009db7000e97013b6e000f0b009db7000f83009db7000fff006dfc40133c009db70013d5013b6e001473009db70015be009db70017d6009db7001a22009db7001af3013b6e001bca009db7001ca8013dc5b81d8d00995df01f6c012273b02067007b1cd843c001ea867045de0126fde8480c001dcef84a4c0026d7784c9e019c402872460224a76875d801a71a70afc7⟩
def q75 : Packed := ⟨⟨75,2508,3800,368639,(-19997),(-19996),1292000,808410338,47815646,5004038331,1564022295,11,6878598709,#[]⟩,166,jumpList 47 0xb796809cc0013a7280a1a0010f8700a6a0021cf480abd003306680b12003c2e280b6a00301a280bc5006ef4500c23003ff6e80c84000270e80ce800729fa80d4f004f1d180db9008cdea00e26009b46200f0b013b6e000f83009db700118b009db7001217009db70012a7009b462013d50000591017d60055d090189400ff3fa8195800a027e81a2200ee09201bca009877282067009db700227500f277a834fb0022e9a036a20007d0803a19009db7003be9013b6e003fb6006296404a4c0029dea84c9e0170e5504f0202d555d061fd00a027e8650c00439f307d520054f1e0afc7003e0168c0c600f4df08c6cc00194b30e7db02120800ef19008bda60f69100975c810e68032c20a91f9101286289288d0118e1c931d1⟩
def q76 : Packed := ⟨⟨76,2508,3800,368639,(-20306),(-20305),1292000,808776691,41050137,5050618795,1580352534,12,6937260332,#[]⟩,166,jumpList 46 0xb63d009cc0013b0d00a1a0009cd900a6a002471e80abd002dfbb80b12004380600b6a00240c500bc5002a46100c2300bad7a00c84000e3c200d4f0089a5e00db9003301580e260098c1f00e97009db7000f83009db7000fff009db700107f00481198118b0015ae681217009db70012a7009db700133c009db70013d5008b739817d600affa681894008b7398195800326a401ca8005770a01d8d0049aa9822750033b19825c9009af53026f701371c20282e00568e18296f012d31f02aba01175aa82d6f009db700305000aa1e603360001c7ad034fb007f64e036a2013b6e00385700cbbe78540500975720595a00fb7ca89b6d011ae100baef00ab02b0c0c600960d11288d033ef981453a012e5fabd88a⟩
def q77 : Packed := ⟨⟨77,2508,3800,368639,(-6005),(-6004),1292000,1021296202,19354173,4829922624,2027290685,14,7150856029,#[]⟩,166,jumpList 49 0x9c42809cc0011f1e80a1a0018c8100a6a00272f680abd000657980b120039de380b6a00372d280bc5005321680c2300370de80c84004edba80ce8007b2b900d4f000119680db9008ba6280e2600449ad00e97009db7000f0b0038fcf80fff009db700107f009db700118b00689d401217008c60e015be0017ecc0171e009db70017d6000f41401ca8013ab2601d8d011199c82275002fcdd826f70111cd80282e00899280296f009cdb602d6f013b6e002eda00f84a40305000daa04033600058fa4043c00090492045de000a21a0480c02bb18204c9e005d23005405008c610056a50096e0e0595a0003e7a05c240139f6c05f050068008061fd001f9d40650c006726206834007ba7206ed000cf26a0724600ab438075d8001c8e608545029dcbe08dba⟩
def q78 : Packed := ⟨⟨78,2508,3800,368639,(-148294),(-148293),1292000,596228109,229791666,5195862114,1161282390,9,6841221960,#[]⟩,166,jumpList 34 0x1b037009cc002294f00a1a00321ee00a6a0023e3800abd0017d6f00b120065a2600b6a005944f00bc5001352b00c230042cef00c8400f04e600ce800321ee00db900a24da00e2600adfc700e97008b3f100f830081c2c00fff009db7001103009db700133c009db70013d5013b6e00166b009db700171e009db7001958009db7001a22013b6e001af3009db7001e79013b6e001f6c009db700206700449b3034fb00dd12e03a1901496be03dc8002a52983fb60020cd1841b301e553a07d52018b3d61453a0089cac47708⟩
def q79 : Packed := ⟨⟨79,2508,3800,368639,(-1546),(-1545),1292000,1246511514,4013294,4581031747,2503596433,18,7372026620,#[]⟩,166,jumpList 53 0x9553809cc0012f9f80a1a001a0e780a6a001e92b80abd002af5300b120022f7b80b6a002e49780bc50033d3100c230047dae00c8400203a100ce8004e00c00d4f00a193b00db900442e900e97008ee3800f0b010980d0107f013b6e00118b0020a5f012a70000305013d50066c5a01473005c3540166b009de750171e008afe701894002d1f301bca00901c101ca80016d9801d8d00a7cd702275005d84602388009de75024a4011978d82aba002d7fe82d6f012e064030500049137031d20085cce034fb0000a7c038570024fc983a19004da8c83fb60026e85043c000974cf845de006da718480c005216384a4c00965b904f02009a4660517a000635186ed000b991c0724600bc9eb8813c0064c670854501d1f9d8896f01928e108dba009d5670922700901c3096b8003dd920baef02041490c0c600b77618cd02⟩
def q80 : Packed := ⟨⟨80,2508,3800,368639,(-39646),(-39645),1292000,708163675,67997969,5068717803,1394649951,10,6789900444,#[]⟩,166,jumpList 33 0xdc03009cc001784300a1a001e5a300a6a002a12300abd003cd3a00b1200349cc00b6a0049c4200bc5004ebc400c23006981200c84001371e00d4f00296ae00db9009290300e26013a0b300e97009db7000f0b013b6e001103009db7001217013b6e00151600313c80166b009db70019580039a7701a220101c6901ca8005dc2081f6c001f6c60216a009db700227500852dc02388014790e026f702392fb831d2000a0c403fb6013b6e0041b3009db70043c00135c8c8480c027205184a4c009db7004c9e⟩
def q81 : Packed := ⟨⟨81,2508,3800,368639,(-4620),(-4619),1292000,952875997,8519122,5375150520,1881833494,14,7555782511,#[]⟩,166,jumpList 44 0x998e009cc0011f6300a1a001b99900a6a001ddc600abd00295bb00b1200221aa80b6a003c43480bc500282c080c23004f8fd80c840046ebf80ce8002831080d4f009d9f400db9005bcd180e26008c0a280f0b009db7000f83009db7000fff00976380107f000653801103009db700118b013b6e001217009db700133c008bad80147300bb54e01516007b9d501bca0077ec50238800400de8282e013adda8296f00ba91e82aba0026be282c0f016149f82eda02277028305000e18e9031d20088ef1033600143a03834fb00d42590517a013adda8540500a4c888595a013be3905c2400c7a6205f05005125d061fd003aa888e0d500b290a14f63009a77896fd1020537c17b4f⟩
def q82 : Packed := ⟨⟨82,2508,3800,368639,(-17278),(-17277),1292000,833088326,33697662,5648654929,1637110337,12,7610893551,#[]⟩,166,jumpList 42 0xb053009cc001296b00a1a001dd1b00a6a0026da300abd001c79f00b12003b45a00b6a00488b300bc5003f82d80c23003095800c84002490f80ce8006e26280d4f0080df580db90092c8700e97007254d00f83005387b00fff009db700107f009db7001103009db700118b009db7001217009db70012a7013b6e00133c009db7001516013b6e00171e01d925001bca009db7001ca8004a1a9026f7002cf4b0282e00d998e0296f009301b02aba013abb302c0f01d925002d6f009db7002eda0006a0303050009db70031d2002073704f020063a4b0517a01e51ba06b7500511088baef006160d8c0c600e37550c6cc0148b8e0cd0201716e20e0d5⟩
def q83 : Packed := ⟨⟨83,2508,3800,368639,(-1436),(-1435),1292000,1244449753,3791190,4802763214,2487982779,18,7586167041,#[]⟩,166,jumpList 52 0x958a809cc001239d80a1a00149bb80a6a001df9e80abd0031c0680b12002f94f80b6a0021fd200bc5003a68200c230040ad800c84007de8600ce80013f2d80d4f0043cde80db9008b17600e260051c7800f0b000186a00f8300ef0380107f003f68601217011d976012a70022a8f8133c010efd0813d5002c17481473009d8a281516007e7188189400698c481af3009d78881f6c001f51a8206700c6fd90216a0071a04825c900956298296f00fb53c02c0f001ab2b02eda00dfaa2031d20061d8e833600149f6883be9005e72d83dc8012938483fb6009d8a2841b3010b2cb843c000291dc845de01462278480c002dd1387986006fa628854501cbab80896f00895de08dba00e9cf0092270000f60096b8009b59409b6d008fd6013b5f00002ce1453a020355716fd10168cff9872900ea71a99362⟩
def q84 : Packed := ⟨⟨84,2508,3800,368639,(-196244),(-196243),1292000,576599603,265248043,4831034663,1087227610,8,6420240815,#[]⟩,166,jumpList 37 0x20dde009cc0027b3e00a1a0033aa600a6a0014c8200abd004926600b120067b2800b6a005fdae00bc500413ec00c8400fa07a00ce8003a2a400db900a3b9e00e2600adfae00e970056ab80118b00fe4d601516013b6e0015be0064bbc01bca013b6e0020670021f71824a4013b6e0025c901d925002aba009db7002c0f010ae89031d2009db7003360010fd22834fb014065b0650c04edb8006834001e6ce06ed00063ba807986000863e0854501f9cdf0922700325b1096b800322a48e0d5001cbdf9453a003651a1c83600047401d677032ab499e52a0046f29cf708⟩
def q85 : Packed := ⟨⟨85,2508,3800,368639,(-7364),(-7363),1292000,1013172458,18860650,4888862034,1988295524,14,7171104525,#[]⟩,166,jumpList 59 0x9eea009cc001122600a1a00175c200a6a002853e00abd0020cdc80b12002629e80b6a00354fb00bc50039a9600c230020a3200c8400d1ed800ce80000e6200d4f001402480db9000d09f80e260087aa200e97003347f80f0b0056e7080f830045f5380fff000d75e8110300285c60118b01322700121700c493e013d5009e9d201473000bd49815be003a34b01958007446d81a22009592181d8d008fe0681e79009b59a020670076d1a0216a006c716022750058970023880000e62024a400e0a76025c9009e9d2026f700952300282e00773260336000290f6034fb01da0b2036a200a72b803dc80050030043c0002fb520480c007c3c004a4c00d350a04f0200cf57c05c24009ac1a06b750042cb88724600b0f82879860212f3607d5200850060813c0138bbb88545004cd960896f008209d08dba0084136896b8007c1fa09b6d002de620a54a0100b9a0aa7402431fc0afc703195020b5450000e620baef⟩
def q86 : Packed := ⟨⟨86,2508,3800,368639,(-17058),(-17057),1292000,828472102,31674662,5029746249,1608741805,12,6935702251,#[]⟩,166,jumpList 46 0xafe5009cc001212d00a1a001cd0d00a6a001520100abd001adcd00b12002894480b6a0087f2d80bc5005536500c23000215100c840007b4600ce800610bc00d4f008010e00db90092fad00e26009d7a500e97013b6e000f0b009db7000f83000966401103013207c01217004f9f9813d5009db7001473004e176817d6003d66c01a22009db7001af3009d3a001bca00007d001ca8000215101d8d00752a202c0f0105a82831d2002c2cf036a2006722b03857005eb8383a19013b2a283dc8003b90383fb600ead42043c001a42c4045de0029f5184c9e005b5388650c02aad8f0683401c866686b7500adc5c07986011baf387d5200c6a5a08dba020511a8922702c479a896b8009db7009b6d00f73d91f453⟩
def q87 : Packed := ⟨⟨87,2508,3800,368639,(-11093),(-11092),1292000,924997576,22212786,5195536188,1824589360,13,7323143369,#[]⟩,166,jumpList 54 0xa632809cc001158680a1a000d70680a6a001bf7280abd002d0e280b12002463680b6a003018800bc5005365900c23005fb6e80c84003f40380ce8003f5ec00d4f00860b680db9007cc4680e26000cdb300f0b009db7000f830005dee0107f00425e18121700412f8012a7013b6e00133c00015aa813d500587bc0151600c3aae015be0007a480166b00b6432817d60051ad28189400e332101958009db7001a22007189681af300ab0b101bca00a06c501ca8013b6e001d8d013b6e001e79009db7001f6c009db700206700cad9803050003c14d031d20002b5503360002bc208385700861aa84c9e006d46904f0200ad1368595a00d065905c2400355e105f05006dc39061fd003d6f78650c0024aaa0683400b89da06b75017727f86ed00126fd7075d800547be879860007cc49063700304071288d0037ba0131d10362ade93b5f⟩
def q88 : Packed := ⟨⟨88,2508,3800,368639,(-26539),(-26538),1292000,777456861,43799018,5357904898,1506715518,11,7183004262,#[]⟩,166,jumpList 39 0xc269809cc0014f0980a1a000c84580a6a002aab180abd002089580b1200348e580b6a00153d800bc5004890f00c23005b92580c84004641980ce800787e300d4f0004b4500db90090b8200e26012d31c00e9700aee1400f83008c8cc0118b00b337d8121700883628133c013b6e001516009db70015be013b6e00166b009db70017d6009db700189400de90102388009db70024a40065aa80282e006147e02aba001b5f502c0f0274d99831d201cc64983360002bf47036a20070bc98385700d16860480c013b6e004a4c001d2930da05023dc250e0d500b0d7099ffd0519efd1acfc0069eb79ba63⟩
def q89 : Packed := ⟨⟨89,2508,3800,368639,(-1641),(-1640),1292000,1253101156,3357066,5085095685,2490200329,18,7881664939,#[]⟩,166,jumpList 54 0x9524009cc001047800a1a001582580a6a001722680abd0029ab800b12002f7db00b6a004858080bc5002b89080c23005fc8080c84000fa8d00ce800374c400d4f000b63100db9004ed2580e26007d9a300e97005805500f0b0045b1b00fff00d2bed0107f01107600118b002af80012a7009db700133c009d83c013d5012987801473001c5d4015160113cd0015be002cb7482067006066f8216a009d83c022750042dc4024a400f6810025c90039a94026f700e51c802aba009d83c02c0f008762c02eda007b30003fb60118d1004a4c006529804c9e00452a4054050046e600595a011ce0c05c2400c02d8061fd01c564c0724600b8808075d8013bf738813c008218088545006a4a00896f01c16a008dba0150f5409227021baea8a54a00cefcc8aa74015d4ca8baef0053c180c0c6000ffa80ef19016caa019362004c9dc99ffd⟩
def q90 : Packed := ⟨⟨90,2508,3800,368639,(-244808),(-244807),1292000,546685696,289588983,4746672324,1037207437,8,6304823943,#[]⟩,166,jumpList 38 0x26cb8009cc002d63000a1a003a92000a6a0014ba800abd004744000b1200464a000b6a006684000bc5007180800c23001de2400c84005f50400ce80039d6800d4f00c363400db9009ae2400e97004995c00fff009db700118b00067840133c0040c4b013d500025ed01473009db7001516009db700166b009db700171e00ef09801a22009db7001bca009db700206700e4d4b82eda0028c5803050013b6e0034fb01d9250036a20276dc003857000b51c86834001b13806b75014b85006ed001de3f80724601358c0075d801d925007986017d58a1453a014e5eb164ac00085e2cf708⟩
def q91 : Packed := ⟨⟨91,2508,3800,368639,(-6775),(-6774),1292000,1035909707,16505622,4561936085,2050799847,15,6893751007,#[]⟩,166,jumpList 49 0x9dc3809cc001054780a1a00145bb80a6a002320f80abd00164fb80b12003c07f80b6a003224b80bc5003495b80c230000d3b80c84005ba5b80ce8002cc5b80d4f008371380db9008e8cf80e2600513e700e970071f5180f83009db7000fff009db7001103009db700118b0073ce7012a7013b6e00133c0000d3b813d500530840195800366a781a22009e8ab81af300e51b9026f7007046f8282e010b32582aba0000a6682c0f00da5b382eda005945e8305000df1df831d2008fddb0336000143a20517a0001a7705405006cd1085c24017ec1f05f05018d307861fd002fee50650c016d65686834009db7006b7501054e8875d800b4c55879860082f4387d52005938a0a54a000a4420aa74010d2ef0c6cc00aa2da0cd02002a26a1288d04ca5ec931d1⟩
def q92 : Packed := ⟨⟨92,2508,3800,368639,(-20021),(-20020),1292000,817731452,33075944,5062043703,1601268209,12,6962920345,#[]⟩,166,jumpList 42 0xb5ae809cc0013a7e80a1a001cb0680a6a001f9e680abd00047e800b12003345000b6a00192d380bc5003519c00c23005f76d00c840066a9e80ce8002dc6c00d4f00ca17500db90077f0d00e97007099d00f0b013b6e000f8300c016d8118b007116281217002ca0d812a700655e281473009db7001516000bb8001894009db7001958002ca0d81af3009db7001bca00bf48181ca801b09f501d8d008b87681e7900f55dd0216a0069d6682275019d7af834fb009db70036a200a12bd84a4c00cf27e84f0201a15c68517a00e59de8540500d5f108854500372e50896f0067c5208dba00d21d20a04802b230d0a54a00c388bc37080161248c9708⟩
def q93 : Packed := ⟨⟨93,2508,3800,368639,(-10272),(-10271),1292000,926105789,20729950,4479316507,1830154599,13,6582579914,#[]⟩,166,jumpList 48 0xa498009cc001083400a1a001e6dc00a6a001e8d000abd001936e80b120026f0580b6a004a40800bc500559ac00c23000141000c84006c4f400ce8007456200db9008d14880e2600986ec80e97001511d00f0b009db7000f83009db7001103009db700118b009db7001217009db70012a70001410013d5000141001473009db7001516004ba0c015be001138101ca8002a89502067009db7002388013b6e0024a400191d08296f00b261582aba01165a802c0f006d49402d6f0004a64031d2005869d836a2003c80e83be900dfb0503fb601779cd84f02000e3ad85c2400961fc061fd0183b808650c003148886834007ce6986b75011084506ed0013b9df0aa7401660e18afc7011c5040da0500b5e7c0ef1902985140f69100584171c836⟩
def q94 : Packed := ⟨⟨94,2508,3800,368639,(-16798),(-16797),1292000,839117468,28443837,5024604134,1631871526,12,6951178536,#[]⟩,166,jumpList 49 0xaf63009cc001304b00a1a001d45b00a6a001e01300abd001a57b00b12002f95300b6a004a31b00bc50055ab300c23006124b00c8400020cf00ce8006aaa300d4f001af3f00db9000808300e26009e2db00e97006a09f00f8300829d800fff009db700107f009db7001103004ec69012a70098d50013d500fd8a401516009db70015be009db700166b001ca5701af301b51ff01f6c00241bb020670033af10238800ed863024a400e20cb025c90106abb026f7002d62b0282e0021e930296f0049ae103857003ef6b03a19004a70303be900af575041b300e75ec04c9e009db7004f02029d23e0517a0041bed05f0500c4b41061fd01193360650c0067a8f075d80203d830798600542de07d52002a1cf08545005ed9f11f91013110b9ba6303da7a89c836⟩
def q95 : Packed := ⟨⟨95,2508,3800,368639,(-7272),(-7271),1292000,1006182173,16211141,4616766536,1993917357,14,6891322404,#[]⟩,166,jumpList 49 0x9ebc009cc00119c800a1a0015a3c00a6a001584800abd003253800b12001332c00b6a003735800bc500551dc00c230060b6800c840005c5400ce8006f1e000d4f002b0fa00db90000b4e00e2600672ec00e97009db7000f0b009db7000f8300376b800fff009db7001103006d0eb01217009db70012a7009db700133c009db70013d5002a231815be00c98148166b001699701a2200960dc01af30067d0d01bca00ed43701ca8003ad0201e79009cd3c81f6c007cb9082067001299b026f7008cf8802c0f0035ec082d6f0103d1583be900f9c7004a4c00760f08724601a21d1875d8011427e0896f00147680922701a2d240a54a002c60c0aa7401267400cd020091eb00d36a002e3540e0d5030aee00ef19011eb880f69101d4a640fe45000911010637⟩
def q96 : Packed := ⟨⟨96,2508,3800,368639,(-66375),(-66374),1292000,639456910,80457806,5042434803,1236905492,9,6610971722,#[]⟩,166,jumpList 42 0x11037809cc0013f1780a1a001c3e780a6a000e15780abd00242db80b12004503f80b6a0050bbf80bc5005c73f80c2300682bf80c8400061a800ce80015d1f00d4f002979880db9008272900e26012be1900e97009db7000f0b009db7000f83013b6e000fff0030eb08118b0015a378133c00f4df8013d5009db7001516009db70015be009db7001a22009db7001af3013b6e0022750027ee402eda0003d4783050009db70031d200b9a37034fb0040e54843c0016e0ef045de001d30a8480c009db7004a4c01012bf04c9e006f01f8517a005c6458595a01dda1705f0501f812f861fd005582a08dba00f5aca0aa7400d99520e7db0126dc60ef19⟩
def q97 : Packed := ⟨⟨97,2508,3800,368639,(-1547),(-1546),1292000,1261300734,2604075,4811815091,2517564982,18,7625159369,#[]⟩,166,jumpList 48 0x9553009cc000e1dc00a1a001761d80a6a00186f780abd001c52000b120022c7b80b6a00320c280bc50022d8700c23005581300c840067b1700ce8007f4ee00db9009893a00e97013b6e000f0b009db700107f00622500118b009d86b013d5012b01701473009d86b015be002759d0171e00561d7017d6010d51f01bca0011d2801ca8009ba89020670018268026f700744f80296f00ce49a02aba0029a3302eda012dd8903050009054d031d200d4adf036a2015720e0385700cdc8e84c9e0099a1984f02003323585405004940f056a5016eead07986013b6e007d52017974788545009fe138896f0160cb708dba0238b468922700649e00c0c60159aaf10637000f2b8116db00b95e991f91005e99594f6301543c0259c300392c526c91⟩
def q98 : Packed := ⟨⟨98,2508,3800,368639,(-30917),(-30916),1292000,747522954,47203694,5025519421,1457724864,11,6789777762,#[]⟩,166,jumpList 41 0xcaf6809cc001440e80a1a001385680a6a001191680abd00343c680b12000809580b6a00426aa00bc5004e61200c23000c0de00c84005b0de80ce8001bb3280d4f00ec6e300db9000bd9e00e97009db7000f0b009db7000f83009db7000fff009db700107f009db7001103009db700118b009db7001217009db70012a7013b6e0013d5009db7001473004fe7a01e7900799000216a0088676026f701b0a0a0282e011ee020296f00a6c2202aba00265a004f02009db700517a00046a405c24011c30a05f0501adf12061fd023fb1a0650c011e46a8e0d50004e9e8f691000608590637007a6ab1288d032578d964ac00a9a3216fd1⟩
def q99 : Packed := ⟨⟨99,2508,3800,368639,(-12711),(-12710),1292000,879509160,25632884,4853016983,1722808819,13,6864491732,#[]⟩,166,jumpList 47 0xa95b809cc000fd5780a1a001265b80a6a00112e080abd00283b600b120031f0880b6a00479eb80bc5000288e00c230060a3500c84006db4b80ce80079ca780d4f00018d380db90039fa280e26009db7000e97009db7000f0b009db7000fff008ced4812170094fd7812a7009db700133c0017d6d013d50096dcf0166b00622e10171e0044845017d600509a101894009c29d0195800cf8e101a22011292501af3009c29d01bca009c29d01ca80139e0d01d8d009db7001e790095bfa0305000383be8517a00919ba85f05009db70061fd001a8ab06ed002329220724600662df0896f009b3ff0afc700c7f880b54502611f00fe45008808a159de00252d5964ac00dd06917b4f023b0ac98729021c2cb1936200947d319ffd⟩
def q100 : Packed := ⟨⟨100,2508,3800,368639,(-39646),(-39645),1292000,714875821,54398376,4743333075,1388687310,10,6431699587,#[]⟩,166,jumpList 45 0xdc03009cc001513300a1a001496300a6a002aae700abd000014300b12003b53800b6a00258df00bc5005604300c23006239300c84000c74580ce80064fc080d4f0009f1280db900681b780e2600a0f7b00e97005c4fc80f0b009db7000f83004167380fff009db700107f013b6e001103001217c8133c000846381473009570c81516009db70015be009db7001894001211001958009db7001af3009db7001ca8002226f822750076c84825c9003330d826f7006d0d58282e017d4ff03360009db70034fb009db70036a2009db70038570127cf583fb601d9250041b30138e6e0480c00df56805405016440c0afc701db4160b54500189701f4530040416235d90011f8c5570802de9fe57708⟩
def q101 : Packed := ⟨⟨101,2508,3800,368639,(-1462),(-1461),1292000,1255414834,2368559,5159403068,2482151507,18,7949585335,#[]⟩,166,jumpList 53 0x957d809cc000e97980a1a0015a4e00a6a001b77400abd001efa500b12003637d00b6a001078600bc50050c1180c23003efa980c84002a41580ce80007e0d80d4f008369d80db9003cfa980e97009db7000f0b006e2c580f83006c16a80fff009db70011030031a058121700b2d53812a70091cef0147300abd4081516008e7c10195800d12c181a220113f1d81af300b883981bca0001f6701ca80015bcf01f6c00feeb902067009db700216a00002db0227500005b6024a4017e617025c90067733026f700c4a8002eda011048903be9018984783fb60045996043c00129bd3045de00f3d988480c006ce5704a4c009d89584c9e00fe48304f020025cb88517a0089d13056a5009db700595a0051f0c8798602ddc348e0d5001e360916db00ce40f931d1023dc1b13b5f02e88bd159de00008e0164ac035e4e316fd1⟩
def q102 : Packed := ⟨⟨102,2508,3800,368639,(-135146),(-135145),1292000,618286898,162452102,4819427613,1166221518,9,6387527208,#[]⟩,166,jumpList 42 0x19689009cc00165b500a1a002add500a6a001f01800abd001aa1100b12004616100b6a004308d00bc5004904100c2300693e100c840075b1900ce8008225100d4f007b92200e2600a7fc900e97009db7000f83002ab980107f000d8cc011030059dec8121700364b7812a7009db700133c009db70013d5009db700147300676b881bca00e1f3c0282e009db700296f00779a382c0f0149994031d2003f61a0336001cbbc1034fb01406c683be9009db7003dc8005c7e703fb600b948f841b300f2e27045de004a4f005f05002d722061fd01ed6d10650c0276dc00683401eafc106b75009db7006ed001dfab019ffd034fb099acfc009db701ba63⟩
def q103 : Packed := ⟨⟨103,2508,3800,368639,(-1455),(-1454),1292000,1258100962,2276810,4843754896,2513554177,18,7653878264,#[]⟩,166,jumpList 58 0x9581009cc000fcaa00a1a0014edf80a6a0016fb880abd00275f900b120027af180b6a0024ebb80bc50037f6b80c23001487b80c84005913f80ce8007a00f80d4f0029ed000db9009173d00e2600241f200e97007997e00f0b009db7000f83009683401103007178501217009db70012a7009db700133c00974fd013d50032e7401473009d899015be00293450166b005ad4e017d600639c101e7900002d781f6c0057e130216a009db7002275008e3ee824a400bd386026f700a53d30296f01b2b4202aba00c585602d6f005c3ad02eda001894f041b3009d899043c000673a3045de0073b090480c009db7004a4c008b67e05f050083bc8061fd0113a560650c004a4bf06834001df3c06ed0000b6e30724600fb2d3075d800b84b107986024a3fc08545005fefd08dba008699c8c0c6006d6640e7db00c4347131d101d10e113b5f00a86c49936200fd07b19ffd001c12c9c8360083ed49e52a⟩
def q104 : Packed := ⟨⟨104,2508,3800,368639,(-23789),(-23788),1292000,793880747,35102306,4776493120,1553198705,11,6617981815,#[]⟩,166,jumpList 46 0xbd0a809cc000fb8a80a1a0017e6680a6a001a38280abd001c67a00b12003a40e00b6a002f91500bc500437aa80c23005359280c840069cf280ce8007681280d4f000fb4700e26008b5e880e97009db7000f0b007361d80fff009db70011030029f76813d5013b6e00151600997a3815be00043cc817d600483458189400b5e28019580064c4e81a22013b6e001af30038f2181bca004248c01d8d014a7f001e79002e950025c90041fd1026f70025b1a8282e009db700296f00b6b6a82aba00acec1031d2017267f836a2007160a838570080243043c00023595045de0030d248517a00e807a854050020c7109227017ed2f09b6d013b6e00a04803851920afc701171260baef005670319ffd00cce28d5708⟩
def q105 : Packed := ⟨⟨105,2508,3800,368639,(-59306),(-59305),1292000,709473710,100109487,4017610679,1378401687,10,5711962358,#[]⟩,166,jumpList 45 0x1045d009cc00121a900a1a00246a100a6a0009ecd00abd002f1e800b12003293100b6a001fa7500bc5004271900c2300030d400c8400517ee00ce8002c11400d4f0068cfa00db90096ac100e26003a98000e97006a5c500f0b009db7000f83009db7000fff009db700107f003379f0121700323718133c009db70013d5003800d8195800dc40901a2200c9db601af3000afbd034fb001b4be03857001026903a19015629c03dc8013b6e003fb6009db7004a4c01e19ad04c9e009db7004f0200565750595a009afd4072460128a18079860139f8e09227003f25d096b801951870afc700f22920b5450118e038f691019085e8fe4500eebb51288d000497b1d677015d06421414005409ea7ff5⟩
end FR7022TwoStage
namespace FR7022Second
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def sign (k : Nat) : Int := if (0x888a2644084c2cc640040aca00e088802e602ac2882040080e88280c424a0482c0400a42068662c402040ca04ca0882c860a644e8a022006a02640c06c2600ac82a662a0c086ca4c84c4a4e6608020464aa8c8e880620ceeec602286c220e888e84224a84acce66064c0a860aa4a42c4686062406c8cc062c08884e8a0400a082806a00c80e00e00062000020060206a0e40a8c4c86c8468662acec402022400ea28268e8ac4e0e4a24c0e2c0ca084088400460e82044082caa80e4008288080c6226004ac0e84428ce4e26ca0a82a0404cca002e484006284480ae642c42c04240c82e242caa402ee428a8c2482e80c044206280ae8606a40c8ae0228466e24820888c4668c800aa0c28024ca4e8280c4040804e202422a0c04268284662862004462262240026040068c2e22aac808682cae8a26446a044864640288e2e08a444c0c48acc8e40242a0ac2a6ea0468cc0284006a2080a80ce20080408c84a22486060c8a088644e26422ca240c0e6440a0c488006a08cc6a22c0cc84a2602480a660c8ec6a284a84082000e24c0480020a4a824648686c6a0c0acc262222642a44468e0200842a8884ec4620824480428c6ca8422ec8880440a48628028042ee66e040a860042c806e0620cc88400e8e42422468840ce0460c442:Nat).testBit k then 1 else if (0x2644c802e28002282e888424620a6466c00e800c6680aae0e06646a00ca4e2082caec42c88488c2060e8e24a220e04c260e088a0446c8ac80ec0aa0c82c86e024440844a286820202a024a0088640ea8240206064688e000020e84482cc2022404ac4a068402000a882e060e0484ac22828084a402220a88266068044e2ca44646e04aa06a0e40aec8ce66e8e48e8e00808e442222804a860804002aa4c848460446804064220a0848a26080c24e60e268ee28202c8aae640044e0266686466e20888cea4060288c420208000e4604aaca0246e0086aee042a80e000a82842e84aa24c0c242048ac002c00424a6402e0e2ac2080c40684800c06406c860880c228e4260a00224ea0402068ca20202c4c28e2e2e804ec0c84c2aac0684808c60cae8a8480c8a8cc8e2c8842c0c440246486420044c08280e8a68a0aa0460c0260a8a0e22202060a64284c4284000e086226c2ace00466a04a20c6c0e8a626248c860e84220c668200888cc244aa2400aa6000846ce04a60284c422206a480e82480886220080c6242ac68ee40880ea6c6ca48424a0a280820440a40248c4888844aa2820ccee42c0646a0228864c0a62a02080462c800246e22a4868842c2e8c00800aac46864a824a00e0c80066ae20208c2cc28208e20e08a28ac:Nat).testBit k then -1 else 0
def base (k : Nat) : Int := sign k * (min 1292 (3800-k):Nat)
def extra (k : Nat) : Int := if 2508<k ∧ k≤3800 then 1 else 0
def radix : Int := 2^64
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def bitsum : Nat → Nat → (Nat → Int) → Int
  | 0,s,f => f s
  | d+1,s,f => bitsum d s f + bitsum d (s+2^d) f
def low (b : Nat) := 4096*b+1
def len (b : Nat) := min 4096 (368640-low b)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def geo (start n k : Nat) : Int :=
  let r := (k-start % k) % k
  let m := if r<n then (n-1-r)/k+1 else 0
  if m=0 then 0 else if m=1 then radix^r else radix^r*((radix^(k*m)-1)/(radix^k-1))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def repeatNat (gap : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 1 + (repeatNat gap n <<< gap)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem repeat_prod (gap n : ℕ) :
    (repeatNat gap n:ℤ) * ((2:ℤ)^gap-1) = 2^(gap*n)-1 := by
  induction n with
  | zero => simp [repeatNat]
  | succ n ih =>
    simp only [repeatNat,Nat.shiftLeft_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat,
      Nat.mul_succ,pow_add]
    calc
      _ = 2^gap*((repeatNat gap n:ℤ)*(2^gap-1))+(2^gap-1) := by ring
      _ = _ := by rw [ih]; ring
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem repeat_eq (gap n : ℕ) (hg : 0<gap) :
    (repeatNat gap n:ℤ) = ((2:ℤ)^(gap*n)-1)/(2^gap-1) := by
  rw [←repeat_prod,Int.mul_ediv_cancel]
  have := one_lt_pow₀ (by decide : (1:ℤ)<2) hg.ne'
  omega
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def manyHits (r k m : ℕ) : ℤ :=
  let top := ((1:ℤ) <<< (64*(k*m))) - 1
  let bot := ((1:ℤ) <<< (64*k)) - 1
  (top / bot) <<< (64*r)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def geoFast (start n k : ℕ) : ℤ :=
  let r := (k-start % k) % k
  let m := if r<n then (n-1-r)/k+1 else 0
  if m=0 then 0 else if m=1 then (1:ℤ) <<< (64*r) else
    if m≤16 then ((repeatNat (64*k) m <<< (64*r):ℕ):ℤ) else
    manyHits r k m
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem geoFast_eq (start n k : ℕ) (hk : 0<k) : geoFast start n k = geo start n k := by
  let r := (k-start % k) % k
  let m := if r<n then (n-1-r)/k+1 else 0
  change (if m=0 then 0 else if m=1 then (1:ℤ) <<< (64*r) else
    if m≤16 then ((repeatNat (64*k) m <<< (64*r):ℕ):ℤ) else
    manyHits r k m) =
    (if m=0 then 0 else if m=1 then radix^r else radix^r*((radix^(k*m)-1)/(radix^k-1)))
  by_cases h0 : m=0
  · simp only [ite_eq_left h0]
  by_cases h1 : m=1
  · simp [h1,Int.shiftLeft_eq,radix,pow_mul]
  simp only [ite_eq_right h0,ite_eq_right h1]
  by_cases hm : m≤16
  · rw [ite_eq_left hm, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      repeat_eq _ _ (Nat.mul_pos (by decide : 0<64) hk)]
    simp only [radix,pow_mul]
    exact mul_comm _ _
  · rw [ite_eq_right hm]
    simp only [manyHits,Int.shiftLeft_eq,one_mul,radix,pow_mul]
    exact mul_comm _ _
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def blockWord (f : Nat → Int) (b : Nat) : Int :=
  bitsum 12 1 (fun k => let c:=f k; if c=0 then 0 else c*geo (low b) (len b) k)
open Finset FR7022Lane
def totalLen (b : ℕ) := min (4096*b) 368639
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def original (f : ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ k ∈ Ico 1 4097, if k ∣ i+1 then f k else 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem bitsum_spec (d a : ℕ) (f : ℕ → ℤ) :
    bitsum d a f = ∑ i ∈ range (2^d), f (a+i) := by
  induction d generalizing a with
  | zero => simp [bitsum]
  | succ d ih => rw [bitsum,ih,ih,pow_succ,Nat.mul_two,sum_range_add]; simp [Nat.add_assoc]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def blockFast (f : Nat → Int) (b : Nat) : Int :=
  bitsum 12 1 (fun k => let c:=f k; if c=0 then 0 else c*geoFast (low b) (len b) k)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem blockWord_eq_fast (f : Nat → Int) (b : Nat) : blockWord f b = blockFast f b := by
  rw [blockWord,blockFast,bitsum_spec,bitsum_spec]
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [geoFast_eq (low b) (len b) (1+k) (by omega)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem source_block (f : ℕ → ℤ) (b : ℕ) :
    eval radix (len b) (fun i => original f (4096*b+i)) = blockWord f b := by
  unfold original
  have e := divisor_block (Ico 1 4097) f radix (by decide) (low b) (len b) (fun k h => (mem_Ico.mp h).1)
  change eval radix (len b) (fun i => ∑ k ∈ Ico 1 4097, if k ∣ 4096*b+i+1 then f k else 0) = _
  have ix (i : ℕ) : 4096*b+i+1 = low b+i := by unfold low; omega
  simp only [ix]
  rw [e,sum_Ico_eq_sum_range, blockWord,bitsum_spec]
  apply sum_congr rfl; intro j _
  dsimp only
  split_ifs with h
  · simp [h]
  · rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem base_above (k : ℕ) (hk : 3800<k) : base k=0 := by simp [base, Nat.sub_eq_zero_of_le hk.le]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def fastAssemble (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | b+1 => fastAssemble f b + (blockFast f b <<< (64*(4096*b)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem source_pieces (f : ℕ → ℤ) (b : ℕ) (hb : b≤90) :
    eval radix (totalLen b) (original f) = fastAssemble f b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hn : totalLen b=4096*b := by unfold totalLen; omega
    have hl : totalLen (b+1)=totalLen b+len b := by unfold totalLen len low; omega
    rw [hl,eval_split,ih (by omega),fastAssemble,hn]
    apply congrArg (fun z : ℤ => fastAssemble f b + z)
    have ex : (fun i => original f (i+4096*b)) = (fun i => original f (4096*b+i)) :=
      funext (fun i => by rw [Nat.add_comm i])
    rw [ex,source_block,blockWord_eq_fast,Int.shiftLeft_eq]
    simp only [radix,pow_mul]
    exact mul_comm _ _
def fastBase := fastAssemble base 90
def fastExtra := fastAssemble extra 90
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem fastBase_spec : eval radix 368639 (original base) = fastBase :=
  source_pieces base 90 (by decide)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem fastExtra_spec : eval radix 368639 (original extra) = fastExtra :=
  source_pieces extra 90 (by decide)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem original_linear (u v : ℤ) (f g : ℕ → ℤ) (i : ℕ) :
    original (fun k => u*f k+v*g k) i = u*original f i+v*original g i := by
  unfold original
  rw [mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro k _
  split_ifs <;> simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem globalWeighted_spec (u v : ℤ) :
    eval radix 368639 (original (fun k => u*base k+v*extra k)) = u*fastBase+v*fastExtra := by
  rw [←fastBase_spec,←fastExtra_spec,eval_eq_sum,eval_eq_sum,eval_eq_sum,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [original_linear]
  ring
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def increment (u v scale : ℤ) (t : ℕ) : ℤ :=
  original (fun k => u*base k+v*extra k) (t-1) - (if t=1 then scale else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem correctedWord (u v scale : ℤ) :
    eval radix 368639 (fun i => increment u v scale (i+1)) =
      u*fastBase+v*fastExtra-scale := by
  have eqf : (fun i => increment u v scale (i+1)) =
      (fun i => original (fun k => u*base k+v*extra k) i - if i=0 then scale else 0) := by
    funext i
    simp [increment]
  rw [eqf,eval_sub,globalWeighted_spec,eval_eq_sum]
  simp [mul_ite,Finset.sum_ite_eq']
end FR7022Second
namespace FR7022TwoStage
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def increases (r : Packed) : List (Nat×Nat) := r.rises
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def integerWordWith (x y : ℤ) (r : Packed) (a : Int) : Int :=
  1000*x+a*y-Int.ofNat r.params.scale
def integerWord := integerWordWith FR7022Second.fastBase FR7022Second.fastExtra
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def certifiedWith (x y : ℤ) (r : Packed) (a : Int) : Bool :=
  FR7022Verified.fastVerify r.params.B r.params.q ((r.params.B/r.params.q).log2+1)
    (integerWordWith x y r a) (increases r)
def certified := certifiedWith FR7022Second.fastBase FR7022Second.fastExtra
def oneRow (x y : ℤ) (r : Packed) := certifiedWith x y r r.params.alphaLo && certifiedWith x y r r.params.alphaHi
end FR7022TwoStage
namespace FR7022Rational
structure Poly where
  d : Int
  a : Int
  e : Int
def clip (m : Nat) : Int → Int
  | .ofNat a => Int.ofNat (a &&& m)
  | .negSucc a => -Int.ofNat ((a+1) &&& m)
def withNat {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)
def withInt {α : Type} (x : Int) (f : Int → α) : α :=
  match x with
  | .ofNat n => withNat n (fun a => f (.ofNat a))
  | .negSucc n => withNat n (fun a => f (.negSucc a))
def withPoly {α : Type} (x : Poly) (f : Int → Int → Int → α) : α :=
  withInt x.d (fun d => withInt x.a (fun a => withInt x.e (f d a)))
def merge (m : Nat) (x y : Poly) : Poly :=
  withPoly x (fun d a e => withPoly y (fun g b f =>
    ⟨clip m (d*g),clip m (a*g+b*d),clip m (e*g+f*d)⟩))
def inv (d : Int) (w : Nat) : Nat → Int
  | 0 => 1
  | h+1 =>
    let m : Int := Int.ofNat (1 <<< (min w (2^(h+1))))
    withInt (inv d w h) (fun v => (v*(2-(d % m)*v)) % m)
theorem withNat_eq {α} (x : Nat) (f : Nat → α) : withNat x f = f x := by cases x <;> rfl
theorem withInt_eq {α} (x : Int) (f : Int → α) : withInt x f = f x := by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl
theorem withPoly_eq {α} (x : Poly) (f : Int → Int → Int → α) :
    withPoly x f = f x.d x.a x.e := by simp [withPoly,withInt_eq]
theorem clip_spec (w : Nat) (x : Int) : clip (2^w-1) x ≡ x [ZMOD (2:ℤ)^w] := by
  cases x with
  | ofNat n =>
    simpa [clip,Nat.and_two_pow_sub_one_eq_mod,Int.natCast_emod] using (Int.mod_modEq (n:ℤ) (2^w))
  | negSucc n =>
    change -((↑((n+1) &&& (2^w-1)):ℤ)) ≡ -((↑(n+1):ℤ)) [ZMOD (2:ℤ)^w]
    apply Int.neg_modEq_neg.mpr
    simpa [Nat.and_two_pow_sub_one_eq_mod,Int.natCast_emod] using (Int.mod_modEq (↑(n+1):ℤ) (2^w))
private theorem merge_col (w : Nat) (d g a b X Y : ℤ)
    (hx : d*X ≡ a [ZMOD (2:ℤ)^w]) (hy : g*Y ≡ b [ZMOD (2:ℤ)^w]) :
    clip (2^w-1) (d*g) * (X+Y) ≡ clip (2^w-1) (a*g+b*d) [ZMOD (2:ℤ)^w] := by
  calc
    _ ≡ (d*g)*(X+Y) [ZMOD (2:ℤ)^w] := (clip_spec _ _).mul_right _
    _ = (d*X)*g+(g*Y)*d := by ring
    _ ≡ a*g+b*d [ZMOD (2:ℤ)^w] := (hx.mul_right _).add (hy.mul_right _)
    _ ≡ _ [ZMOD (2:ℤ)^w] := (clip_spec _ _).symm
def Represents (w : ℕ) (v : Poly) (x y : ℤ) : Prop :=
  v.d*x ≡ v.a [ZMOD (2:ℤ)^w] ∧ v.d*y ≡ v.e [ZMOD (2:ℤ)^w] ∧ v.d ≡ 1 [ZMOD 2]
theorem merge_represents (w : Nat) (hw : 0 < w) (l r : Poly) (a b c d : ℤ)
    (hl : Represents w l a b) (hr : Represents w r c d) :
    Represents w (merge (2^w-1) l r) (a+c) (b+d) := by
  simp only [merge,withPoly_eq,Represents]
  refine ⟨merge_col _ _ _ _ _ _ _ hl.1 hr.1,merge_col _ _ _ _ _ _ _ hl.2.1 hr.2.1,?_⟩
  have e : (2:ℤ) ∣ 2^w := by simpa using (pow_dvd_pow (2:ℤ) (show 1 ≤ w by omega))
  exact ((clip_spec _ _).of_dvd e).trans (by simpa using hl.2.2.mul hr.2.2)
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
namespace FR7022Narrow
open FR7022Rational
open FR7022Second FR7022Lane Finset
def countN := 368639
def narrow : ℤ := 2^18
def width := 18*countN
def word (f : ℕ → ℤ) (k : ℕ) := f k * divisorWord narrow 1 countN k
theorem den_leaf (k : ℕ) (hk : 0 < k) (hu : k≤8192) :
    (1-narrow^k) * divisorWord narrow 1 countN k ≡ narrow^(k-1) [ZMOD (2:ℤ)^width] := by
  have hn : 2*k ≤ countN := by dsimp [countN]; omega
  have rk : firstOffset 1 k=k-1 := by
    unfold firstOffset
    by_cases h1 : k=1
    · simp [h1]
    · simp [Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt (show k-1 < k by omega)]
  have hits : numHits (k-1) k countN = countN/k := by
    unfold numHits
    rw [ite_eq_left (by omega),show countN-1-(k-1)=countN-k by omega]
    rw [← Nat.add_div_right _ hk,Nat.sub_add_cancel (by omega)]
  have hm : 2 ≤ countN/k := (Nat.le_div_iff_mul_le hk).mpr hn
  have nz : narrow^k-1 ≠ 0 := by
    have := one_lt_pow₀ (by decide : (1:ℤ) < narrow) hk.ne'
    omega
  rw [divisorWord,rk,hits,ite_eq_right (by omega),ite_eq_right (by omega)]
  rw [pow_mul,← geom_sum_mul (narrow^k) (countN/k),Int.mul_ediv_cancel _ nz]
  have hnext : countN ≤ (k-1)+k*(countN/k) := by
    have := Nat.mod_add_div countN k
    have := Nat.mod_lt countN hk
    omega
  apply Int.modEq_iff_dvd.mpr
  have dd := pow_dvd_pow narrow hnext
  have rm : (2:ℤ)^width = narrow^countN := by simp [width,narrow,pow_mul]
  rw [rm]
  convert dd using 1
  rw [pow_add,pow_mul]
  have geom := geom_sum_mul (narrow^k) (countN/k)
  linear_combination (narrow^(k-1)) * geom
def column18 {α : Type} (m : Nat) : Nat → Nat → (Int → Int → α) → α
  | 0,i,fn =>
    let k := 2*i+1
    let c := base k
    let e := base (2*k)
    if e=0 then
      if c=0 then fn 1 0 else
        withInt (1-((1:Int)<<<(18*k))) (fun d => withInt (c<<<(18*(k-1))) (fn d))
    else
      withInt (1-((1:Int)<<<(36*k))) (fun d =>
        withInt ((c<<<(18*(k-1)))+((c+e)<<<(18*(2*k-1)))) (fn d))
  | h+1,k,fn =>
    column18 m h k (fun d a => column18 m h (k+2^h) (fun g b =>
      withInt (clip m (d*g)) (fun D => withInt (clip m (a*g+b*d)) (fn D))))
def rawAt (w : Nat) : Int :=
  let M : Nat := 1<<<w
  withNat (M-1) (fun m => column18 m 11 0 (fun d a =>
    withInt (inv d w ((w-1).log2+1)) (fun v => (a*v) % (M:Int))))
def base18 := rawAt (18*368639)
private theorem above (k : ℕ) (h : 3800 < k) : word base k=0 := by simp [word,base_above k h]
set_option maxRecDepth 10000 in
private theorem four_table : ∀ i : Fin 951, base (4*(i:ℕ))=0 := by decide +kernel
private theorem four (k : ℕ) : word base (4*k)=0 := by
  by_cases h : k<951
  · simp [word,four_table ⟨k,h⟩]
  · exact above _ (by omega)
private theorem split_two (s : ℕ) (f : ℕ→ℤ) :
    (∑ j ∈ range (2*s), f j)=∑ k ∈ range s, (f (2*k)+f (2*k+1)) := by
  induction s with
  | zero => simp
  | succ s ih => rw [Nat.mul_succ,sum_range_succ,sum_range_succ,ih,sum_range_succ]; ring
private theorem reorder : (∑ j ∈ range 4096, word base (j+1)) =
    ∑ i ∈ range 2048, (word base (2*i+1) + word base (2*(2*i+1))) := by
  have h := split_two 2048 (fun i => word base (i+1))
  have g := split_two 1024 (fun i => word base (2*i+1+1))
  have z (i : ℕ) : 2*(2*i+1)+1+1 = 4*(i+1) := by omega
  have a (i : ℕ) : 2*(2*i)+1+1 = 2*(2*i+1) := by omega
  simp only [z,a,four,add_zero] at g
  rw [h,sum_add_distrib,sum_add_distrib,g]
  apply congrArg (fun v : ℤ => (∑ i ∈ range 2048, word base (2*i+1))+v)
  apply sum_subset
  · exact range_mono (by decide)
  · intro i hi hn; simp only [mem_range] at *; exact above _ (by omega)
def value (i : ℕ) := word base (2*i+1)+word base (2*(2*i+1))
def pairLeaf (i : ℕ) : Poly :=
  let k:=2*i+1
  let c:=base k
  let e:=base (2*k)
  if e=0 then
    if c=0 then ⟨1,0,0⟩ else ⟨1-((1:ℤ)<<<(18*k)), c<<<(18*(k-1)), 0⟩
  else ⟨1-((1:ℤ)<<<(36*k)),(c<<<(18*(k-1)))+((c+e)<<<(18*(2*k-1))),0⟩
private theorem odd_d (q : ℕ) (hq : 0 < q) : 1-narrow^q ≡ 1 [ZMOD 2] := by
  apply Int.modEq_iff_dvd.mpr
  simpa using (by decide : (2:ℤ)∣narrow).trans (by simpa using pow_dvd_pow narrow (show 1 ≤ q by omega))
theorem leaf_good (i : ℕ) (hi : i<2048) : Represents width (pairLeaf i) (value i) 0 := by
  let k:=2*i+1
  have kp : 0 < k := by dsimp [k]; omega
  have hp : 2*k≤8192 := by dsimp [k]; omega
  have wf (j : ℕ) (hj : 0 < j) (hu : j≤8192) :
      (1-narrow^j)*word base j ≡ base j*narrow^(j-1) [ZMOD (2:ℤ)^width] := by
    calc
      _ = base j*((1-narrow^j)*divisorWord narrow 1 countN j) := by unfold word; ring
      _ ≡ _ [ZMOD (2:ℤ)^width] := (den_leaf j hj hu).mul_left (base j)
  have hk := wf k kp (by omega)
  have hh := wf (2*k) (by omega) hp
  have sh (x : ℤ) (j : ℕ) : x<<<(18*j)=x*narrow^j := by rw [Int.shiftLeft_eq,pow_mul]; rfl
  have ds : 1-((1:ℤ)<<<(36*k))=1-narrow^(2*k) := by
    rw [show 36*k=18*(2*k) by omega,sh,one_mul]
  dsimp only [pairLeaf,value]
  change Represents width (if base (2*k)=0 then
    if base k=0 then ⟨1,0,0⟩ else ⟨1-((1:ℤ)<<<(18*k)),base k<<<(18*(k-1)),0⟩
    else ⟨1-((1:ℤ)<<<(36*k)),(base k<<<(18*(k-1)))+((base k+base (2*k))<<<(18*(2*k-1))),0⟩)
    (word base k+word base (2*k)) 0
  by_cases eh : base (2*k)=0
  · rw [ite_eq_left eh]
    have ez : word base (2*k)=0 := by simp [word,eh]
    rw [ez,add_zero]
    by_cases ch : base k=0
    · rw [ite_eq_left ch,show word base k=0 by simp [word,ch]]
      exact ⟨by simp,by simp,.refl _⟩
    · rw [ite_eq_right ch,sh,sh,one_mul]
      exact ⟨hk,by simp,odd_d _ kp⟩
  · rw [ite_eq_right eh,ds,sh,sh]
    refine ⟨?_,by simp,odd_d _ (by omega)⟩
    have prod : narrow^k*narrow^(k-1)=narrow^(2*k-1) := by rw [←pow_add]; congr 1; omega
    have sq : narrow^(2*k)=narrow^k*narrow^k := by rw [two_mul,pow_add]
    calc
      _ = (1+narrow^k)*((1-narrow^k)*word base k)+(1-narrow^(2*k))*word base (2*k) := by rw [sq]; ring
      _ ≡ (1+narrow^k)*(base k*narrow^(k-1))+base (2*k)*narrow^(2*k-1) [ZMOD (2:ℤ)^width] :=
        (hk.mul_left _).add hh
      _ = _ := by linear_combination (base k)*prod
def table (m : ℕ) : ℕ→ℕ→Poly
  | 0,k => pairLeaf k
  | h+1,k => merge m (table m h k) (table m h (k+2^h))
theorem table_correct (h k : ℕ) (hk : k+2^h≤2048) :
    Represents width (table (2^width-1) h k) (binarySum h k value) 0 := by
  induction h generalizing k with
  | zero => exact leaf_good k (by simp at hk; omega)
  | succ h ih =>
    simp only [table,binarySum]
    rw [pow_succ] at hk
    simpa only [add_zero] using merge_represents width (by decide) _ _ _ 0 _ 0
      (ih k (by omega)) (ih _ (by omega))
theorem column_correct {α : Type} (m h k : Nat) (fn : Int → Int → α) :
    column18 m h k fn=fn (table m h k).d (table m h k).a := by
  induction h generalizing k fn with
  | zero =>
    simp only [column18,table,pairLeaf,withInt_eq]
    split_ifs <;> rfl
  | succ h ih => simp only [column18,ih,table,merge,withInt_eq,withPoly_eq]
theorem global_sum : binarySum 11 0 value=eval narrow countN (original base) := by
  unfold original
  have t := divisor_block (Ico 1 4097) base narrow (by decide) 1 countN (fun k h => (mem_Ico.mp h).1)
  rw [show (fun i => ∑ k ∈ Ico 1 4097, if k ∣ i+1 then base k else 0) =
    (fun i => ∑ k ∈ Ico 1 4097, if k ∣ 1+i then base k else 0) from funext (fun i => by rw [Nat.add_comm i]),t,
    sum_Ico_eq_sum_range,binarySum_spec]
  simpa only [zero_add,value,word,Nat.add_comm 1,show 2^11=2048 by decide,show 4097-1=4096 by decide] using reorder.symm
theorem rawAt_eq (w : ℕ) : rawAt w =
    let s := table (2^w-1) 11 0
    (s.a*inv s.d w ((w-1).log2+1)) % (2:ℤ)^w := by
  simp only [rawAt,withNat_eq,column_correct,withInt_eq,Nat.shiftLeft_eq,one_mul,Nat.cast_pow,Nat.cast_ofNat]
private theorem extract (M d v X a : ℤ) (h : d*X ≡ a [ZMOD M]) (iv : d*v ≡ 1 [ZMOD M]) :
    (a*v) % M ≡ X [ZMOD M] := by
  calc
    _ ≡ a*v [ZMOD M] := Int.mod_modEq _ _
    _ ≡ (d*X)*v [ZMOD M] := h.symm.mul_right _
    _ = X*(d*v) := by ring
    _ ≡ X*1 [ZMOD M] := iv.mul_left X
    _ = _ := mul_one _
theorem base18_spec : base18 ≡ eval narrow countN (original base) [ZMOD (2:ℤ)^width] := by
  have h := table_correct 11 0 (by decide)
  rw [global_sum] at h
  have hi := inv_spec _ _ 23 (by decide : 0 < width) h.2.2
  rw [min_eq_left (by decide : width≤2^23)] at hi
  rw [base18,show 18*368639=width from rfl,rawAt_eq,show (width-1).log2+1=23 by decide]
  exact extract _ _ _ _ _ h.1 hi
end FR7022Narrow
namespace FR7022Separated
open FR7022Second FR7022Lane Finset
def unit64 (n m : Nat) :=
  let t:=min 3800 (n/m)-2508
  if t=0 then 0 else ((1<<<(64*m*t))-1) / ((1<<<(64*m))-1)
def extraSum (n : Nat) : Nat → Nat → Nat
  | 0,m => unit64 n m
  | h+1,m => extraSum n h m + (extraSum n h (m+2^h) <<< (64*2509*(2^h)))
def extra64 := extraSum 368639 8 1 <<< (64*2508)
private abbrev totalN : Nat := 368639
private def geom (n m : Nat) := unit64 n m <<< (64*(2509*m-1))
private theorem divisor_terms (k : ℕ) (hk : 2509 ≤ k) (hu : k≤3800) :
    divisorWord radix 1 totalN k = ∑ t ∈ range (totalN/k), radix^((t+1)*k-1) := by
  have hn : 2*k ≤ totalN := by dsimp [totalN]; omega
  have kp : 0 < k := by omega
  have rk : firstOffset 1 k=k-1 := by
    simp [firstOffset,Nat.mod_eq_of_lt (show 1 < k by omega),Nat.mod_eq_of_lt (show k-1 < k by omega)]
  have hits : numHits (k-1) k totalN = totalN/k := by
    unfold numHits
    rw [ite_eq_left (by omega),show totalN-1-(k-1)=totalN-k by omega]
    rw [←Nat.add_div_right _ kp,Nat.sub_add_cancel (by omega)]
  have hm : 2 ≤ totalN/k := (Nat.le_div_iff_mul_le kp).mpr hn
  have nz : radix^k-1 ≠ 0 := by
    have := one_lt_pow₀ (by decide : (1:ℤ) < radix) kp.ne'
    omega
  rw [divisorWord,rk,hits,ite_eq_right (by omega),ite_eq_right (by omega)]
  rw [pow_mul,←geom_sum_mul (radix^k) (totalN/k),Int.mul_ediv_cancel _ nz,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [←pow_mul,←pow_add]
  congr 1
  rw [Nat.add_mul,Nat.mul_comm k j,one_mul]
  omega
private theorem filtered_terms (k : ℕ) (hk : 2509 ≤ k) (hu : k≤3800) :
    divisorWord radix 1 totalN k =
      ∑ j ∈ range 256, if (j+1)*k ≤ totalN then radix^((j+1)*k-1) else 0 := by
  rw [divisor_terms k hk hu,←sum_filter]
  have kp : 0 < k := by omega
  have bound : totalN/k < 257 := (Nat.div_lt_iff_lt_mul kp).mpr (by dsimp [totalN]; omega)
  congr 1
  ext j
  simp only [mem_range,mem_filter,← Nat.le_div_iff_mul_le kp]
  omega
private theorem geo_terms (t : ℕ) (ht : 0 < t) :
    (geom totalN t:ℤ)=∑ k ∈ Icc 2509 (min 3800 (totalN/t)), radix^(t*k-1) := by
  let u := min 3800 (totalN/t)
  change (geom totalN t:ℤ)=∑ k ∈ Icc 2509 u, radix^(t*k-1)
  unfold geom unit64
  change (↑((if u-2508=0 then (0:ℕ) else _) <<< _) : ℤ) = _
  rw [←Ico_add_one_right_eq_Icc 2509 u,sum_Ico_eq_sum_range,
    show u+1-2509=u-2508 by omega]
  by_cases hz : u-2508=0
  · simp [hz]
  · simp only [ite_eq_right hz]
    have z1 : 1 ≤ (2:ℕ)^(64*t*(u-2508)) := Nat.one_le_two_pow
    have z2 : 1 ≤ (2:ℕ)^(64*t) := Nat.one_le_two_pow
    have den : radix^t-1 ≠ 0 := by
      have := one_lt_pow₀ (by decide : (1:ℤ) < radix) ht.ne'
      omega
    have castM (v : ℕ) : (↑((1<<<v)-1:ℕ):ℤ)=(2:ℤ)^v-1 := by
      rw [Nat.shiftLeft_eq,one_mul,Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow]
      rfl
    simp only [Nat.shiftLeft_eq,one_mul,Nat.cast_mul,Int.natCast_ediv] at castM ⊢
    rw [castM,castM,Nat.cast_pow,Nat.cast_ofNat]
    rw [show (2:ℤ)^(64*t*(u-2508)) = (radix^t)^(u-2508) by simp [radix,pow_mul],
      show (2:ℤ)^(64*t) = radix^t by simp [radix,pow_mul],
      ←geom_sum_mul (radix^t) (u-2508),Int.mul_ediv_cancel _ den,sum_mul]
    apply sum_congr rfl
    intro j _
    rw [show (2:ℤ)^(64*(2509*t-1)) = radix^(2509*t-1) by simp [radix,pow_mul],
      ←pow_mul,←pow_add]
    congr 1
    rw [Nat.mul_add,Nat.mul_comm t 2509]
    omega
private theorem sum_tree (n h m : ℕ) :
    (extraSum n h m : ℤ)=∑ i ∈ range (2^h), (unit64 n (m+i):ℤ)*radix^(2509*i) := by
  induction h generalizing m with
  | zero => simp only [extraSum,pow_zero,sum_range_one,Nat.add_zero,Nat.mul_zero,mul_one]
  | succ h ih =>
    rw [pow_succ,show 2^h*2=2^h+2^h by omega,sum_range_add,extraSum,Nat.cast_add,
      Nat.shiftLeft_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ih,ih]
    congr 1
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    rw [show (2:ℤ)^(64*2509*2^h)=radix^(2509*2^h) by simp only [radix,←pow_mul]; congr 1; ring,
        mul_assoc,←pow_add,←Nat.add_assoc]
    rw [Nat.mul_add,Nat.add_comm (2509*2^h)]
private theorem sum_shift (n h : ℕ) :
    (↑(extraSum n h 1 <<< (64*2508)):ℤ)=
      ∑ j ∈ range (2^h), (geom n (j+1):ℤ) := by
  rw [Nat.shiftLeft_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,sum_tree,sum_mul]
  apply sum_congr rfl
  intro j _
  simp only [geom,Nat.shiftLeft_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,radix,←pow_mul,mul_assoc,←pow_add]
  rw [Nat.add_comm 1 j]
  rw [show 64*(2509*j)+64*2508 = 64*(2509*(j+1)-1) by omega]
private theorem extra64_sum : (extra64:ℤ)=∑ j ∈ range 256, (geom totalN (j+1):ℤ) :=
  sum_shift totalN 8
theorem extra64_spec : (extra64:ℤ)=eval radix totalN (original extra) := by
  rw [extra64_sum]
  unfold original
  have eqF : (fun i => ∑ k ∈ Ico 1 4097, if k ∣ i+1 then extra k else 0) =
    (fun i => ∑ k ∈ Ico 1 4097, if k ∣ 1+i then extra k else 0) :=
    funext (fun i => by rw [Nat.add_comm i])
  rw [eqF,divisor_block (Ico 1 4097) extra radix (by decide) 1 totalN
    (fun k hk => (mem_Ico.mp hk).1)]
  have cut : (∑ k ∈ Icc 2509 3800, divisorWord radix 1 totalN k) =
    ∑ k ∈ Ico 1 4097, extra k * divisorWord radix 1 totalN k := by
    calc
      _ = ∑ k ∈ Icc 2509 3800, extra k * divisorWord radix 1 totalN k := by
        apply sum_congr rfl
        intro k h; have h := mem_Icc.mp h; simp [extra,show 2508 < k by omega,h.2]
      _ = _ := by
        apply sum_subset
        · intro k h; have h := mem_Icc.mp h; exact mem_Ico.mpr ⟨by omega,by omega⟩
        · intro k _ hn
          have h : ¬(2508 < k ∧ k≤3800) := by simp only [mem_Icc] at hn; omega
          simp [extra,h]
  rw [←cut]
  have eq' : (∑ k ∈ Icc 2509 3800, divisorWord radix 1 totalN k) =
      ∑ k ∈ Icc 2509 3800, ∑ j ∈ range 256, if (j+1)*k ≤ totalN then radix^((j+1)*k-1) else 0 := by
    apply sum_congr rfl; intro k h; exact filtered_terms k (mem_Icc.mp h).1 (mem_Icc.mp h).2
  rw [eq',sum_comm]
  apply sum_congr rfl
  intro j _
  rw [geo_terms (j+1) (by omega),←sum_filter]
  apply sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [mem_Icc,mem_filter,le_min_iff,Nat.le_div_iff_mul_le (show 0 < j+1 by omega)]
  rw [Nat.mul_comm k]
  exact and_assoc.symm
end FR7022Separated
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
def decode (iw ow : ℕ) (g : ℕ→ℕ) : ℕ → ℕ → ℕ
  | 0,z => g z
  | d+1,z =>
    let n := 2^d
    let s := 1 <<< ((iw+1)*n)
    decode iw ow g d (z % s) + (decode iw ow g d (z/s) <<< ((ow+1)*n))
theorem decode_pack (iw ow : ℕ) (g : ℕ→ℕ) (d : ℕ) (f : ℕ→ℕ)
    (hb : ∀ i<2^d, f i < 2^(iw+1)) :
    decode iw ow g d (pack iw (2^d) f) = pack ow (2^d) (fun i => g (f i)) := by
  induction d generalizing f with
  | zero => simp [decode,pack]
  | succ d ih =>
    let n := 2^d
    have nodes : 2^(d+1)=n+n := by simp [n,pow_succ,Nat.mul_two]
    have bound : pack iw n f < (2^(iw+1))^n := by
      simpa only [pow_mul] using (pack_lt_radix_power iw n f (fun i hi => hb i (by rw [nodes]; omega)))
    have scalePos : 0<(2^(iw+1))^n := by positivity
    rw [decode,nodes,pack_split iw,pack_split ow]
    simp only [Nat.shiftLeft_eq,one_mul,pow_mul]
    have hd : (pack iw n f+(2^(iw+1))^n*pack iw n (fun i => f (i+n)))/(2^(iw+1))^n =
        pack iw n (fun i => f (i+n)) := by
      rw [Nat.add_mul_div_left _ _ scalePos,Nat.div_eq_of_lt bound,zero_add]
    have hm : (pack iw n f+(2^(iw+1))^n*pack iw n (fun i => f (i+n))) % (2^(iw+1))^n =
        pack iw n f := by simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
    change decode iw ow g d (_ % (2^(iw+1))^n) + decode iw ow g d (_ / (2^(iw+1))^n)*(2^(ow+1))^n = _
    rw [hm,hd,ih f (fun i hi => hb i (by rw [nodes]; omega)),
      ih (fun i => f (i+n)) (fun i hi => hb (i+n) (by rw [nodes]; omega)),Nat.mul_comm]
end FR7022Unpack
namespace FR7022Unpack
open FR7022Lane
def padded (n : ℕ) (f : ℕ→ℕ) (i : ℕ) := if i < n then f i else 0
theorem pack_zero_values (w n : ℕ) : pack w n (fun _ => 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pack,ih]
theorem pack_unique_prefix (w n m : ℕ) (f g : ℕ→ℕ) (hm : n ≤ m)
    (h : ∀ i < n, g i=f i) (z : ∀ i, n ≤ i → g i=0) :
    pack w m g = pack w n f := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pack_split,pack_ext w n g f h]
  have ht := pack_ext w t (fun i => g (i+n)) (fun _ => 0) (fun i _ => z (i+n) (by omega))
  rw [ht,pack_zero_values,mul_zero,add_zero]
def units (w n : ℕ) := ((1 <<< ((w+1)*n))-1)/((1 <<< (w+1))-1)
theorem units_spec (w n : ℕ) : units w n = pack w n (fun _ => 1) := by
  have hp : 0 < 2^(w+1)-1 := by have := Nat.one_lt_two_pow (Nat.succ_ne_zero w); omega
  unfold units
  simp only [Nat.shiftLeft_eq,one_mul]
  calc
    _ = (pack w n (fun _ => 1)*(2^(w+1)-1))/(2^(w+1)-1) := by rw [pack_const_mul,one_mul]
    _ = _ := Nat.mul_div_cancel _ hp
theorem eval_bias (r : ℤ) (n : ℕ) (f : ℕ→ℤ) (b : ℤ) :
    eval r n (fun i => f i+b) = eval r n f + b*eval r n (fun _ => 1) := by
  induction n generalizing f with
  | zero => simp [eval]
  | succ n ih =>
    simp only [eval]
    rw [ih (fun i => f (i+1))]
    ring
theorem pack_as_eval (w n : ℕ) (f : ℕ→ℕ) (g : ℕ→ℤ)
    (hg : ∀ i < n, (f i:ℤ)=g i) : (pack w n f:ℤ) = eval ((2:ℤ)^(w+1)) n g := by
  rw [pack_int,eval_eq_sum,eval_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [hg i (Finset.mem_range.mp hi)]
end FR7022Unpack
namespace FR7022Support
open Finset FR7022Second
def smallPrimes : Finset ℕ := {2,3,5,7,11,13}
theorem six_factors (n : ℕ) (hn : 0 < n) (bound : n≤368639) : n.primeFactors.card≤6 := by
  let s := n.primeFactors
  let a := s.filter (fun p => p<17)
  let b := s.filter (fun p => ¬p<17)
  have table : ∀ t ∈ smallPrimes.powerset, 368639 < (∏ p ∈ t, p)*17^(7-t.card) := by decide +kernel
  have small : a∈smallPrimes.powerset := by
    apply mem_powerset.mpr
    intro p hp
    obtain ⟨hs,lt⟩ := mem_filter.mp hp
    have pp := (Nat.mem_primeFactors.mp hs).1
    have test : ∀ j : Fin 17, j.val.Prime → j.val∈smallPrimes := by decide +kernel
    exact test ⟨p,lt⟩ pp
  have cards : a.card+b.card=s.card := card_filter_add_card_filter_not ..
  have scale : 17^b.card≤∏ p ∈ b, p := by
    calc
      _ = ∏ _p ∈ b, (17:ℕ) := by simp
      _ ≤ _ := prod_le_prod' (fun p h => Nat.le_of_not_gt (mem_filter.mp h).2)
  have spl : (∏ p ∈ a, p)*(∏ p ∈ b, p) = ∏ p ∈ s, p :=
    prod_filter_mul_prod_filter_not s (fun p => p<17) id
  by_contra! more
  have pow := Nat.pow_le_pow_right (by decide : 0<17) (show 7-a.card ≤ b.card by change 6 < s.card at more; omega)
  have cap := Nat.le_of_dvd hn n.prod_primeFactors_dvd
  have step := Nat.mul_le_mul_left (∏ p ∈ a, p) (pow.trans scale)
  rw [spl] at step
  exact (Nat.not_lt_of_ge (step.trans (cap.trans bound))) (table a small)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem support_table : ∀ k ∈ Ico 1 4097, base k ≠ 0 →
    (∏ p ∈ k.primeFactors, p)=k ∧ |base k|≤1292 := by decide +kernel
theorem tight (i : ℕ) (hi : i<368639) : |original base i| < 131072 := by
  let s := (Ico 1 4097).filter (fun k => k ∣ i+1 ∧ base k ≠ 0)
  have trim : original base i=∑ k ∈ s, base k := by
    unfold original
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases hd : k ∣ i+1 <;> by_cases z : base k=0 <;> simp [hd,z]
  have card : s.card≤(i+1).primeFactors.powerset.card := by
    apply card_le_card_of_injOn (fun k => k.primeFactors)
    · intro k h
      exact mem_powerset.mpr (Nat.primeFactors_mono (mem_filter.mp h).2.1 (by omega))
    · intro k hk l hl eq
      have a := (support_table k (mem_filter.mp hk).1 (mem_filter.mp hk).2.2).1
      have b := (support_table l (mem_filter.mp hl).1 (mem_filter.mp hl).2.2).1
      rw [←a,←b,show k.primeFactors=l.primeFactors from eq]
  rw [card_powerset] at card
  have cnt : s.card≤64 := card.trans (Nat.pow_le_pow_right (by decide) (six_factors _ (by omega) (by omega)))
  have total : (∑ k ∈ s, |base k|) ≤ ∑ _k ∈ s, (1292:ℤ) := by
    apply sum_le_sum
    intro k h
    exact (support_table k (mem_filter.mp h).1 (mem_filter.mp h).2.2).2
  simp only [sum_const,nsmul_eq_mul] at total
  rw [trim]
  have triangle := abs_sum_le_sum_abs (fun k => base k) s
  omega
end FR7022Support
namespace FR7022Short
open FR7022Lane FR7022Unpack
def short (iw ow : ℕ) (g : ℕ→ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | m+1,z =>
    ((short iw ow g m (z >>> (iw+1))) <<< (ow+1)) + g (z &&& ((1 <<< (iw+1))-1))
theorem short_pack (iw ow : ℕ) (g : ℕ→ℕ) (n : ℕ) (f : ℕ→ℕ)
    (hf : ∀ i < n, f i<2^(iw+1)) :
    short iw ow g n (pack iw n f) = pack ow n (fun i => g (f i)) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have bound := hf 0 (by omega)
    have pos : 0<2^(iw+1) := by positivity
    conv_lhs => rw [short,pack]
    conv_rhs => rw [pack]
    simp only [Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,one_mul,Nat.and_two_pow_sub_one_eq_mod,
      Nat.mul_add_div pos,Nat.div_eq_of_lt bound,Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt bound]
    rw [ih (fun i => f (i+1)) (fun i h => hf (i+1) (by omega)),Nat.mul_comm]
def chunks (w : ℕ) (f : ℕ→ℕ) (i : ℕ) := pack w 16 (fun j => f (j+16*i))
theorem grouped (w n : ℕ) (f : ℕ→ℕ) :
    pack w (16*n) f = pack ((w+1)*16-1) n (chunks w f) := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    change pack w (16*(n+1)) f =
      2^((w+1)*16-1+1) * pack _ n (fun i => chunks w f (i+1)) + chunks w f 0
    rw [Nat.mul_succ,Nat.add_comm (16*n) 16,pack_split w 16,ih,
      show (w+1)*16-1+1=(w+1)*16 by omega,pow_mul]
    have step : chunks w (fun i => f (i+16)) = (fun i => chunks w f (i+1)) := by
      funext i
      apply pack_ext
      intro j _
      change f (j+16*i+16)=f (j+16*(i+1))
      congr 1
    have start : chunks w f 0=pack w 16 f := by simp [chunks]
    rw [step,start,Nat.add_comm]
def wide (iw ow : ℕ) (g : ℕ→ℕ) (d z : ℕ) :=
  decode ((iw+1)*16-1) ((ow+1)*16-1) (short iw ow g 16) d z
theorem wide_pack (iw ow : ℕ) (g : ℕ→ℕ) (d : ℕ) (f : ℕ→ℕ)
    (hf : ∀ i<2^(d+4), f i<2^(iw+1)) :
    wide iw ow g d (pack iw (2^(d+4)) f) = pack ow (2^(d+4)) (fun i => g (f i)) := by
  have len : 2^(d+4)=16*2^d := by rw [pow_add,Nat.mul_comm]; rfl
  have sub (i j : ℕ) (h : i<2^d) (h' : j<16) : j+16*i<2^(d+4) := by rw [len]; omega
  have each (i : ℕ) (h : i<2^d) : chunks iw f i < 2^((iw+1)*16-1+1) := by
    rw [show (iw+1)*16-1+1=(iw+1)*16 by omega,pow_mul]
    exact pack_lt_radix_power iw 16 _ (fun j hj => hf _ (sub i j h hj))
  rw [len,grouped iw,grouped ow,wide,decode_pack _ _ _ d _ each]
  apply pack_ext
  intro i h
  exact short_pack _ _ _ _ _ (fun j hj => hf _ (sub i j h hj))
end FR7022Short
namespace FR7022Short18
open FR7022Short FR7022Lane FR7022Unpack
def biased18 (n : ℕ) (raw : ℤ) :=
  ((raw+131072*(units 17 n:ℤ)) % ((1:ℤ) <<< (18*n))).toNat
def base64 (n d z : ℕ) : ℤ := (wide 17 63 id d z:ℤ)-131072*(units 63 n:ℤ)
theorem base64_exact (n d : ℕ) (hn : n≤2^(d+4)) (raw : ℤ) (f : ℕ→ℤ)
    (bound : ∀ i < n, |f i|<131072)
    (source : Int.ModEq ((2:ℤ)^(18*n)) raw (eval ((2:ℤ)^18) n f)) :
    base64 n d (biased18 n raw) = eval ((2:ℤ)^64) n f := by
  let v := padded n (fun i => (f i+131072).toNat)
  have digits (i : ℕ) (h : i < n) : (v i:ℤ)=f i+131072 := by
    have low := (abs_lt.mp (bound i h)).1
    simp only [v,padded,ite_eq_left h,Int.toNat_of_nonneg (show 0 ≤ f i+131072 by omega)]
  have fit (i : ℕ) : v i < 2^18 := by
    by_cases h : i < n
    · have e := digits i h
      have high := (abs_lt.mp (bound i h)).2
      omega
    · simp [v,padded,h]
  have word (w : ℕ) : (pack w n v:ℤ)=eval ((2:ℤ)^(w+1)) n f + 131072*(units w n:ℤ) := by
    have e := pack_as_eval w n v _ digits
    rw [eval_bias] at e
    have u := pack_as_eval w n (fun _ => 1) (fun _ => 1) (by simp)
    rwa [←u,←units_spec] at e
  have mod := source.add_right (131072*(units 17 n:ℤ))
  change _ % _ = _ % _ at mod
  rw [←word 17] at mod
  have small : pack 17 n v < (2^18)^n := by
    simpa only [pow_mul] using pack_lt_radix_power 17 n v (fun i _ => fit i)
  have cap : (pack 17 n v:ℤ)<(2:ℤ)^(18*n) := by rw [pow_mul]; exact_mod_cast small
  have encoded : biased18 n raw = pack 17 n v := by
    rw [biased18,Int.shiftLeft_eq,one_mul,mod,Int.emod_eq_of_lt (Int.natCast_nonneg _) cap,Int.toNat_natCast]
  have extend (w : ℕ) : pack w (2^(d+4)) v = pack w n v :=
    pack_unique_prefix _ _ _ _ _ hn (fun _ _ => rfl) (fun i hi => by simp [v,padded,not_lt.mpr hi])
  have decoded := wide_pack 17 63 id d v (fun i _ => fit i)
  change wide 17 63 id d (pack 17 (2^(d+4)) v) = pack 63 (2^(d+4)) v at decoded
  rw [extend,extend] at decoded
  rw [base64,encoded,decoded,word]
  ring
end FR7022Short18
namespace FR7022Narrow
open FR7022TwoStage FR7022Short18 FR7022Second
theorem exact_base : base64 368639 15 (biased18 368639 base18) = fastBase := by
  have col := base64_exact 368639 15 (by decide) base18 (original base)
    FR7022Support.tight base18_spec
  exact col.trans fastBase_spec
end FR7022Narrow
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
def base64 (n z : Nat) : Int :=
  (expand 18 64 19 z 1 : Int) - 131072 * (FR7022Unpack.units 63 n : Int)
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
namespace FR7022Flat
open FR7022Hyperbola FR7022Lane FR7022Unpack FR7022Short
theorem expand_eighteen (rule : SplitRule) (z : ℕ) (hz : z < 2^(18*2^19)) :
    expand 18 64 19 z 1 = wide 17 63 id 15 z := by
  let N : ℕ := 2^19
  let f := fun i => slice 18 z i 1
  have fits (i : ℕ) : f i < 2^18 := by
    change (z >>> (18*i)) &&& (2^18-1) < 2^18
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide : (2^18-1:ℕ)<2^18)
  have rep : z = word 18 N f := word_of_slots (u:=18) (N:=N) (table:=z)
    (by decide) hz f (fun i _ => fits i) (fun _ _ => rfl)
  calc
    expand 18 64 19 z 1 = expand 18 64 19 (word 18 N f) 1 := congrArg (fun t=>expand 18 64 19 t 1) rep
    _ = word 64 N f := expand_word rule 18 64 (by decide) (by decide) f fits 19
    _ = wide 17 63 id 15 (word 18 N f) := (wide_pack 17 63 id 15 f (fun i _ => fits i)).symm
    _ = wide 17 63 id 15 z := congrArg (wide 17 63 id 15) rep.symm
theorem base64_matches (rule : SplitRule) (n : ℕ) (hn : n≤2^19) (raw : ℤ) :
    base64 n (FR7022Short18.biased18 n raw) =
    FR7022Short18.base64 n 15 (FR7022Short18.biased18 n raw) := by
  have pos : 0<(2:ℤ)^(18*n) := by positivity
  have small : FR7022Short18.biased18 n raw < 2^(18*n) := by
    unfold FR7022Short18.biased18
    rw [Int.shiftLeft_eq,one_mul]
    have e := Int.emod_lt_of_pos (raw+131072*(units 17 n:ℤ)) pos
    have g := Int.emod_nonneg (raw+131072*(units 17 n:ℤ)) (ne_of_gt pos)
    exact_mod_cast (show (((raw+131072*(units 17 n:ℤ)) % (2:ℤ)^(18*n)).toNat:ℤ) < (2:ℤ)^(18*n) by
      rwa [Int.toNat_of_nonneg g])
  have bound := small.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 18 hn))
  rw [base64,FR7022Short18.base64,expand_eighteen rule _ bound]
end FR7022Flat
namespace FR7022LightEnv
open FR7022Verified
def placed (n : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (p,v)::xs => (v <<< (64*(min p n))) + placed n xs
def env (n : Nat) (xs : List (Nat × Nat)) : Nat :=
  (((shiftPower n : Int) * ((xs.map Prod.snd).sum : Nat) - (placed n xs : Int)) / (A-1)).toNat
end FR7022LightEnv
namespace FR7022LightEnv
open FR7022Verified
private theorem telescoped (n : ℕ) (xs : List (ℕ × ℕ)) :
  (xs.map (fun p => ((shiftPower n : ℤ) - shiftPower (min p.1 n)) * (p.2:ℤ))).sum =
    (shiftPower n : ℤ) * ((xs.map Prod.snd).sum : ℕ) - (placed n xs : ℤ) := by
  induction xs with
  | nil => simp [placed]
  | cons hd xs ih =>
    obtain ⟨i,v⟩ := hd
    rw [List.map_cons,List.sum_cons,ih]
    simp only [List.map_cons,List.sum_cons,placed,Nat.cast_add,Nat.shiftLeft_eq,Nat.cast_mul,
      shiftPower,one_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
theorem env_eq (n : ℕ) (xs : List (ℕ × ℕ)) : env n xs=fastEnv n xs := by
  unfold env fastEnv
  dsimp only
  rw [telescoped]
end FR7022LightEnv
namespace FR7022LightEnv
open FR7022Verified FR7022TwoStage FR7022RadixPrefix FR7022Rational
def both (n q d : Nat) (g slack m : Nat) (T : Int) : Bool :=
  withNat (prefixPacked (m-1) d q ((T % (m:Int)).toNat)) (fun p =>
    ((p+slack) &&& g)==0 && (((slack+m)-p) &&& g)==0)
def row (x y : Int) (r : Packed) : Bool :=
  let n := r.params.B
  let q := r.params.q
  let d := (n/q).log2+1
  withNat (shiftPower n) (fun m => withNat (fastMask q n) (fun g =>
    withNat ((2^63-1)*fastRep n - env n (increases r)) (fun s =>
      both n q d g s m (integerWordWith x y r r.params.alphaLo) &&
      both n q d g s m (integerWordWith x y r r.params.alphaHi))))
end FR7022LightEnv
namespace FR7022LightEnv
open FR7022Verified FR7022TwoStage FR7022Rational
theorem row_eq (x y : Int) (r : Packed) : row x y r = oneRow x y r := by
  simp only [row,both,withNat_eq,env_eq,oneRow,certifiedWith,fastVerify]
end FR7022LightEnv
namespace FR7022Flat
open FR7022TwoStage FR7022Narrow FR7022Short18 FR7022Second
theorem split_complete : SplitRule := @split_lanes
theorem exact_base : base64 368639 (biased18 368639 base18) = fastBase :=
  (base64_matches split_complete 368639 (by decide) base18).trans FR7022Narrow.exact_base
end FR7022Flat
namespace FR7022Pin
open FR7022Flat FR7022Narrow FR7022Short18 FR7022LightEnv FR7022TwoStage
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
noncomputable def raw : {v : Int // v=FR7022Narrow.base18} := by
  have e : FR7022Narrow.base18=FR7022Narrow.base18 := rfl
  conv at e =>
    lhs
    reduce
  exact ⟨_,e⟩
theorem raw_source : raw.1=FR7022Narrow.base18 := raw.2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
noncomputable def biased : {v : Nat // v=FR7022Short18.biased18 368639 raw.1} := by
  have e : FR7022Short18.biased18 368639 raw.1=FR7022Short18.biased18 368639 raw.1 := rfl
  conv at e =>
    lhs
    reduce
  exact ⟨_,e⟩
theorem biased_source : biased.1=FR7022Short18.biased18 368639 raw.1 := biased.2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
noncomputable def base : {v : Int // v=FR7022Flat.base64 368639 biased.1} := by
  have e : FR7022Flat.base64 368639 biased.1=FR7022Flat.base64 368639 biased.1 := rfl
  conv at e =>
    lhs
    reduce
  exact ⟨_,e⟩
theorem base_source : base.1=FR7022Flat.base64 368639 biased.1 := base.2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
noncomputable def extra : {v : Nat // v=FR7022Separated.extra64} := by
  have e : FR7022Separated.extra64=FR7022Separated.extra64 := rfl
  conv at e =>
    lhs
    reduce
  exact ⟨_,e⟩
theorem extra_source : extra.1=FR7022Separated.extra64 := extra.2
end FR7022Pin
namespace FR7022Pin
open FR7022TwoStage FR7022Second
theorem base_original : FR7022Pin.base.1=fastBase := by
  rw [base_source,biased_source,raw_source]
  exact FR7022Flat.exact_base
theorem extra_original : (FR7022Pin.extra.1:ℤ)=fastExtra := by
  rw [extra_source]
  exact FR7022Separated.extra64_spec.trans fastExtra_spec
theorem row_implies (r : Packed) (h : FR7022LightEnv.row FR7022Pin.base.1 FR7022Pin.extra.1 r) :
    certified r r.params.alphaLo && certified r r.params.alphaHi := by
  rw [FR7022LightEnv.row_eq,base_original,extra_original] at h
  exact h
end FR7022Pin
namespace FR7022TwoStage
open FR7022Pin (row_implies)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q2_verified : certified q2 q2.params.alphaLo && certified q2 q2.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q4_verified : certified q4 q4.params.alphaLo && certified q4 q4.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q6_verified : certified q6 q6.params.alphaLo && certified q6 q6.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q8_verified : certified q8 q8.params.alphaLo && certified q8 q8.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q10_verified : certified q10 q10.params.alphaLo && certified q10 q10.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q12_verified : certified q12 q12.params.alphaLo && certified q12 q12.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q14_verified : certified q14 q14.params.alphaLo && certified q14 q14.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q16_verified : certified q16 q16.params.alphaLo && certified q16 q16.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q18_verified : certified q18 q18.params.alphaLo && certified q18 q18.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q20_verified : certified q20 q20.params.alphaLo && certified q20 q20.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q22_verified : certified q22 q22.params.alphaLo && certified q22 q22.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q24_verified : certified q24 q24.params.alphaLo && certified q24 q24.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q26_verified : certified q26 q26.params.alphaLo && certified q26 q26.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q28_verified : certified q28 q28.params.alphaLo && certified q28 q28.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q30_verified : certified q30 q30.params.alphaLo && certified q30 q30.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q32_verified : certified q32 q32.params.alphaLo && certified q32 q32.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q34_verified : certified q34 q34.params.alphaLo && certified q34 q34.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q36_verified : certified q36 q36.params.alphaLo && certified q36 q36.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q38_verified : certified q38 q38.params.alphaLo && certified q38 q38.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q40_verified : certified q40 q40.params.alphaLo && certified q40 q40.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q42_verified : certified q42 q42.params.alphaLo && certified q42 q42.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q44_verified : certified q44 q44.params.alphaLo && certified q44 q44.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q46_verified : certified q46 q46.params.alphaLo && certified q46 q46.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q48_verified : certified q48 q48.params.alphaLo && certified q48 q48.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q50_verified : certified q50 q50.params.alphaLo && certified q50 q50.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q52_verified : certified q52 q52.params.alphaLo && certified q52 q52.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q53_verified : certified q53 q53.params.alphaLo && certified q53 q53.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q54_verified : certified q54 q54.params.alphaLo && certified q54 q54.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q55_verified : certified q55 q55.params.alphaLo && certified q55 q55.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q56_verified : certified q56 q56.params.alphaLo && certified q56 q56.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q57_verified : certified q57 q57.params.alphaLo && certified q57 q57.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q58_verified : certified q58 q58.params.alphaLo && certified q58 q58.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q59_verified : certified q59 q59.params.alphaLo && certified q59 q59.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q60_verified : certified q60 q60.params.alphaLo && certified q60 q60.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q61_verified : certified q61 q61.params.alphaLo && certified q61 q61.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q62_verified : certified q62 q62.params.alphaLo && certified q62 q62.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q63_verified : certified q63 q63.params.alphaLo && certified q63 q63.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q64_verified : certified q64 q64.params.alphaLo && certified q64 q64.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q65_verified : certified q65 q65.params.alphaLo && certified q65 q65.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q66_verified : certified q66 q66.params.alphaLo && certified q66 q66.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q67_verified : certified q67 q67.params.alphaLo && certified q67 q67.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q68_verified : certified q68 q68.params.alphaLo && certified q68 q68.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q69_verified : certified q69 q69.params.alphaLo && certified q69 q69.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q70_verified : certified q70 q70.params.alphaLo && certified q70 q70.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q71_verified : certified q71 q71.params.alphaLo && certified q71 q71.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q72_verified : certified q72 q72.params.alphaLo && certified q72 q72.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q73_verified : certified q73 q73.params.alphaLo && certified q73 q73.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q74_verified : certified q74 q74.params.alphaLo && certified q74 q74.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q75_verified : certified q75 q75.params.alphaLo && certified q75 q75.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q76_verified : certified q76 q76.params.alphaLo && certified q76 q76.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q77_verified : certified q77 q77.params.alphaLo && certified q77 q77.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q78_verified : certified q78 q78.params.alphaLo && certified q78 q78.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q79_verified : certified q79 q79.params.alphaLo && certified q79 q79.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q80_verified : certified q80 q80.params.alphaLo && certified q80 q80.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q81_verified : certified q81 q81.params.alphaLo && certified q81 q81.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q82_verified : certified q82 q82.params.alphaLo && certified q82 q82.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q83_verified : certified q83 q83.params.alphaLo && certified q83 q83.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q84_verified : certified q84 q84.params.alphaLo && certified q84 q84.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q85_verified : certified q85 q85.params.alphaLo && certified q85 q85.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q86_verified : certified q86 q86.params.alphaLo && certified q86 q86.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q87_verified : certified q87 q87.params.alphaLo && certified q87 q87.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q88_verified : certified q88 q88.params.alphaLo && certified q88 q88.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q89_verified : certified q89 q89.params.alphaLo && certified q89 q89.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q90_verified : certified q90 q90.params.alphaLo && certified q90 q90.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q91_verified : certified q91 q91.params.alphaLo && certified q91 q91.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q92_verified : certified q92 q92.params.alphaLo && certified q92 q92.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q93_verified : certified q93 q93.params.alphaLo && certified q93 q93.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q94_verified : certified q94 q94.params.alphaLo && certified q94 q94.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q95_verified : certified q95 q95.params.alphaLo && certified q95 q95.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q96_verified : certified q96 q96.params.alphaLo && certified q96 q96.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q97_verified : certified q97 q97.params.alphaLo && certified q97 q97.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q98_verified : certified q98 q98.params.alphaLo && certified q98 q98.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q99_verified : certified q99 q99.params.alphaLo && certified q99 q99.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q100_verified : certified q100 q100.params.alphaLo && certified q100 q100.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q101_verified : certified q101 q101.params.alphaLo && certified q101 q101.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q102_verified : certified q102 q102.params.alphaLo && certified q102 q102.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q103_verified : certified q103 q103.params.alphaLo && certified q103 q103.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q104_verified : certified q104 q104.params.alphaLo && certified q104 q104.params.alphaHi := row_implies _ (by decide +kernel)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q105_verified : certified q105 q105.params.alphaLo && certified q105 q105.params.alphaHi := row_implies _ (by decide +kernel)
end FR7022TwoStage
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
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
namespace FR7022TwoStage
open Finset FR7022Verified FR7022Lane FR7022FiniteCount FR7022ProgressionTail
def domain : Finset ℕ := Ico 1 4097
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def coeff (sign : ℕ → ℤ) (a : ℤ) (k : ℕ) : ℤ :=
  1000*(sign k * ((min 1292 (3800-k):ℕ):ℤ))+a*(if 2508<k ∧ k≤3800 then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def boundOK (r : Packed) : Bool := decide (
    r.params.B=368639 ∧ 0<r.params.q ∧ r.params.q≤r.params.B ∧
    r.params.B≤r.params.q*2^((r.params.B/r.params.q).log2+1) ∧
    r.params.scale≤10000000 ∧ |r.params.alphaLo|≤1000000 ∧ |r.params.alphaHi|≤1000000 ∧
    ((increases r).map Prod.snd).sum ≤ 10000000000)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rises_le (xs : List (ℕ×ℕ)) (i : ℕ) :
    fromRises xs i ≤ (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons x l ih =>
    change ray x.1 x.2 i+fromRises l i ≤ x.2+(l.map Prod.snd).sum
    apply Nat.add_le_add _ ih
    unfold ray
    split <;> omega
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coeff_le (sign : ℕ→ℤ) (sg : ∀ k, |sign k|≤1) (a : ℤ) (ha : |a|≤1000000) (k : ℕ) :
    |coeff sign a k| ≤ 10000000 := by
  unfold coeff
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_mul]
  have hh : |((min 1292 (3800-k):ℕ):ℤ)| ≤ 1292 := by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast (min_le_left 1292 (3800-k))
  have c := mul_le_mul (sg k) hh (abs_nonneg _) (by decide : (0:ℤ)≤1)
  split <;> norm_num at * <;> omega
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def TrueWord (r : Packed) (sign : ℕ→ℤ) (a : ℤ) : Prop :=
  eval A r.params.B (fun i => centered domain (coeff sign a) r.params.scale (i+1)) = integerWord r a
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def CountBound (r : Packed) (sign : ℕ→ℤ) (a : ℤ) : Prop :=
  ∀ t, 0<t → t≤r.params.B → ∀ h, h.Coprime r.params.q →
  |(∑ k∈domain, (count r.params.q h t k:ℤ)*coeff sign a k) -
    (if 1 % r.params.q=h % r.params.q then (r.params.scale:ℤ) else 0)| ≤
     (fromRises (increases r) (t-1):ℤ)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bound_from_word (r : Packed) (sign : ℕ→ℤ) (sg : ∀ k, |sign k|≤1) (a : ℤ)
    (endpt : a=r.params.alphaLo ∨ a=r.params.alphaHi)
    (ok : boundOK r = true) (word : TrueWord r sign a) (hc : certified r a=true) :
    CountBound r sign a := by
  obtain ⟨hB,hq,hn,hlen,hscale,hlo,hhi,henv⟩ := of_decide_eq_true ok
  have hscalar : |a| ≤ 1000000 := endpt.elim (fun e => e ▸ hlo) (fun e => e ▸ hhi)
  apply certified_finite domain (coeff sign a) r.params.scale r.params.B r.params.q
    ((r.params.B/r.params.q).log2+1) 10000000 10000000000 (integerWord r a) (increases r)
    (fun _ h => (mem_Ico.mp h).1) (fun k _ => coeff_le sign sg a hscalar k) hq hn hlen word
    (fun i _ => (rises_le _ i).trans henv) _ hc
  have hd : domain.card=4096 := by simp [domain]
  rw [hB,hd]
  omega
end FR7022TwoStage
namespace FR7022TwoStage
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q2_parameters : boundOK q2=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q4_parameters : boundOK q4=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q6_parameters : boundOK q6=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q8_parameters : boundOK q8=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q10_parameters : boundOK q10=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q12_parameters : boundOK q12=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q14_parameters : boundOK q14=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q16_parameters : boundOK q16=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q18_parameters : boundOK q18=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q20_parameters : boundOK q20=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q22_parameters : boundOK q22=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q24_parameters : boundOK q24=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q26_parameters : boundOK q26=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q28_parameters : boundOK q28=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q30_parameters : boundOK q30=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q32_parameters : boundOK q32=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q34_parameters : boundOK q34=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q36_parameters : boundOK q36=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q38_parameters : boundOK q38=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q40_parameters : boundOK q40=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q42_parameters : boundOK q42=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q44_parameters : boundOK q44=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q46_parameters : boundOK q46=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q48_parameters : boundOK q48=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q50_parameters : boundOK q50=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q52_parameters : boundOK q52=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q53_parameters : boundOK q53=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q54_parameters : boundOK q54=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q55_parameters : boundOK q55=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q56_parameters : boundOK q56=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q57_parameters : boundOK q57=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q58_parameters : boundOK q58=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q59_parameters : boundOK q59=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q60_parameters : boundOK q60=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q61_parameters : boundOK q61=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q62_parameters : boundOK q62=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q63_parameters : boundOK q63=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q64_parameters : boundOK q64=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q65_parameters : boundOK q65=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q66_parameters : boundOK q66=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q67_parameters : boundOK q67=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q68_parameters : boundOK q68=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q69_parameters : boundOK q69=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q70_parameters : boundOK q70=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q71_parameters : boundOK q71=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q72_parameters : boundOK q72=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q73_parameters : boundOK q73=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q74_parameters : boundOK q74=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q75_parameters : boundOK q75=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q76_parameters : boundOK q76=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q77_parameters : boundOK q77=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q78_parameters : boundOK q78=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q79_parameters : boundOK q79=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q80_parameters : boundOK q80=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q81_parameters : boundOK q81=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q82_parameters : boundOK q82=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q83_parameters : boundOK q83=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q84_parameters : boundOK q84=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q85_parameters : boundOK q85=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q86_parameters : boundOK q86=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q87_parameters : boundOK q87=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q88_parameters : boundOK q88=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q89_parameters : boundOK q89=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q90_parameters : boundOK q90=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q91_parameters : boundOK q91=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q92_parameters : boundOK q92=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q93_parameters : boundOK q93=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q94_parameters : boundOK q94=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q95_parameters : boundOK q95=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q96_parameters : boundOK q96=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q97_parameters : boundOK q97=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q98_parameters : boundOK q98=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q99_parameters : boundOK q99=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q100_parameters : boundOK q100=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q101_parameters : boundOK q101=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q102_parameters : boundOK q102=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q103_parameters : boundOK q103=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q104_parameters : boundOK q104=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem q105_parameters : boundOK q105=true := by decide +kernel
end FR7022TwoStage
namespace FR7022TwoStage
open Finset FR7022FiniteCount FR7022ProgressionTail FR7022Lane
def unitsDomain (q : ℕ) : Finset ℕ := (Icc 1 3800).filter (fun k => k.Coprime q)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restrict_count (r : Packed) (sign : ℕ→ℤ) (a : ℤ) (t h : ℕ) (hc : h.Coprime r.params.q) :
    (∑ k∈unitsDomain r.params.q, (count r.params.q h t k:ℤ)*coeff sign a k) =
    ∑ k∈domain, (count r.params.q h t k:ℤ)*coeff sign a k := by
  apply sum_subset
  · intro k hk
    have v := mem_Icc.mp (mem_filter.mp hk).1
    exact mem_Ico.mpr ⟨v.1,by omega⟩
  · intro k hk hn
    by_cases hu : k.Coprime r.params.q
    · have hb : 3800<k := by
        by_contra! hK
        exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Ico.mp hk).1,hK⟩,hu⟩)
      simp [coeff, Nat.sub_eq_zero_of_le hb.le,show ¬k≤3800 by omega]
    · simp [count_nonunit _ _ _ _ hc hu]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finite_real (r : Packed) (sign : ℕ→ℤ) (c : ℕ→ℝ) (hs : 0<r.params.scale)
    (cl : CountBound r sign r.params.alphaLo) (ch : CountBound r sign r.params.alphaHi)
    (between : ∀ k∈unitsDomain r.params.q, (coeff sign r.params.alphaLo k:ℝ)≤r.params.scale*c k ∧
      r.params.scale*c k≤(coeff sign r.params.alphaHi k:ℝ))
    (t h : ℕ) (ht : 0<t) (hT : t≤r.params.B) (hu : h.Coprime r.params.q) :
    |(∑ k∈unitsDomain r.params.q, c k*(count r.params.q h t k:ℝ)) -
      (if h % r.params.q=1 % r.params.q then (1:ℝ) else 0)| ≤
      (fromRises (increases r) (t-1):ℝ)/r.params.scale := by
  let z : ℤ := if 1 % r.params.q=h % r.params.q then ↑r.params.scale else 0
  let v (a : ℤ) := ∑ k∈unitsDomain r.params.q,(count r.params.q h t k:ℤ)*coeff sign a k
  let main := ∑ k∈unitsDomain r.params.q, c k*(count r.params.q h t k:ℝ)
  let E := fromRises (increases r) (t-1)
  have bound (a : ℤ) (ha : CountBound r sign a) : |v a-z|≤(E:ℤ) := by
    simpa only [v,z,restrict_count r sign a t h hu,E] using ha t ht hT h hu
  have low := (abs_le.mp (bound _ cl)).1
  have high := (abs_le.mp (bound _ ch)).2
  have lr : -(E:ℝ) ≤ (v r.params.alphaLo:ℝ)-(z:ℝ) := by exact_mod_cast low
  have ur : (v r.params.alphaHi:ℝ)-(z:ℝ) ≤ E := by exact_mod_cast high
  have eqn : (r.params.scale:ℝ)*main =
      ∑ k∈unitsDomain r.params.q,(count r.params.q h t k:ℝ)*((r.params.scale:ℝ)*c k) := by
    rw [show main = _ by rfl,mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  have vlo : (v r.params.alphaLo:ℝ) ≤ r.params.scale*main := by
    rw [eqn]
    dsimp only [v]
    push_cast
    exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (between k hk).1 (by positivity))
  have vhi : (r.params.scale:ℝ)*main ≤ (v r.params.alphaHi:ℝ) := by
    rw [eqn]
    dsimp only [v]
    push_cast
    exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (between k hk).2 (by positivity))
  let target : ℝ := if h % r.params.q=1 % r.params.q then 1 else 0
  have z_eq : (z:ℝ) = r.params.scale*target := by
    dsimp only [z,target]
    by_cases hh : 1 % r.params.q=h % r.params.q
    · rw [if_pos hh,if_pos hh.symm]; simp
    · rw [if_neg hh,if_neg (Ne.symm hh)]; simp
  have ps : (0:ℝ)<r.params.scale := by exact_mod_cast hs
  change |main-target|≤(E:ℝ)/r.params.scale
  apply (le_div_iff₀ ps).mpr
  rw [← abs_of_pos ps,← abs_mul,abs_le]
  rw [z_eq] at lr ur
  constructor <;> linarith
end FR7022TwoStage
namespace FR7022TwoStage
open Finset FR7022Second FR7022Verified FR7022Lane FR7022FiniteCount
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sign_bounded (k : ℕ) : |sign k| ≤ 1 := by
  unfold sign
  split
  · decide
  · split <;> decide
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def SourceCorrect : Prop := ∀ u v scale : ℤ,
  eval radix 368639 (fun i => increment u v scale (i+1)) =
    u*fastBase+v*fastExtra-scale
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem row_word (r : Packed) (hs : r.params.B=368639) (a : ℤ) (source : SourceCorrect) :
    TrueWord r sign a := by
  unfold TrueWord
  rw [hs]
  have e : (fun i => centered domain (coeff sign a) r.params.scale (i+1)) =
      fun i => increment 1000 a (r.params.scale:ℤ) (i+1) := by
    funext i
    simp only [centered,GoldbachCoefficientPrefix.divisorWeight,domain,coeff,increment,original,
      FR7022Second.base,FR7022Second.extra,Nat.add_sub_cancel]
  rw [e]
  exact source 1000 a r.params.scale
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def goodRow (r : Packed) : Prop := boundOK r = true ∧
  (certified r r.params.alphaLo && certified r r.params.alphaHi) = true
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def pass : List Packed → Prop
  | [] => True
  | r::rest => goodRow r ∧ pass rest
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good_of_mem {r : Packed} (xs : List Packed) (h : pass xs) (hr : r∈xs) : goodRow r := by
  induction xs with
  | nil => simp at hr
  | cons x xs ih =>
    rcases List.mem_cons.mp hr with eq | rest
    · exact eq ▸ h.1
    · exact ih h.2 rest
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pair_of_good (r : Packed) (good : goodRow r) (src : SourceCorrect) :
    CountBound r sign r.params.alphaLo ∧ CountBound r sign r.params.alphaHi := by
  obtain ⟨pr,ck⟩ := good
  have hB := (of_decide_eq_true pr).1
  have hc : certified r r.params.alphaLo = true ∧ certified r r.params.alphaHi = true := by simpa only [Bool.and_eq_true] using ck
  exact ⟨bound_from_word r sign sign_bounded _ (Or.inl rfl) pr (row_word r hB _ src) hc.1,
    bound_from_word r sign sign_bounded _ (Or.inr rfl) pr (row_word r hB _ src) hc.2⟩
end FR7022TwoStage
namespace FR7022TwoStage
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def coveredRows : List Packed := [q2,q4,q6,q8,q10,q12,q14,q16,q18,q20,q22,q24,q26,q28,q30,q32,q34,q36,q38,q40,q42,q44,q46,q48,q50,q52,q53,q54,q55,q56,q57,q58,q59,q60,q61,q62,q63,q64,q65,q66,q67,q68,q69,q70,q71,q72,q73,q74,q75,q76,q77,q78,q79,q80,q81,q82,q83,q84,q85,q86,q87,q88,q89,q90,q91,q92,q93,q94,q95,q96,q97,q98,q99,q100,q101,q102,q103,q104,q105]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rows_pass : pass coveredRows := ⟨⟨q2_parameters,q2_verified⟩,⟨q4_parameters,q4_verified⟩,⟨q6_parameters,q6_verified⟩,⟨q8_parameters,q8_verified⟩,⟨q10_parameters,q10_verified⟩,⟨q12_parameters,q12_verified⟩,⟨q14_parameters,q14_verified⟩,⟨q16_parameters,q16_verified⟩,⟨q18_parameters,q18_verified⟩,⟨q20_parameters,q20_verified⟩,⟨q22_parameters,q22_verified⟩,⟨q24_parameters,q24_verified⟩,⟨q26_parameters,q26_verified⟩,⟨q28_parameters,q28_verified⟩,⟨q30_parameters,q30_verified⟩,⟨q32_parameters,q32_verified⟩,⟨q34_parameters,q34_verified⟩,⟨q36_parameters,q36_verified⟩,⟨q38_parameters,q38_verified⟩,⟨q40_parameters,q40_verified⟩,⟨q42_parameters,q42_verified⟩,⟨q44_parameters,q44_verified⟩,⟨q46_parameters,q46_verified⟩,⟨q48_parameters,q48_verified⟩,⟨q50_parameters,q50_verified⟩,⟨q52_parameters,q52_verified⟩,⟨q53_parameters,q53_verified⟩,⟨q54_parameters,q54_verified⟩,⟨q55_parameters,q55_verified⟩,⟨q56_parameters,q56_verified⟩,⟨q57_parameters,q57_verified⟩,⟨q58_parameters,q58_verified⟩,⟨q59_parameters,q59_verified⟩,⟨q60_parameters,q60_verified⟩,⟨q61_parameters,q61_verified⟩,⟨q62_parameters,q62_verified⟩,⟨q63_parameters,q63_verified⟩,⟨q64_parameters,q64_verified⟩,⟨q65_parameters,q65_verified⟩,⟨q66_parameters,q66_verified⟩,⟨q67_parameters,q67_verified⟩,⟨q68_parameters,q68_verified⟩,⟨q69_parameters,q69_verified⟩,⟨q70_parameters,q70_verified⟩,⟨q71_parameters,q71_verified⟩,⟨q72_parameters,q72_verified⟩,⟨q73_parameters,q73_verified⟩,⟨q74_parameters,q74_verified⟩,⟨q75_parameters,q75_verified⟩,⟨q76_parameters,q76_verified⟩,⟨q77_parameters,q77_verified⟩,⟨q78_parameters,q78_verified⟩,⟨q79_parameters,q79_verified⟩,⟨q80_parameters,q80_verified⟩,⟨q81_parameters,q81_verified⟩,⟨q82_parameters,q82_verified⟩,⟨q83_parameters,q83_verified⟩,⟨q84_parameters,q84_verified⟩,⟨q85_parameters,q85_verified⟩,⟨q86_parameters,q86_verified⟩,⟨q87_parameters,q87_verified⟩,⟨q88_parameters,q88_verified⟩,⟨q89_parameters,q89_verified⟩,⟨q90_parameters,q90_verified⟩,⟨q91_parameters,q91_verified⟩,⟨q92_parameters,q92_verified⟩,⟨q93_parameters,q93_verified⟩,⟨q94_parameters,q94_verified⟩,⟨q95_parameters,q95_verified⟩,⟨q96_parameters,q96_verified⟩,⟨q97_parameters,q97_verified⟩,⟨q98_parameters,q98_verified⟩,⟨q99_parameters,q99_verified⟩,⟨q100_parameters,q100_verified⟩,⟨q101_parameters,q101_verified⟩,⟨q102_parameters,q102_verified⟩,⟨q103_parameters,q103_verified⟩,⟨q104_parameters,q104_verified⟩,⟨q105_parameters,q105_verified⟩,True.intro⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_pairs (r : Packed) (hr : r∈coveredRows)  : CountBound r FR7022Second.sign r.params.alphaLo ∧ CountBound r FR7022Second.sign r.params.alphaHi := pair_of_good r (good_of_mem _ rows_pass hr) FR7022Second.correctedWord
end FR7022TwoStage
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022ProgressionTail
open Finset
end FR7022ProgressionTail
namespace FR7022TailCoefficients
open Finset
def positiveBits : ℕ := 4375244540887692929201012076453091842270142628553079148257566174243942641277925997958801498631459775338635065550430291437041907412341552636735637345606277021783195976465663159667938386855881280648717815427658654889739922620529081241066156896203452419580566171782378986722102167211251220921940445908029174790376068892898336465616082672825461061284666334645667244280406454603958376673197991208701264598837392510020511461691560920900125071429385428849508165664706412337173395730235695378166920510455179298715913042753716420129833118910713276837361401790232556919165344997485671499976861006904656486517012749693665202262156081482051453462005244482845040184944603415405601200294801739163625479856595755116533802216666684679335995381892540642255182668478448342030642981181339583342082166181473873018128886703017194895914769102196308685394282947314258827122699844231173221173672682781879971976777637371334267635271108362296611473854035538735786358370016326542655795229412487452549957880271314571046522260233656410626296633219573056356750235187962246580689930183529755078874261170429505017585970077210583262748355981256791169072406008808417829266179138
def negativeBits : ℕ := 1226272546120844461864561007325799316384974111801254158504776751126923247678827413881192466442958786038667336231561737530758783550053746011679138765613684835192487010446363710634731470436936751793602188589960924502439371347758055726671884639001300328823934519205264196202568505075447983916398940660851283467419725242481277244867414763342858963271480567332447422287361879729386320930456593410118728256663791991841678398975060900587820180865236510898135418168695746010820863734629253268787493274393551696023383258367307404101111722244806866840463616105810587773632312539706647924361583749149364774460638319689682212546253147608559828036025210837092894701076154854846659805787413007639155766238781552772360298142042417228537145621537175839839412826586473250062141739843353722573657798668093577990020489255191602681355183919787183801934102134384364099818250475329888964633086126148083548986845333109018862182315951892469684388049280794893533481195763559210418349560984036673868850766594419935544091896145293509690169956494610143299366402147436227119189823230635118188230994011541934030627815774864419976937048097032437929854375315854471496676812972
def coefficientSign (k : ℕ) : ℤ :=
  if positiveBits.testBit k then 1 else if negativeBits.testBit k then -1 else 0
def commonMultiple : ℕ := 5157169965563293454320527512278747758474263544853589583009538033848758936772500367196811716579946578552771164260151895076565918829939072809978040242147954461185824814211598636880626727219048820861003667379393479139646123930291535292188571108416507109242963006043256925894576214647747922610528209041402562139495480630559016218850236118596345721493276099047365299893172348654092491670060296346055331801656140978635787477423112600945130839095257597693038987817480745796222970442155464971987126659561725094744964373764410407520761630572864385687207875003655021668248919889228820381387152008947123807540677818245236771244807416467475056353449245015024051753361333250371135484310772126133433870441962252325955554379092402058289847623325723910323349042683759386940485433384053034491182476318761401588816060140874864211108952071872547948110676700672276822636413870722226290264190538553035965646089097794845686983400835281713698848434764140348378496857873166159066899089097449334513347593537541808324647558759503084805519607531342957389820224671886804183743394604766134717768859699263599511925196486522436085654116435690438512492083112226437986313327421589099520250403360986368212051948804994275761098853826469855123907052069129623936893346849781886611336320596180470787748828268336482423782343991716983708941590357434814369374161582456989547788919499267102670026702069208563451336637083578031420192302693745996775888967078185514423042005517853776664868575993371105991846038635380664138269917141864418576386199136684154403541272012200522846892213721611990181350953856670146899414452352589731042032935623346323645584031915881450973748896785361318488263879123200000
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem common_dvd : ∀ k ∈ Icc 1 3800, 0 < k ∧ k ∣ commonMultiple := by decide +kernel
def baseCoeff (k : ℕ) : ℤ := coefficientSign k * (if k ≤ 2508 then 1292 else ((3800-k:ℕ):ℤ))
def extraCoeff (k : ℕ) : ℤ := if 2508 < k then 1 else 0
end FR7022TailCoefficients
namespace FR7022CompactTail
open Finset FR7022ProgressionTail FR7022TailCoefficients
structure Row where
  q : ℕ
  al : ℤ
  ah : ℤ
  mass : ℕ
  budget : ℕ
  bases : ℕ
  invs : ℕ
def Row.S (r : Row) := (Icc 1 3800).filter (fun k => k.Coprime r.q)
def Row.units (r : Row) := (range r.q).filter (fun u => u.Coprime r.q)
def Row.inverse (r : Row) (k : ℕ) : ℕ := (r.invs >>> (7*k)) % 128
def Row.res (r : Row) (h k : ℕ) := (h % r.q*r.inverse (k % r.q)) % r.q
def Row.m (r : Row) (h k : ℕ) : ℤ := r.q-2*(firstResidue r.q (r.res h k):ℤ)
def Row.z (r : Row) (h : ℕ) : ℤ := if h % r.q=1 % r.q then 1 else 0
def Row.fac (r : Row) : ℤ := 2*(r.q:ℤ)*1292000
def Row.cap (r : Row) : ℤ := 2*(r.q:ℤ)*r.budget-r.q*r.mass
def Row.bSum (r : Row) (u : ℕ) : ℤ := (((r.bases >>> (20*u)) % 1048576:ℕ):ℤ)-524288
def Row.numExtra (r : Row) (u : ℕ) : ℤ := (((3800-u)/r.q-(2508-u)/r.q:ℕ):ℤ)
def Row.tab (r : Row) (v : ℤ) (u : ℕ) : ℤ := 1000*r.bSum u+v*r.numExtra u
def Row.low (r : Row) (h : ℕ) : ℤ := (∑ u ∈ r.units, min (r.tab r.al u*r.m h u) (r.tab r.ah u*r.m h u))-r.fac*r.z h
def Row.high (r : Row) (h : ℕ) : ℤ := (∑ u ∈ r.units, max (r.tab r.al u*r.m h u) (r.tab r.ah u*r.m h u))-r.fac*r.z h
def fastSum (q u : ℕ) (v : ℤ) : ℤ := ∑ j ∈ range ((3800-u)/q+1), endpointWeight baseCoeff extraCoeff v 1000 (u+q*j)
noncomputable def Row.alpha (r : Row) : ℝ :=
  -(harmonicInteger r.S baseCoeff commonMultiple:ℝ)/(harmonicInteger r.S extraCoeff commonMultiple:ℝ)
noncomputable def Row.c (r : Row) : ℕ → ℝ := affineCoeff baseCoeff extraCoeff 1292 r.alpha
structure Certified (r : Row) : Prop where
  qlow : 2 ≤ r.q
  qhigh : r.q ≤ 105
  slope : 0 < harmonicInteger r.S extraCoeff commonMultiple
  alBound : r.al*harmonicInteger r.S extraCoeff commonMultiple ≤ -harmonicInteger r.S baseCoeff commonMultiple*1000
  ahBound : -harmonicInteger r.S baseCoeff commonMultiple*1000 ≤ r.ah*harmonicInteger r.S extraCoeff commonMultiple
  norm : endpointMass r.S baseCoeff extraCoeff r.al r.ah 1000 = r.mass
  inverses : ∀ u ∈ r.units, (r.inverse u*u) % r.q=1
  table : ∀ u ∈ r.units, fastSum r.q u r.al = r.tab r.al u ∧ fastSum r.q u r.ah = r.tab r.ah u
  centers : ∀ h ∈ r.units, -r.cap ≤ r.low h ∧ r.high h ≤ r.cap
private theorem in_units (r : Row) (hq : 0<r.q) {k : ℕ} (hc : k.Coprime r.q) : k % r.q ∈ r.units := by
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),?_⟩
  change Nat.gcd (k % r.q) r.q = 1
  rw [←Nat.gcd_rec r.q k,Nat.gcd_comm]
  exact hc
private theorem resolve_ok (r : Row) (H : Certified r) (h k : ℕ) (hc : k.Coprime r.q) :
    r.res h k*k ≡ h [MOD r.q] := by
  have hq := H.qlow
  have hi : r.inverse (k % r.q)*(k % r.q) ≡ 1 [MOD r.q] := by
    change _ % r.q=1 % r.q
    rw [Nat.mod_eq_of_lt (show 1<r.q by omega)]
    exact H.inverses _ (in_units r (by omega) hc)
  have ik := (((Nat.mod_modEq k r.q).mul_left (r.inverse (k % r.q))).symm).trans hi
  calc
    r.res h k*k ≡ (h % r.q*r.inverse (k % r.q))*k [MOD r.q] := (Nat.mod_modEq _ _).mul_right k
    _ = (h % r.q)*(r.inverse (k % r.q)*k) := by ring
    _ ≡ (h % r.q)*1 [MOD r.q] := ik.mul_left _
    _ = h % r.q := by simp
    _ ≡ h [MOD r.q] := Nat.mod_modEq _ _
private theorem sum_lane (r : Row) (H : Certified r) {u : ℕ} (hu : u∈r.units) (v : ℤ) :
    (∑ k ∈ r.S.filter (fun k => k % r.q=u), endpointWeight baseCoeff extraCoeff v 1000 k) = fastSum r.q u v := by
  have hq := H.qlow
  have hp : 0<r.q := by omega
  have hlt := mem_range.mp (mem_filter.mp hu).1
  have hc := (mem_filter.mp hu).2
  have hup : 0<u := by
    by_contra! h0
    have hz : u=0 := by omega
    rw [hz] at hc
    simp only [Nat.coprime_zero_left] at hc
    omega
  have hmax := H.qhigh
  have hset : r.S.filter (fun k => k % r.q=u) = (range ((3800-u)/r.q+1)).image (fun j => u+r.q*j) := by
    ext k
    simp only [Row.S,mem_filter,mem_Icc,mem_image,mem_range]
    constructor
    · rintro ⟨⟨⟨hk1,hk2⟩,_⟩,hm⟩
      have he := Nat.mod_add_div k r.q
      rw [hm] at he
      refine ⟨k/r.q,?_,he⟩
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le hp).mpr
      rw [Nat.mul_comm]
      omega
    · rintro ⟨j,hj,rfl⟩
      have hj' := (Nat.le_div_iff_mul_le hp).mp (Nat.lt_succ_iff.mp hj)
      rw [Nat.mul_comm] at hj'
      have um : (u+r.q*j) % r.q=u := by simp [Nat.add_mod,Nat.mod_eq_of_lt hlt]
      have uc : (u+r.q*j).Coprime r.q := by
        change Nat.gcd (u+r.q*j) r.q = 1
        rw [Nat.gcd_comm,Nat.gcd_rec r.q,um]
        exact hc
      exact ⟨⟨⟨by omega,by omega⟩,uc⟩,um⟩
  unfold fastSum
  rw [hset,sum_image]
  intro x hx y hy he
  change u+r.q*x=u+r.q*y at he
  exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel he)
theorem infinite_tail (r : Row) (H : Certified r) (h t : ℕ) (hh : h.Coprime r.q) :
    |G r.S r.c r.q h t - (if h % r.q=1 % r.q then (1:ℝ) else 0)| ≤ (r.budget:ℝ)/1292000 := by
  have hq := H.qlow
  have hqp : (0:ℝ)<r.q := by exact_mod_cast (show 0<r.q by omega)
  have hM : 0<commonMultiple := by decide
  have hs : ∀ k∈r.S, 0<k ∧ k∣commonMultiple := fun k hk => common_dvd k (mem_filter.mp hk).1
  have hz : (∑ k∈r.S,r.c k/k)=0 := by
    exact (affine_cancel_iff_integer_ratio _ _ _ _ hM hs _ _ (by norm_num) H.slope).mpr rfl
  have hab := cancellation_bracket_of_integers _ _ _ _ hM hs 1292 r.alpha (by norm_num) H.slope hz r.al 1000 r.ah 1000
    (by decide) (by decide) H.alBound H.ahBound
  have hE (k : ℕ) : 0≤extraCoeff k := by unfold extraCoeff; split <;> omega
  have hm := affine_l1_le_endpointMass r.S baseCoeff extraCoeff (fun k _ => hE k) 1292 r.alpha (by norm_num : (0:ℝ)<1292) _ _ _ (by decide : (0:ℤ)<1000) hab.1 hab.2
  rw [H.norm] at hm
  change (∑ k∈r.S,|r.c k|) ≤ (r.mass:ℝ)/(1292*1000) at hm
  have laneBounds {u : ℕ} (hu : u∈r.units) :
      (r.tab r.al u:ℝ) ≤ ∑ k∈r.S.filter (fun k => k % r.q=u), 1292000*r.c k ∧
      (∑ k∈r.S.filter (fun k => k % r.q=u), 1292000*r.c k) ≤ (r.tab r.ah u:ℝ) := by
    have pl := (sum_lane r H hu r.al).trans (H.table u hu).1
    have ph := (sum_lane r H hu r.ah).trans (H.table u hu).2
    rw [←pl,←ph]
    simp only [Int.cast_sum]
    constructor
    · apply sum_le_sum
      intro k hk
      have e := mul_le_mul_of_nonneg_right hab.1 (show 0≤(extraCoeff k:ℝ) by exact_mod_cast hE k)
      unfold endpointWeight Row.c affineCoeff
      push_cast at *
      linarith
    · apply sum_le_sum
      intro k hk
      have e := mul_le_mul_of_nonneg_right hab.2 (show 0≤(extraCoeff k:ℝ) by exact_mod_cast hE k)
      unfold endpointWeight Row.c affineCoeff
      push_cast at *
      linarith
  let C : ℝ := ∑ k∈r.S,r.c k * residueCenter r.q (r.res h k)
  let Z : ℝ := if h % r.q=1 % r.q then 1 else 0
  have fac_pos : 0<(r.fac:ℝ) := by simp [Row.fac]; positivity
  have fac_eq : (r.fac:ℝ) = 1292000*(2*(r.q:ℝ)) := by simp [Row.fac]; ring
  have m_eq (k : ℕ) : (r.m h k:ℝ) = (2*(r.q:ℝ))*residueCenter r.q (r.res h k) := by
    simp only [Row.m,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,residueCenter]
    field_simp
  have grouped : (r.fac:ℝ)*C =
      ∑ u∈r.units, (∑ k∈r.S.filter (fun k => k % r.q=u),1292000*r.c k)*(r.m h u:ℝ) := by
    have mp : ∀ k∈r.S,k % r.q∈r.units := fun k hk => in_units r (by omega) (mem_filter.mp hk).2
    dsimp only [C]
    rw [mul_sum,←sum_fiberwise_of_maps_to mp (fun k => (r.fac:ℝ)*(r.c k*residueCenter r.q (r.res h k)))]
    apply sum_congr rfl
    intro u hu
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    have he := (mem_filter.mp hk).2
    have me : r.m h u = r.m h k := by rw [←he]; simp [Row.m,Row.res]
    rw [me,m_eq,fac_eq]
    ring
  have lr {u : ℕ} (hu : u∈r.units) :
      ((min (r.tab r.al u*r.m h u) (r.tab r.ah u*r.m h u):ℤ):ℝ) ≤
        (∑ k∈r.S.filter (fun k => k % r.q=u),1292000*r.c k)*(r.m h u:ℝ) ∧
        (∑ k∈r.S.filter (fun k => k % r.q=u),1292000*r.c k)*(r.m h u:ℝ) ≤
      ((max (r.tab r.al u*r.m h u) (r.tab r.ah u*r.m h u):ℤ):ℝ) := by
    have a := laneBounds hu
    simp only [Int.cast_min,Int.cast_max,Int.cast_mul]
    by_cases hp : 0≤(r.m h u:ℝ)
    · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_right a.1 hp),
        (mul_le_mul_of_nonneg_right a.2 hp).trans (le_max_right ..)⟩
    · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_right a.2 (le_of_not_ge hp)),
        (mul_le_mul_of_nonpos_right a.1 (le_of_not_ge hp)).trans (le_max_left ..)⟩
  have lc := sum_le_sum (s:=r.units) (fun u hu => (lr hu).1)
  have uc := sum_le_sum (s:=r.units) (fun u hu => (lr hu).2)
  rw [←grouped] at lc uc
  have ie := H.centers (h % r.q) (in_units r (by omega) hh)
  have leq : r.low (h % r.q)=r.low h := by simp [Row.low,Row.m,Row.res,Row.z]
  have ueq : r.high (h % r.q)=r.high h := by simp [Row.high,Row.m,Row.res,Row.z]
  rw [leq,ueq] at ie
  have lo : -(r.cap:ℝ) ≤ (r.low h:ℝ) := by exact_mod_cast ie.1
  have hi : (r.high h:ℝ) ≤ (r.cap:ℝ) := by exact_mod_cast ie.2
  have ze : (r.z h:ℝ)=Z := by unfold Row.z Z; split <;> norm_num
  simp only [Row.low,Int.cast_sub,Int.cast_mul,Int.cast_sum,ze] at lo
  simp only [Row.high,Int.cast_sub,Int.cast_mul,Int.cast_sum,ze] at hi
  have ca : |C-Z| ≤ (r.cap:ℝ)/r.fac := by
    apply abs_le.mpr
    constructor
    · rw [←neg_div]
      apply (div_le_iff₀ fac_pos).mpr
      nlinarith only [lc,lo]
    · apply (le_div_iff₀ fac_pos).mpr
      nlinarith only [uc,hi]
  have tails := centered_tail_bound r.S r.c r.q h t (r.res h) (by omega) (fun k hk => (hs k hk).1)
    (fun k hk => (mem_filter.mp hk).2) (fun k hk => resolve_ok r H h k (mem_filter.mp hk).2) hz Z
  change |G r.S r.c r.q h t-Z| ≤ |C-Z|+(∑ k∈r.S,|r.c k|)/2 at tails
  apply tails.trans
  calc
    _ ≤ (r.cap:ℝ)/r.fac + ((r.mass:ℝ)/(1292*1000))/2 := by linarith
    _ = _ := by
      rw [fac_eq]
      simp only [Row.cap,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
      field_simp
      ring
end FR7022CompactTail
namespace FR7022CompactTail
open Finset FR7022TailCoefficients FR7022ProgressionTail
structure ScalarFacts (r : Row) : Prop where
  pos : 0 < harmonicInteger r.S extraCoeff commonMultiple
  left : r.al*harmonicInteger r.S extraCoeff commonMultiple ≤ -harmonicInteger r.S baseCoeff commonMultiple*1000
  right : -harmonicInteger r.S baseCoeff commonMultiple*1000 ≤ r.ah*harmonicInteger r.S extraCoeff commonMultiple
  l1 : endpointMass r.S baseCoeff extraCoeff r.al r.ah 1000 = r.mass
end FR7022CompactTail
namespace FR7022CompactTail
open Finset FR7022ProgressionTail
abbrev Lane := ℤ × ℤ × ℕ
def unitList (r : Row) := (List.range r.q).filter fun u => u.Coprime r.q
def laneList (r : Row) : List Lane := (unitList r).map fun u =>
  (r.tab r.al u,r.tab r.ah u,r.inverse (u % r.q))
def factor (q h inv : ℕ) : ℤ := (q:ℤ)-2*(firstResidue q ((h % q*inv) % q):ℤ)
def loPart (q h : ℕ) (e : Lane) : ℤ := min (e.1*factor q h e.2.2) (e.2.1*factor q h e.2.2)
def hiPart (q h : ℕ) (e : Lane) : ℤ := max (e.1*factor q h e.2.2) (e.2.1*factor q h e.2.2)
def tally (q h : ℕ) : List Lane → ℤ → ℤ → ℤ×ℤ
  | [], l, u => (l,u)
  | x::xs, l, u =>
    let d:=factor q h x.2.2
    let a:=x.1*d
    let b:=x.2.1*d
    tally q h xs (l+min a b) (u+max a b)
private theorem tally_spec (q h : ℕ) (xs : List Lane) (l u : ℤ) : tally q h xs l u =
    (l+(xs.map (loPart q h)).sum,u+(xs.map (hiPart q h)).sum) := by
  induction xs generalizing l u with
  | nil => simp [tally]
  | cons a as ih => simp [tally,ih,loPart,hiPart,add_assoc]
private theorem sum_unitList (r : Row) (f : ℕ→ℤ) : ((unitList r).map f).sum=∑ i∈r.units,f i := by
  have nd : (unitList r).Nodup := List.Nodup.filter _ List.nodup_range
  have eq : (unitList r).toFinset=r.units := by ext i; simp [unitList,Row.units]
  simpa only [eq] using (List.sum_toFinset f nd).symm
theorem tally_eq (r : Row) (h : ℕ) : tally r.q h (laneList r) 0 0 =
    ((∑ u∈r.units,min (r.tab r.al u*r.m h u) (r.tab r.ah u*r.m h u)),
     (∑ u∈r.units,max (r.tab r.al u*r.m h u) (r.tab r.ah u*r.m h u))) := by
  rw [tally_spec]
  simp only [zero_add,laneList,List.map_map,sum_unitList]
  rfl
end FR7022CompactTail
namespace FR7022CompactTail
open Finset FR7022TailCoefficients FR7022ProgressionTail
def laneWalk (q u : ℕ) : ℕ → ℤ → ℤ → ℤ×ℤ
  | 0,b,e => (b,e)
  | n+1,b,e =>
    let k:=u+q*n
    laneWalk q u n (b+baseCoeff k) (e+extraCoeff k)
private theorem laneWalk_spec (q u n : ℕ) (b e : ℤ) : laneWalk q u n b e =
    (b+∑ j∈range n,baseCoeff (u+q*j),e+∑ j∈range n,extraCoeff (u+q*j)) := by
  induction n generalizing b e with
  | zero => simp [laneWalk]
  | succ n ih => simp only [laneWalk,ih,sum_range_succ]; congr 1 <;> ac_rfl
def laneCheck (r : Row) : Bool := (unitList r).all fun u =>
  let x:=laneWalk r.q u ((3800-u)/r.q+1) 0 0
  decide (x.1=r.bSum u ∧ x.2=r.numExtra u)
theorem fastSum_of_lanes (r : Row) (data : laneCheck r=true) {u : ℕ} (hu : u∈r.units) (a : ℤ) :
    fastSum r.q u a = r.tab a u := by
  have hm : u∈unitList r := by simpa [unitList,Row.units] using hu
  have f := List.all_eq_true.mp data u hm
  dsimp only at f
  rw [laneWalk_spec] at f
  simp only [zero_add] at f
  have p := of_decide_eq_true f
  unfold fastSum Row.tab endpointWeight
  rw [sum_add_distrib,←mul_sum,←mul_sum,p.1,p.2]
end FR7022CompactTail
namespace FR7022CompactTail
open Finset FR7022ProgressionTail
private theorem pos_unit (r : Row) (hq : 2≤r.q) {h : ℕ} (hh : h∈r.units) : 0<h := by
  have hc := (mem_filter.mp hh).2
  by_contra! hn
  have he : h=0 := by omega
  rw [he,Nat.coprime_zero_left] at hc
  omega
private theorem opp_unit (r : Row) (hq : 2≤r.q) {h : ℕ} (hh : h∈r.units) : r.q-h∈r.units := by
  have hh' := mem_range.mp (mem_filter.mp hh).1
  have hc := (mem_filter.mp hh).2
  have hp := pos_unit r hq hh
  refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
  have z : (r.q-h).Coprime (h+(r.q-h)) := Nat.coprime_add_self_right.mpr ((Nat.coprime_sub_self_left hh'.le).mpr hc.symm)
  simpa only [Nat.add_sub_of_le hh'.le] using z
private theorem opp_m (r : Row) (hq : 2≤r.q) (inv : ∀ u∈r.units, (r.inverse u*u) % r.q=1)
    {h u : ℕ} (hh : h∈r.units) (hu : u∈r.units) : r.m (r.q-h) u = -r.m h u := by
  let q:=r.q
  let i:=r.inverse u
  have hpos : 0<h := pos_unit r hq hh
  have hlt : h<q := mem_range.mp (mem_filter.mp hh).1
  have ult : u<q := mem_range.mp (mem_filter.mp hu).1
  have qp : 0<q := by dsimp only [q]; omega
  have hsmall : q-h<q := by omega
  let a:=(h*i) % q
  let b:=((q-h)*i) % q
  have ax : a<q := Nat.mod_lt _ qp
  have bx : b<q := Nat.mod_lt _ qp
  have pa : 0<a := by
    have id : (a*u) % q=h := calc
      _ = (h*i*u) % q := Nat.mod_mul_mod _ _ _
      _ = (h*(i*u)) % q := by rw [Nat.mul_assoc]
      _ = (h*((i*u) % q)) % q := (Nat.mul_mod_mod _ _ _).symm
      _ = h := by rw [show (i*u) % q=1 from inv u hu,Nat.mul_one,Nat.mod_eq_of_lt hlt]
    by_contra! ha
    have az:a=0 := by omega
    rw [az,Nat.zero_mul,Nat.zero_mod] at id
    omega
  have abmod : (a+b) % q=0 := calc
    _ = (h*i+(q-h)*i) % q := (Nat.add_mod _ _ _).symm
    _ = ((h+(q-h))*i) % q := by rw [Nat.add_mul]
    _ = 0 := by rw [show h+(q-h)=q by omega,Nat.mul_mod_right]
  have lo : q≤a+b := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero abmod)
  have sm : a+b-q<q := by omega
  rw [Nat.mod_eq_sub_mod lo,Nat.mod_eq_of_lt sm] at abmod
  have ab : a+b=q := by omega
  have pb : 0<b := by omega
  change (q:ℤ)-2*(firstResidue q (((q-h) % q * r.inverse (u % q)) % q):ℤ) =
    -((q:ℤ)-2*(firstResidue q ((h % q*r.inverse (u % q)) % q):ℤ))
  rw [Nat.mod_eq_of_lt hlt,Nat.mod_eq_of_lt hsmall,Nat.mod_eq_of_lt ult]
  change (q:ℤ)-2*(firstResidue q b:ℤ) = -((q:ℤ)-2*(firstResidue q a:ℤ))
  simp only [firstResidue,Nat.mod_eq_of_lt ax,Nat.mod_eq_of_lt bx,Nat.ne_of_gt pa,Nat.ne_of_gt pb,if_false]
  omega
private theorem oppositePair (r : Row) (hq : 2≤r.q) (inv : ∀ u∈r.units, (r.inverse u*u) % r.q=1)
    {h : ℕ} (hh : h∈r.units) : tally r.q (r.q-h) (laneList r) 0 0 =
      (-(tally r.q h (laneList r) 0 0).2,-(tally r.q h (laneList r) 0 0).1) := by
  simp only [tally_eq]
  apply Prod.ext <;> simp only <;> rw [←sum_neg_distrib] <;> apply sum_congr rfl <;> intro u hu <;>
    rw [opp_m r hq inv hh hu] <;> simp only [mul_neg,min_def,max_def] <;> split <;> split <;> omega
def good (r : Row) (h : ℕ) (v : ℤ×ℤ) : Prop := -r.cap≤v.1-r.fac*r.z h ∧ v.2-r.fac*r.z h≤r.cap
instance (r : Row) (h : ℕ) (v : ℤ×ℤ) : Decidable (good r h v) := inferInstanceAs (Decidable (_ ∧ _))
def halfTest (r : Row) (xs : List Lane) : Bool := (unitList r).all fun h =>
  if 2*h≤r.q then
    let v:=tally r.q h xs 0 0
    decide (good r h v ∧ good r (r.q-h) (-v.2,-v.1))
  else true
theorem centers_of_half (r : Row) (hq : 2≤r.q) (inv : ∀ u∈r.units, (r.inverse u*u) % r.q=1)
    (xs : List Lane) (rows : laneList r=xs) (ok : halfTest r xs=true)
    (h : ℕ) (hh : h∈r.units) : -r.cap≤r.low h ∧ r.high h≤r.cap := by
  subst xs
  have small (v : ℕ) (hv : v∈r.units) (hv' : 2*v≤r.q) :
      good r v (tally r.q v (laneList r) 0 0) ∧ good r (r.q-v) (tally r.q (r.q-v) (laneList r) 0 0) := by
    have mem : v∈unitList r := by simpa [unitList,Row.units] using hv
    have b := List.all_eq_true.mp ok v mem
    dsimp only at b
    rw [if_pos hv'] at b
    rw [oppositePair r hq inv hv]
    exact of_decide_eq_true b
  have g : good r h (tally r.q h (laneList r) 0 0) := by
    by_cases isSmall : 2*h≤r.q
    · exact (small h hh isSmall).1
    · have hl : h<r.q := mem_range.mp (mem_filter.mp hh).1
      have b := (small (r.q-h) (opp_unit r hq hh) (by omega)).2
      rwa [show r.q-(r.q-h)=h by omega] at b
  rw [tally_eq] at g
  exact g
end FR7022CompactTail
namespace FR7022CompactTail
open FR7022ProgressionTail
structure Core (r : Row) : Prop where
  lo : 2≤r.q
  hi : r.q≤105
  inv : ∀ u∈r.units, (r.inverse u*u) % r.q=1
  lanes : ∀ u∈r.units, fastSum r.q u r.al=r.tab r.al u ∧ fastSum r.q u r.ah=r.tab r.ah u
  bounds : ∀ h∈r.units, -r.cap≤r.low h ∧ r.high h≤r.cap
theorem certified_of_core (r : Row) (c : Core r) (s : ScalarFacts r) : Certified r :=
  ⟨c.lo,c.hi,s.pos,s.left,s.right,s.l1,c.inv,c.lanes,c.bounds⟩
theorem numericCore (r : Row) (xs : List Lane) (ok : 2≤r.q ∧ r.q≤105 ∧
    (∀u∈r.units,(r.inverse u*u) % r.q=1) ∧ laneCheck r=true ∧ laneList r=xs ∧ halfTest r xs=true) : Core r := by
  rcases ok with ⟨lo,hi,inv,table,ls,h⟩
  exact ⟨lo,hi,inv,fun u hu => ⟨fastSum_of_lanes _ table hu _,fastSum_of_lanes _ table hu _⟩,
    centers_of_half r lo inv xs ls h⟩
end FR7022CompactTail
namespace FR7022CompactData
open FR7022CompactTail FR7022TailCoefficients FR7022ProgressionTail
def r2 : Row := ⟨2,-7755,-7754,1652914426,827749213,0x7a62d00000,0x80⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c2 : Core r2 := numericCore r2 (laneList r2) (by decide +kernel)
def r4 : Row := ⟨4,-7755,-7754,1652914426,829901044,0x7e3e6000007c24700000,0x600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4 : Core r4 := numericCore r4 (laneList r4) (by decide +kernel)
def r6 : Row := ⟨6,-66375,-66374,1243217805,623821183,0x7507800000000000000076aa700000,0x2800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c6 : Core r6 := numericCore r6 (laneList r6) (by decide +kernel)
def r8 : Row := ⟨8,-7755,-7754,1652914426,831677042,0x8105d000007d909000007d389000007e93e00000,0xe002800600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c8 : Core r8 := numericCore r8 (laneList r8) (by decide +kernel)
def r10 : Row := ⟨10,-39646,-39645,1380549036,695689325,0x7bd39000007a9510000000000000007cc25000007e12b00000,0x48006000000e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c10 : Core r10 := numericCore r10 (laneList r10) (by decide +kernel)
def r12 : Row := ⟨12,-66375,-66374,1243217805,624451905,0x7a9b70000000000000007c149000007a6c10000000000000007a95e00000,0x16000000e002800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c12 : Core r12 := numericCore r12 (laneList r12) (by decide +kernel)
def r14 : Row := ⟨14,-30917,-30916,1449228758,728604911,0x7d9d0000007d843000007cba00000000000000007d600000007f3da000007ec4b00000,0x680120058000001800a00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c14 : Core r14 := numericCore r14 (laneList r14) (by decide +kernel)
def r16 : Row := ⟨16,-7755,-7754,1652914426,840051166,0x7ee23000007c2ec000007df14000007dfa8000008223a000008161d000007f475000008099600000,0x1e0028006004800e006801600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16 : Core r16 := numericCore r16 (laneList r16) (by decide +kernel)
def r18 : Row := ⟨18,-66375,-66374,1243217805,631212556,0x7e7f20000000000000007d5c600000797b20000000000000007d756000007d0d40000000000000007bd8b00000,0x88000003800a000001a005800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c18 : Core r18 := numericCore r18 (laneList r18) (by decide +kernel)
def r20 : Row := ⟨20,-39646,-39645,1380549036,695390182,0x7e104000007dd7f0000000000000007d9ef000007dee6000007dc35000007cbd20000000000000007f236000008024500000,0x26006800000880160048006000000e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c20 : Core r20 := numericCore r20 (laneList r20) (by decide +kernel)
def r22 : Row := ⟨22,-26539,-26538,1516554760,774481405,0x7efde000007d9d600000802a40000082dd0000007c28d00000000000000080782000007e8f8000007d772000007eb1a000007e5ac00000,0xa800e006800600880000028026004801e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c22 : Core r22 := numericCore r22 (laneList r22) (by decide +kernel)
def r24 : Row := ⟨24,-66375,-66374,1243217805,623272774,0x7dc2c0000000000000007dc28000007d5b00000000000000007cdc8000007cd8b0000000000000007e521000007d1110000000000000007db9600000,0x2e000002600880000068016000000e002800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c24 : Core r24 := numericCore r24 (laneList r24) (by decide +kernel)
def r26 : Row := ⟨26,-23789,-23788,1536348534,790940620,0x7d576000008152e000007e0c70000080ee40000083659000007e04500000000000000080ee8000007bd19000007b0aa000007f8c4000007f423000008010000000,0xc8022002801600b800e0000026001801e00a801200080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c26 : Core r26 := numericCore r26 (laneList r26) (by decide +kernel)
def r28 : Row := ⟨28,-30917,-30916,1449228758,743243127,0x813e9000007f3c6000007fb170000000000000007ec3e00000833fa00000807c6000007c5e7000007e47d000007d0890000000000000007e9c2000007bfe0000007e48500000,0x3600480160000006002801e006802e00c8000008802600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c28 : Core r28 := numericCore r28 (laneList r28) (by decide +kernel)
def r30 : Row := ⟨30,-244808,-244807,1049276885,527472658,0x7a5cc00000000000000000000000007b3040000000000000007b2fe000007a4580000000000000007b6c1000007ba660000000000000007ac5400000000000000000000000007b19100000,0xe80000000022000002600b80000038016000001a000000000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c30 : Core r30 := numericCore r30 (laneList r30) (by decide +kernel)
def r32 : Row := ⟨32,-7755,-7754,1652914426,842074106,0x7f1ac000007c10400000807cc0000082c7f0000082c8e00000813f5000007dead0000080d71000007fc7700000801e8000007d748000007b329000007f5ac000008022800000815c8000007fc2500000,0x3e00a8026004800e00e8036008801e002800600c802e006801600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c32 : Core r32 := numericCore r32 (laneList r32) (by decide +kernel)
def r34 : Row := ⟨34,-20568,-20567,1563317349,802117403,0x811c6000007da4c000007a197000007de8b000007da6b0000081bdb00000819a700000802e00000000000000007f5d30000080355000007d6660000080682000007f659000008462d000007dc98000007f49600000,0x10801600d803a00780060068012000003200a803e009800a003802e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c34 : Core r34 := numericCore r34 (laneList r34) (by decide +kernel)
def r36 : Row := ⟨36,-66375,-66374,1243217805,636857398,0x7d9610000000000000007f6d2000007c5270000000000000007dcb9000007fdcb0000000000000007cfda0000080e910000000000000007def4000007d28b0000000000000007fa9d000007d3090000000000000007edb100000,0x46000000e002800000680160000026008800000c802e000003e00e800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c36 : Core r36 := numericCore r36 (laneList r36) (by decide +kernel)
def r38 : Row := ⟨38,-20306,-20305,1572979465,809418603,0x7da9100000829c80000080fb2000008062b000007e8c6000007fa5c000008140c000007a57b000008275e0000000000000007f6410000082cbd000007d574000007ebb0000007f34e000007e9a4000007ea03000007ce350000080fb400000,0x128032007803600a803e011800a00e80000048042001800e008801600b801a00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c38 : Core r38 := numericCore r38 (laneList r38) (by decide +kernel)
def r40 : Row := ⟨40,-39646,-39645,1380549036,707921653,0x80321000007dc490000000000000007dcb100000805da000007f90a000007d8360000000000000007cf6c000007efdb000007dde300000801360000000000000007fd3e000007d90c000007e32b000007f39c000000000000000822ca000008126a00000,0x4e0068000008803e00e8006000000e00a802601080000128016004802e000003600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c40 : Core r40 := numericCore r40 (laneList r40) (by decide +kernel)
def r42 : Row := ⟨42,-196244,-196243,1098426830,558727541,0x7c5a50000000000000007bd0b00000000000000000000000007e120000007ba4f0000000000000007d1f6000007d1120000000000000007bea4000007d0210000000000000007e0fe000007cffd00000000000000000000000007dcf10000000000000007ef1c00000,0x14800000c8000000002600e80000128016000003e0028000006802e0000000008800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c42 : Core r42 := numericCore r42 (laneList r42) (by decide +kernel)
def r44 : Row := ⟨44,-26539,-26538,1516554760,776154653,0x7e7dc000007ee680000081084000007ef6700000808020000000000000007f2b6000007e46700000804610000081f1e000007d00b0000080802000007eb6e000007f2200000083e69000007ba8b000000000000000814cc0000080491000007d311000007cbfc00000815a100000,0x5600e804600c804e0000036014803e012802e00a800e006800600880000028026004801e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c44 : Core r44 := numericCore r44 (laneList r44) (by decide +kernel)
def r46 : Row := ⟨46,-20021,-20020,1585738015,813646341,0x822a9000007e67d000007dbf2000007c8460000080307000007fab1000007f53f00000823c700000816d9000007e6c600000808d60000000000000007f5c0000007caf6000007f30b000007f530000008085b0000080256000007fc5200000811cf000008173e0000080228000007ca8900000,0x16801e004801a0028032003800600d803a011800000580220098056013802a0148042012803e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c46 : Core r46 := numericCore r46 (laneList r46) (by decide +kernel)
def r48 : Row := ⟨48,-66375,-66374,1243217805,635777709,0x7e8cd0000000000000007d341000007e6230000000000000007e51c000007d9260000000000000007d780000007d9800000000000000007e40c000007f35f000000000000000808e7000007ef8d0000000000000007e8ac000007f46500000000000000080da1000007f7910000000000000007f78a00000,0x5e000002601480000068016000003e002800000c802e000005600880000128046000000e00e800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c48 : Core r48 := numericCore r48 (laneList r48) (by decide +kernel)
def r50 : Row := ⟨50,-39646,-39645,1380549036,704017950,0x807f4000007cb62000000000000000804130000082889000007f55e000007d91d0000000000000007e51a000007e461000007eff700000814bb0000000000000007fb30000007f95e0000081547000007f8b90000000000000007e993000007eb66000007baa9000007f75e0000000000000007fe35000007ef7d00000,0x188042000000e005801200b8000017802a009801a000004a00f803a001800000d80520138056000002200080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c50 : Core r50 := numericCore r50 (laneList r50) (by decide +kernel)
def r52 : Row := ⟨52,-23789,-23788,1536348534,791617031,0x80805000007fb92000007e680000007eba500000805a2000007cf840000000000000007facc000007bfbd000007e36b000007f0ba0000081e80000008031b000007cd71000008199c000007fa47000008233f00000830b700000810c10000000000000008141c000007fd5c000007cd3f000008080a000007d5a3000007fde500000,0x66008803e012802e01080000168006014805e004803600c80560028016018800e000002600e801e00a804600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c52 : Core r52 := numericCore r52 (laneList r52) (by decide +kernel)
def r53 : Row := ⟨53,-2575,-2574,2434251331,1242343172,0x7eed8822ef80b078000f7ef7b7cc127fb247fff580f9e7ee8c80fdc7ebcf7fef67ee2d8026680f24827d88072f812ae8039481cf97dcc7818897eea6835b97f1077e1f87f0978121881796823988022f80ef18025280c717faed7d62c7d7b67e5f5803b07e0847e2667f1aa7e5598126a7f4c18135e8159381bab801fe7ce19839a600000,0x34348c695583d0af4a60b04441d59c649d685185c5a404cc8aa3ca58081c0cc8a5c4d89f3a403144c25028246c080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c53 : Core r53 := numericCore r53 (laneList r53) (by decide +kernel)
def r54 : Row := ⟨54,-66375,-66374,1243217805,637820823,0x81bfe0000000000000007eeab000007d1630000000000000007ccd9000007e7ab0000000000000007f7d7000007f68100000000000000080bc1000007cf650000000000000007ebda000007f6150000000000000007eaca000007d5730000000000000007db5a000007f6ea00000000000000081ea3000007f3140000000000000007daea00000,0x1a8000015802e000006200e80000098022000000e0148000006805e000004a011800000c800a000003e005800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c54 : Core r54 := numericCore r54 (laneList r54) (by decide +kernel)
def r55 : Row := ⟨55,-8472,-8471,1895048552,965910078,0x7f9d48011a80caf81ab4000007e0b47f9c07f9077dbf70000000000813ae7ebed7f5f3000007e3b181a9283c5b818590000080da2000007f0017e34d0000082332817127e123818f7000007f0f87e7840000080f44000007cf927d3157e1697fc160000082f307f6ff7fadf000000000082653814647db4782e48000007ef5a7cf297fc727f9e900000,0xd8d9252004af6018000409998030a819a008802b20009826a900271800a803ad069f0010897000188710b800e4a70080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c55 : Core r55 := numericCore r55 (laneList r55) (by decide +kernel)
def r56 : Row := ⟨56,-30917,-30916,1449228758,751085062,0x825b1000007d14e000007ee500000000000000007f8160000080378000007f498000007d79d000007eb6a000007d6140000000000000007da14000007dd4800000808da000007ee3800000822780000080cc70000000000000007f4280000083082000008132e000007ee4a000007f913000007fa7500000000000000080fae000007e298000007dbab00000,0x6e0128016000003e0028056014802e01a8000008805e00e8036004804e0000006010801e006806600c8000016802600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c56 : Core r56 := numericCore r56 (laneList r56) (by decide +kernel)
def r57 : Row := ⟨57,-9818,-9817,1769266133,913739528,0x7ed97814e300000817c080aaa0000081a907f19d000007f7298340500000806bc7dd28000007e4b380b9a00000000007ea7200000807c47fd0f000007db707d68a0000082b4e7daa9000008088e820a8000007d8cc8104b000007f0fc00000000007ebc181a220000081e817e601000007e48a7e836000007eb7f80c2e0000080ce57e94b000007e12481a5800000,0x3838007220020380227c023080100a000128058d00295c00137002c8000a34014000179900d4b0034a00326200bab0074080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c57 : Core r57 := numericCore r57 (laneList r57) (by decide +kernel)
def r58 : Row := ⟨58,-19182,-19181,1598847177,822602792,0x8219b00000807e40000081921000007e9b1000007d794000007f36c00000807d80000080583000007d15e000007edea000007fc11000007f646000007ebec00000811f20000000000000007d56e000007f9d600000808a30000081665000007eb9f00000827b6000007e340000007fbee00000800cf0000082b1e000007f1cf000007d9b6000007db3a0000080fcf00000,0x1c802600b8042016802a01880360088006005800a019801e0000056003806a017806e014803e004804a0068032011804e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c58 : Core r58 := numericCore r58 (laneList r58) (by decide +kernel)
def r59 : Row := ⟨59,-1599,-1598,2437494279,1245814316,0x81a887f9077baed7fcc6800c581c437e3a67fc707f3ee8097a7ea877f183801778202e7f6f17f6f17c7ae823a68272c819e2828b27e905825148264382e697f06f831807ed307d6e9801ca7f50080d1d81cb980c5f81f3a8042380e5a7fa81805287b64a7dfbc7d90f7e60582a6a830827bdc77e6947f9037f4d2802cb806957ff5b8427c7c1c1804d880e4d7c30d8237900000,0xe8ea758bd8aa2c35a906c24ab716d121f703842936851185009c934664d2024cd683385c3b008999055619725222860f2878080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c59 : Core r59 := numericCore r59 (laneList r59) (by decide +kernel)
def r60 : Row := ⟨60,-244808,-244807,1049276885,537615706,0x7c37a00000000000000000000000007d7800000000000000007c602000007c8290000000000000007e5d1000007cc630000000000000007cee100000000000000000000000007b697000007e25200000000000000000000000007db840000000000000007ecfc000007dc2f0000000000000007d0f0000007ee030000000000000007dd7300000000000000000000000007fafa00000,0x7600000000088000018802e000000e01480000068000000003e00e8000000005e000002601a800001280160000056000000000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c60 : Core r60 := numericCore r60 (laneList r60) (by decide +kernel)
def r61 : Row := ⟨61,-1402,-1401,2438397196,1247092080,0x805147e7b081a1080cb67fed27f0237f76f808207e59c8223f80f5e821377dee680ada7ef5d80d8980278816b67e9dd7d2b6803a5800d4824517f03880ad680db6819e17c51d817c07ff9e80e187cdb380aa57f9c37eb3b7de8283d0c818eb803cc82ede7d5147de1c81ec27e7ec807237f15581f64801867f5267d2ca7f185806857e2017de628030c838ae7ffe1803ad7f15381f9c00000,0x3c3c5078c146931b0c2c28e1a109ab584019d48d50a70e2529504ed41868d8b1c106503a5a4492a72c17b864dd11746cd8ae527c080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c61 : Core r61 := numericCore r61 (laneList r61) (by decide +kernel)
def r62 : Row := ⟨62,-18701,-18700,1602129281,818801299,0x808150000080914000007d9b10000080237000007f19f000007e2890000081ffa000007ed8d000007f04f000007c90f000007e1c20000082f1d000008071e0000082008000007ec6c000000000000000803b3000007f3bc000007ff5f000007d6ad0000082daa0000083061000007f7830000082628000007db6b00000815b9000007cf8f000007d4b9000007f03f000007eb63000008120300000,0x1e8052012806a01b805a0098042019801a01d804601c804e0178000007802e00280360018062005803a0158022003801200c802a00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c62 : Core r62 := numericCore r62 (laneList r62) (by decide +kernel)
def r63 : Row := ⟨63,-15964,-15963,1630895646,835931445,0x80abf7f559000007f8767ea8e00000000008185b000007f959806a7000007db4e00000000007f1497da06000008199180be6000007f7427f262000007f0627d0ef00000000007d5d2000007fa747f114000008199600000000007f7d480ebb00000802d17fb3c000007dc8c7f0fb000008097b816200000000000831f9000008049282727000007e427000000000081b047fa85000007d0848145c00000,0xf8f805e640006e01628007400076940352c00a34001570000340027a019000045d0016ac0291400d0400011002e4c00800013100080080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c63 : Core r63 := numericCore r63 (laneList r63) (by decide +kernel)
def r64 : Row := ⟨64,-7755,-7754,1652914426,843668766,0x80ae3000007ea26000008041e0000082ea5000008121a00000813d9000007fdfe00000818d3000008347e000007f95d000007e907000007e067000008049b000007eb84000007e5b2000007ff70000007e6c9000007d6de00000803ae000007fdda0000081a74000008001c000007e0af000007f49e000007c7f9000008088b000007ee41000007d2c2000007f11100000816a40000083016000007fcb500000,0x7e00a8066004800e00e8076008801e012800600c802e0168016010803e01a8026014804e01e8036018805e002804601c806e006805600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c64 : Core r64 := numericCore r64 (laneList r64) (by decide +kernel)
def r65 : Row := ⟨65,-8288,-8287,1920079114,981433074,0x8230b7fe077eb0c7d27b000007d32b7ea8b7f16680d07000007fd4d7fac7000007eb0d000007ee4f802247ea0980430000007f5377f7e17fdaf812120000000000811df816b880694000007ecd87fdb77fc3b81cd900000810357e4e38180d00000000008042f817708170381b8b0000080cba820db81f5980a040000080f1c000007ca127e41f000007d4ed7fe177f9c98243800000815f77eb0c7ec947dcc700000,0x4040ac8006c9442400ecd80660022a24a40227cc17000031d3800b013f2a004876a00013220cf8030bcbbd00380260c00eb9382c0312c84080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c65 : Core r65 := numericCore r65 (laneList r65) (by decide +kernel)
def r66 : Row := ⟨66,-158537,-158536,1146469554,585779829,0x802ad0000000000000007e7d1000007f27600000000000000000000000008053d0000000000000007d531000007d3220000000000000007cd69000007d22c0000000000000008085a000007e02a0000000000000007db7a000007d3610000000000000007fbae000007cf1a0000000000000007f00d000007f1600000000000000007d31000000000000000000000000007f0ea000007eef20000000000000007f3a300000,0x208000006805e0000000002800000f8076000005600e800000c802200000620148000012802e000000e011800001e8000000002601a800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c66 : Core r66 := numericCore r66 (laneList r66) (by decide +kernel)
def r67 : Row := ⟨67,-1451,-1450,2441632941,1248246534,0x8207e806797eeb47db58816ac813a37e3dc7d4ca7f718804ad801447f3807c2b982026807ef857c581000807fe80c0a81cdb7fab77f9d27faf881d3c81ac2812297cdf080845815a77e57a7f62e7f0b9806017e4fb7fa557f52e80a367eb708268b809ec809f07fae2801a58118c7bee0820e6835507bf787fd017e92b7f5ee81a787fc5281e3580d23803687fba8818b68139b7e2b67e53a7dc267f2427dfb37ec7b8219c00000,0x10909664a059332d0a064e915ba5cfcd0714cc1a06a2093e6e78eb62e0a0ac1a9928c0ac5d8e470083978a42151260f9c7abc7aa60e0d915a88080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c67 : Core r67 := numericCore r67 (laneList r67) (by decide +kernel)
def r68 : Row := ⟨68,-20568,-20567,1563317349,808794442,0x80081000007ffd3000007d72d000007e9b5000007ffba00000804c500000825fc00000800c00000000000000007f040000008101a000007d4e1000007f4b6000008034e00000831f00000081118000007d5ef0000081145000007da79000007ca6a000007f4d6000007dab10000081716000007f3ab000008022000000000000000080593000007f33b000008018500000811cc000007f30b000008143d000007cb800000081ea700000,0x86016803600e801e012805e004800000c806e0208026002800e01c8046010801601e807e01880060068056000007600a803e01a804e014802e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c68 : Core r68 := numericCore r68 (laneList r68) (by decide +kernel)
def r69 : Row := ⟨69,-10761,-10760,1784949987,914280290,0x8103e7d082000007f6db7e80a000007d8447e2ee000007f82f80a05000007f8de801d0000007ee25807ed0000080fb17f698000007e6b10000000000803a07f8ed000007ed297f90000000809918271c000007ea3680c36000007ff5c81e780000081a298197d000007f85d8023a00000000007f3ad00000824a67ed17000007f8517e973000007dbef819940000080be87f645000008086a82b39000007eda07d879000008186a8030600000,0x4444008b700ed5807c640358001c040074f805e0000b7a010130050e00050c02962019250021d000058026500208d0014800581c01a1400734008c080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c69 : Core r69 := numericCore r69 (laneList r69) (by decide +kernel)
def r70 : Row := ⟨70,-118734,-118733,1217451173,624989462,0x7f2e3000007ddf700000000000000000000000007f8bb000007de8d000007ea320000000000000007ee2f000007f0950000000000000007f9250000000000000007d992000007dad1000007f700000007f9060000000000000007db42000007fa94000007ff89000007e1d80000000000000007ec160000000000000007eaf7000007e9b1000000000000000808f4000007f40c000007db940000000000000000000000000805ed000007f74d00000,0x22802e000000000f80260158000012801600000060000072014801201a8000008807a00e801a00000860000076010800000d80660138000000005e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c70 : Core r70 := numericCore r70 (laneList r70) (by decide +kernel)
def r71 : Row := ⟨71,-1631,-1630,2443563453,1251683511,0x802f5805737fbb97e1257fcfe7ff71800477f8488261a82801806c47fd087f9ec80eb880dae8068f815bb7f10a8115e7d8d880dc1812128356b80f3882fb981d4a7e9ad819487e97b7e515819587c9d87f8c77d8e681953812c97efaf7ddc67db577f15c7de5d7db598032d8058c7e5e47dfd17ffdc7eb5081803803ce7ef5480bb182dc7801ea81bed7f4127fd81822727f48f8131983c517b16b7f268817477f91b7ee128180d810f07eb817d8ef00000,0x1191af6a39d8a7cfc3ba82f02b43e661b84e6cea58844f154c58d1066ad8028a5ce146eb58a164a5b0344a96201e1172827085861b004097a31c923090080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c71 : Core r71 := numericCore r71 (laneList r71) (by decide +kernel)
def r72 : Row := ⟨72,-66375,-66374,1243217805,638728073,0x7e0360000000000000007e749000007df6b0000000000000007f43f000008150d0000000000000007e007000008024d00000000000000080a5200000813380000000000000008050c000007ea01000000000000000804e7000007f92b00000000000000080f89000007e5bc0000000000000007e87a000007e8be0000000000000007efd30000080c440000000000000007d4a2000007bf530000000000000007f591000007e9080000000000000007e8ca00000,0x8e000005601480000068016000006e01a800000c802e000008602080000128046000000e0028000018805e0000026008800001e8076000003e00e800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c72 : Core r72 := numericCore r72 (laneList r72) (by decide +kernel)
def r73 : Row := ⟨73,-1674,-1673,2444434122,1244424365,0x851b77d2bb7fdb1813477f93e800b27e4507ef047dd64809257f4987ea1a800ca821687fe70810467ed1c8228f808947d2127fcad810ad8001880a2a7f0687eb6980fad7ed347f3f0805af815d98079d81d4080248803a6811447d9a0808598146983ef67f987800f67e7807e2aa8092a813847f017809087ff917f402825967f0547fd8b7d2167e01c7faa682f30810b97fd348137080a167e0b481d2a7fcdb7e4967e299826ac80c2c80bb87dc927f3297e86100000,0x48486091d18d048866d431c348949e085df427e4c1a31c6c68522a1caa1e6414760e8f9042e223c5ced3466c2838b65155a04ebd6c3285a0c02af56376294080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c73 : Core r73 := numericCore r73 (laneList r73) (by decide +kernel)
def r74 : Row := ⟨74,-19191,-19190,1610376794,826842271,0x808ac0000081243000007e2c1000007fe2300000805a4000007e0d4000007f24f0000081e400000080c9c00000813b9000007e481000007f2e2000007d400000007f3bc00000829ae0000080a96000007fba6000007cf95000000000000000805920000082598000007f5fb000007e2ef0000081228000007f1bd00000817670000080e2e000007e58e000007cd47000007edb900000800eb0000081f18000007f037000007ec380000081f19000007d4af000008122200000,0x24806201d802a014805e008808a0068046003805a023807e019803e0208026000006e004805600b8016001803a021804e01e800a01c8036010806a007803200080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c74 : Core r74 := numericCore r74 (laneList r74) (by decide +kernel)
def r75 : Row := ⟨75,-19997,-19996,1553883599,808410338,0x805737e8cc0000082b240000000000806f97f0ce00000000007f046000007ff4b80805000007bfbf7d888000007ef0300000000007f9c281bed00000000007fc5f000007d5ec7c8ea00000814ab81e2700000804e200000000007f2b17f03d0000000000801a2000007f5787eb1400000812b5803390000080144000000000080039806140000000000814c50000080f9f82b36000007f9828035f000007d65b0000000000806c77f60600000000007e984000007f4b880cc600000,0x12928070000203800022005c8001c58047000088d0001880107c01d0e00580000a48001000445c0164300680007ce80000801abd00eda00520002f56000130098080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c75 : Core r75 := numericCore r75 (laneList r75) (by decide +kernel)
def r76 : Row := ⟨76,-20306,-20305,1572979465,808776691,0x7c10d00000831ef0000082006000008282200000806140000080b320000080761000007c72e0000081e59000000000000000802b9000007fb0b000007ede6000007eef40000081300000007ef9b000007fafe000007e67e000008025e0000081984000007f7d9000007efac000007de09000007e2b2000007ef2a0000080cab000007de4d00000809050000000000000007f38800000831b2000007e78e000007fcbc000007e04e000007fa09000007ef05000007e7b70000080d5600000,0x9600c801e020807602280460028086000005e0108006016806e018802e006804e012807e01a803600a803e024805600e8000004808e014800e008801601e806600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c76 : Core r76 := numericCore r76 (laneList r76) (by decide +kernel)
def r77 : Row := ⟨77,-6005,-6004,1987681259,1021296202,0x7f1697ff768262780b6c803d480d9700000815127e8407efa8000007e2ee806eb000007efe37f69c7e8447f3518079f7f42700000000007f6b47e30380e5481eae7f67700000808937f4dc7fc417f59b0000081bd3000007f202811717fc2d7fddf7e933807c700000816d200000814df80e2b7cd7a7ec3f000007dfd08239f7fcf680fbb81ab500000000007f20281a8b7e66580ecd7fd1381ea1000008024b7bb7c000008187781b277cc5e0000082641807b1813b07de407d3d580d2300000,0x4c4ccc9ae80018112e0104700a4c095e11900002882894e404577206005601f34052cc8f00880410a48400280d2bd860001b927a235480032d00d9e1d0034fba349c080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c77 : Core r77 := numericCore r77 (laneList r77) (by decide +kernel)
def r78 : Row := ⟨78,-148294,-148293,1160891614,596228109,0x7ec800000000000000007f29f000007e38c0000000000000007e76a00000000000000000000000007d935000007c5e40000000000000007ea1f000007ffac0000000000000007f3f7000007d65800000000000000081bcb000007e2650000000000000007ed49000007de010000000000000007e8ef000007fd670000000000000007db9c00000802b30000000000000007fa93000007ee8e00000000000000000000000007f5350000000000000007dde4000007ec800000000000000007f26200000,0x26800000f8016000000e000000001b8052000007a01a8000015800a000006201d8000009803a0000092011800000c8022000004a00b8000000008e0000086017800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c78 : Core r78 := numericCore r78 (laneList r78) (by decide +kernel)
def r79 : Row := ⟨79,-1546,-1545,2446932388,1246511514,0x7eb4e7f95582087800d581a657e343803e87f76f7f6d57f5f082b2780597811957fb9a7e88c81ece8178f81b2d7d8228177982e457e5797f065827f57fdc580d557eebe80ad17fd058109a812137ff7b7ed1980ae5813187fbeb81fcd81e1a7e31d7dfb17f1a17f527819ec7fd81808d97ea7d807337d97a80ce57cb727f8857ebbf81da07f7a07dbaf7fd24818047cb8b829c280ac87e5d77fbe5812177f70180efd804d4818207e1b58064a7dea481efd7f6388018f7f03b7e36b801b97e52d806f400000,0x13939a76fc6ad8a8e3ab5c19f159505cb6963de982ef01a63ec591c4b0e4098880d829ad178b8c1c62a6674f3053309b86e4a004325870574464a1482160a45088146aa0080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79 : Core r79 := numericCore r79 (laneList r79) (by decide +kernel)
def r80 : Row := ⟨80,-39646,-39645,1380549036,708163675,0x8064e000007e0150000000000000007d2ee00000825a90000082401000007e1420000000000000007f165000007f257000007e4d90000080a020000000000000007df5600000804f4000007ec74000007ef8c000000000000000823b9000008076e000007fcd3000007fc34000000000000000809c3000007e031000007d509000007f6f40000000000000007de07000007fd84000007f90a000007f73400000000000000081de8000007d418000007f6b700000804100000000000000007ff110000080afc00000,0x9e01a800001c808e00e8056000005e00a802602480000268016018807e0000086014804e0068000008803e0228006000000e01e807601080000128066004802e000003600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c80 : Core r80 := numericCore r80 (laneList r80) (by decide +kernel)
def r81 : Row := ⟨81,-4620,-4619,1861026891,952875997,0x814737df3f0000080f6c7f313000007f90e7ee080000081bdb7f9a4000007ee3a7fef80000080dc081adf000007f9dc81e5d0000082c3b81fdd0000080b21815230000081e337fd8e000007e6927f92f000007ee828026c000007d2b27dc4f0000081cd47f529000007fcfb7e166000007fbbf81318000007f6d4815a3000007aa237e67300000815f480b5100000805a57ff0f000007ef4782b62000008043a7fca8000007eb3f800e3000007f98d811ec000007f83c817c6000007e7cb7edcf00000818877cd9c00000,0x505000a10005c500105803868002930044200161c0443800d4300bd5806494023620014f0081700587c026440073700d4680951804d8001f4c0074c80772404774020bd00a4080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c81 : Core r81 := numericCore r81 (laneList r81) (by decide +kernel)
def r82 : Row := ⟨82,-17278,-17277,1614644333,833088326,0x809e60000080769000008135600000816750000081cf3000007f9de000007caf8000007e1df000007ef0c0000081267000007d52000000801670000081ae2000007ed09000008174d00000827fe000007e84f000007dbd9000007e680000008104e0000000000000007eccf00000816720000080838000007f655000007fa61000007f9150000080855000007f1b10000081626000007f5e1000007dd38000008195d000007ffa7000007ffab00000819c6000007f123000007e26f000007d864000007e7df000008093200000,0x2880360188046004808601f808e01a808a013807201d8006020804a026800e00f802a000007a0198096002805a008809e00b8032015801a00e8016009801e024805e010806e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c82 : Core r82 := numericCore r82 (laneList r82) (by decide +kernel)
def r83 : Row := ⟨83,-1436,-1435,2448565050,1244449753,0x7f7b68186b807247ead4800db808278124f7fa9b80d7c7cec881ff3824ac7f02c81172819177f7cd7fbca800f97e3fd7ff387fc657f256802797fb4d7f3bd7fc1c81cd47f2bb8390d7e5547ffc880a70813ce7ef7f8126f7fbc980fca81b8a7e90e8079681049804657eed48139f7f2b97ee158184e7ff547d8a980466804187f6e67fe1b7ffd1815977f3ff81d737e11f7d28e7fffb7f9037f2267ec7f8167c80157814927e97e800827d1ee80526814f97fc94800437e124820b6805c57d160819ff7e8da80bf2819d27ef3900000,0x1494b77c862c73eb9d0f98ce68b729cbb03b3d8924d261aba0517888c15ec06b28c11700a89b84ec49e265a70d9691f83504052d828823646f161a901900788652b4183991538a8080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c83 : Core r83 := numericCore r83 (laneList r83) (by decide +kernel)
def r84 : Row := ⟨84,-196244,-196243,1098426830,576599603,0x7de450000000000000007fbc500000000000000000000000008111a000007e5730000000000000007e3d0000008014f0000000000000007f4d6000007e2e100000000000000081441000007ed940000000000000000000000000810fa0000000000000007f8a5000007e7600000000000000007c14600000000000000000000000007d006000007d4dc0000000000000007ee26000007cfc30000000000000007c9ce000007ed400000000000000007ccbd000007e26900000000000000000000000007cbf70000000000000007f67700000,0xa60000086000000001e808e000009e01a8000024805e000006e020800000000760000056014800000c8000000002600e80000128016000003e0028000006802e0000000008800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c84 : Core r84 := numericCore r84 (laneList r84) (by decide +kernel)
def r85 : Row := ⟨85,-7364,-7363,1954198800,1013172458,0x7f16f7ebca7dfe380805000008011b7d4607eecd80770000007f837827cf82bca7fb3e000007f4c8000007e0f77f3020000082a627fc357ed4c7e86e000007bf2e80bd480b7d7eae30000080eb880bee7f89700000000007f28b7ee1a7ff567dedb00000813bb7f5d77eb027e72e00000835677f9a8819978165d0000000000833627f36e80ea3000007c73d818c180da1821de0000080ec77f120812ea81347000007ff2d7f0390000081870000007f4117f217800247f9b8000008159581a6480bce819f2000007e2c17d6437f53c7fa3a00000,0x545470a801c31ac200d838d0c02280433000436c170062581a9012a6920001dbe4cf401d054dc0030bcb9a000218816016527e900274aea88012d0010013e44e3e009a0931c04072ac080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c85 : Core r85 := numericCore r85 (laneList r85) (by decide +kernel)
def r86 : Row := ⟨86,-17058,-17057,1616524308,828472102,0x7f3090000081166000008238f000007f4b8000007ef3b00000801580000080a32000007d77c0000081f9e00000808d00000080c66000007f60d000007e393000007e368000007edaf000007f467000007e8b9000007f4b300000806470000082b26000007e90e0000000000000008147f000008130800000801320000080e11000007f50a000007e8b0000007f851000007ffdc000007efa5000007df45000007fe09000007e25f00000800a60000081d9e000007d2df000007f9ef0000080fbb0000084276000007f30e000007ef82000007eb1500000,0x2a80720088062009804e010807e0028012016808e01b8046029807a00680360278016020800000a809600380760248032001806600f801e014809a028802e01a805e021804a022803a00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c86 : Core r86 := numericCore r86 (laneList r86) (by decide +kernel)
def r87 : Row := ⟨87,-11093,-11092,1800379576,924997576,0x7f9f57fecf000007e458829de0000080b8c8051900000800407f10f00000806b27e462000008009a7eadf000007d5e1819a1000007f8427fa58000008016b7ef7700000810d700000000007cef581c0500000800827e5a30000080fb07d582000007e044808d6000008001e81b0c000007eb988098a00000829707dd3f0000081c8880f2f000007eed27fe900000000000813ed00000801dc821f80000081d1d7e02a000007fb177ed040000080c767e56f000008016c8015900000806bf80d400000081c17803c9000007c7337eb3c00000800da820a600000,0x15958082d003e9800d4f0050f804cb80201a029a20140500760000e2600bd200bc8006518002aa008a5011d4000b00044920001c01343806a1004a6e014b100e218010f400b320119600b0080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87 : Core r87 := numericCore r87 (laneList r87) (by decide +kernel)
def r88 : Row := ⟨88,-26539,-26538,1516554760,777456861,0x7e1fd000007fc0f000008012400000801800000080ae10000000000000007eaae000007ff6c0000081861000007f54a000007e04500000803c8000007ef17000007ee1c0000083c1e000007ddb200000000000000080bff000007f359000007d6b2000007e3fb000008245c00000805df000007f2590000080f60000007ede7000007fd2100000000000000080808000007e4fb000007ec0000000829d4000007efc6000008043a000007fc570000080404000008024b000007dcd9000000000000000808cd0000081138000007fc5f000007e801000007f14500000,0xae00e804600c804e0000036014803e0128086020800e006800600880000028026004801e0168056024809e02280a6000008e02a8096028802e00a806601c805e01e8000018807e01a807600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c88 : Core r88 := numericCore r88 (laneList r88) (by decide +kernel)
def r89 : Row := ⟨89,-1641,-1640,2451121137,1253101156,0x80c7f806bb7deaa7e7207e7fe810737de1e81042815c67f3937e5018287c8194b800d47f93c805c481bfa80d0e81a3c824b1808ca7ef088034f7ee3f7dff27ee9e7ede67f5eb80b2380189830ee7f39d808ae7f38481a657f7ec808967f06b801c97e03d81f908022981a567fe737fcd77ddf87eca280991800028101b7e8dc82abe80ca17ebeb814688151e8037f812267ed307c697811d67fb888175b804d581ad37e8f37f9ac80b687f0547fa3c7a9817ede980a77805638050c7ea1380952810627eaea82bcc7eb317c7358155c812737e6d37f678808fe8294f00000,0x5858ecb4794985cfa0212a9274d944a83944808e9fa082e1b2ead08cbe44f550c0f24a0d48f01573ad6645214a6af38dcdc02e0d5a34261c9a3f548b19614aa70d19834a22454e663c9433cb4080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c89 : Core r89 := numericCore r89 (laneList r89) (by decide +kernel)
def r90 : Row := ⟨90,-244808,-244807,1049276885,546685696,0x7ded400000000000000000000000007ee0200000000000000080347000007f74f0000000000000007e984000007f38a000000000000000804d200000000000000000000000007dd2f000007de6f0000000000000000000000000804e20000000000000007d564000007da3e0000000000000007ddf70000080a080000000000000007c5f800000000000000000000000007d84d000007e88900000000000000000000000007c0200000000000000007da53000007d2cb0000000000000007ef46000007bcd40000000000000007e18a00000000000000000000000007fc1500000,0x2c8000000009a00000620298000012808e0000056000000000f803a00000000088000027802e000008600580000248000000007a01d8000000005e000002601a80000038052000001a000000000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c90 : Core r90 := numericCore r90 (laneList r90) (by decide +kernel)
def r91 : Row := ⟨91,-6775,-6774,2014661311,1035909707,0x7f35980b088127a7f2227e7af7fe940000080f887e9507edb6827aa7f2870000000000802a880c71808778062f7fb6780260000007f1007e6687e37f7f7fe000007e68300000813b07e9a67fafd7c36a7eea48049300000808f97ed26807ab000008099982e00000007e8a07fea280b848148b7eb1581ad400000814447f9f5000007f0557e83d7ee0e000008082080f48813788011183c40803e20000080cd1000007ebfc811a07f97781389000007ffd680219805c98124d817787d90c0000000000803287dd9c80b407d6c0803ee000007fec1807ae802db80bdf7f6317fd5500000,0x16969e884878044284a16a0000622402c36401f5790a004001141ac6c2c40060ee780331c0373e0acbc4800a42003102b014e8255f60b0036019930874029315a5caaa00026754a8b901324977ab8080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91 : Core r91 := numericCore r91 (laneList r91) (by decide +kernel)
def r92 : Row := ⟨92,-20021,-20020,1585738015,817731452,0x80921000007fffc000007eab6000007f9fb000007fc68000007d8c600000804750000082b36000007fac1000007d634000007f1c50000000000000007f797000007fefa00000808cf000007fe460000080326000007f9490000081def00000810b60000082e3b000007f7c9000007de1c0000081988000007e681000007f13c000007ce4b000008069f00000821eb000007f0ca000007f8910000081c18000008109200000817110000000000000007fe29000007cbfc000007ea3c000007f6ea0000080535000008090d000007de630000080119000007e9030000080a5f000007ec6d00000,0xb601e806e006806600c800e018803600e80460000016008802602c804e00a80ae01080a6026805e016801e0048076002808e01a80060248096028800001c807e020805602a8086014809e012803e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c92 : Core r92 := numericCore r92 (laneList r92) (by decide +kernel)
def r93 : Row := ⟨93,-10272,-10271,1804064265,926105789,0x7fea681039000007f1fa7f58d000007f8697e721000007fc657e71f00000800537f48b000008385e81b86000007f55382f250000080a9a7f460000007f30c7ea1900000809797e09200000000007f1af000007e7017f4a5000007f82e815a4000007f3f0830130000081c3582cb1000007e8b17e4fd000007fc7f80066000008014d7db56000007f6f87ffe800000812b6809c4000008027700000000007fd6b81df5000008059f8127300000804767fe69000007ef887f95e000007f10a801d400000801807ec1b000007dddb80c8100000814fc7c41d000007def280c0b000007fb158109c00000,0x5c5c00ba500d5d0083300329200ed200b27804c1001a32029900001e8053540052c02b220140980056c04a1a01d87011ec0010d0020000268a0112180b2dc00e62005c0005158022700235001c4600bc080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c93 : Core r93 := numericCore r93 (laneList r93) (by decide +kernel)
def r94 : Row := ⟨94,-16798,-16797,1619655169,839117468,0x7f89e000008125400000800230000080fc8000007d6b3000007e6ea000007e7d9000007efe90000081741000007d3f20000080783000007f8ed000007e75e00000804ae0000082ce100000812cf000007e36f00000811f3000007ed01000007eb75000007dc52000008051700000828290000000000000007f6ad000007d801000007eb7600000826e9000007f4c40000082b940000081920000008071e000007e9910000082154000008006d000007e309000008299d00000826c8000007f674000007fcf8000007d89f00000807aa0000081871000007cfb7000007f198000007f61a000007e10300000,0x2e803e02580860248022020803200580b202a806200780ae02880060128066010806a01b8076023800000b8046013805201e805601c80b6006800e027805a004800a029808a00e809a00a8036009807e00080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c94 : Core r94 := numericCore r94 (laneList r94) (by decide +kernel)
def r95 : Row := ⟨95,-7272,-7271,1966043216,1006182173,0x800987fa97804d780f74000007e4a5814bc804ad7fd480000080358811a87f8597dc96000007dc7f8115e80c6400000000007f1cd7ebe27e7b081489000007f9af7d7c981ab87ee84000007fb49817e27f05f7efa80000080abf8163e000007f5be000007ebf980ca6809c77f64d00000805f07e5787ec1080e28000007fcdc80d6f7db90810d3000007fef4000007ee1f8121a0000081c2f7fe63802b37ed150000080e497e8408246b7f0d000000817fe7eb797e3f87ff1100000000007e4ac80231840030000080c26807197f986804e100000813f77f5567feea808d6000007f146803117fa1f8080300000,0x1797bf8e0279ba654045af25e80b30dd000026921b602a079c90031b85e8803b3403800b1a355202002ba7c03654ad9804e00942003a4035c01d91b02c0047c36b000094e060088b08340250c884001840c0080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95 : Core r95 := numericCore r95 (laneList r95) (by decide +kernel)
def r96 : Row := ⟨96,-66375,-66374,1243217805,639456910,0x801510000000000000007f9c4000007f3c60000000000000007f313000007d8c20000000000000007eeca000007e60e0000000000000007d113000007f26b000000000000000803ff000007dc940000000000000007d6ea000007f9ff00000000000000080783000007f6910000000000000007f701000007e77c0000000000000007d97d000007f25d0000000000000007f20900000800640000000000000007e8b6000007f372000000000000000812f900000800f4000000000000000804e800000812f9000000000000000811c2000007fa660000000000000008061e00000801000000000000000008008900000,0xbe0000026014800001e8076000009e002800000c802e0000056020800002a80a6000000e00e8000018805e000008602c80000068016000003e01a8000024808e00000b600880000128046000006e026800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c96 : Core r96 := numericCore r96 (laneList r96) (by decide +kernel)
def r97 : Row := ⟨97,-1547,-1546,2453741447,1261300734,0x7e9617fdd47fab082de680668812b4836727fe707ff4e7fac98344a80b3f7fa757f3648060f7f24181c087e9677f0fb7e1a7805667cf73806ae7f3da8128b80711801127e5ce8078f807d580ad9810467e92c7e3bc7fb107def28000b7f2d38160b810587e4a881a368046f7fdde80b3b7f5007e94a7eef8806e97fb0c7e8507e8a6800037f9b27fbb682c7e7fc75822be7fd0d7fe107f2fc7f2d4800b37fbc382a92802fa7d03c7fad07ecd2813977fc0e831be7f40381d78823917f62a7def77f98f7f6ac7e9a97dd488230c814977f0077f1717ff3281e8a7fb83814167e35c8069d8099f7ed0a80288804688044b00000,0x606080c3a214c62b3ab0452b5503398ccdfbc2cec21f533d68a54641af9a911cc957281a3c2459c9c8415f804e2d6b10e3910a5cabe7a5195e90debb424e215d4d2d2a25c6d45b1a1c7d96b11b551d453c982c4080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c97 : Core r97 := numericCore r97 (laneList r97) (by decide +kernel)
def r98 : Row := ⟨98,-30917,-30916,1449228758,747522954,0x81c61000007fb0c000008077b0000000000000007f9a20000081103000007ded6000007f1e200000809d2000007fc4f0000000000000007f6ff000007dc0f000007f9760000080f7b0000080f8f00000806e7000000000000000828f200000800c3000008066c000007e825000007cd6b000007f0dc0000000000000007f846000007fd9200000801a9000007f8f8000008009a000007d7ec0000000000000007ec94000008030e000007e72a000007dc0700000807b0000007ffb00000000000000007fddb000008046f0000080f18000007feee000007ee21000007f8770000000000000007d9b800000800f600000815a800000,0x308082013800002b80b2007801a00b80860000022017803a00d809e02f8000016800a01580520128032000009201e807201b80ba01a80000018026023808a01980a2000003e02580aa0298012005800001d804200080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c98 : Core r98 := numericCore r98 (laneList r98) (by decide +kernel)
def r99 : Row := ⟨99,-12711,-12710,1706710859,879509160,0x811bf7f628000007f596809fa000007fd4b803ea000007e3160000000000834317ffa2000007e7c07fb2500000816678015200000000007f919000007faa77f69e000007e9e182537000007fb0f817ea00000800907dcff0000080aa47e63100000802a5825510000080c9e0000000000809758031d0000080dea7f7e2000007e39a7f871000000000080257000007e1c67fcdc0000080c6f7ff98000007efb37dbdb00000815607ff43000007df03825ce0000081f027fdc3000007fc2c00000000007ea5180278000007fff0806c4000007e4477d54900000000007f86f000007fba78137a000007eb3a7e89100000808b07faf200000,0x189880953c00e4a02c800098380890001abc0002b017c9806ae8053440105200206805f1801700023a8000b08076700009800eb4015ad80230c04120014ae01402007000005920119f0171e80002803eaa00a1900c8080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c99 : Core r99 := numericCore r99 (laneList r99) (by decide +kernel)
def r100 : Row := ⟨100,-39646,-39645,1380549036,714875821,0x7f7dd000007dfb30000000000000007fb750000081d020000080932000007e4660000000000000007e66000000806e5000007f95c000007f6c70000000000000007fe4f000008053b00000810fa000007daaa0000000000000007f22d000007ff96000007ff52000007f43f0000000000000007ea0b000007f35d0000081017000007ebaf0000000000000008089e0000080b87000007ec2c000007f4b70000000000000007feba000007dd7c000007f69b0000081df40000000000000007fce1000007f423000008044d0000081e0f0000000000000007f766000007ebd0000007bb57000008031f0000000000000008142a000007fc2000000,0xc6010800001c8016004802e000005e00a80260068000012803e00e80060000036014804e02e8000008806601880a6000000e01e80760248000030808e022807e00000ae028809e01a800002680b602c8056000008600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c100 : Core r100 := numericCore r100 (laneList r100) (by decide +kernel)
def r101 : Row := ⟨101,-1462,-1461,2454850389,1255414834,0x8197c7e47c7f0ab828a47f22c810a27e02480e1f7e8f2810927f55a7fbdd8032c80aca7fba77fcd7813667f0dd7e5307e9a57f9977e59582d317ee1280c4f7f3f2823b77fe107fcde7eaab7e64a7f77f7fe577c5a87e2e781f277f6c382b88813177eaa17e4017ec6c8173682e517f5097fb117f1357de5f80fea7e31580ab3806c67f9f87f9d5821b37fa56809ec8035080f39801d580baf7fdda821f37dd92802f3813dd804d2813707e8ee80d6b809637da637e3f281d67808ff7e311811d681ec2819b47df41800217e8e180ab4811798087f7f6e27eb667ded7805057fb59812a17f9657fda7800458071c819be80efe8141b80063811d200000,0x64650cc94a921fb814dd51f492a95f39542989d3ca84855895e4a354b4c52c71ebab1aa018d93dcb4e9ec4058d0a8562c4be5f662b072223d7340d8bcb1003d31e8f0d02c5e6e02124313370633b5d6d6a63a468cc44cc080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c101 : Core r101 := numericCore r101 (laneList r101) (by decide +kernel)
def r102 : Row := ⟨102,-135146,-135145,1180092861,618286898,0x803740000000000000007b2ad000007dd120000000000000007e6a5000007f4eb00000000000000000000000007ef890000000000000007f41f000008050c0000000000000008150c000007e5220000000000000007e2d0000007d64200000000000000080bf6000007ee0d00000000000000080c7c000007f0bb0000000000000007f5b0000007f23b0000000000000007ebbf000007d5030000000000000007eea6000007fb9500000000000000080e22000007f9150000000000000007dc6a000008159d0000000000000007f16b00000000000000000000000007f7f3000007dafd0000000000000008033f000007ff680000000000000007e95e00000,0x32800001e803a000004a01780000000076000003e01a8000003802e0000086005800003080a6000001a026800000c80b20000026002800002d8046000009e02f8000018808e0000056000000001b80820000092014800000080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c102 : Core r102 := numericCore r102 (laneList r102) (by decide +kernel)
def r103 : Row := ⟨103,-1455,-1454,2455344344,1258100962,0x804f87e354803ee8236e7fd4c81ac07f1dc8093e8188a8125b7e0c47f4827ff9a820e77e7637f96282cca8138c8049d7d5d58010781ba67f48c7ea8e809b6812567f9f67d57b808bd7f8de7fc4d7fa507edc681857808fa7daa9829958148c7f17b81b897fadb7ef467e7b27defe826dd81414803d38178e7ed177e6ff804167de7b7ebff808a77e17d80225828f57f8fc80ea682197803ce808427ec9b8009c8010a813597e27d7df148064e7d2477fc218011d7f8ef7ddfb80e26807a581a14806cf7fd0e7f29a7e39a7d8507f8f07fe6481fe481a5f80ca6806137f2147e084823d2817ee80f717eb1d7e9d7808e381a467fa0780f37806008078b7ea4000000,0x1999a29aa48acb54241c797cb305a1944148c475e3d1b1bd171cc5d95381b22902a42241665b0e417ae1e55182cb1295872e2be0186f1554a4d3d36b90c9d153d05c54110c91365b434cff0ba6f4442b967cb8d7759f1a8ad0080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c103 : Core r103 := numericCore r103 (laneList r103) (by decide +kernel)
def r104 : Row := ⟨104,-23789,-23788,1536348534,793880747,0x8005d000008248d000007f929000007ff9e000007fa6f000007e5e60000000000000007eb5f000007e08400000803a8000007e62400000823ae00000801a9000007cd5c0000080e4100000806f20000081d1000000823d4000007eb680000000000000007f6eb000008013d000007d4f7000008138d000007e46a000007fda900000807a8000007d705000007ed57000007ec070000080b33000007e99e00000000000000080f6d000007df39000007dfc30000080a96000007fad2000008017200000800150000080b5b000007f355000008062f0000080ce3000008255900000000000000081d31000007fc1f000007f848000007f47d000007f139000008003c00000,0xce02280a602c802e02a8000030806e02e80c6004809e026805601c807e0328076000008e00e808602480ae01a8066008803e012809601080000168006014805e01e803600c80be0028016018800e0000026028801e00a804600080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c104 : Core r104 := numericCore r104 (laneList r104) (by decide +kernel)
def r105 : Row := ⟨105,-59306,-59305,1368545173,709473710,0x802037eba4000007f4f60000000000000008087000000000007f39b000007f6de00000000007fa1e7dc480000081186000000000082d6080ef100000000007dc9f000000000080b53000007e3f88021a000007feb200000000007e98a7fa3c00000000008154c000007d8bc7dd87000007f9b28145000000000000000000000812037f688000000000000000000007fee080a61000008037f810de000007d9040000000000805df7fee0000000000080284000007fde080e2a000007f3db00000000008184400000000007d5507ea7200000000007f655000007fa377e2eb00000000007ecef000007f15300000000007de800000000000000007fff0000007f91a7f9d900000,0x686800d000000680004c0080001da5002c0007d24000080004c00b29008e000117400040014cf80b30c000000016700000004c4004a2c0148000bec0000880177a00e80019400040ac000bc0222e0003080ac0005c000004f00d4080⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c105 : Core r105 := numericCore r105 (laneList r105) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def rows : List Row := [r2,r4,r6,r8,r10,r12,r14,r16,r18,r20,r22,r24,r26,r28,r30,r32,r34,r36,r38,r40,r42,r44,r46,r48,r50,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem all_cores {r : Row} (hr : r ∈ rows) : Core r := by
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r
  · exact c2
  · exact c4
  · exact c6
  · exact c8
  · exact c10
  · exact c12
  · exact c14
  · exact c16
  · exact c18
  · exact c20
  · exact c22
  · exact c24
  · exact c26
  · exact c28
  · exact c30
  · exact c32
  · exact c34
  · exact c36
  · exact c38
  · exact c40
  · exact c42
  · exact c44
  · exact c46
  · exact c48
  · exact c50
  · exact c52
  · exact c53
  · exact c54
  · exact c55
  · exact c56
  · exact c57
  · exact c58
  · exact c59
  · exact c60
  · exact c61
  · exact c62
  · exact c63
  · exact c64
  · exact c65
  · exact c66
  · exact c67
  · exact c68
  · exact c69
  · exact c70
  · exact c71
  · exact c72
  · exact c73
  · exact c74
  · exact c75
  · exact c76
  · exact c77
  · exact c78
  · exact c79
  · exact c80
  · exact c81
  · exact c82
  · exact c83
  · exact c84
  · exact c85
  · exact c86
  · exact c87
  · exact c88
  · exact c89
  · exact c90
  · exact c91
  · exact c92
  · exact c93
  · exact c94
  · exact c95
  · exact c96
  · exact c97
  · exact c98
  · exact c99
  · exact c100
  · exact c101
  · exact c102
  · exact c103
  · exact c104
  · exact c105
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem all_certified_of_scalars (r : Row) (hr : r∈rows) (s : ScalarFacts r) : Certified r := certified_of_core r (all_cores hr) s
end FR7022CompactData
namespace FR7022CompactTail
open Finset FR7022ProgressionTail FR7022TailCoefficients
theorem cancellation (r : Row) (H : Certified r) :
    (∑ k ∈ FR7022TwoStage.unitsDomain r.q, r.c k/k)=0 := by
  have hM : 0<commonMultiple := by decide
  have hs : ∀ k∈r.S, 0<k ∧ k∣commonMultiple := fun k hk => common_dvd k (mem_filter.mp hk).1
  exact (affine_cancel_iff_integer_ratio r.S _ _ _ hM hs _ _ (by norm_num) H.slope).mpr rfl
theorem alpha_bounds (r : Row) (H : Certified r) :
    (r.al:ℝ)/1000 ≤ r.alpha ∧ r.alpha ≤ (r.ah:ℝ)/1000 := by
  have hM : 0<commonMultiple := by decide
  have hs : ∀ k∈r.S, 0<k ∧ k∣commonMultiple := fun k hk => common_dvd k (mem_filter.mp hk).1
  exact cancellation_bracket_of_integers r.S _ _ _ hM hs 1292 r.alpha (by norm_num)
    H.slope (cancellation r H) _ 1000 _ 1000 (by decide) (by decide) H.alBound H.ahBound
theorem finite_endpoint (k : ℕ) (hk : k≤3800) (v : ℤ) :
    FR7022TwoStage.coeff FR7022Second.sign v k = endpointWeight baseCoeff extraCoeff v 1000 k := by
  have heq : FR7022Second.sign k=coefficientSign k := rfl
  unfold FR7022TwoStage.coeff endpointWeight baseCoeff extraCoeff
  rw [heq]
  by_cases hb : k≤2508
  · have hmin : 1292≤3800-k := by omega
    simp [hb,not_lt.mpr hb,min_eq_left hmin]
  · have hmin : 3800-k≤1292 := by omega
    simp [hb,lt_of_not_ge hb,hk,min_eq_right hmin]
theorem between (r : Row) (H : Certified r) (k : ℕ) (hk : k∈FR7022TwoStage.unitsDomain r.q) :
    (FR7022TwoStage.coeff FR7022Second.sign r.al k:ℝ) ≤ 1292000*r.c k ∧
    1292000*r.c k ≤ (FR7022TwoStage.coeff FR7022Second.sign r.ah k:ℝ) := by
  have kB := (mem_Icc.mp (mem_filter.mp hk).1).2
  rw [finite_endpoint k kB,finite_endpoint k kB]
  have h := alpha_bounds r H
  have h0 : (r.al:ℝ) ≤ r.alpha*1000 := (div_le_iff₀ (by norm_num : (0:ℝ)<1000)).mp h.1
  have h1 : r.alpha*1000 ≤ (r.ah:ℝ) := (le_div_iff₀ (by norm_num : (0:ℝ)<1000)).mp h.2
  have hx : 0≤(extraCoeff k:ℝ) := by unfold extraCoeff; split <;> norm_num
  have hlo := mul_le_mul_of_nonneg_right h0 hx
  have hhi := mul_le_mul_of_nonneg_right h1 hx
  simp only [endpointWeight,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Row.c,affineCoeff]
  constructor <;> linarith
end FR7022CompactTail
namespace FR7022SignedLog
open Finset
end FR7022SignedLog
namespace FR7022SignedLog
open Finset
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
end FR7022SignedLog
namespace FR7022ScalarTable
abbrev W : Nat := 1000000000000
abbrev LD : Nat := 40960000000000
def ceilN (n d : Nat) := (n+d-1)/d
def ceilZ (n : Int) (d : Nat) : Int := -((-n)/(d:Int))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
structure Row where
  q : Nat
  k0 : Nat
  k1 : Nat
  phi : Nat
  al : Int
  ah : Int
  finiteCost : Nat
  tailCost : Nat
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
structure Sums where
  k : Nat := 1
  hLo : Int := 0
  hHi : Int := 0
  logLo : Int := 0
  logHi : Int := 0
  mass : Nat := 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def step (r : Row) (s : Sums) (entry : Nat) : Sums := Id.run do
  let k := s.k
  if k>r.k1 || k.gcd r.q != 1 then return {s with k:=k+1}
  let sign : Int := if entry % 4=1 then 1 else if entry % 4=2 then -1 else 0
  let base := sign * Int.ofNat (min (r.k1-r.k0) (r.k1-k))
  let v0 := 1000*base + (if k>r.k0 then r.al else 0)
  let v1 := 1000*base + (if k>r.k0 then r.ah else 0)
  let b := entry/4
  let l : Int := Int.ofNat (b*6931471803)
  let h : Int := if k=1 then 0 else Int.ofNat ((b+1)*6931471808)
  return ⟨k+1,s.hLo + ceilZ (W*v0) k,s.hHi+(W*v1)/(k:Int),
    s.logLo + (min (v0*l) (v0*h))/(k:Int),
    s.logHi + ceilZ (max (v1*l) (v1*h)) k,
    s.mass + max v0.natAbs v1.natAbs⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def runDigits (r : Row) : Nat → Nat → Sums → Sums
  | 0, _, s => s
  | n+1, z, s => runDigits r n (z >>> 18) (step r s (z % 262144))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def powerDigits : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | n+1, k, z =>
    let b := (z % 262144)/4
    let val := k^4096
    decide (2^b ≤ val ∧ val < 2^(b+1)) && powerDigits n (k+1) (z >>> 18)
def tab0 : Nat := 0x600017e885f4457b925e821787e5dba5754d5cea172015c1416e965b3516b095a4d16754595c1637e586055f78575915b465646956e255261524553f754d6652b8148455166542d5500013d124e82936ea4cea130504b3552934495c12182475951919452610fde42b81059a40000fa093cea4ecd6395c0dd6635264cae030000b3aa295c4949a200006572100080001
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab0_powers : powerDigits 64 1 tab0 = true := by decide +kernel
def tab1 : Nat := 0x70001bf466fa21bdcc6f441bc516ee45bacc6e821b9456e1f5b7b46dba1b61d6d539b47e6cea1b2d56c809b12a6c141af766ba55adb66b351abee6ac29aa226a4d1a84469d51a666695c1a47968df5a28168601a07d67de19e72675919c5966d159a3166461980265b8595c065261937264919911163f718ea4635958c2662b8189966211986f161661843a60b59816d
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab1_powers : powerDigits 64 65 tab1 = true := by decide +kernel
def tab2 : Nat := 0x795c1e4f6791e9e3f878df1e30178a09e20178601e101781f9dffe77de1def6779c5dded77591dce077169dbd276d11dabc768c9d9a876461d88e76005d77275b81d65275701d52d75261d40574dc5d2da74911d1ad74449d07873f71cf4273a91ce0673591ccc473095cb8172b81ca3972655c8ed72111c79e71bc9c64671661c4e8710e5c38970b51c222705b9c0b5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab2_powers : powerDigits 64 129 tab2 = true := by decide +kernel
def tab3 : Nat := 0x80001ffa27fd15fee97fa21fe2e7f731fd717f441fcb17f149fbf07ee41fb307eb31fa6e7e821f9a67e519f8e17e1f1f8197ded1f74e7dba1f6827d879f5b67d531f4e67d1f5f4147cea1f3427cb59f26d7c801f1957c4a5f0bd7c141efe17bdd5ef057ba51ee267b6d5ed457b351ec607afb5eb7d7ac21ea957a885e9a97a4d1e8be7a111e7ce79d51e6de79995e5ea
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab3_powers : powerDigits 64 193 tab3 = true := by decide +kernel
def tab4 : Nat := 0x8526214518501a13ba84dc2132484b66128e8491211fa846ba115d8444210c6841e2102983f720f9183d060ef183a920e55838160db4835920d15833120c76830920bd582e0a0b3082b820a8d828ea09ea826520942823ba089a8211207f081e76074681bc2069c8191605ee816620542813a20492810e203e180e2a033180b52027e8088601c8805b20111802da005e
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab4_powers : powerDigits 64 257 tab4 = true := by decide +kernel
def tab5 : Nat := 0x895c22532893d624b5891e2243a88fe223bd88df2233c88c0a22c288a0222418880a21c08860221428840a20c1881f2203c87ff61fbc87de21f3a87bd61eb6879c21e2d877ba1daa875921d24873821c9e871621c1686f461b8e86d121b0086af21a79868c219ed866a219628646218d58623618448600217ba85dc6172985b821699859461608857021575854ba14e5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab5_powers : powerDigits 64 321 tab5 = true := by decide +kernel
def tab6 : Nat := 0x8cea233758cd06330d8cb5232a28c9ba32348c80231ce8c65a31618c4a230f28c2fa30868c142301a8bf8a2faa8bdd22f3d8bc1a2ecc8ba522e5c8b8962dee8b6d22d7e8b51a2d0d8b3522c998b1822c298afb22bb58adfa2b428ac222acd8aa5a2a588a88229e58a6aa296e8a4d228fa8a2f628828a112280989f36279189d52271989b7626a2899922624897a625ae
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab6_powers : powerDigits 64 385 tab6 = true := by decide +kernel
def tab7 : Nat := 0x900023fd18fe863f768fd123f188fbaa3eb98fa223e5e8f8b63dfd8f7323da28f5ca3d418f4423ce08f2ca3c818f1423c228efc23bc18ee423b628ecc23afd8eb323a9e8e9b63a398e82239da8e69639748e51239108e38a38ad8e1f238498e06a37e58ded237828dd36371e8dba236b68da06364e8d87235e88d6d635828d532351a8d39634b18d1f234498d05233e2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab7_powers : powerDigits 64 449 tab7 = true := by decide +kernel
def tab8 : Nat := 0x92b824ab492a3a4a65928e24a12927a649be926524968925064919923b248c692266487292112481991fc247c691e72477291d16471d91bc246c591a72467091912461a917b645c591662456d915064516913a244bc912464465910e2440d90f8a43b590e22435c90cca430490b5242a9909f642509088241f690722419a905b241419044a40e5902d2408990176402c
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab8_powers : powerDigits 64 513 tab8 = true := by decide +kernel
def tab9 : Nat := 0x9526254749514a54289501253e194ee6539594dc2534a94c92530194b6252b694a36526894912521d947e651d0946b251869457a513a9444250ee94316509e941e25051940aa500693f724fb693e4a4f6893d024f1893bca4ece93a924e7e9395a4e2d938124dde936d24d8e935924d3d9345a4ced933124c9e931d64c4c930924bfd92f5a4bad92e024b5992cc24b0a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab9_powers : powerDigits 64 577 tab9 = true := by decide +kernel
def tab10 : Nat := 0x975925d45974925d02973825cbd972765c79971625c35970565bf096f425bae96e365b6996d125b2596c025ae196af25a9a969ea5a55968c25a11967ba59ca966a2598496586593e9646258f99635a58b19623258699611258269600257de95ee6579695dc2574e95caa570495b8256bd95a6a567695942562e9582255e595702559a955da5552954b2550a9539a54be
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab10_powers : powerDigits 64 641 tab10 = true := by decide +kernel
def tab11 : Nat := 0x995c26551994c66510993d264d5992da6496991e2645a990e6641a98fe263dd98efa639d98df2635e98cf2631d98c0262e098b0662a198a0262629890a62229880261e29870261a19860261609850661229840260e19830a60a0981f2605e980f2601c97ff25fdd97ef25f9997de25f5a97ce65f1597bd25ed697ad65e91979c25e50978ba5e0e977b25dc9976a65d8a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab11_powers : powerDigits 64 705 tab11 = true := by decide +kernel
def tab12 : Nat := 0x9b3526cb59b26a6c7e9b1826c469b0aa6c0c9afb26bd29aeda6b9a9adf26b5c9ad066b259ac226aed9ab3a6ab19aa526a769a9626a3e9a8826a019a79a69ca9a6a2698d9a5b669509a4d269159a3e668de9a2f268a29a20668659a11268299a02a67ed99f3267b299e4a677599d52673899c6a66fd99b7266c199a86668299992664499892660a997a265cd996b6658e
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab12_powers : powerDigits 64 769 tab12 = true := by decide +kernel
def tab13 : Nat := 0x9cea273919cdda735d9cd0273249cc3a72f19cb5272be9ca8672869c9b272529c8d2721e9c80271e59c73671b29c65271789c58a71449c4a2710d9c3c670d99c2f270a09c21670699c14270369c0666ffe9bf826fc69bea66f8e9bdd26f589bcfa6f229bc126ee99bb326eb19ba526e789b9726e409b8926e099b7b66dd09b6d26d9a9b5f66d609b5126d299b43a6cf0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab13_powers : powerDigits 64 833 tab13 = true := by decide +kernel
def tab14 : Nat := 0x9e82279f19e76679c29e692798d9e5d2795e9e51279299e44278f99e38278ca9e2ba78949e1f278659e12a78329e06277fd9df9a77ce9ded2779a9de0677699dd3277349dc7677029dba276cc9dad6769c9da0276699d93676359d87276029d7a275cd9d6d2759a9d60675659d53275369d46675009d39274ce9d2ca74959d1f274629d12a742d9d05273f99cf8673c6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab14_powers : powerDigits 64 897 tab14 = true := by decide +kernel
def tab15 : Nat := 0xa00027fea9ff4a7fba9fe827f8e9fdd67f5c9fd127f2e9fc627f029fba27ed19faea7ea29fa227e759f9767e469f8b27e159f7fa7de69f7327db49f6867d8a9f5c27d599f50a7d299f4427cfa9f3827cc99f2c27c9a9f20a7c699f1427c3a9f0867c089efc27bd99ef0a7baa9ee427b789ed867b499ecc27b169ebfa7ae69eb327ab69ea767a859e9b27a549e8ea7a20
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab15_powers : powerDigits 64 961 tab15 = true := by decide +kernel
def tab16 : Nat := 0xa16628582a15ba8556a1502852ca14568501a13a284d5a12f284a9a1242847ca119a8451a10e28424a103a83faa0f8283cda0eda839ea0e228372a0d728346a0cc28319a0c1282eda0b5282c1a0aaa8294a09f28266a0942823aa0882820da07d681dea072281b1a06668185a05b28156a050a8129a044280fca039a80cea02d280a2a022a8070a01728045a00b28014
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab16_powers : powerDigits 64 1025 tab16 = true := by decide +kernel
def tab17 : Nat := 0xa2b828acaa2ad28aa1a2a328a79a299a8a4da28e28a24a284689fda27a289d1a26f689a9a26528981a25a28955a2502892ea246a8902a23b288d8a231688aca22628886a21c68859a21128831a206a8806a1fc287dda1f1687b2a1e728785a1dc6875ea1d128730a1c7a8706a1bc286dea1b1a86b1a1a728685a19c2865aa19128632a18668606a17b285daa171a85ac
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab17_powers : powerDigits 64 1089 tab17 = true := by decide +kernel
def tab18 : Nat := 0xa3f728fc8a3ed68fa2a3e428f7da3da28f56a3d028f2da3c628f05a3bc28edda3b368ebaa3a928e91a39f68e68a39528e41a38ba8e1aa38128df1a37768dc9a36d28da2a36368d7aa35928d50a34fa8d2aa34528d00a33ba8cd9a33128cb0a32768c8aa31d28c62a31328c39a30928c11a2ffa8be9a2f528bc2a2eba8b94a2e028b6da2d6a8b45a2cc28b1da2c268af6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab18_powers : powerDigits 64 1153 tab18 = true := by decide +kernel
def tab19 : Nat := 0xa52629486a51d29462a5142943ca50a29419a501293f1a4f8a93cca4ee293a9a4e5a9382a4dc2935da4d269339a4c929312a4c0a92eda4b6292c9a4ad692a1a4a32927ca49a29256a49129231a487a920aa47e291e5a474291bda46b2919aa46169172a4572914ea44e69124a444290fea43b690daa431290b1a4276908ca41e29066a414a903ea40a29019a40168ff2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab19_powers : powerDigits 64 1217 tab19 = true := by decide +kernel
def tab20 : Nat := 0xa64629909a63ea98e4a635298c1a62ca98a1a6232987ea61aa9859a61129834a60969811a600297eea5f7697c8a5ee297a4a5e569782a5dc2975ea5d36973da5ca29719a5c1296f5a5b8296d2a5afa96aea5a629686a59d69660a5942963ea58b6961aa582295f5a579a95d2a570295aea56669589a55d29566a55469542a54b29518a542694f5a539294d2a52f694ae
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab20_powers : powerDigits 64 1281 tab20 = true := by decide +kernel
def tab21 : Nat := 0xa75929d56a751a9d35a74929d11a74069cf1a73829ccea72fa9cada72729c8ca71ea9c69a71629c49a70da9c25a70529c05a6fc29be1a6f429bbda6eb69b9ea6e329b79a6daa9b58a6d129b34a6c9a9b16a6c029af1a6b8a9acca6af29aaea6a669a89a69e29a65a695a9a46a68c29a20a684a99fda67b299dda672699baa66a29995a66129971a65829951a64f6992d
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab21_powers : powerDigits 64 1345 tab21 = true := by decide +kernel
def tab22 : Nat := 0xa8602a172a8582a151a8502a130a8486a111a8402a0f2a838aa0d1a8302a0b2a8282a08da81f2a06ea8176a04ea80f2a02ea8072a00ca7ff29feea7f7a9fcca7ef29faaa7e6a9f89a7de29f6aa7d669f49a7ce29f2aa7c5a9f06a7bd29ee4a7b569ec6a7ad29ea6a7a4a9e80a79c29e62a79429e40a78b29e1ea78369dfda77b29ddda772a9db8a76a29d99a76269d7a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab22_powers : powerDigits 64 1409 tab22 = true := by decide +kernel
def tab23 : Nat := 0xa95c2a561a954aa542a94c2a522a9442a505a93d2a4e5a935aa4c4a92d2a4a6a9256a488a91e2a468a9166a449a90e2a42aa9066a409a8fe2a3eea8f7aa3cda8ef2a3ada8e7aa38ea8df2a36ca8d76a34da8cf2a32ea8c7aa311a8c02a2f2a8b82a2d2a8b02a2b2a8a8aa292a8a02a272a8986a250a8902a232a8886a212a8802a1f2a8786a1d1a8702a1b0a868aa191
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab23_powers : powerDigits 64 1473 tab23 = true := by decide +kernel
def tab24 : Nat := 0xaa4d2a926aa45aa90aaa3e2a8eaaa376a8ccaa2f2a8adaa286a891aa202a874aa19aa855aa112a83aaa0aaa81aaa022a7fea9fbaa7dda9f32a7c0a9ec6a7a0a9e42a786a9ddaa765a9d52a74aa9ce2a729a9c62a709a9bfaa6eda9b72a6cea9b0aa6b0a9a82a691a9a06a676a9992a656a9912a636a9892a61aa9826a5faa97a2a5daa973aa5bda96b2a59ca9636a57d
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab24_powers : powerDigits 64 1537 tab24 = true := by decide +kernel
def tab25 : Nat := 0xab352acc6ab2daaca9ab262ac8eab1f6ac72ab182ac51ab116ac36ab0a2ac19ab032abfdaafb2abe0aaf46abc6aaed2aba5aae66ab89aadf2ab6daad72ab52aad02ab36aac9aab15aac22aaf9aabbaaadcaab32aac2aaacaaaa0aaa52aa85aa9d6aa6aaa962aa4aaa8f6aa2caa882aa12aa80aa9f6aa792a9d4aa726a9baaa6a2a99eaa63aa97eaa5b2a961aa542a942
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab25_powers : powerDigits 64 1601 tab25 = true := by decide +kernel
def tab26 : Nat := 0xac142b041ac0d6b024ac062b00aabff6aff2abf82afd4abf16afb9abea2af9cabe36af81abdd2af65abd62af4aabcf2af2dabc86af12abc12aef5abbaaaed8abb32aec2abacaaea6aba52ae8aab9e2ae6eab972ae51ab902ae35ab892ae19ab82aadfdab7b2ade0ab742adc4ab6d2ada9ab666ad8aab5f2ad6cab582ad51ab512ad35ab4aaad1aab432acfeab3c2ace0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab26_powers : powerDigits 64 1665 tab26 = true := by decide +kernel
def tab27 : Nat := 0xacea2b39cace4ab386acdd2b36aacd7ab34dacd02b336acc92b319acc32b2fdacbcab2e6acb52b2c8acaf6b2acaca82b296aca16b279ac9b2b25eac946b245ac8d2b229ac876b20dac802b1f6ac79ab1d9ac732b1bcac6c6b1a2ac652b189ac5e2b16eac582b152ac512b135ac4a2b11eac43ab102ac3c2b0e5ac36ab0c8ac2f2b0adac282b096ac212b079ac1aab05e
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab27_powers : powerDigits 64 1729 tab27 = true := by decide +kernel
def tab28 : Nat := 0xadba2b6deadb32b6c1adad2b6a9ada72b68cada02b676ad9aab65cad932b641ad8dab629ad872b60dad806b5f5ad7a2b5ddad73ab5c2ad6d2b5aaad666b58dad602b574ad59ab558ad532b542ad4d6b525ad462b50dad402b4f1ad392b4d8ad336b4bcad2c2b4a6ad25ab488ad1f2b471ad186b454ad122b43dad0bab422ad052b405acfeab3edacf82b3d1acf16b3b9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab28_powers : powerDigits 64 1793 tab28 = true := by decide +kernel
def tab29 : Nat := 0xae822b9fdae7cab9e4ae762b9cdae706b9b6ae692b998ae63ab981ae5d2b96aae576b952ae512b939ae4aab91eae442b904ae3eab8edae382b8d5ae326b8b9ae2b2b8a1ae252b88aae1f2b872ae19ab856ae122b83dae0c6b824ae062b80eadffab7f2adf92b7d8adf36b7c2aded2b7a6ade66b78eade02b776addaab759add32b740adcd2b72aadc72b70cadc06b6f5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab29_powers : powerDigits 64 1857 tab29 = true := by decide +kernel
def tab30 : Nat := 0xaf442bd05af3e6bcedaf382bcd6af32abcbdaf2c2bca4af266bc8eaf202bc74af1aabc5daf142bc45af0e6bc2eaf082bc15af022bbfdaefc2bbe5aef6abbcdaef02bbb6aeea6bb9caee42bb86aede2bb6eaed82bb56aed2abb3daecc2bb21aec56bb09aebf2baf1aeb96bad9aeb32bac0aead6baaaaea72ba92aea1aba79ae9b2ba61ae952ba44ae8e2ba2dae882ba15
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab30_powers : powerDigits 64 1921 tab30 = true := by decide +kernel
def tab31 : Nat := 0xb0002bff5affa6bfddaff42bfc4afee6bfadafe82bf96afe36bf82afdd2bf6aafd72bf51afd12bf39afcb6bf22afc62bf0eafc06bef4afba2bedcafb4abec5afae2beadafa86be96afa22be82af9dabe6aaf972be52af916be38af8b2be20af85abe09af7f2bdf2af796bddaaf732bdc2af6d2bdaaaf682bd95af626bd7eaf5c2bd65af56abd4caf502bd36af4aabd1d
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab31_powers : powerDigits 64 1985 tab31 = true := by decide +kernel
def tab32 : Nat := 0xb0b52c2ceb0b0ac2b6b0aa2c29cb0a52c289b09f2c271b0996c259b0942c246b08e6c22cb0882c219b083ac202b07d2c1eab0776c1d6b0722c1beb06cac1a6b0662c192b061ac17ab05b2c160b0556c14db0502c134b04aac11db0442c105b03f2c0f2b0392c0dab0336c0c2b02d2c0aeb0286c094b0222c07db01c2c064b0172c052b011ac03ab00b2c021b0052c009
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab32_powers : powerDigits 64 2049 tab32 = true := by decide +kernel
def tab33 : Nat := 0xb1662c58cb1606c579b15b2c561b1556c54cb1502c535b14b2c521b1452c50ab140ac4f6b13a2c4ddb135ac4c9b12f2c4b1b12aac49eb1242c484b11f2c471b1192c459b114ac445b10e2c42eb1092c41ab1032c402b0fe6c3eeb0f82c3d6b0f3ac3c0b0ed2c3aab0e76c396b0e22c37db0dc6c368b0d72c351b0d16c33ab0cc2c325b0c6ac30db0c12c2f8b0bbac2e2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab33_powers : powerDigits 64 2113 tab33 = true := by decide +kernel
def tab34 : Nat := 0xb2112c83ab20cac826b2062c812b2016c7feb1fc2c7e5b1f7ac7d1b1f12c7bdb1ec6c7a4b1e72c790b1e1ac77eb1dc2c765b1d76c751b1d12c73db1cc2c726b1c72c712b1c16c6fcb1bc2c6e6b1b76c6d0b1b12c6beb1acac6a5b1a72c691b1a1ac67cb19c2c665b1966c652b1912c639b18c6c625b1862c610b1816c5fab17b2c5e5b1766c5cdb1712c5bab16b2c5a1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab34_powers : powerDigits 64 2177 tab34 = true := by decide +kernel
def tab35 : Nat := 0xb2b82cad4b2b26cac2b2ad2caacb2a8aca9ab2a32ca80b29eaca6eb2992ca59b293aca46b28e2ca32b2892ca1db2842ca05b27fac9f2b27a2c9ddb274ac9c8b26f2c9b4b26aac99eb2652c989b260ac976b25a2c962b255ac94eb2502c935b24b6c922b2462c90cb2406c8f9b23b2c8e2b2362c8cdb2312c8bab22b2c8a5b2262c88eb2216c879b21c2c866b216ac850
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab35_powers : powerDigits 64 2241 tab35 = true := by decide +kernel
def tab36 : Nat := 0xb3592cd5cb3542cd4ab34f2cd35b34a6cd21b3452cd0db3402ccfab33b2cce6b336accd1b3312ccbeb32c2cca8b3272cc96b3226cc82b31d2cc6eb3186cc5ab3132cc46b30eacc32b3092cc19b304acc06b2ff2cbf0b2faacbddb2f52cbc9b2f06cbb4b2eb2cba1b2e52cb8db2e02cb79b2dbacb65b2d62cb51b2d1acb3cb2cc2cb26b2c7acb12b2c22cafdb2bd6cae9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab36_powers : powerDigits 64 2305 tab36 = true := by decide +kernel
def tab37 : Nat := 0xb3f72cfd6b3f22cfc1b3ed2cfadb3e86cf98b3e42cf86b3dfacf70b3da2cf5db3d56cf4ab3d02cf39b3cbacf25b3c62cf12b3c1acefeb3bc2cee9b3b7aced6b3b32cec0b3ae6ceacb3a92ce9ab3a4ace86b39f2ce71b39a2ce5eb3952ce4db390ace3ab38b2ce26b3866ce10b3812cdfeb37cacdeab3772cdd6b372acdc2b36d2cdacb3686cd9ab3632cd86b35e6cd71
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab37_powers : powerDigits 64 2369 tab37 = true := by decide +kernel
def tab38 : Nat := 0xb4912d239b48cad224b4872d215b4826d201b47e2d1edb479ad1dab4742d1c9b46fad1b5b46b2d1a1b4666d18eb4612d17cb45c6d16ab4572d155b4536d141b44e2d12eb4492d11eb4442d109b43f6d0f5b43b2d0e2b4366d0ccb4312d0bdb42cad0a9b4272d096b4232d081b41e2d06eb4196d05eb4142d049b40f6d036b40a2d020b406ad00eb4012cff9b3fc6cfe5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab38_powers : powerDigits 64 2433 tab38 = true := by decide +kernel
def tab39 : Nat := 0xb5262d491b5216d47eb51d2d46eb5186d45ab5142d446b50f2d436b50a2d420b506ad40db5012d3feb4fcad3e8b4f82d3d6b4f32d3c5b4ee2d3b0b4eaad39db4e52d38eb4e06d378b4dc2d364b4d7ad354b4d22d340b4cead32eb4c92d31db4c46d309b4c02d2f5b4bbad2e5b4b62d2d0b4b2ad2bdb4ad2d2a9b4a8ad29ab4a32d286b49f2d271b49a2d260b4956d24d
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab39_powers : powerDigits 64 2497 tab39 = true := by decide +kernel
def tab40 : Nat := 0xb5b82d6d9b5b46d6c6b5af2d6b4b5ab6d6a2b5a62d691b5a16d67eb59d2d66db5982d65ab5942d64ab58f6d635b58b2d625b5866d610b5822d5fdb57dad5ecb5792d5dab5746d5cab5702d5b6b56b6d5a5b5662d591b562ad582b55d2d56cb5596d559b5542d54ab5506d535b54b2d524b5462d511b5422d4fdb53dad4edb5392d4d9b5346d4c8b52f2d4b5b52b6d4a1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab40_powers : powerDigits 64 2561 tab40 = true := by decide +kernel
def tab41 : Nat := 0xb6462d912b642ad902b63e2d8eeb6392d8ddb6352d8ceb630ad8bab62c2d8a8b628ad894b6232d886b61f6d875b61a2d862b616ad852b6112d83eb60d2d82db6092d81ab604ad80ab6002d7f4b5fb6d7e5b5f72d7d5b5f22d7c1b5ee2d7b2b5e92d79cb5e52d78db5e06d779b5dc2d76ab5d76d754b5d32d746b5cfad732b5ca2d721b5c6ad70db5c12d6fdb5bdad6e8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab41_powers : powerDigits 64 2625 tab41 = true := by decide +kernel
def tab42 : Nat := 0xb6d12db3eb6cd2db2eb6c92db1db6c56db08b6c02daf9b6bcadaeab6b82dad6b6b32dac6b6af2dab5b6ab6daa5b6a62da92b6a2ada82b69e2da70b699ada5cb6952da4db6916da3db68c2da2ab6882da1ab6842da06b67fad9f6b67b2d9e6b677ad9d0b6722d9c2b66e6d9b1b66a2d99eb665ad98db6612d97eb65cad96ab6582d958b654ad946b64f2d934b64bad926
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab42_powers : powerDigits 64 2689 tab42 = true := by decide +kernel
def tab43 : Nat := 0xb7592dd5db7556dd4db7512dd3db74dadd2cb7492dd19b744add09b7402dcfab73cadceab7382dcd8b7336dcc6b72f2dcb6b72badca4b7272dc96b7232dc82b71e2dc71b71aadc61b7162dc50b712adc3cb70d2dc2db709adc1eb7052dc0cb701adbf9b6fc2dbe9b6f8adbdab6f42dbcab6efadbb6b6eb2dba4b6e76db95b6e32db81b6deadb71b6da2db62b6d62db52
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab43_powers : powerDigits 64 2753 tab43 = true := by decide +kernel
def tab44 : Nat := 0xb7de2df72b7da6df62b7d62df50b7d2adf40b7ce2df30b7ca6df21b7c52df0db7c16defeb7bd2deedb7b92dedeb7b52decdb7b16debeb7ad2deadb7a96de98b7a42de8ab7a02de7ab79c2de6ab7986de59b7942de4ab7902de39b78b2de25b7876de16b7832de04b77faddf6b77b2dde5b777addd6b7722ddc1b76e2ddb0b76a2dda1b766add92b7622dd82b75e6dd6c
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab44_powers : powerDigits 64 2817 tab44 = true := by decide +kernel
def tab45 : Nat := 0xb8602e178b85c6e169b8582e15ab854ae14ab8502e139b84c2e129b8482e119b844ae109b8402e0fab83c6e0e8b8382e0d9b834ae0c9b8302e0bab82c6e0aab8282e09ab823ae085b81f2e075b81b6e066b8172e054b8136e046b80f2e036b80b6e025b8072e015b8032e006b7ff2dff6b7fb6dfe5b7f72dfd4b7f32dfc4b7ef2dfb2b7ea6dfa1b7e62df90b7e2adf81
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab45_powers : powerDigits 64 2881 tab45 = true := by decide +kernel
def tab46 : Nat := 0xb8df2e375b8db2e365b8d72e355b8d3ae346b8cf2e336b8cb6e324b8c72e319b8c4ae309b8c02e2f9b8bc6e2e8b8b82e2d9b8b46e2cab8b02e2b9b8ac6e2a9b8a82e298b8a46e289b8a02e278b89c6e269b8982e25ab8942e24ab8902e23ab88c6e229b8882e21ab8846e208b8802e1f9b87c6e1eab8782e1dab874ae1cab8702e1b9b86c2e1a9b8682e199b864ae18a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab46_powers : powerDigits 64 2945 tab46 = true := by decide +kernel
def tab47 : Nat := 0xb95c2e569b958ae558b9542e54ab9506e539b94c2e529b9486e51ab9442e50ab941ae4fdb93d2e4eeb939ae4ddb9352e4ccb9312e4beb92d2e4adb9296e49db9252e48db9222e482b91e2e471b91a2e462b9162e451b912ae440b90e2e431b90a6e421b9062e411b902ae400b8fe2e3f2b8fb6e3e6b8f72e3d6b8f3ae3c5b8ef2e3b4b8ebae3a5b8e72e396b8e36e386
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab47_powers : powerDigits 64 3009 tab47 = true := by decide +kernel
def tab48 : Nat := 0xb9d52e74db9d26e741b9ce2e731b9caae722b9c62e711b9c2ae704b9bf2e6f4b9bbae6e6b9b72e6d6b9b36e6c5b9b02e6bab9ac2e6a9b9a82e69ab9a4ae68ab9a02e679b99d6e66cb9992e65db9956e64db9912e63db98d6e62db9892e621b9866e611b9822e601b97e6e5f2b97a2e5e0b9766e5d1b9732e5c6b96fae5b6b96b2e5a6b9672e595b9632e584b95fae575
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab48_powers : powerDigits 64 3073 tab48 = true := by decide +kernel
def tab49 : Nat := 0xba4d2e92dba496e91dba452e90cba426e901ba3e2e8f2ba3a6e8e1ba372e8d6ba332e8c4ba2f2e8b5ba2bae8aaba282e898ba24ae888ba202e878ba1d2e86dba192e85eba15ae84eba112e83eba0e6e832ba0a2e822ba066e811ba022e804b9ff6e7f6b9fb2e7e5b9f7ae7d5b9f32e7c9b9f02e7b9b9ec2e7a9b9e82e79ab9e42e78db9e16e77cb9dd2e76db9d9ae75e
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab49_powers : powerDigits 64 3137 tab49 = true := by decide +kernel
def tab50 : Nat := 0xbac22eb01babeaeaf1babb2eae6bab72ead6bab32eac5bab06eababaac2eaaabaa82ea9cbaa52ea8dbaa1aea7eba9d2ea72ba9a6ea61ba962ea51ba926ea46ba8f2ea35ba8b2ea25ba882ea18ba846ea0aba802e9f9ba7d6e9ecba792e9ddba752e9ceba722e9c2ba6e6e9b2ba6a2e9a1ba676e994ba632e984ba5f6e976ba5b2e969ba58ae959ba542e94aba506e93e
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab50_powers : powerDigits 64 3201 tab50 = true := by decide +kernel
def tab51 : Nat := 0xbb352eccdbb316ecbcbb2d2ecb2bb2aaeca0bb262ec92bb236ec85bb1f2ec75bb1c6ec6abb182ec5abb14aec4dbb112ec3ebb0d6ec31bb0a2ec20bb06aec12bb032ec06baffaebf6bafb2ebe9baf82ebd9baf42ebc9baf16ebbebaed2ebadbae9aeba0bae62eb90bae2aeb81badf2eb75badbaeb65bad72eb58bad46eb49bad02eb3abacd6eb2dbac92eb1cbac5aeb11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab51_powers : powerDigits 64 3265 tab51 = true := by decide +kernel
def tab52 : Nat := 0xbba52ee8ebba26ee82bb9e2ee71bb9b6ee65bb972ee55bb94aee48bb902ee39bb8daee2dbb892ee1cbb86aee12bb822ee02bb7faedf5bb7b2ede6bb782edd9bb742edcabb712edbebb6d2edaebb6aaeda0bb662ed92bb626ed85bb5f2ed75bb5b2ed69bb582ed5abb54aed4ebb512ed3ebb4daed31bb4a2ed20bb466ed11bb432ed06bb3f6ecf6bb3c2eceabb382ecda
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab52_powers : powerDigits 64 3329 tab52 = true := by decide +kernel
def tab53 : Nat := 0xbc142f049bc10af039bc0d2f02ebc092f022bc062f010bc026f006bbff2eff5bbfc6efeabbf82efd9bbf52efcdbbf12efc2bbeeaefb2bbea2efa5bbe72ef94bbe32ef89bbe0aef78bbdd2ef6ebbd9aef5dbbd62ef51bbd26ef42bbcf2ef35bbcbaef2abbc82ef18bbc46ef0dbbc12eefebbbdaeef2bbba2eee1bbb62eed5bbb32eec6bbb06eeb9bbac2eeaabba96ee9c
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab53_powers : powerDigits 64 3393 tab53 = true := by decide +kernel
def tab54 : Nat := 0xbc802f1f8bc7d6f1eebc792f1e2bc76af1d1bc732f1c6bc6f2f1b4bc6c2f1aabc686f19dbc652f18dbc62af180bc5e2f176bc5b6f165bc582f15abc546f149bc512f13ebc4daf131bc4a2f121bc476f116bc432f108bc406f0f8bc3c2f0ecbc39af0debc362f0d0bc322f0c5bc2f2f0b6bc2baf0aabc282f09abc256f08cbc212f07ebc1eaf072bc1a2f065bc176f056
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab54_powers : powerDigits 64 3457 tab54 = true := by decide +kernel
def tab55 : Nat := 0xbcea2f3a6bce72f396bce42f389bce16f37cbcdd2f370bcda6f360bcd72f356bcd3af349bcd02f33abccd6f32ebcc92f321bcc6af311bcc32f306bcbfaf2fabcbc2f2e8bcb96f2debcb52f2d1bcb22f2c0bcaf2f2b6bcab2f2a9bca82f299bca56f28ebca12f282bc9eaf270bc9b2f266bc976f25abc942f24abc91af23ebc8d2f232bc8aaf220bc872f215bc83af209
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab55_powers : powerDigits 64 3521 tab55 = true := by decide +kernel
def tab56 : Nat := 0xbd532f545bd506f538bd4d2f52ebd49af521bd462f511bd43af506bd402f4f9bd3caf4eebd392f4debd362f4d1bd332f4c4bd2f2f4b8bd2c2f4aabd296f49ebd252f492bd222f486bd1f2f476bd1caf46abd182f45dbd152f450bd122f442bd0faf436bd0b2f429bd086f419bd052f40dbd01af402bcfe2f3f5bcfbaf3e6bcf82f3d8bcf4af3cdbcf12f3bdbceeaf3b2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab56_powers : powerDigits 64 3585 tab56 = true := by decide +kernel
def tab57 : Nat := 0xbdba2f6e1bdb76f6d6bdb32f6c9bdb0af6bdbdad2f6acbdaaaf6a2bda72f694bda32f68abda02f67dbd9d6f66dbd9a2f662bd972f656bd932f649bd90af63ebd8d2f62dbd8aaf620bd872f615bd83af60abd802f5fcbd7daf5eebd7a2f5e2bd77af5d5bd732f5c9bd706f5b9bd6d2f5acbd6a6f5a1bd662f596bd63af58abd602f57abd5d2f56dbd592f561bd562f555
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab57_powers : powerDigits 64 3649 tab57 = true := by decide +kernel
def tab58 : Nat := 0xbe1f2f874be1c6f868be192f85cbe156f852be122f846be0faf83abe0c2f829be092f81ebe062f812be036f804bdff2f7f9bdfc6f7ecbdf92f7e0bdf62f7d1bdf32f7c5bdf06f7babded2f7adbde96f7a2bde62f796bde36f785bde02f778bddd6f76ebdda2f762bdd6af756bdd32f74abdd02f738bdcd2f72ebdca6f720bdc72f716bdc32f708bdc02f6fdbdbdaf6ed
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab58_powers : powerDigits 64 3713 tab58 = true := by decide +kernel
def tab59 : Nat := 0xbe442f90dbe412f902be3e2f8f1be3baf8e6be382f8d9be35af8ccbe322f8c1be2eaf8b5be2b2f8aabe28af89dbe252f88ebe226f881
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tab59_powers : powerDigits 24 3777 tab59 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def chunks : List (Nat × Nat) := [(64,tab0),(64,tab1),(64,tab2),(64,tab3),(64,tab4),(64,tab5),(64,tab6),(64,tab7),(64,tab8),(64,tab9),(64,tab10),(64,tab11),(64,tab12),(64,tab13),(64,tab14),(64,tab15),(64,tab16),(64,tab17),(64,tab18),(64,tab19),(64,tab20),(64,tab21),(64,tab22),(64,tab23),(64,tab24),(64,tab25),(64,tab26),(64,tab27),(64,tab28),(64,tab29),(64,tab30),(64,tab31),(64,tab32),(64,tab33),(64,tab34),(64,tab35),(64,tab36),(64,tab37),(64,tab38),(64,tab39),(64,tab40),(64,tab41),(64,tab42),(64,tab43),(64,tab44),(64,tab45),(64,tab46),(64,tab47),(64,tab48),(64,tab49),(64,tab50),(64,tab51),(64,tab52),(64,tab53),(64,tab54),(64,tab55),(64,tab56),(64,tab57),(64,tab58),(24,tab59)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def evaluate (r : Row) : Sums :=
  chunks.foldl (fun s d => runDigits r d.1 d.2 s) {}
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def report (r : Row) (s : Sums) : Nat × Nat × Nat :=
  let scale := (r.k1-r.k0)*1000
  let den := scale*LD*r.q
  let phi := Int.ofNat r.phi
  let cost := ceilN (W * max (phi*s.logLo+den).natAbs (phi*s.logHi+den).natAbs) (r.phi*den)
  let loss := ceilN (91*s.mass*W) (scale*(if r.q=1 then 10^10 else 10^16))
  let conv := if r.q=1 then ceilN (31*(r.finiteCost+r.tailCost)) 20
    else ceilN (26*(r.finiteCost+r.tailCost)) 25
  (cost,loss,cost+loss+conv)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def rowPass (r : Row) (s : Sums) : Bool := Id.run do
  let (_,_,total) := report r s
  let phi := ((List.range r.q).filter (fun k => k.gcd r.q == 1)).length
  return s.hLo ≤ 0 && 0 ≤ s.hHi && r.phi == phi &&
    decide (if r.q=1 then total*25<W else total*10000<96*W)
def checkRow (r : Row) := rowPass r (evaluate r)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def massTable : Array ℕ := #[0,0,1652914426,0,1652914426,0,1243217805,0,1652914426,0,1380549036,0,1243217805,0,1449228758,0,1652914426,0,1243217805,0,1380549036,0,1516554760,0,1243217805,0,1536348534,0,1449228758,0,1049276885,0,1652914426,0,1563317349,0,1243217805,0,1572979465,0,1380549036,0,1098426830,0,1516554760,0,1585738015,0,1243217805,0,1380549036,0,1536348534,2434251331,1243217805,1895048552,1449228758,1769266133,1598847177,2437494279,1049276885,2438397196,1602129281,1630895646,1652914426,1920079114,1146469554,2441632941,1563317349,1784949987,1217451173,2443563453,1243217805,2444434122,1610376794,1553883599,1572979465,1987681259,1160891614,2446932388,1380549036,1861026891,1614644333,2448565050,1098426830,1954198800,1616524308,1800379576,1516554760,2451121137,1049276885,2014661311,1585738015,1804064265,1619655169,1966043216,1243217805,2453741447,1449228758,1706710859,1380549036,2454850389,1180092861,2455344344,1536348534,1368545173]
def expectedMass (q : ℕ) : ℕ := massTable[q]!
def passWithMass (s : Row) (v : Sums) := rowPass s v && decide (v.mass=expectedMass s.q)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem split_mass (s : Row) (h : passWithMass s (evaluate s)=true) :
    checkRow s=true ∧ (evaluate s).mass=expectedMass s.q := by
  simpa only [passWithMass,Bool.and_eq_true,decide_eq_true_eq,checkRow] using h



abbrev walkSpec (a b : Row) : Prop :=
  a.k0=b.k0 ∧ a.k1=b.k1 ∧ a.al=b.al ∧ a.ah=b.ah ∧ 0<a.q ∧ b.q∣a.q ∧
  (List.range a.q).all (fun k => (k.gcd a.q != 1) == (k.gcd b.q != 1)) = true

theorem reducedMod (k q : Nat) : (k % q).gcd q = k.gcd q :=
  (Nat.gcd_rec q k).symm.trans (Nat.gcd_comm q k)

theorem sameEvaluation (a b : Row) (h : walkSpec a b) : evaluate a=evaluate b := by
  obtain ⟨k0,k1,al,ah,hq,dvd,ok⟩ := h
  have dg (k : Nat) : (k.gcd a.q != 1) = (k.gcd b.q != 1) := by
    have comp := List.all_eq_true.mp ok (k % a.q) (List.mem_range.mpr (Nat.mod_lt _ hq))
    have gd : (k % a.q).gcd b.q=k.gcd b.q := by
      rw [←reducedMod (k % a.q) b.q,Nat.mod_mod_of_dvd k dvd,reducedMod]
    simpa only [reducedMod k a.q,gd,beq_iff_eq] using comp
  have st (v : Sums) (e : Nat) : step a v e=step b v e := by
    simp only [step,k0,k1,al,ah,dg]
  have rd (n z : Nat) (v : Sums) : runDigits a n z v=runDigits b n z v := by
    induction n generalizing z v with
    | zero => rfl
    | succ n ih => simp only [runDigits,st,ih]
  unfold evaluate
  have fn : (fun (v:Sums) (p:Nat×Nat) => runDigits a p.1 p.2 v) =
      (fun (v:Sums) (p:Nat×Nat) => runDigits b p.1 p.2 v) := by
    funext v p
    exact rd _ _ _
  rw [fn]

def digest (v : Sums) : Nat × Int × Int × Int × Int × Nat :=
  (v.k,v.hLo,v.hHi,v.logLo,v.logHi,v.mass)

theorem digest_inj {a b : Sums} (h : digest a=digest b) : a=b := by
  cases a
  cases b
  simpa only [digest,Prod.mk.injEq,Sums.mk.injEq] using h

def q2 : Row := ⟨2,2508,3800,1,(-7755),(-7754),6317662722,1645039694⟩
def cache2 : Sums := ⟨3801,-64876530182,142881182657,-105803656534030246157,-105776255908868146622,1652914426⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc2 : evaluate q2=cache2 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q2_costmass : passWithMass q2 (evaluate q2) = true := by
  rw [calc2]
  decide +kernel
theorem q2_cost : checkRow q2 = true := (split_mass _ q2_costmass).1
def q4 : Row := ⟨4,2508,3800,2,(-7755),(-7754),6730509879,1654287709⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q4_costmass : passWithMass q4 (evaluate q4) = true := by
  rw [sameEvaluation q4 q2 (by decide +kernel),calc2]
  decide +kernel
theorem q4_cost : checkRow q4 = true := (split_mass _ q4_costmass).1
def q6 : Row := ⟨6,2508,3800,2,(-66375),(-66374),6637725472,1214288205⟩
def cache6 : Sums := ⟨3801,-116338482180,22254421950,-158361122927159747302,-158342061231935180531,1243217805⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc6 : evaluate q6=cache6 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q6_costmass : passWithMass q6 (evaluate q6) = true := by
  rw [calc6]
  decide +kernel
theorem q6_cost : checkRow q6 = true := (split_mass _ q6_costmass).1
def q8 : Row := ⟨8,2508,3800,4,(-7755),(-7754),7389324137,1642416650⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q8_costmass : passWithMass q8 (evaluate q8) = true := by
  rw [sameEvaluation q8 q2 (by decide +kernel),calc2]
  decide +kernel
theorem q8_cost : checkRow q8 = true := (split_mass _ q8_costmass).1
def q10 : Row := ⟨10,2508,3800,4,(-39646),(-39645),6378665671,1369006115⟩
def cache10 : Sums := ⟨3801,-83461295090,82824623975,-132025277835484833601,-132003119843077501639,1380549036⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc10 : evaluate q10=cache10 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q10_costmass : passWithMass q10 (evaluate q10) = true := by
  rw [calc10]
  decide +kernel
theorem q10_cost : checkRow q10 = true := (split_mass _ q10_costmass).1
def q12 : Row := ⟨12,2508,3800,4,(-66375),(-66374),6259076610,1226582310⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q12_costmass : passWithMass q12 (evaluate q12) = true := by
  rw [sameEvaluation q12 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q12_cost : checkRow q12 = true := (split_mass _ q12_costmass).1
def q14 : Row := ⟨14,2508,3800,6,(-30917),(-30916),7260544935,1429268630⟩
def cache14 : Sums := ⟨3801,-100175990744,77957987907,-123249186461198856012,-123225552874212951478,1449228758⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc14 : evaluate q14=cache14 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q14_costmass : passWithMass q14 (evaluate q14) = true := by
  rw [calc14]
  decide +kernel
theorem q14_cost : checkRow q14 = true := (split_mass _ q14_costmass).1
def q16 : Row := ⟨16,2508,3800,8,(-7755),(-7754),7265893841,1649659262⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q16_costmass : passWithMass q16 (evaluate q16) = true := by
  rw [sameEvaluation q16 q2 (by decide +kernel),calc2]
  decide +kernel
theorem q16_cost : checkRow q16 = true := (split_mass _ q16_costmass).1
def q18 : Row := ⟨18,2508,3800,6,(-66375),(-66374),6897623316,1227327983⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q18_costmass : passWithMass q18 (evaluate q18) = true := by
  rw [sameEvaluation q18 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q18_cost : checkRow q18 = true := (split_mass _ q18_costmass).1
def q20 : Row := ⟨20,2508,3800,8,(-39646),(-39645),5519970941,1366185915⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q20_costmass : passWithMass q20 (evaluate q20) = true := by
  rw [sameEvaluation q20 q10 (by decide +kernel),calc10]
  decide +kernel
theorem q20_cost : checkRow q20 = true := (split_mass _ q20_costmass).1
def q22 : Row := ⟨22,2508,3800,10,(-26539),(-26538),6994983493,1512292983⟩
def cache22 : Sums := ⟨3801,-10424398887,178374617192,-116234554255058292112,-116209514575957568026,1516554760⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc22 : evaluate q22=cache22 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q22_costmass : passWithMass q22 (evaluate q22) = true := by
  rw [calc22]
  decide +kernel
theorem q22_cost : checkRow q22 = true := (split_mass _ q22_costmass).1
def q24 : Row := ⟨24,2508,3800,8,(-66375),(-66374),5883463489,1226652896⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q24_costmass : passWithMass q24 (evaluate q24) = true := by
  rw [sameEvaluation q24 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q24_cost : checkRow q24 = true := (split_mass _ q24_costmass).1
def q26 : Row := ⟨26,2508,3800,12,(-23789),(-23788),7360631554,1544678812⟩
def cache26 : Sums := ⟨3801,-120528769243,71103718199,-114481035811090496309,-114455610625261396072,1536348534⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc26 : evaluate q26=cache26 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q26_costmass : passWithMass q26 (evaluate q26) = true := by
  rw [calc26]
  decide +kernel
theorem q26_cost : checkRow q26 = true := (split_mass _ q26_costmass).1
def q28 : Row := ⟨28,2508,3800,12,(-30917),(-30916),6561190048,1448021674⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q28_costmass : passWithMass q28 (evaluate q28) = true := by
  rw [sameEvaluation q28 q14 (by decide +kernel),calc14]
  decide +kernel
theorem q28_cost : checkRow q28 = true := (split_mass _ q28_costmass).1
def q30 : Row := ⟨30,2508,3800,8,(-244808),(-244807),5574897161,1016677589⟩
def cache30 : Sums := ⟨3801,-66680676999,44219332123,-197079081944558161451,-197064055180292199607,1049276885⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc30 : evaluate q30=cache30 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q30_costmass : passWithMass q30 (evaluate q30) = true := by
  rw [calc30]
  decide +kernel
theorem q30_cost : checkRow q30 = true := (split_mass _ q30_costmass).1
def q32 : Row := ⟨32,2508,3800,16,(-7755),(-7754),6537698059,1662860297⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q32_costmass : passWithMass q32 (evaluate q32) = true := by
  rw [sameEvaluation q32 q2 (by decide +kernel),calc2]
  decide +kernel
theorem q32_cost : checkRow q32 = true := (split_mass _ q32_costmass).1
def q34 : Row := ⟨34,2508,3800,16,(-20568),(-20567),6317240784,1580040390⟩
def cache34 : Sums := ⟨3801,-86281227542,109287382718,-112297967607047128336,-112272041918085140210,1563317349⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc34 : evaluate q34=cache34 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q34_costmass : passWithMass q34 (evaluate q34) = true := by
  rw [calc34]
  decide +kernel
theorem q34_cost : checkRow q34 = true := (split_mass _ q34_costmass).1
def q36 : Row := ⟨36,2508,3800,12,(-66375),(-66374),5968229744,1240504698⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q36_costmass : passWithMass q36 (evaluate q36) = true := by
  rw [sameEvaluation q36 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q36_cost : checkRow q36 = true := (split_mass _ q36_costmass).1
def q38 : Row := ⟨38,2508,3800,18,(-20306),(-20305),6767319301,1592375351⟩
def cache38 : Sums := ⟨3801,-156262547761,40560690285,-111569760410369750076,-111543664053680212441,1572979465⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc38 : evaluate q38=cache38 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q38_costmass : passWithMass q38 (evaluate q38) = true := by
  rw [calc38]
  decide +kernel
theorem q38_cost : checkRow q38 = true := (split_mass _ q38_costmass).1
def q40 : Row := ⟨40,2508,3800,16,(-39646),(-39645),6392026309,1375821819⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q40_costmass : passWithMass q40 (evaluate q40) = true := by
  rw [sameEvaluation q40 q10 (by decide +kernel),calc10]
  decide +kernel
theorem q40_cost : checkRow q40 = true := (split_mass _ q40_costmass).1
def q42 : Row := ⟨42,2508,3800,12,(-196244),(-196243),5373864603,1082796861⟩
def cache42 : Sums := ⟨3801,-14160813450,104462134473,-184049966200104029354,-184033806233919654929,1098426830⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc42 : evaluate q42=cache42 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q42_costmass : passWithMass q42 (evaluate q42) = true := by
  rw [calc42]
  decide +kernel
theorem q42_cost : checkRow q42 = true := (split_mass _ q42_costmass).1
def q44 : Row := ⟨44,2508,3800,20,(-26539),(-26538),6458734832,1518241530⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q44_costmass : passWithMass q44 (evaluate q44) = true := by
  rw [sameEvaluation q44 q22 (by decide +kernel),calc22]
  decide +kernel
theorem q44_cost : checkRow q44 = true := (split_mass _ q44_costmass).1
def q46 : Row := ⟨46,2508,3800,22,(-20021),(-20020),6493960702,1589748941⟩
def cache46 : Sums := ⟨3801,-84326736731,114485330576,-110504848864760160999,-110478505578188244546,1585738015⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem calc46 : evaluate q46=cache46 := digest_inj (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q46_costmass : passWithMass q46 (evaluate q46) = true := by
  rw [calc46]
  decide +kernel
theorem q46_cost : checkRow q46 = true := (split_mass _ q46_costmass).1
def q48 : Row := ⟨48,2508,3800,16,(-66375),(-66374),5250689464,1225623697⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q48_costmass : passWithMass q48 (evaluate q48) = true := by
  rw [sameEvaluation q48 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q48_cost : checkRow q48 = true := (split_mass _ q48_costmass).1
def q50 : Row := ⟨50,2508,3800,20,(-39646),(-39645),5624618498,1373639821⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q50_costmass : passWithMass q50 (evaluate q50) = true := by
  rw [sameEvaluation q50 q10 (by decide +kernel),calc10]
  decide +kernel
theorem q50_cost : checkRow q50 = true := (split_mass _ q50_costmass).1
def q52 : Row := ⟨52,2508,3800,24,(-23789),(-23788),6525892929,1554573894⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q52_costmass : passWithMass q52 (evaluate q52) = true := by
  rw [sameEvaluation q52 q26 (by decide +kernel),calc26]
  decide +kernel
theorem q52_cost : checkRow q52 = true := (split_mass _ q52_costmass).1
def q53 : Row := ⟨53,2508,3800,52,(-2575),(-2574),5744270410,2485389454⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q53_costmass : passWithMass q53 (evaluate q53) = true := by decide +kernel
theorem q53_cost : checkRow q53 = true := (split_mass _ q53_costmass).1
def q54 : Row := ⟨54,2508,3800,18,(-66375),(-66374),5925729652,1232152483⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q54_costmass : passWithMass q54 (evaluate q54) = true := by
  rw [sameEvaluation q54 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q54_cost : checkRow q54 = true := (split_mass _ q54_costmass).1
def q55 : Row := ⟨55,2508,3800,40,(-8472),(-8471),5225675199,1905491290⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q55_costmass : passWithMass q55 (evaluate q55) = true := by decide +kernel
theorem q55_cost : checkRow q55 = true := (split_mass _ q55_costmass).1
def q56 : Row := ⟨56,2508,3800,24,(-30917),(-30916),5940372984,1451764122⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q56_costmass : passWithMass q56 (evaluate q56) = true := by
  rw [sameEvaluation q56 q14 (by decide +kernel),calc14]
  decide +kernel
theorem q56_cost : checkRow q56 = true := (split_mass _ q56_costmass).1
def q57 : Row := ⟨57,2508,3800,36,(-9818),(-9817),5587916351,1791548645⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q57_costmass : passWithMass q57 (evaluate q57) = true := by decide +kernel
theorem q57_cost : checkRow q57 = true := (split_mass _ q57_costmass).1
def q58 : Row := ⟨58,2508,3800,28,(-19182),(-19181),6092725911,1610810290⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q58_costmass : passWithMass q58 (evaluate q58) = true := by decide +kernel
theorem q58_cost : checkRow q58 = true := (split_mass _ q58_costmass).1
def q59 : Row := ⟨59,2508,3800,58,(-1599),(-1598),5775653500,2487050497⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q59_costmass : passWithMass q59 (evaluate q59) = true := by decide +kernel
theorem q59_cost : checkRow q59 = true := (split_mass _ q59_costmass).1
def q60 : Row := ⟨60,2508,3800,16,(-244808),(-244807),5414864345,1029528849⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q60_costmass : passWithMass q60 (evaluate q60) = true := by
  rw [sameEvaluation q60 q30 (by decide +kernel),calc30]
  decide +kernel
theorem q60_cost : checkRow q60 = true := (split_mass _ q60_costmass).1
def q61 : Row := ⟨61,2508,3800,60,(-1402),(-1401),5341463373,2493213105⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q61_costmass : passWithMass q61 (evaluate q61) = true := by decide +kernel
theorem q61_cost : checkRow q61 = true := (split_mass _ q61_costmass).1
def q62 : Row := ⟨62,2508,3800,30,(-18701),(-18700),5730728221,1585767163⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q62_costmass : passWithMass q62 (evaluate q62) = true := by decide +kernel
theorem q62_cost : checkRow q62 = true := (split_mass _ q62_costmass).1
def q63 : Row := ⟨63,2508,3800,36,(-15964),(-15963),5214717967,1646376765⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q63_costmass : passWithMass q63 (evaluate q63) = true := by decide +kernel
theorem q63_cost : checkRow q63 = true := (split_mass _ q63_costmass).1
def q64 : Row := ⟨64,2508,3800,32,(-7755),(-7754),5605426683,1655260633⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q64_costmass : passWithMass q64 (evaluate q64) = true := by
  rw [sameEvaluation q64 q2 (by decide +kernel),calc2]
  decide +kernel
theorem q64_cost : checkRow q64 = true := (split_mass _ q64_costmass).1
def q65 : Row := ⟨65,2508,3800,48,(-8288),(-8287),5670217854,1953917828⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q65_costmass : passWithMass q65 (evaluate q65) = true := by decide +kernel
theorem q65_cost : checkRow q65 = true := (split_mass _ q65_costmass).1
def q66 : Row := ⟨66,2508,3800,20,(-158537),(-158536),5680007778,1127157704⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q66_costmass : passWithMass q66 (evaluate q66) = true := by decide +kernel
theorem q66_cost : checkRow q66 = true := (split_mass _ q66_costmass).1
def q67 : Row := ⟨67,2508,3800,66,(-1451),(-1450),5189514085,2493086114⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q67_costmass : passWithMass q67 (evaluate q67) = true := by decide +kernel
theorem q67_cost : checkRow q67 = true := (split_mass _ q67_costmass).1
def q68 : Row := ⟨68,2508,3800,32,(-20568),(-20567),5610566107,1562752628⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q68_costmass : passWithMass q68 (evaluate q68) = true := by
  rw [sameEvaluation q68 q34 (by decide +kernel),calc34]
  decide +kernel
theorem q68_cost : checkRow q68 = true := (split_mass _ q68_costmass).1
def q69 : Row := ⟨69,2508,3800,44,(-10761),(-10760),4940220826,1811321493⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q69_costmass : passWithMass q69 (evaluate q69) = true := by decide +kernel
theorem q69_cost : checkRow q69 = true := (split_mass _ q69_costmass).1
def q70 : Row := ⟨70,2508,3800,24,(-118734),(-118733),5021974971,1222074527⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q70_costmass : passWithMass q70 (evaluate q70) = true := by decide +kernel
theorem q70_cost : checkRow q70 = true := (split_mass _ q70_costmass).1
def q71 : Row := ⟨71,2508,3800,70,(-1631),(-1630),5520781747,2495378709⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q71_costmass : passWithMass q71 (evaluate q71) = true := by decide +kernel
theorem q71_cost : checkRow q71 = true := (split_mass _ q71_costmass).1
def q72 : Row := ⟨72,2508,3800,24,(-66375),(-66374),4987913029,1237496862⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q72_costmass : passWithMass q72 (evaluate q72) = true := by
  rw [sameEvaluation q72 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q72_cost : checkRow q72 = true := (split_mass _ q72_costmass).1
def q73 : Row := ⟨73,2508,3800,72,(-1674),(-1673),5269178949,2493793907⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q73_costmass : passWithMass q73 (evaluate q73) = true := by decide +kernel
theorem q73_cost : checkRow q73 = true := (split_mass _ q73_costmass).1
def q74 : Row := ⟨74,2508,3800,36,(-19191),(-19190),5878411288,1625769965⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q74_costmass : passWithMass q74 (evaluate q74) = true := by decide +kernel
theorem q74_cost : checkRow q74 = true := (split_mass _ q74_costmass).1
def q75 : Row := ⟨75,2508,3800,40,(-19997),(-19996),5004038331,1564022295⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q75_costmass : passWithMass q75 (evaluate q75) = true := by decide +kernel
theorem q75_cost : checkRow q75 = true := (split_mass _ q75_costmass).1
def q76 : Row := ⟨76,2508,3800,36,(-20306),(-20305),5050618795,1580352534⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q76_costmass : passWithMass q76 (evaluate q76) = true := by
  rw [sameEvaluation q76 q38 (by decide +kernel),calc38]
  decide +kernel
theorem q76_cost : checkRow q76 = true := (split_mass _ q76_costmass).1
def q77 : Row := ⟨77,2508,3800,60,(-6005),(-6004),4829922624,2027290685⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q77_costmass : passWithMass q77 (evaluate q77) = true := by decide +kernel
theorem q77_cost : checkRow q77 = true := (split_mass _ q77_costmass).1
def q78 : Row := ⟨78,2508,3800,24,(-148294),(-148293),5195862114,1161282390⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q78_costmass : passWithMass q78 (evaluate q78) = true := by decide +kernel
theorem q78_cost : checkRow q78 = true := (split_mass _ q78_costmass).1
def q79 : Row := ⟨79,2508,3800,78,(-1546),(-1545),4581031747,2503596433⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q79_costmass : passWithMass q79 (evaluate q79) = true := by decide +kernel
theorem q79_cost : checkRow q79 = true := (split_mass _ q79_costmass).1
def q80 : Row := ⟨80,2508,3800,32,(-39646),(-39645),5068717803,1394649951⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q80_costmass : passWithMass q80 (evaluate q80) = true := by
  rw [sameEvaluation q80 q10 (by decide +kernel),calc10]
  decide +kernel
theorem q80_cost : checkRow q80 = true := (split_mass _ q80_costmass).1
def q81 : Row := ⟨81,2508,3800,54,(-4620),(-4619),5375150520,1881833494⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q81_costmass : passWithMass q81 (evaluate q81) = true := by decide +kernel
theorem q81_cost : checkRow q81 = true := (split_mass _ q81_costmass).1
def q82 : Row := ⟨82,2508,3800,40,(-17278),(-17277),5648654929,1637110337⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q82_costmass : passWithMass q82 (evaluate q82) = true := by decide +kernel
theorem q82_cost : checkRow q82 = true := (split_mass _ q82_costmass).1
def q83 : Row := ⟨83,2508,3800,82,(-1436),(-1435),4802763214,2487982779⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q83_costmass : passWithMass q83 (evaluate q83) = true := by decide +kernel
theorem q83_cost : checkRow q83 = true := (split_mass _ q83_costmass).1
def q84 : Row := ⟨84,2508,3800,24,(-196244),(-196243),4831034663,1087227610⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q84_costmass : passWithMass q84 (evaluate q84) = true := by
  rw [sameEvaluation q84 q42 (by decide +kernel),calc42]
  decide +kernel
theorem q84_cost : checkRow q84 = true := (split_mass _ q84_costmass).1
def q85 : Row := ⟨85,2508,3800,64,(-7364),(-7363),4888862034,1988295524⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q85_costmass : passWithMass q85 (evaluate q85) = true := by decide +kernel
theorem q85_cost : checkRow q85 = true := (split_mass _ q85_costmass).1
def q86 : Row := ⟨86,2508,3800,42,(-17058),(-17057),5029746249,1608741805⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q86_costmass : passWithMass q86 (evaluate q86) = true := by decide +kernel
theorem q86_cost : checkRow q86 = true := (split_mass _ q86_costmass).1
def q87 : Row := ⟨87,2508,3800,56,(-11093),(-11092),5195536188,1824589360⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q87_costmass : passWithMass q87 (evaluate q87) = true := by decide +kernel
theorem q87_cost : checkRow q87 = true := (split_mass _ q87_costmass).1
def q88 : Row := ⟨88,2508,3800,40,(-26539),(-26538),5357904898,1506715518⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q88_costmass : passWithMass q88 (evaluate q88) = true := by
  rw [sameEvaluation q88 q22 (by decide +kernel),calc22]
  decide +kernel
theorem q88_cost : checkRow q88 = true := (split_mass _ q88_costmass).1
def q89 : Row := ⟨89,2508,3800,88,(-1641),(-1640),5085095685,2490200329⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q89_costmass : passWithMass q89 (evaluate q89) = true := by decide +kernel
theorem q89_cost : checkRow q89 = true := (split_mass _ q89_costmass).1
def q90 : Row := ⟨90,2508,3800,24,(-244808),(-244807),4746672324,1037207437⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q90_costmass : passWithMass q90 (evaluate q90) = true := by
  rw [sameEvaluation q90 q30 (by decide +kernel),calc30]
  decide +kernel
theorem q90_cost : checkRow q90 = true := (split_mass _ q90_costmass).1
def q91 : Row := ⟨91,2508,3800,72,(-6775),(-6774),4561936085,2050799847⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q91_costmass : passWithMass q91 (evaluate q91) = true := by decide +kernel
theorem q91_cost : checkRow q91 = true := (split_mass _ q91_costmass).1
def q92 : Row := ⟨92,2508,3800,44,(-20021),(-20020),5062043703,1601268209⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q92_costmass : passWithMass q92 (evaluate q92) = true := by
  rw [sameEvaluation q92 q46 (by decide +kernel),calc46]
  decide +kernel
theorem q92_cost : checkRow q92 = true := (split_mass _ q92_costmass).1
def q93 : Row := ⟨93,2508,3800,60,(-10272),(-10271),4479316507,1830154599⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q93_costmass : passWithMass q93 (evaluate q93) = true := by decide +kernel
theorem q93_cost : checkRow q93 = true := (split_mass _ q93_costmass).1
def q94 : Row := ⟨94,2508,3800,46,(-16798),(-16797),5024604134,1631871526⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q94_costmass : passWithMass q94 (evaluate q94) = true := by decide +kernel
theorem q94_cost : checkRow q94 = true := (split_mass _ q94_costmass).1
def q95 : Row := ⟨95,2508,3800,72,(-7272),(-7271),4616766536,1993917357⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q95_costmass : passWithMass q95 (evaluate q95) = true := by decide +kernel
theorem q95_cost : checkRow q95 = true := (split_mass _ q95_costmass).1
def q96 : Row := ⟨96,2508,3800,32,(-66375),(-66374),5042434803,1236905492⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q96_costmass : passWithMass q96 (evaluate q96) = true := by
  rw [sameEvaluation q96 q6 (by decide +kernel),calc6]
  decide +kernel
theorem q96_cost : checkRow q96 = true := (split_mass _ q96_costmass).1
def q97 : Row := ⟨97,2508,3800,96,(-1547),(-1546),4811815091,2517564982⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q97_costmass : passWithMass q97 (evaluate q97) = true := by decide +kernel
theorem q97_cost : checkRow q97 = true := (split_mass _ q97_costmass).1
def q98 : Row := ⟨98,2508,3800,42,(-30917),(-30916),5025519421,1457724864⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q98_costmass : passWithMass q98 (evaluate q98) = true := by
  rw [sameEvaluation q98 q14 (by decide +kernel),calc14]
  decide +kernel
theorem q98_cost : checkRow q98 = true := (split_mass _ q98_costmass).1
def q99 : Row := ⟨99,2508,3800,60,(-12711),(-12710),4853016983,1722808819⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q99_costmass : passWithMass q99 (evaluate q99) = true := by decide +kernel
theorem q99_cost : checkRow q99 = true := (split_mass _ q99_costmass).1
def q100 : Row := ⟨100,2508,3800,40,(-39646),(-39645),4743333075,1388687310⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q100_costmass : passWithMass q100 (evaluate q100) = true := by
  rw [sameEvaluation q100 q10 (by decide +kernel),calc10]
  decide +kernel
theorem q100_cost : checkRow q100 = true := (split_mass _ q100_costmass).1
def q101 : Row := ⟨101,2508,3800,100,(-1462),(-1461),5159403068,2482151507⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q101_costmass : passWithMass q101 (evaluate q101) = true := by decide +kernel
theorem q101_cost : checkRow q101 = true := (split_mass _ q101_costmass).1
def q102 : Row := ⟨102,2508,3800,32,(-135146),(-135145),4819427613,1166221518⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q102_costmass : passWithMass q102 (evaluate q102) = true := by decide +kernel
theorem q102_cost : checkRow q102 = true := (split_mass _ q102_costmass).1
def q103 : Row := ⟨103,2508,3800,102,(-1455),(-1454),4843754896,2513554177⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q103_costmass : passWithMass q103 (evaluate q103) = true := by decide +kernel
theorem q103_cost : checkRow q103 = true := (split_mass _ q103_costmass).1
def q104 : Row := ⟨104,2508,3800,48,(-23789),(-23788),4776493120,1553198705⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q104_costmass : passWithMass q104 (evaluate q104) = true := by
  rw [sameEvaluation q104 q26 (by decide +kernel),calc26]
  decide +kernel
theorem q104_cost : checkRow q104 = true := (split_mass _ q104_costmass).1
def q105 : Row := ⟨105,2508,3800,48,(-59306),(-59305),4017610679,1378401687⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q105_costmass : passWithMass q105 (evaluate q105) = true := by decide +kernel
theorem q105_cost : checkRow q105 = true := (split_mass _ q105_costmass).1
end FR7022ScalarTable
namespace FR7022ScalarTable
def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, z => (z % 262144) :: unpack n (z >>> 18)
abbrev entryList := chunks.flatMap (fun c => unpack c.1 c.2)
theorem run_as_list (r : Row) (n z : Nat) (s : Sums) :
  runDigits r n z s = (unpack n z).foldl (step r) s := by
  induction n generalizing s z with
  | zero => rfl
  | succ n ih => exact ih _ _
theorem eval_as_list (r : Row) : evaluate r = entryList.foldl (step r) {} := by
  have aux (cs : List (Nat × Nat)) (s : Sums) :
      cs.foldl (fun t d => runDigits r d.1 d.2 t) s =
        (cs.flatMap fun d => unpack d.1 d.2).foldl (step r) s := by
    induction cs generalizing s with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.foldl_cons,List.flatMap_cons,List.foldl_append]
      rw [ih,run_as_list]
  exact aux _ _
theorem step_progress (r : Row) (s : Sums) (entry : Nat) : (step r s entry).k = s.k+1 := by
  by_cases h : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = true <;> simp [step,h]
theorem register (r : Row) (f : Sums → Int) (v : Nat → Nat → Int)
    (inc : ∀ s a, f (step r s a) = f s + v s.k a) :
    f (evaluate r) = f {} + (entryList.zipIdx 1 |>.map (fun t => v t.2 t.1)).sum := by
  have aux (l : List Nat) (s : Sums) : f (l.foldl (step r) s) =
      f s + ((l.zipIdx s.k).map (fun t => v t.2 t.1)).sum := by
    induction l generalizing s with
    | nil => simp
    | cons a l ih =>
      simp only [List.foldl_cons,List.zipIdx_cons,List.map_cons,List.sum_cons]
      rw [ih,inc,step_progress,Int.add_assoc]
  rw [eval_as_list]
  exact aux _ _
end FR7022ScalarTable
namespace FR7022ScalarTable
open Finset
theorem zip_sum (l : List Nat) (off : Nat) (v : Nat → Nat → Int) :
  ((l.zipIdx off).map (fun t => v t.2 t.1)).sum =
    ∑ i ∈ range l.length, v (off+i) ((l[i]?).getD 0) := by
  induction l generalizing off with
  | nil => simp
  | cons a l ih =>
    simp only [List.zipIdx_cons,List.map_cons,List.sum_cons,List.length_cons,sum_range_succ']
    rw [ih]
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Int.add_comm]
def entryAt (k : Nat) := (entryList[k-1]?).getD 0
theorem table_size : entryList.length=3800 := by decide +kernel
theorem sum_of_steps (r : Row) (f : Sums → Int) (v : Nat → Nat → Int)
    (inc : ∀ s a, f (step r s a) = f s + v s.k a) :
    f (evaluate r) = f {} + ∑ i ∈ range 3800, v (i+1) (entryAt (i+1)) := by
  rw [register r f v inc, zip_sum, table_size]
  simp [entryAt, Nat.add_comm]
end FR7022ScalarTable
namespace FR7022ScalarTable
open Finset
def supportAll : Finset ℕ := (range 3800).image (fun i => i+1)
def inactive (r : Row) (k : ℕ) : Bool := decide (k>r.k1) || k.gcd r.q != 1
def val (r : Row) (k entry : ℕ) (alpha : ℤ) : ℤ :=
  if inactive r k then 0 else
    let sign : ℤ := if entry % 4=1 then 1 else if entry % 4=2 then -1 else 0
    1000*(sign*Int.ofNat (min (r.k1-r.k0) (r.k1-k))) + (if r.k0<k then alpha else 0)
def logLow (entry : ℕ) : ℤ := Int.ofNat (entry/4*6931471803)
def logHigh (k entry : ℕ) : ℤ :=
  if k=1 then 0 else Int.ofNat ((entry/4+1)*6931471808)
theorem domain_register (r : Row) (f : Sums → Int) (v : Nat → Nat → Int)
    (init : f {}=0) (inc : ∀ s a, f (step r s a) = f s + v s.k a) :
    f (evaluate r) = ∑ k ∈ supportAll, v k (entryAt k) := by
  rw [sum_of_steps r f v inc,init,zero_add,supportAll,Finset.sum_image]
  intro a _ b _ eq
  exact Nat.add_right_cancel eq
def atomhLo (r : Row) (k a : ℕ) : ℤ := ceilZ (W*val r k a r.al) k
theorem actual_hLo (r : Row) :
    (Sums.hLo) (evaluate r) = ∑ k ∈ supportAll, atomhLo r k (entryAt k) := by
  apply domain_register r Sums.hLo (atomhLo r) (by rfl)
  intro s a
  by_cases h : inactive r s.k = true
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = true := h
    simp [step,atomhLo,val,logLow,logHigh,h,t,ceilZ]
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = false := Bool.eq_false_iff.mpr h
    simp [step,atomhLo,val,logLow,logHigh,h,t,ceilZ]
def atomhHi (r : Row) (k a : ℕ) : ℤ := (W*val r k a r.ah)/(k:ℤ)
theorem actual_hHi (r : Row) :
    (Sums.hHi) (evaluate r) = ∑ k ∈ supportAll, atomhHi r k (entryAt k) := by
  apply domain_register r Sums.hHi (atomhHi r) (by rfl)
  intro s a
  by_cases h : inactive r s.k = true
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = true := h
    simp [step,atomhHi,val,logLow,logHigh,h,t,ceilZ]
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = false := Bool.eq_false_iff.mpr h
    simp [step,atomhHi,val,logLow,logHigh,h,t,ceilZ]
def atomlogLo (r : Row) (k a : ℕ) : ℤ := (min (val r k a r.al*logLow a) (val r k a r.al*logHigh k a))/(k:ℤ)
theorem actual_logLo (r : Row) :
    (Sums.logLo) (evaluate r) = ∑ k ∈ supportAll, atomlogLo r k (entryAt k) := by
  apply domain_register r Sums.logLo (atomlogLo r) (by rfl)
  intro s a
  by_cases h : inactive r s.k = true
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = true := h
    simp [step,atomlogLo,val,logLow,logHigh,h,t,ceilZ]
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = false := Bool.eq_false_iff.mpr h
    simp [step,atomlogLo,val,logLow,logHigh,h,t,ceilZ]
def atomlogHi (r : Row) (k a : ℕ) : ℤ := ceilZ (max (val r k a r.ah*logLow a) (val r k a r.ah*logHigh k a)) k
theorem actual_logHi (r : Row) :
    (Sums.logHi) (evaluate r) = ∑ k ∈ supportAll, atomlogHi r k (entryAt k) := by
  apply domain_register r Sums.logHi (atomlogHi r) (by rfl)
  intro s a
  by_cases h : inactive r s.k = true
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = true := h
    simp [step,atomlogHi,val,logLow,logHigh,h,t,ceilZ]
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = false := Bool.eq_false_iff.mpr h
    simp [step,atomlogHi,val,logLow,logHigh,h,t,ceilZ]
def atommass (r : Row) (k a : ℕ) : ℤ := (max (val r k a r.al).natAbs (val r k a r.ah).natAbs:ℕ)
theorem actual_mass (r : Row) :
    ((fun s => (s.mass:ℤ))) (evaluate r) = ∑ k ∈ supportAll, atommass r k (entryAt k) := by
  apply domain_register r (fun s => (s.mass:ℤ)) (atommass r) (by rfl)
  intro s a
  by_cases h : inactive r s.k = true
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = true := h
    simp [step,atommass,val,logLow,logHigh,h,t,ceilZ]
  · have t : (decide (s.k>r.k1) || s.k.gcd r.q != 1) = false := Bool.eq_false_iff.mpr h
    simp [step,atommass,val,logLow,logHigh,h,t,ceilZ]
end FR7022ScalarTable
namespace FR7022ScalarTable
open Finset FR7022SignedLog
theorem mem_support {k : ℕ} : k∈supportAll ↔ 0<k ∧ k≤3800 := by
  simp only [supportAll,mem_image,mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨h,h'⟩; exact ⟨k-1,by omega,by omega⟩
theorem entry_width (k : ℕ) (hk : k∈supportAll) : entryAt k<262144 := by
  have w : entryList.all (fun e => e<262144) = true := by decide +kernel
  have j : k-1<entryList.length := by
    rw [table_size]
    obtain ⟨h,h'⟩ := mem_support.mp hk
    omega
  unfold entryAt
  rw [List.getElem?_eq_getElem j]
  exact of_decide_eq_true (List.all_eq_true.mp w _ (List.getElem_mem j))
def PowersValid : Prop := ∀ k, 0<k → k≤3800 →
   2^((entryAt k % 262144)/4) ≤ k^4096 ∧ k^4096 < 2^((entryAt k % 262144)/4+1)
theorem actual_log_interval (power : PowersValid) (k : ℕ) (hk : k∈supportAll) :
    (logLow (entryAt k):ℝ) ≤ (LD:ℝ)*Real.log k ∧ (LD:ℝ)*Real.log k ≤ logHigh k (entryAt k) := by
  obtain ⟨hp,ht⟩ := mem_support.mp hk
  have f := power k hp ht
  rw [Nat.mod_eq_of_lt (entry_width _ hk)] at f
  have h := from_power k 4096 (entryAt k/4) hp f.1 f.2
  constructor
  · norm_num [logLow,Int.ofNat_eq_natCast] at h ⊢; exact h.1
  · by_cases h1 : k=1
    · subst k; simp [logHigh]
    · norm_num [logHigh,h1,Int.ofNat_eq_natCast] at h ⊢; exact h.2
theorem signed_low_eq (a l h : ℤ) (hl : l≤h) : signedLow a l h = min (a*l) (a*h) := by
  by_cases ha : 0≤a
  · simp [signedLow,ha,min_eq_left (mul_le_mul_of_nonneg_left hl ha)]
  · simp [signedLow,ha,min_eq_right (mul_le_mul_of_nonpos_left hl (le_of_not_ge ha))]
theorem signed_high_eq (a l h : ℤ) (hl : l≤h) : signedHigh a l h = max (a*l) (a*h) := by
  by_cases ha : 0≤a
  · simp [signedHigh,ha,max_eq_right (mul_le_mul_of_nonneg_left hl ha)]
  · simp [signedHigh,ha,max_eq_left (mul_le_mul_of_nonpos_left hl (le_of_not_ge ha))]
def Between (r : Row) (C : ℕ→ℝ) (D : ℕ) : Prop :=
  ∀ k∈supportAll, (val r k (entryAt k) r.al:ℝ) ≤ D*C k ∧ D*C k ≤ (val r k (entryAt k) r.ah:ℝ)
theorem scalar_moment (power : PowersValid) (r : Row) (C : ℕ→ℝ) (D : ℕ) (bet : Between r C D) :
    ((evaluate r).logLo:ℝ) ≤ (D*LD:ℕ)*(∑ k∈supportAll, C k*Real.log k/k) ∧
    (D*LD:ℕ)*(∑ k∈supportAll, C k*Real.log k/k) ≤ ((evaluate r).logHi:ℝ) := by
  let ll := fun k => logLow (entryAt k)
  let lh := fun k => logHigh k (entryAt k)
  let vl := fun k => val r k (entryAt k) r.al
  let vh := fun k => val r k (entryAt k) r.ah
  have rel (k : ℕ) (hk : k∈supportAll) : ll k ≤ lh k := by
    have b := actual_log_interval power k hk
    exact_mod_cast b.1.trans b.2
  have bl : (evaluate r).logLo = ∑ k∈supportAll, signedLow (vl k) (ll k) (lh k)/(k:ℤ) := by
    rw [actual_logLo]
    exact sum_congr rfl (fun k hk => by rw [signed_low_eq _ _ _ (rel k hk)]; rfl)
  have bh : (evaluate r).logHi = ∑ k∈supportAll, -((-signedHigh (vh k) (ll k) (lh k))/(k:ℤ)) := by
    rw [actual_logHi]
    exact sum_congr rfl (fun k hk => by rw [signed_high_eq _ _ _ (rel k hk)]; rfl)
  rw [bl,bh,Nat.cast_mul]
  exact real_interval supportAll C vl vh ll lh D LD (fun k hk => (mem_support.mp hk).1)
    bet (actual_log_interval power) (by norm_num)
theorem scalar_l1 (r : Row) (C : ℕ→ℝ) (D : ℕ) (bet : Between r C D) :
    (D:ℝ)*(∑ k∈supportAll, |C k|) ≤ (evaluate r).mass := by
  have m := actual_mass r
  have mc := congrArg (fun z : ℤ => (z:ℝ)) m
  push_cast at mc
  rw [mc,mul_sum]
  apply sum_le_sum
  intro k hk
  let v0 := val r k (entryAt k) r.al
  let v1 := val r k (entryAt k) r.ah
  let m := max v0.natAbs v1.natAbs
  have lo : -((m:ℕ):ℝ) ≤ (v0:ℝ) := by
    exact_mod_cast (show -(m:ℤ) ≤ v0 by
      have h : |v0|≤(m:ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_left v0.natAbs v1.natAbs
      exact (abs_le.mp h).1)
  have hi : (v1:ℝ) ≤ (m:ℝ) := by
    exact_mod_cast (show v1 ≤ (m:ℤ) by
      have h : |v1|≤(m:ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_right v0.natAbs v1.natAbs
      exact (abs_le.mp h).2)
  change (D:ℝ)*|C k| ≤ ((m:ℕ):ℝ)
  rw [← abs_of_nonneg (Nat.cast_nonneg D : (0:ℝ)≤D),← abs_mul,abs_le]
  exact ⟨lo.trans (bet k hk).1,(bet k hk).2.trans hi⟩
end FR7022ScalarTable
namespace FR7022SignedLog
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
end FR7022SignedLog
namespace FR7022ScalarTable
open Finset FR7022SignedLog
theorem ceil_bounds (x d : ℕ) (hd : 0<d) : x≤ceilN x d*d := by
  let z := x+d-1
  have m := Nat.mod_lt z hd
  have h := Nat.mod_add_div z d
  rw [mul_comm d] at h
  change x≤z/d*d
  dsimp only [z] at h m ⊢
  omega
theorem priced (x den : ℕ) (hd : 0<den) :
    (x:ℝ)/den ≤ (ceilN (W*x) den:ℝ)/W := by
  have dz : (0:ℝ)<den := by exact_mod_cast hd
  apply (div_le_div_iff₀ dz (by norm_num)).mpr
  rw [mul_comm (x:ℝ)]
  exact_mod_cast ceil_bounds (W*x) den hd
def mainPrice (r : Row) :=
  let s := evaluate r
  let den := (r.k1-r.k0)*1000*LD*r.q
  let φ : ℤ := r.phi
  ceilN (W*max (φ*s.logLo+den).natAbs (φ*s.logHi+den).natAbs) (r.phi*den)
def lossPrice (r : Row) :=
  ceilN (91*(evaluate r).mass*W) (((r.k1-r.k0)*1000)*(if r.q=1 then 10^10 else 10^16))
set_option maxRecDepth 65536 in
theorem actual_price (power : PowersValid) (r : Row) (C : ℕ→ℝ) (hq : 0<r.q) (hp : 0<r.phi)
    (hk : r.k0<r.k1) (bet : Between r C ((r.k1-r.k0)*1000)) :
    |(-(∑ k∈supportAll, C k*Real.log k/k))/(r.q:ℝ)-1/(r.phi:ℝ)| ≤ (mainPrice r:ℝ)/W := by
  let D := (r.k1-r.k0)*1000
  let Z := D*LD
  let M := ∑ k∈supportAll, C k*Real.log k/k
  let s := evaluate r
  let den := Z*r.q
  let cost := max (((r.phi:ℤ)*s.logLo+(den:ℕ)).natAbs) (((r.phi:ℤ)*s.logHi+(den:ℕ)).natAbs)
  have hD : 0<D := Nat.mul_pos (Nat.sub_pos_of_lt hk) (by decide)
  have hZ : 0<Z := Nat.mul_pos hD (by decide)
  have ds : (Z:ℝ)*r.q*r.phi = ((r.phi*den:ℕ):ℝ) := by dsimp only [den]; push_cast; ring
  have bound := normalized_error M Z r.q r.phi s.logLo s.logHi hZ hq hp (scalar_moment power r C D bet)
  change _ ≤ (cost:ℝ)/((Z:ℝ)*r.q*r.phi) at bound
  rw [ds] at bound
  exact bound.trans (priced cost (r.phi*den) (Nat.mul_pos hp (Nat.mul_pos hZ hq)))
theorem actual_loss (r : Row) (C : ℕ→ℝ) (hk : r.k0<r.k1)
    (bet : Between r C ((r.k1-r.k0)*1000)) :
    (∑ k∈supportAll, |C k|) * (91/(if r.q=1 then (10^10:ℝ) else 10^16)) ≤ (lossPrice r:ℝ)/W := by
  let D := (r.k1-r.k0)*1000
  let N : ℕ := if r.q=1 then 10^10 else 10^16
  have hD : 0<D := Nat.mul_pos (Nat.sub_pos_of_lt hk) (by decide)
  have hN : 0<N := by dsimp [N]; split <;> decide
  have hd : 0<(D:ℝ) := by exact_mod_cast hD
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have eqn : (if r.q=1 then (10^10:ℝ) else 10^16)=(N:ℝ) := by dsimp [N]; split <;> norm_num
  rw [eqn]
  have h := scalar_l1 r C D bet
  have p := priced (91*(evaluate r).mass) (D*N) (Nat.mul_pos hD hN)
  have l : (∑ k∈supportAll, |C k|)*(91/(N:ℝ)) ≤ ((91*(evaluate r).mass:ℕ):ℝ)/(D*N:ℕ) := by
    push_cast
    apply (le_div_iff₀ (mul_pos hd hn)).mpr
    field_simp
    nlinarith only [h]
  apply l.trans
  simpa only [lossPrice,D,N,mul_comm W] using p
end FR7022ScalarTable
namespace FR7022ScalarTable
def goodAt (k e : Nat) : Prop :=
  2^((e % 262144)/4) ≤ k^4096 ∧ k^4096 < 2^((e % 262144)/4+1)
def goodList (xs : List Nat) (k : Nat) : Prop :=
  ∀ i < xs.length, goodAt (k+i) ((xs[i]?).getD 0)
theorem unpack_len (n z : Nat) : (unpack n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [unpack,ih]
theorem goodDigits (n k z : Nat) (h : powerDigits n k z = true) : goodList (unpack n z) k := by
  induction n generalizing k z with
  | zero => simp [goodList,unpack]
  | succ n ih =>
    simp only [powerDigits] at h
    simp only [Bool.and_eq_true] at h
    have both := h
    intro i hi
    cases i with
    | zero => simpa [unpack,goodAt,Nat.mod_mod] using of_decide_eq_true both.1
    | succ j =>
      have hj : j < (unpack n (z >>> 18)).length := by simpa [unpack] using hi
      simpa [unpack,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih _ _ both.2 j hj
def goodChunks : List (Nat × Nat) → Nat → Prop
  | [], _ => True
  | c::cs, k => powerDigits c.1 k c.2 = true ∧ goodChunks cs (k+c.1)
theorem goodJoin (a b : List Nat) (k : Nat) (ha : goodList a k)
    (hb : goodList b (k+a.length)) : goodList (a++b) k := by
  intro i hi
  by_cases h : i < a.length
  · simpa [List.getElem?_append_left h] using ha i h
  · have hbi : i-a.length < b.length := by simp only [List.length_append] at hi; omega
    have heq : k + a.length + (i-a.length) = k+i := by omega
    simpa [List.getElem?_append_right (by omega : a.length ≤ i), heq] using hb _ hbi
theorem chunksSound (cs : List (Nat × Nat)) (k : Nat) (h : goodChunks cs k) :
    goodList (cs.flatMap (fun c => unpack c.1 c.2)) k := by
  induction cs generalizing k with
  | nil => simp [goodList]
  | cons c cs ih =>
    apply goodJoin
    · exact goodDigits _ _ _ h.1
    · rw [unpack_len]
      exact ih _ h.2
end FR7022ScalarTable
namespace FR7022ScalarTable
set_option maxRecDepth 32768 in
theorem tableChecks : goodChunks chunks 1 := ⟨tab0_powers,tab1_powers,tab2_powers,tab3_powers,tab4_powers,tab5_powers,tab6_powers,tab7_powers,tab8_powers,tab9_powers,tab10_powers,tab11_powers,tab12_powers,tab13_powers,tab14_powers,tab15_powers,tab16_powers,tab17_powers,tab18_powers,tab19_powers,tab20_powers,tab21_powers,tab22_powers,tab23_powers,tab24_powers,tab25_powers,tab26_powers,tab27_powers,tab28_powers,tab29_powers,tab30_powers,tab31_powers,tab32_powers,tab33_powers,tab34_powers,tab35_powers,tab36_powers,tab37_powers,tab38_powers,tab39_powers,tab40_powers,tab41_powers,tab42_powers,tab43_powers,tab44_powers,tab45_powers,tab46_powers,tab47_powers,tab48_powers,tab49_powers,tab50_powers,tab51_powers,tab52_powers,tab53_powers,tab54_powers,tab55_powers,tab56_powers,tab57_powers,tab58_powers,tab59_powers,True.intro⟩
set_option maxRecDepth 32768 in
theorem all_powers (k : Nat) (hk : 0<k) (hK : k≤3800) :
    goodAt k ((entryList[k-1]?).getD 0) := by
  have hs := chunksSound chunks 1 tableChecks
  have hlen : entryList.length=3800 := by decide +kernel
  have hi : k-1 < entryList.length := by omega
  have h := hs (k-1) hi
  simpa only [show 1+(k-1)=k by omega] using h
end FR7022ScalarTable
namespace FR7022ScalarTable
open Finset
theorem frozen_powers : PowersValid := by
  intro k hk hK
  exact all_powers k hk hK
def passPrices : List Row → Prop
  | [] => True
  | x::xs => (checkRow x=true ∧ x.k0=2508 ∧ x.k1=3800 ∧ 1<x.q ∧ x.phi=x.q.totient) ∧ passPrices xs
theorem prices_mem (rs : List Row) (hp : passPrices rs) (r : Row) (hr : r∈rs) :
    checkRow r=true ∧ r.k0=2508 ∧ r.k1=3800 ∧ 1<r.q ∧ r.phi=r.q.totient := by
  induction rs with
  | nil => simp at hr
  | cons x xs ih =>
    rcases List.mem_cons.mp hr with eq | rest
    · exact eq ▸ hp.1
    · exact ih hp.2 rest
private theorem extract_total (r : Row) (s : Sums) (hq : 1<r.q)
    (hc : rowPass r s = true) :
    ((report r s).2.2)*10000<96*W := by
  change (_ && decide (if r.q=1 then (report r s).2.2*25<W
      else (report r s).2.2*10000<96*W))=true at hc
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
  rwa [if_neg (show r.q≠1 by omega)] at h
private theorem total_formula (r : Row) (s : Sums) (hq : 1<r.q) :
    (report r s).2.2 =
    (let den := (r.k1-r.k0)*1000*LD*r.q
     ceilN (W*max (((r.phi:ℤ)*s.logLo+den).natAbs) (((r.phi:ℤ)*s.logHi+den).natAbs)) (r.phi*den)) +
    ceilN (91*s.mass*W) (((r.k1-r.k0)*1000)*(if r.q=1 then 10^10 else 10^16)) +
    ceilN (26*(r.finiteCost+r.tailCost)) 25 := by
  have hq' : r.q≠1 := by omega
  simp only [report,hq',ite_false,Int.ofNat_eq_natCast]
theorem combined_budget (r : Row) (hq : 1<r.q) (hc : checkRow r = true) :
    (mainPrice r+lossPrice r+ceilN (26*(r.finiteCost+r.tailCost)) 25)*10000 < 96*W := by
  have h := extract_total r (evaluate r) hq hc
  rw [total_formula r (evaluate r) hq] at h
  exact h
end FR7022ScalarTable
namespace FR7022ScalarTable
def pricedRows : List Row := [q2,q4,q6,q8,q10,q12,q14,q16,q18,q20,q22,q24,q26,q28,q30,q32,q34,q36,q38,q40,q42,q44,q46,q48,q50,q52,q53,q54,q55,q56,q57,q58,q59,q60,q61,q62,q63,q64,q65,q66,q67,q68,q69,q70,q71,q72,q73,q74,q75,q76,q77,q78,q79,q80,q81,q82,q83,q84,q85,q86,q87,q88,q89,q90,q91,q92,q93,q94,q95,q96,q97,q98,q99,q100,q101,q102,q103,q104,q105]
theorem q2_props : q2.k0=2508 ∧ q2.k1=3800 ∧ 1<q2.q ∧ q2.phi=q2.q.totient := by decide +kernel
theorem q4_props : q4.k0=2508 ∧ q4.k1=3800 ∧ 1<q4.q ∧ q4.phi=q4.q.totient := by decide +kernel
theorem q6_props : q6.k0=2508 ∧ q6.k1=3800 ∧ 1<q6.q ∧ q6.phi=q6.q.totient := by decide +kernel
theorem q8_props : q8.k0=2508 ∧ q8.k1=3800 ∧ 1<q8.q ∧ q8.phi=q8.q.totient := by decide +kernel
theorem q10_props : q10.k0=2508 ∧ q10.k1=3800 ∧ 1<q10.q ∧ q10.phi=q10.q.totient := by decide +kernel
theorem q12_props : q12.k0=2508 ∧ q12.k1=3800 ∧ 1<q12.q ∧ q12.phi=q12.q.totient := by decide +kernel
theorem q14_props : q14.k0=2508 ∧ q14.k1=3800 ∧ 1<q14.q ∧ q14.phi=q14.q.totient := by decide +kernel
theorem q16_props : q16.k0=2508 ∧ q16.k1=3800 ∧ 1<q16.q ∧ q16.phi=q16.q.totient := by decide +kernel
theorem q18_props : q18.k0=2508 ∧ q18.k1=3800 ∧ 1<q18.q ∧ q18.phi=q18.q.totient := by decide +kernel
theorem q20_props : q20.k0=2508 ∧ q20.k1=3800 ∧ 1<q20.q ∧ q20.phi=q20.q.totient := by decide +kernel
theorem q22_props : q22.k0=2508 ∧ q22.k1=3800 ∧ 1<q22.q ∧ q22.phi=q22.q.totient := by decide +kernel
theorem q24_props : q24.k0=2508 ∧ q24.k1=3800 ∧ 1<q24.q ∧ q24.phi=q24.q.totient := by decide +kernel
theorem q26_props : q26.k0=2508 ∧ q26.k1=3800 ∧ 1<q26.q ∧ q26.phi=q26.q.totient := by decide +kernel
theorem q28_props : q28.k0=2508 ∧ q28.k1=3800 ∧ 1<q28.q ∧ q28.phi=q28.q.totient := by decide +kernel
theorem q30_props : q30.k0=2508 ∧ q30.k1=3800 ∧ 1<q30.q ∧ q30.phi=q30.q.totient := by decide +kernel
theorem q32_props : q32.k0=2508 ∧ q32.k1=3800 ∧ 1<q32.q ∧ q32.phi=q32.q.totient := by decide +kernel
theorem q34_props : q34.k0=2508 ∧ q34.k1=3800 ∧ 1<q34.q ∧ q34.phi=q34.q.totient := by decide +kernel
theorem q36_props : q36.k0=2508 ∧ q36.k1=3800 ∧ 1<q36.q ∧ q36.phi=q36.q.totient := by decide +kernel
theorem q38_props : q38.k0=2508 ∧ q38.k1=3800 ∧ 1<q38.q ∧ q38.phi=q38.q.totient := by decide +kernel
theorem q40_props : q40.k0=2508 ∧ q40.k1=3800 ∧ 1<q40.q ∧ q40.phi=q40.q.totient := by decide +kernel
theorem q42_props : q42.k0=2508 ∧ q42.k1=3800 ∧ 1<q42.q ∧ q42.phi=q42.q.totient := by decide +kernel
theorem q44_props : q44.k0=2508 ∧ q44.k1=3800 ∧ 1<q44.q ∧ q44.phi=q44.q.totient := by decide +kernel
theorem q46_props : q46.k0=2508 ∧ q46.k1=3800 ∧ 1<q46.q ∧ q46.phi=q46.q.totient := by decide +kernel
theorem q48_props : q48.k0=2508 ∧ q48.k1=3800 ∧ 1<q48.q ∧ q48.phi=q48.q.totient := by decide +kernel
theorem q50_props : q50.k0=2508 ∧ q50.k1=3800 ∧ 1<q50.q ∧ q50.phi=q50.q.totient := by decide +kernel
theorem q52_props : q52.k0=2508 ∧ q52.k1=3800 ∧ 1<q52.q ∧ q52.phi=q52.q.totient := by decide +kernel
theorem q53_props : q53.k0=2508 ∧ q53.k1=3800 ∧ 1<q53.q ∧ q53.phi=q53.q.totient := by decide +kernel
theorem q54_props : q54.k0=2508 ∧ q54.k1=3800 ∧ 1<q54.q ∧ q54.phi=q54.q.totient := by decide +kernel
theorem q55_props : q55.k0=2508 ∧ q55.k1=3800 ∧ 1<q55.q ∧ q55.phi=q55.q.totient := by decide +kernel
theorem q56_props : q56.k0=2508 ∧ q56.k1=3800 ∧ 1<q56.q ∧ q56.phi=q56.q.totient := by decide +kernel
theorem q57_props : q57.k0=2508 ∧ q57.k1=3800 ∧ 1<q57.q ∧ q57.phi=q57.q.totient := by decide +kernel
theorem q58_props : q58.k0=2508 ∧ q58.k1=3800 ∧ 1<q58.q ∧ q58.phi=q58.q.totient := by decide +kernel
theorem q59_props : q59.k0=2508 ∧ q59.k1=3800 ∧ 1<q59.q ∧ q59.phi=q59.q.totient := by decide +kernel
theorem q60_props : q60.k0=2508 ∧ q60.k1=3800 ∧ 1<q60.q ∧ q60.phi=q60.q.totient := by decide +kernel
theorem q61_props : q61.k0=2508 ∧ q61.k1=3800 ∧ 1<q61.q ∧ q61.phi=q61.q.totient := by decide +kernel
theorem q62_props : q62.k0=2508 ∧ q62.k1=3800 ∧ 1<q62.q ∧ q62.phi=q62.q.totient := by decide +kernel
theorem q63_props : q63.k0=2508 ∧ q63.k1=3800 ∧ 1<q63.q ∧ q63.phi=q63.q.totient := by decide +kernel
theorem q64_props : q64.k0=2508 ∧ q64.k1=3800 ∧ 1<q64.q ∧ q64.phi=q64.q.totient := by decide +kernel
theorem q65_props : q65.k0=2508 ∧ q65.k1=3800 ∧ 1<q65.q ∧ q65.phi=q65.q.totient := by decide +kernel
theorem q66_props : q66.k0=2508 ∧ q66.k1=3800 ∧ 1<q66.q ∧ q66.phi=q66.q.totient := by decide +kernel
theorem q67_props : q67.k0=2508 ∧ q67.k1=3800 ∧ 1<q67.q ∧ q67.phi=q67.q.totient := by decide +kernel
theorem q68_props : q68.k0=2508 ∧ q68.k1=3800 ∧ 1<q68.q ∧ q68.phi=q68.q.totient := by decide +kernel
theorem q69_props : q69.k0=2508 ∧ q69.k1=3800 ∧ 1<q69.q ∧ q69.phi=q69.q.totient := by decide +kernel
theorem q70_props : q70.k0=2508 ∧ q70.k1=3800 ∧ 1<q70.q ∧ q70.phi=q70.q.totient := by decide +kernel
theorem q71_props : q71.k0=2508 ∧ q71.k1=3800 ∧ 1<q71.q ∧ q71.phi=q71.q.totient := by decide +kernel
theorem q72_props : q72.k0=2508 ∧ q72.k1=3800 ∧ 1<q72.q ∧ q72.phi=q72.q.totient := by decide +kernel
theorem q73_props : q73.k0=2508 ∧ q73.k1=3800 ∧ 1<q73.q ∧ q73.phi=q73.q.totient := by decide +kernel
theorem q74_props : q74.k0=2508 ∧ q74.k1=3800 ∧ 1<q74.q ∧ q74.phi=q74.q.totient := by decide +kernel
theorem q75_props : q75.k0=2508 ∧ q75.k1=3800 ∧ 1<q75.q ∧ q75.phi=q75.q.totient := by decide +kernel
theorem q76_props : q76.k0=2508 ∧ q76.k1=3800 ∧ 1<q76.q ∧ q76.phi=q76.q.totient := by decide +kernel
theorem q77_props : q77.k0=2508 ∧ q77.k1=3800 ∧ 1<q77.q ∧ q77.phi=q77.q.totient := by decide +kernel
theorem q78_props : q78.k0=2508 ∧ q78.k1=3800 ∧ 1<q78.q ∧ q78.phi=q78.q.totient := by decide +kernel
theorem q79_props : q79.k0=2508 ∧ q79.k1=3800 ∧ 1<q79.q ∧ q79.phi=q79.q.totient := by decide +kernel
theorem q80_props : q80.k0=2508 ∧ q80.k1=3800 ∧ 1<q80.q ∧ q80.phi=q80.q.totient := by decide +kernel
theorem q81_props : q81.k0=2508 ∧ q81.k1=3800 ∧ 1<q81.q ∧ q81.phi=q81.q.totient := by decide +kernel
theorem q82_props : q82.k0=2508 ∧ q82.k1=3800 ∧ 1<q82.q ∧ q82.phi=q82.q.totient := by decide +kernel
theorem q83_props : q83.k0=2508 ∧ q83.k1=3800 ∧ 1<q83.q ∧ q83.phi=q83.q.totient := by decide +kernel
theorem q84_props : q84.k0=2508 ∧ q84.k1=3800 ∧ 1<q84.q ∧ q84.phi=q84.q.totient := by decide +kernel
theorem q85_props : q85.k0=2508 ∧ q85.k1=3800 ∧ 1<q85.q ∧ q85.phi=q85.q.totient := by decide +kernel
theorem q86_props : q86.k0=2508 ∧ q86.k1=3800 ∧ 1<q86.q ∧ q86.phi=q86.q.totient := by decide +kernel
theorem q87_props : q87.k0=2508 ∧ q87.k1=3800 ∧ 1<q87.q ∧ q87.phi=q87.q.totient := by decide +kernel
theorem q88_props : q88.k0=2508 ∧ q88.k1=3800 ∧ 1<q88.q ∧ q88.phi=q88.q.totient := by decide +kernel
theorem q89_props : q89.k0=2508 ∧ q89.k1=3800 ∧ 1<q89.q ∧ q89.phi=q89.q.totient := by decide +kernel
theorem q90_props : q90.k0=2508 ∧ q90.k1=3800 ∧ 1<q90.q ∧ q90.phi=q90.q.totient := by decide +kernel
theorem q91_props : q91.k0=2508 ∧ q91.k1=3800 ∧ 1<q91.q ∧ q91.phi=q91.q.totient := by decide +kernel
theorem q92_props : q92.k0=2508 ∧ q92.k1=3800 ∧ 1<q92.q ∧ q92.phi=q92.q.totient := by decide +kernel
theorem q93_props : q93.k0=2508 ∧ q93.k1=3800 ∧ 1<q93.q ∧ q93.phi=q93.q.totient := by decide +kernel
theorem q94_props : q94.k0=2508 ∧ q94.k1=3800 ∧ 1<q94.q ∧ q94.phi=q94.q.totient := by decide +kernel
theorem q95_props : q95.k0=2508 ∧ q95.k1=3800 ∧ 1<q95.q ∧ q95.phi=q95.q.totient := by decide +kernel
theorem q96_props : q96.k0=2508 ∧ q96.k1=3800 ∧ 1<q96.q ∧ q96.phi=q96.q.totient := by decide +kernel
theorem q97_props : q97.k0=2508 ∧ q97.k1=3800 ∧ 1<q97.q ∧ q97.phi=q97.q.totient := by decide +kernel
theorem q98_props : q98.k0=2508 ∧ q98.k1=3800 ∧ 1<q98.q ∧ q98.phi=q98.q.totient := by decide +kernel
theorem q99_props : q99.k0=2508 ∧ q99.k1=3800 ∧ 1<q99.q ∧ q99.phi=q99.q.totient := by decide +kernel
theorem q100_props : q100.k0=2508 ∧ q100.k1=3800 ∧ 1<q100.q ∧ q100.phi=q100.q.totient := by decide +kernel
theorem q101_props : q101.k0=2508 ∧ q101.k1=3800 ∧ 1<q101.q ∧ q101.phi=q101.q.totient := by decide +kernel
theorem q102_props : q102.k0=2508 ∧ q102.k1=3800 ∧ 1<q102.q ∧ q102.phi=q102.q.totient := by decide +kernel
theorem q103_props : q103.k0=2508 ∧ q103.k1=3800 ∧ 1<q103.q ∧ q103.phi=q103.q.totient := by decide +kernel
theorem q104_props : q104.k0=2508 ∧ q104.k1=3800 ∧ 1<q104.q ∧ q104.phi=q104.q.totient := by decide +kernel
theorem q105_props : q105.k0=2508 ∧ q105.k1=3800 ∧ 1<q105.q ∧ q105.phi=q105.q.totient := by decide +kernel
theorem pricedRows_pass : passPrices pricedRows := ⟨⟨q2_cost,q2_props⟩,⟨q4_cost,q4_props⟩,⟨q6_cost,q6_props⟩,⟨q8_cost,q8_props⟩,⟨q10_cost,q10_props⟩,⟨q12_cost,q12_props⟩,⟨q14_cost,q14_props⟩,⟨q16_cost,q16_props⟩,⟨q18_cost,q18_props⟩,⟨q20_cost,q20_props⟩,⟨q22_cost,q22_props⟩,⟨q24_cost,q24_props⟩,⟨q26_cost,q26_props⟩,⟨q28_cost,q28_props⟩,⟨q30_cost,q30_props⟩,⟨q32_cost,q32_props⟩,⟨q34_cost,q34_props⟩,⟨q36_cost,q36_props⟩,⟨q38_cost,q38_props⟩,⟨q40_cost,q40_props⟩,⟨q42_cost,q42_props⟩,⟨q44_cost,q44_props⟩,⟨q46_cost,q46_props⟩,⟨q48_cost,q48_props⟩,⟨q50_cost,q50_props⟩,⟨q52_cost,q52_props⟩,⟨q53_cost,q53_props⟩,⟨q54_cost,q54_props⟩,⟨q55_cost,q55_props⟩,⟨q56_cost,q56_props⟩,⟨q57_cost,q57_props⟩,⟨q58_cost,q58_props⟩,⟨q59_cost,q59_props⟩,⟨q60_cost,q60_props⟩,⟨q61_cost,q61_props⟩,⟨q62_cost,q62_props⟩,⟨q63_cost,q63_props⟩,⟨q64_cost,q64_props⟩,⟨q65_cost,q65_props⟩,⟨q66_cost,q66_props⟩,⟨q67_cost,q67_props⟩,⟨q68_cost,q68_props⟩,⟨q69_cost,q69_props⟩,⟨q70_cost,q70_props⟩,⟨q71_cost,q71_props⟩,⟨q72_cost,q72_props⟩,⟨q73_cost,q73_props⟩,⟨q74_cost,q74_props⟩,⟨q75_cost,q75_props⟩,⟨q76_cost,q76_props⟩,⟨q77_cost,q77_props⟩,⟨q78_cost,q78_props⟩,⟨q79_cost,q79_props⟩,⟨q80_cost,q80_props⟩,⟨q81_cost,q81_props⟩,⟨q82_cost,q82_props⟩,⟨q83_cost,q83_props⟩,⟨q84_cost,q84_props⟩,⟨q85_cost,q85_props⟩,⟨q86_cost,q86_props⟩,⟨q87_cost,q87_props⟩,⟨q88_cost,q88_props⟩,⟨q89_cost,q89_props⟩,⟨q90_cost,q90_props⟩,⟨q91_cost,q91_props⟩,⟨q92_cost,q92_props⟩,⟨q93_cost,q93_props⟩,⟨q94_cost,q94_props⟩,⟨q95_cost,q95_props⟩,⟨q96_cost,q96_props⟩,⟨q97_cost,q97_props⟩,⟨q98_cost,q98_props⟩,⟨q99_cost,q99_props⟩,⟨q100_cost,q100_props⟩,⟨q101_cost,q101_props⟩,⟨q102_cost,q102_props⟩,⟨q103_cost,q103_props⟩,⟨q104_cost,q104_props⟩,⟨q105_cost,q105_props⟩,True.intro⟩
def massGood : List Row → Prop
  | [] => True
  | x::xs => (evaluate x).mass=expectedMass x.q ∧ massGood xs
theorem massGood_mem (rs : List Row) (h : massGood rs) (s : Row) (hs : s∈rs) :
    (evaluate s).mass=expectedMass s.q := by
  induction rs with
  | nil => simp at hs
  | cons x xs ih =>
    rcases List.mem_cons.mp hs with eq | rest
    · exact eq ▸ h.1
    · exact ih h.2 rest
theorem price_masses : massGood pricedRows := ⟨(split_mass _ q2_costmass).2,(split_mass _ q4_costmass).2,(split_mass _ q6_costmass).2,(split_mass _ q8_costmass).2,(split_mass _ q10_costmass).2,(split_mass _ q12_costmass).2,(split_mass _ q14_costmass).2,(split_mass _ q16_costmass).2,(split_mass _ q18_costmass).2,(split_mass _ q20_costmass).2,(split_mass _ q22_costmass).2,(split_mass _ q24_costmass).2,(split_mass _ q26_costmass).2,(split_mass _ q28_costmass).2,(split_mass _ q30_costmass).2,(split_mass _ q32_costmass).2,(split_mass _ q34_costmass).2,(split_mass _ q36_costmass).2,(split_mass _ q38_costmass).2,(split_mass _ q40_costmass).2,(split_mass _ q42_costmass).2,(split_mass _ q44_costmass).2,(split_mass _ q46_costmass).2,(split_mass _ q48_costmass).2,(split_mass _ q50_costmass).2,(split_mass _ q52_costmass).2,(split_mass _ q53_costmass).2,(split_mass _ q54_costmass).2,(split_mass _ q55_costmass).2,(split_mass _ q56_costmass).2,(split_mass _ q57_costmass).2,(split_mass _ q58_costmass).2,(split_mass _ q59_costmass).2,(split_mass _ q60_costmass).2,(split_mass _ q61_costmass).2,(split_mass _ q62_costmass).2,(split_mass _ q63_costmass).2,(split_mass _ q64_costmass).2,(split_mass _ q65_costmass).2,(split_mass _ q66_costmass).2,(split_mass _ q67_costmass).2,(split_mass _ q68_costmass).2,(split_mass _ q69_costmass).2,(split_mass _ q70_costmass).2,(split_mass _ q71_costmass).2,(split_mass _ q72_costmass).2,(split_mass _ q73_costmass).2,(split_mass _ q74_costmass).2,(split_mass _ q75_costmass).2,(split_mass _ q76_costmass).2,(split_mass _ q77_costmass).2,(split_mass _ q78_costmass).2,(split_mass _ q79_costmass).2,(split_mass _ q80_costmass).2,(split_mass _ q81_costmass).2,(split_mass _ q82_costmass).2,(split_mass _ q83_costmass).2,(split_mass _ q84_costmass).2,(split_mass _ q85_costmass).2,(split_mass _ q86_costmass).2,(split_mass _ q87_costmass).2,(split_mass _ q88_costmass).2,(split_mass _ q89_costmass).2,(split_mass _ q90_costmass).2,(split_mass _ q91_costmass).2,(split_mass _ q92_costmass).2,(split_mass _ q93_costmass).2,(split_mass _ q94_costmass).2,(split_mass _ q95_costmass).2,(split_mass _ q96_costmass).2,(split_mass _ q97_costmass).2,(split_mass _ q98_costmass).2,(split_mass _ q99_costmass).2,(split_mass _ q100_costmass).2,(split_mass _ q101_costmass).2,(split_mass _ q102_costmass).2,(split_mass _ q103_costmass).2,(split_mass _ q104_costmass).2,(split_mass _ q105_costmass).2,True.intro⟩
end FR7022ScalarTable
namespace FR7022ScalarTable
open Finset FR7022TwoStage
def signEntry (e : ℕ) : ℤ := if e % 4=1 then 1 else if e % 4=2 then -1 else 0
def signChecks : List ℕ → ℕ → Bool
  | [], _ => true
  | e::es,k => (signEntry e == FR7022Second.sign k) && signChecks es (k+1)
theorem signChecks_get (es : List ℕ) (k : ℕ) (h : signChecks es k = true) :
    ∀ i<es.length, signEntry ((es[i]?).getD 0) = FR7022Second.sign (k+i) := by
  induction es generalizing k with
  | nil => simp
  | cons e es ih =>
    simp only [signChecks,Bool.and_eq_true,beq_iff_eq] at h
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1) h.2 i (by simpa using hi)
theorem all_signs : signChecks entryList 1=true := by decide +kernel
theorem real_sign (k : ℕ) (hk : k∈supportAll) :
    signEntry (entryAt k) = FR7022Second.sign k := by
  obtain ⟨hp,hk'⟩ := mem_support.mp hk
  have hi : k-1<entryList.length := by rw [table_size]; omega
  simpa only [entryAt,show 1+(k-1)=k by omega] using signChecks_get _ 1 all_signs (k-1) hi
theorem support_filter (q : ℕ) : unitsDomain q = supportAll.filter (·.Coprime q) := by
  ext k
  simp only [unitsDomain,mem_filter,mem_Icc,mem_support]
  rfl
theorem ext_val (r : Row) (hk0 : r.k0=2508) (hk1 : r.k1=3800) (k : ℕ)
    (hk : k∈supportAll) (a : ℤ) : val r k (entryAt k) a =
      if k.Coprime r.q then coeff FR7022Second.sign a k else 0 := by
  have hK : k≤3800 := (mem_support.mp hk).2
  by_cases h : k.Coprime r.q
  · have hg : k.gcd r.q=1 := h
    have hh : inactive r k=false := by simp [inactive,hk1,hg,Nat.not_lt_of_ge hK]
    simp only [val,hh,Bool.false_eq_true,ite_false,hk0,hk1,ite_eq_left h,coeff,hK,and_true]
    change 1000*(signEntry (entryAt k)*_)+_ = _
    rw [real_sign k hk]
    by_cases ht : 2508<k <;> simp only [ht,ite_true,ite_false,mul_one,mul_zero,Int.ofNat_eq_natCast] <;> rfl
  · have hg : k.gcd r.q≠1 := h
    have hh : inactive r k=true := by simp [inactive,hg]
    simp [val,h,hh]
noncomputable def extend (q : ℕ) (c : ℕ→ℝ) (k : ℕ) : ℝ :=
  if k.Coprime q then c k else 0
theorem extend_between (r : Row) (hk0 : r.k0=2508) (hk1 : r.k1=3800) (c : ℕ→ℝ)
    (bet : ∀ k∈unitsDomain r.q,
      (coeff FR7022Second.sign r.al k:ℝ) ≤ 1292000*c k ∧ 1292000*c k ≤ (coeff FR7022Second.sign r.ah k:ℝ)) :
    Between r (extend r.q c) ((r.k1-r.k0)*1000) := by
  intro k hk
  rw [ext_val r hk0 hk1 k hk,ext_val r hk0 hk1 k hk,hk0,hk1]
  by_cases h : k.Coprime r.q
  · have hu : k∈unitsDomain r.q := by rw [support_filter]; exact mem_filter.mpr ⟨hk,h⟩
    simp only [extend,if_pos h]
    norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.cast_ofNat]
    exact bet k hu
  · simp only [extend,if_neg h,Int.cast_zero,mul_zero,le_refl,and_self]
theorem extend_sum (q : ℕ) (c : ℕ→ℝ) (F : ℕ→ℝ→ℝ) (zero : ∀ k, F k 0=0) :
    ∑ k∈supportAll, F k (extend q c k) = ∑ k∈unitsDomain q, F k (c k) := by
  rw [support_filter,sum_filter]
  apply sum_congr rfl
  intro k _
  unfold extend
  by_cases h : k.Coprime q
  · rw [if_pos h,if_pos h]
  · rw [if_neg h,if_neg h,zero]
theorem budget_for_field (s : Row) (pow : PowersValid) (chk : checkRow s=true)
    (h0 : s.k0=2508) (h1 : s.k1=3800) (hq : 1<s.q) (hφ : s.phi=s.q.totient) (c : ℕ→ℝ)
    (bet : ∀ k∈unitsDomain s.q,
      (coeff FR7022Second.sign s.al k:ℝ) ≤ 1292000*c k ∧ 1292000*c k ≤ (coeff FR7022Second.sign s.ah k:ℝ)) :
    (26:ℝ)/25*(((s.finiteCost+s.tailCost:ℕ):ℝ)/1000000000000) +
      |-(∑ k∈unitsDomain s.q,c k*Real.log k/k)/(s.q:ℝ)-1/(s.q.totient:ℝ)| +
      91*(∑ k∈unitsDomain s.q,|c k|)/((10^16:ℕ):ℝ) ≤ 96/10000 := by
  have hq0 : 0<s.q := by omega
  have hp : 0<s.phi := by rw [hφ]; exact Nat.totient_pos.mpr hq0
  have hk : s.k0<s.k1 := by omega
  have e := extend_between s h0 h1 c bet
  have l := actual_price pow s _ hq0 hp hk e
  have h := actual_loss s _ hk e
  have el := extend_sum s.q c (fun k x => x*Real.log k/k) (by simp)
  have ea := extend_sum s.q c (fun _ x => |x|) (by simp)
  try dsimp only at el ea
  rw [el,hφ] at l
  rw [ea,if_neg (show s.q≠1 by omega)] at h
  have conv := ceil_bounds (26*(s.finiteCost+s.tailCost)) 25 (by decide)
  have sum := combined_budget s hq chk
  have cv : (26:ℝ)*(s.finiteCost+s.tailCost)≤(ceilN (26*(s.finiteCost+s.tailCost)) 25:ℝ)*25 := by exact_mod_cast conv
  have su : ((mainPrice s:ℝ)+lossPrice s+ceilN (26*(s.finiteCost+s.tailCost)) 25)*10000<96*1000000000000 := by exact_mod_cast sum
  push_cast
  norm_num only [Nat.cast_ofNat,Nat.cast_pow] at h l ⊢
  linarith only [h,l,cv,su]
end FR7022ScalarTable
namespace FR7022FastTail
open Finset FR7022TwoStage FR7022ProgressionTail FR7022TailCoefficients FR7022CompactTail
open FR7022ScalarTable
private theorem passed_harmonic (s : FR7022ScalarTable.Row) (v : Sums) (h : rowPass s v=true) :
    v.hLo≤0 ∧ 0≤v.hHi := by
  change ((((decide (v.hLo≤0) && decide (0≤v.hHi)) && _) && _)=true) at h
  have ab := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  simpa only [Bool.and_eq_true,decide_eq_true_eq] using ab
theorem fold_units {M : Type*} [AddCommMonoid M] (s : FR7022ScalarTable.Row)
    (h0 : s.k0=2508) (h1 : s.k1=3800) (F : ℕ→ℤ→ℤ→M) (hF : ∀ k, F k 0 0=0) :
    ∑ k∈supportAll, F k (val s k (entryAt k) s.al) (val s k (entryAt k) s.ah) =
      ∑ k∈unitsDomain s.q, F k (coeff FR7022Second.sign s.al k) (coeff FR7022Second.sign s.ah k) := by
  rw [support_filter,sum_filter]
  apply sum_congr rfl
  intro k hk
  rw [ext_val s h0 h1 k hk,ext_val s h0 h1 k hk]
  by_cases h : k.Coprime s.q
  · rw [if_pos h,if_pos h,if_pos h]
  · rw [if_neg h,if_neg h,if_neg h,hF]
private theorem slope_test : ∀ q∈Icc 1 105, (2521:ℕ).Coprime q := by decide +kernel
theorem slope_pos (t : FR7022CompactTail.Row) (hq : t.q∈Icc 1 105) :
    0 < harmonicInteger t.S extraCoeff commonMultiple := by
  have hB : 0<commonMultiple := by decide
  have hk : 2521∈Icc 1 3800 := mem_Icc.mpr ⟨by decide,by decide⟩
  have hd := (common_dvd _ hk).2
  have hp := Nat.div_pos (Nat.le_of_dvd hB hd) (by decide : 0<2521)
  unfold harmonicInteger
  apply sum_pos'
  · intro k _
    have he : 0≤extraCoeff k := by unfold extraCoeff; split <;> decide
    exact mul_nonneg he (Int.natCast_nonneg _)
  · refine ⟨2521,mem_filter.mpr ⟨hk,slope_test _ hq⟩,?_⟩
    rw [show extraCoeff 2521=1 by decide,one_mul]
    exact_mod_cast hp
private theorem integral_bracket (b e a d : ℤ) (m : ℝ) (hm : 0<m)
    (h : (((1000*b+a*e:ℤ):ℝ)/m ≤ 0) ∧ (0 ≤ ((1000*b+d*e:ℤ):ℝ)/m)) :
    a*e ≤ -b*1000 ∧ -b*1000 ≤ d*e := by
  have lo := (div_le_iff₀ hm).mp h.1
  have hi := (le_div_iff₀ hm).mp h.2
  rw [zero_mul] at lo hi
  have i1 : 1000*b+a*e≤0 := by exact_mod_cast lo
  have i2 : 0≤1000*b+d*e := by exact_mod_cast hi
  constructor <;> linarith
private theorem max_mass (x y : ℤ) : max |x| |y| = (max x.natAbs y.natAbs : ℕ) := by
  simp only [Nat.cast_max,Int.natCast_natAbs]
theorem harmonic_and_mass (s : FR7022ScalarTable.Row) (t : FR7022CompactTail.Row)
    (h0 : s.k0=2508) (h1 : s.k1=3800) (hq : s.q=t.q) (hal : s.al=t.al) (hah : s.ah=t.ah)
    (ok : checkRow s=true) :
    (t.al * harmonicInteger t.S extraCoeff commonMultiple ≤ -harmonicInteger t.S baseCoeff commonMultiple*1000) ∧
    (-harmonicInteger t.S baseCoeff commonMultiple*1000 ≤ t.ah * harmonicInteger t.S extraCoeff commonMultiple) ∧
    endpointMass t.S baseCoeff extraCoeff t.al t.ah 1000 = ((evaluate s).mass:ℤ) := by
  let vl := fun k => val s k (entryAt k) s.al
  let vh := fun k => val s k (entryAt k) s.ah
  have hb := passed_harmonic s (evaluate s) ok
  have hl := hb.1
  have hh := hb.2
  rw [actual_hLo] at hl
  rw [actual_hHi] at hh
  have bracket := FR7022SignedLog.bracket_from_rounding supportAll vl vh W (by decide)
    (fun k hk => (mem_support.mp hk).1) (by simpa [vl,atomhLo,ceilZ,neg_mul] using hl) hh
  have elo := fold_units s h0 h1 (fun k x _ => (x:ℝ)/k) (by simp)
  have ehi := fold_units s h0 h1 (fun k _ y => (y:ℝ)/k) (by simp)
  dsimp only [vl,vh] at bracket
  try dsimp only at elo ehi
  rw [elo,ehi,hq,hal,hah] at bracket
  have hS : unitsDomain t.q=t.S := rfl
  rw [hS] at bracket
  have evalH (a : ℤ) :
      (∑ k∈t.S, (coeff FR7022Second.sign a k:ℝ)/k) =
       ((1000*harmonicInteger t.S baseCoeff commonMultiple+a*harmonicInteger t.S extraCoeff commonMultiple:ℤ):ℝ) / commonMultiple := by
    have matchC (k : ℕ) (hk : k∈t.S) :
        coeff FR7022Second.sign a k = endpointWeight baseCoeff extraCoeff a 1000 k := by
      exact finite_endpoint k (mem_Icc.mp (mem_filter.mp hk).1).2 a
    rw [sum_congr rfl (fun k hk => by rw [matchC k hk])]
    change harmonicCoeff t.S (endpointWeight baseCoeff extraCoeff a 1000) = _
    rw [harmonic_as_integer t.S _ _ (by decide) (fun k hk => common_dvd k (mem_filter.mp hk).1)]
    apply congrArg (fun z : ℤ => (z:ℝ)/(commonMultiple:ℝ))
    unfold harmonicInteger endpointWeight
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [evalH,evalH] at bracket
  have hp : (0:ℝ)<commonMultiple := by exact_mod_cast (show 0<commonMultiple by decide)
  have hbnd := integral_bracket _ _ _ _ _ hp bracket
  refine ⟨hbnd.1,hbnd.2,?_⟩
  have em := fold_units s h0 h1 (fun _ x y => max |x| |y|) (by simp)
  refine Eq.trans ?_ (actual_mass s).symm
  unfold endpointMass
  have atomEq : (∑ k∈supportAll, max |val s k (entryAt k) s.al| |val s k (entryAt k) s.ah|) =
      ∑ k∈supportAll, atommass s k (entryAt k) :=
    sum_congr rfl (fun k _ => max_mass _ _)
  refine Eq.trans ?_ (em.symm.trans atomEq)
  rw [hq,hal,hah,hS]
  apply sum_congr rfl
  intro k hk
  rw [finite_endpoint k (mem_Icc.mp (mem_filter.mp hk).1).2 _,finite_endpoint k (mem_Icc.mp (mem_filter.mp hk).1).2 _]
end FR7022FastTail
section
namespace FR7022SecondJumps
open FR7022TwoStage
def last := 368640
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
def fullEdges (r : Packed) : List (Nat × Nat) :=
  let e := increases r
  (r.params.B,r.params.globalMax-(e.map Prod.snd).sum)::e
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
def price (r : Packed) (z : Nat × Nat) : Nat :=
  ceilDiv (z.2*1000000000000) (r.params.scale*(z.1+1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
def check (r : Packed) : Bool :=
  decide (r.params.B=368639 ∧ 0<r.params.scale ∧
    (fullEdges r).all (fun p => decide (p.1 < last)) = true ∧
    ((fullEdges r).map Prod.snd).sum = r.params.globalMax ∧
    ((fullEdges r).map (price r)).sum ≤ r.params.finiteCost+r.params.tailCost)
end FR7022SecondJumps
namespace FR7022SecondJumps
open FR7022TwoStage
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq2 : check q2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq4 : check q4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq6 : check q6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq8 : check q8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq10 : check q10 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq12 : check q12 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq14 : check q14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq16 : check q16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq18 : check q18 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq20 : check q20 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq22 : check q22 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq24 : check q24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq26 : check q26 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq28 : check q28 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq30 : check q30 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq32 : check q32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq34 : check q34 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq36 : check q36 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq38 : check q38 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq40 : check q40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq42 : check q42 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq44 : check q44 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq46 : check q46 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq48 : check q48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq50 : check q50 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq52 : check q52 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq53 : check q53 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq54 : check q54 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq55 : check q55 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq56 : check q56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq57 : check q57 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq58 : check q58 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq59 : check q59 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq60 : check q60 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq61 : check q61 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq62 : check q62 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq63 : check q63 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq64 : check q64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq65 : check q65 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq66 : check q66 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq67 : check q67 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq68 : check q68 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq69 : check q69 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq70 : check q70 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq71 : check q71 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq72 : check q72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq73 : check q73 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq74 : check q74 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq75 : check q75 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq76 : check q76 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq77 : check q77 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq78 : check q78 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq79 : check q79 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq80 : check q80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq81 : check q81 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq82 : check q82 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq83 : check q83 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq84 : check q84 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq85 : check q85 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq86 : check q86 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq87 : check q87 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq88 : check q88 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq89 : check q89 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq90 : check q90 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq91 : check q91 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq92 : check q92 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq93 : check q93 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq94 : check q94 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq95 : check q95 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq96 : check q96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq97 : check q97 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq98 : check q98 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq99 : check q99 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq100 : check q100 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq101 : check q101 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq102 : check q102 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq103 : check q103 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq104 : check q104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hq105 : check q105 = true := by decide +kernel
end FR7022SecondJumps
namespace FR7022SecondJumps
open FR7022TwoStage
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
def pricedRows : List Packed → Prop
  | [] => True
  | r::rs => check r=true ∧ pricedRows rs
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem priced_of_mem {xs : List Packed} (pr : pricedRows xs) {r : Packed} (hr : r∈xs) : check r=true := by
  induction xs with
  | nil => simp at hr
  | cons s tail ih =>
    rcases List.mem_cons.mp hr with eq | ht
    · exact eq ▸ pr.1
    · exact ih pr.2 ht
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem checked_rows : pricedRows coveredRows := ⟨hq2,hq4,hq6,hq8,hq10,hq12,hq14,hq16,hq18,hq20,hq22,hq24,hq26,hq28,hq30,hq32,hq34,hq36,hq38,hq40,hq42,hq44,hq46,hq48,hq50,hq52,hq53,hq54,hq55,hq56,hq57,hq58,hq59,hq60,hq61,hq62,hq63,hq64,hq65,hq66,hq67,hq68,hq69,hq70,hq71,hq72,hq73,hq74,hq75,hq76,hq77,hq78,hq79,hq80,hq81,hq82,hq83,hq84,hq85,hq86,hq87,hq88,hq89,hq90,hq91,hq92,hq93,hq94,hq95,hq96,hq97,hq98,hq99,hq100,hq101,hq102,hq103,hq104,hq105,True.intro⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem registered : (List.range 106).all (fun q =>
    !(decide (1≤q ∧ (q % 2=0 ∨ 51<q))) || coveredRows.any (fun r => r.params.q==q)) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem exists_row (q : Nat) (hq : 1≤q) (hQ : q≤105) (ha : q % 2=0 ∨ 51<q) :
    ∃ r∈coveredRows, r.params.q=q := by
  have h := List.all_eq_true.mp registered q (List.mem_range.mpr (by omega))
  have h' : coveredRows.any (fun r => r.params.q==q)=true := by simpa [hq,ha] using h
  obtain ⟨r,hr,eq⟩ := List.any_eq_true.mp h'
  exact ⟨r,hr,beq_iff_eq.mp eq⟩
end FR7022SecondJumps
namespace FR7022SecondJumps
open Finset FR7022TwoStage FR7022Lane
def thresholds : Finset ℕ := Icc 1 last
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
noncomputable def weights (D : ℕ) (xs : List (ℕ×ℕ)) (t : ℕ) : ℝ :=
  match xs with
  | [] => 0
  | p::rest => (if p.1+1=t then (p.2:ℝ)/D else 0)+weights D rest t
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem weight_nonneg (D : ℕ) (xs : List (ℕ×ℕ)) (t : ℕ) : 0≤weights D xs t := by
  induction xs with
  | nil => simp [weights]
  | cons p tail ih =>
    simp only [weights]
    exact add_nonneg (by split <;> positivity) ih
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem full_value (xs : List (ℕ×ℕ)) (i : ℕ) (h : ∀ p∈xs, p.1 ≤ i) :
    fromRises xs i = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    change ray p.1 p.2 i + fromRises rest i = p.2+(rest.map Prod.snd).sum
    simp only [ray,ite_eq_left (h p (by simp)),ih (fun z hz => h z (by simp [hz]))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem he (r : Packed) (qc : check r = true) (err : ℕ → ℝ)
    (finite : ∀ u, 0<u → u≤r.params.B → err u≤(fromRises (increases r) (u-1):ℝ)/r.params.scale)
    (tail : ∀ u, r.params.B<u → err u≤(r.params.globalMax:ℝ)/r.params.scale)
    (u : ℕ) (hu : 0<u) : err u ≤ ∑ t ∈ thresholds, if t≤u then weights r.params.scale (fullEdges r) t else 0 := by
  obtain ⟨hB,_,hb,hpeak,_⟩ := of_decide_eq_true qc
  have bounds : ∀ p∈fullEdges r, p.1<last := by simpa only [List.all_eq_true,decide_eq_true_eq] using hb
  rw [realized _ _ u hu bounds]
  by_cases h:u≤r.params.B
  · have before : ¬ r.params.B≤u-1 := by omega
    simpa [fullEdges,fromRises,ray,before] using finite u hu h
  · have hh : ∀ p∈fullEdges r, p.1≤u-1 := by
      intro p hp
      have hz := bounds p hp
      unfold last at hz
      omega
    rw [full_value _ _ hh,hpeak]
    exact tail u (by omega)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem priced (r : Packed) (xs : List (ℕ×ℕ)) (hD : 0<r.params.scale) :
    (xs.map (fun p => (p.2:ℝ)/r.params.scale * ((p.1+1:ℕ):ℝ)⁻¹)).sum ≤
      (((xs.map (price r)).sum:ℕ):ℝ)/1000000000000 := by
  induction xs with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div] at ih ⊢
    apply add_le_add _ ih
    simpa only [price,FR7022TwoStage.ceilDiv,FR7022BlockJumps.ceilRatio,Nat.cast_add,Nat.cast_ofNat,←div_eq_mul_inv] using
      FR7022BlockJumps.per_jump_cost p.2 1000000000000 r.params.scale (p.1+1)
        (by decide) hD (by omega)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem hsum (r : Packed) (qc : check r = true) :
    (∑ t ∈ thresholds, weights r.params.scale (fullEdges r) t/t) ≤
       (((r.params.finiteCost+r.params.tailCost:ℕ):ℝ)/1000000000000) := by
  obtain ⟨_,hD,hb,_,hc⟩ := of_decide_eq_true qc
  have bounds : ∀ p∈fullEdges r, p.1<last := by simpa only [List.all_eq_true,decide_eq_true_eq] using hb
  calc
    _ = ((fullEdges r).map (fun p => (p.2:ℝ)/r.params.scale * ((p.1+1:ℕ):ℝ)⁻¹)).sum := by
      simpa only [div_eq_mul_inv] using unroll r.params.scale (fullEdges r) (fun t => (t:ℝ)⁻¹) bounds
    _ ≤ _ := (priced r (fullEdges r) hD).trans (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by norm_num))
end FR7022SecondJumps
namespace FR7022SecondJumps
open Finset FR7022TwoStage FR7022TwoStageBridge FR7022ProgressionTail
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem row (r : Packed) (qc : check r=true) (S : Finset ℕ) (A : ArithmeticFunction ℝ)
    (hs : ∀ k∉S, A k=0) (hb : ∀ k∈S, 0<k ∧ k≤10^16)
    (hc : ∀ k∈S, k.Coprime r.params.q) (hz : ∑ k∈S,A k/k=0)
    (finite : ∀ a u : ℕ, a.Coprime r.params.q → 0<u → u≤r.params.B →
      |G S A r.params.q a u - (if a % r.params.q=1 % r.params.q then (1:ℝ) else 0)| ≤
        (FR7022Lane.fromRises (increases r) (u-1):ℝ)/r.params.scale)
    (tail : ∀ a u : ℕ, a.Coprime r.params.q → r.params.B<u →
      |G S A r.params.q a u - (if a % r.params.q=1 % r.params.q then (1:ℝ) else 0)| ≤
        (r.params.globalMax:ℝ)/r.params.scale)
    (scalar : 26/25*(((r.params.finiteCost+r.params.tailCost:ℕ):ℝ)/1000000000000) +
      |-(∑ k∈S,A k*Real.log k/k)/(r.params.q:ℝ)-1/(r.params.q.totient:ℝ)| +
      91*(∑ k∈S,|A k|)/((10^16:ℕ):ℝ) ≤ 96/10000) :
    Nonempty (Row r.params.q (10^16) 368640 (26/25) (96/10000)) := by
  refine ⟨⟨S,A,hs,hb,hc,hz,thresholds,weights r.params.scale (fullEdges r),
    (fun t _ => weight_nonneg _ _ t),?_,?_,?_⟩⟩
  · intro t ht
    exact mem_Icc.mp ht
  · intro a u hu ha
    exact he r qc _ (fun i hi hl => finite a i ha hi hl) (fun i hi => tail a i ha hi) u hu
  · linarith only [hsum r qc,scalar]
end FR7022SecondJumps
namespace FR7022SecondJumps
open Finset FR7022TwoStage FR7022TwoStageBridge FR7022ProgressionTail
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem of_field (r : Packed) (qc : check r=true) (S : Finset ℕ) (c : ℕ → ℝ)
    (hS : ∀ k∈S, 0<k ∧ k≤10^16) (hc : ∀ k∈S, k.Coprime r.params.q)
    (hz : ∑ k∈S,c k/k=0)
    (finite : ∀ a u : ℕ, a.Coprime r.params.q → 0<u → u≤r.params.B →
      |G S c r.params.q a u - (if a % r.params.q=1 % r.params.q then (1:ℝ) else 0)| ≤
        (FR7022Lane.fromRises (increases r) (u-1):ℝ)/r.params.scale)
    (tail : ∀ a u : ℕ, a.Coprime r.params.q →
      |G S c r.params.q a u - (if a % r.params.q=1 % r.params.q then (1:ℝ) else 0)| ≤
        (r.params.globalMax:ℝ)/r.params.scale)
    (scalar : 26/25*(((r.params.finiteCost+r.params.tailCost:ℕ):ℝ)/1000000000000) +
      |-(∑ k∈S,c k*Real.log k/k)/(r.params.q:ℝ)-1/(r.params.q.totient:ℝ)| +
      91*(∑ k∈S,|c k|)/((10^16:ℕ):ℝ) ≤ 96/10000) :
    Nonempty (Row r.params.q (10^16) 368640 (26/25) (96/10000)) := by
  have h0 : 0∉S := fun h => (Nat.lt_irrefl 0) (hS 0 h).1
  let A : ArithmeticFunction ℝ := ⟨fun k => if k∈S then c k else 0,by simp [h0]⟩
  have eq (k : ℕ) (hk : k∈S) : A k = c k := by
    change (if k∈S then c k else 0)=_
    rw [ite_eq_left hk]
  have geq (a u : ℕ) : G S A r.params.q a u = G S c r.params.q a u := by
    unfold G
    exact sum_congr rfl fun k hk => by rw [eq k hk]
  have slope : (∑ k∈S,A k/k)=∑ k∈S,c k/k := sum_congr rfl fun k hk => by rw [eq k hk]
  have moment : (∑ k∈S,A k*Real.log k/k)=∑ k∈S,c k*Real.log k/k :=
    sum_congr rfl fun k hk => by rw [eq k hk]
  have mass : (∑ k∈S,|A k|)=∑ k∈S,|c k| := sum_congr rfl fun k hk => by rw [eq k hk]
  refine row r qc S A ?_ hS hc (slope.trans hz) ?_ ?_ ?_
  · intro k hk
    change (if k∈S then c k else 0)=0
    rw [ite_eq_right hk]
  · intro a u ha hu hB
    rw [geq]
    exact finite a u ha hu hB
  · intro a u ha _
    rw [geq]
    exact tail a u ha
  · rw [moment,mass]
    exact scalar
end FR7022SecondJumps
namespace FR7022SecondJumps
open Finset FR7022TwoStage FR7022TwoStageBridge
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem frozen_of_covered (rows : ∀ r∈coveredRows,
    Nonempty (Row r.params.q (10^16) 368640 (26/25) (96/10000))) :
    ∀ q a n : ℕ, 1≤q → q≤105 → a.Coprime q → 10^16≤n →
      (n:ℝ)<Real.exp (Real.exp (19/5)) →
      |(∑ k ∈ (range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) -
       (n:ℝ)/q.totient| ≤ (n:ℝ)/100 := by
  classical
  apply FR7022TwoStageBridge.frozen_of_two_stages FR7022OrdinaryStage.first_row.some
  intro q hq hQ ha
  have active : q % 2=0 ∨ 51<q := ha.imp (fun ⟨k,hk⟩ => by omega) id
  have hex := exists_row q hq hQ active
  let r := Classical.choose hex
  have spec := Classical.choose_spec hex
  have h : Nonempty (Row q (10^16) 368640 (26/25) (96/10000)) := by
    rw [← spec.2]
    exact rows r spec.1
  exact h.some
end FR7022SecondJumps
end
namespace FR7022Join
open FR7022TwoStage
structure Agree (p : Packed) (s : FR7022ScalarTable.Row) (t : FR7022CompactTail.Row) : Prop where
  mass : FR7022ScalarTable.expectedMass s.q=t.mass
  qBounds : t.q∈Finset.Icc 1 105
  qScalar : s.q=p.params.q
  qTail : t.q=p.params.q
  k0 : s.k0=2508
  k1 : s.k1=3800
  scale : p.params.scale=1292000
  lowScalar : s.al=p.params.alphaLo
  highScalar : s.ah=p.params.alphaHi
  lowTail : t.al=p.params.alphaLo
  highTail : t.ah=p.params.alphaHi
  cap : t.budget=p.params.globalMax
  finiteCost : s.finiteCost=p.params.finiteCost
  tailCost : s.tailCost=p.params.tailCost
def aligned : List Packed → List FR7022ScalarTable.Row → List FR7022CompactTail.Row → Prop
  | [],[],[] => True
  | p::ps,s::ss,t::ts => Agree p s t ∧ aligned ps ss ts
  | _,_,_ => False
theorem aligned_exists (ps : List Packed) (ss : List FR7022ScalarTable.Row)
    (ts : List FR7022CompactTail.Row) (a : aligned ps ss ts) (p : Packed) (hp : p∈ps) :
    ∃ s∈ss, ∃ t∈ts, Agree p s t := by
  induction ps generalizing ss ts with
  | nil => simp at hp
  | cons x xs ih =>
    cases ss with
    | nil => exact False.elim a
    | cons s ss =>
      cases ts with
      | nil => exact False.elim a
      | cons t ts =>
        rcases List.mem_cons.mp hp with h | h
        · subst p; exact ⟨s,List.mem_cons_self,t,List.mem_cons_self,a.1⟩
        · obtain ⟨s',hs,t',ht,ok⟩ := ih ss ts a.2 h
          exact ⟨s',List.mem_cons_of_mem _ hs,t',List.mem_cons_of_mem _ ht,ok⟩
end FR7022Join
namespace FR7022Join
open FR7022TwoStage
theorem matched2 : Agree q2 FR7022ScalarTable.q2 FR7022CompactData.r2 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched4 : Agree q4 FR7022ScalarTable.q4 FR7022CompactData.r4 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched6 : Agree q6 FR7022ScalarTable.q6 FR7022CompactData.r6 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched8 : Agree q8 FR7022ScalarTable.q8 FR7022CompactData.r8 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched10 : Agree q10 FR7022ScalarTable.q10 FR7022CompactData.r10 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched12 : Agree q12 FR7022ScalarTable.q12 FR7022CompactData.r12 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched14 : Agree q14 FR7022ScalarTable.q14 FR7022CompactData.r14 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched16 : Agree q16 FR7022ScalarTable.q16 FR7022CompactData.r16 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched18 : Agree q18 FR7022ScalarTable.q18 FR7022CompactData.r18 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched20 : Agree q20 FR7022ScalarTable.q20 FR7022CompactData.r20 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched22 : Agree q22 FR7022ScalarTable.q22 FR7022CompactData.r22 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched24 : Agree q24 FR7022ScalarTable.q24 FR7022CompactData.r24 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched26 : Agree q26 FR7022ScalarTable.q26 FR7022CompactData.r26 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched28 : Agree q28 FR7022ScalarTable.q28 FR7022CompactData.r28 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched30 : Agree q30 FR7022ScalarTable.q30 FR7022CompactData.r30 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched32 : Agree q32 FR7022ScalarTable.q32 FR7022CompactData.r32 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched34 : Agree q34 FR7022ScalarTable.q34 FR7022CompactData.r34 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched36 : Agree q36 FR7022ScalarTable.q36 FR7022CompactData.r36 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched38 : Agree q38 FR7022ScalarTable.q38 FR7022CompactData.r38 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched40 : Agree q40 FR7022ScalarTable.q40 FR7022CompactData.r40 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched42 : Agree q42 FR7022ScalarTable.q42 FR7022CompactData.r42 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched44 : Agree q44 FR7022ScalarTable.q44 FR7022CompactData.r44 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched46 : Agree q46 FR7022ScalarTable.q46 FR7022CompactData.r46 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched48 : Agree q48 FR7022ScalarTable.q48 FR7022CompactData.r48 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched50 : Agree q50 FR7022ScalarTable.q50 FR7022CompactData.r50 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched52 : Agree q52 FR7022ScalarTable.q52 FR7022CompactData.r52 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched53 : Agree q53 FR7022ScalarTable.q53 FR7022CompactData.r53 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched54 : Agree q54 FR7022ScalarTable.q54 FR7022CompactData.r54 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched55 : Agree q55 FR7022ScalarTable.q55 FR7022CompactData.r55 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched56 : Agree q56 FR7022ScalarTable.q56 FR7022CompactData.r56 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched57 : Agree q57 FR7022ScalarTable.q57 FR7022CompactData.r57 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched58 : Agree q58 FR7022ScalarTable.q58 FR7022CompactData.r58 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched59 : Agree q59 FR7022ScalarTable.q59 FR7022CompactData.r59 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched60 : Agree q60 FR7022ScalarTable.q60 FR7022CompactData.r60 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched61 : Agree q61 FR7022ScalarTable.q61 FR7022CompactData.r61 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched62 : Agree q62 FR7022ScalarTable.q62 FR7022CompactData.r62 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched63 : Agree q63 FR7022ScalarTable.q63 FR7022CompactData.r63 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched64 : Agree q64 FR7022ScalarTable.q64 FR7022CompactData.r64 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched65 : Agree q65 FR7022ScalarTable.q65 FR7022CompactData.r65 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched66 : Agree q66 FR7022ScalarTable.q66 FR7022CompactData.r66 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched67 : Agree q67 FR7022ScalarTable.q67 FR7022CompactData.r67 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched68 : Agree q68 FR7022ScalarTable.q68 FR7022CompactData.r68 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched69 : Agree q69 FR7022ScalarTable.q69 FR7022CompactData.r69 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched70 : Agree q70 FR7022ScalarTable.q70 FR7022CompactData.r70 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched71 : Agree q71 FR7022ScalarTable.q71 FR7022CompactData.r71 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched72 : Agree q72 FR7022ScalarTable.q72 FR7022CompactData.r72 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched73 : Agree q73 FR7022ScalarTable.q73 FR7022CompactData.r73 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched74 : Agree q74 FR7022ScalarTable.q74 FR7022CompactData.r74 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched75 : Agree q75 FR7022ScalarTable.q75 FR7022CompactData.r75 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched76 : Agree q76 FR7022ScalarTable.q76 FR7022CompactData.r76 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched77 : Agree q77 FR7022ScalarTable.q77 FR7022CompactData.r77 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched78 : Agree q78 FR7022ScalarTable.q78 FR7022CompactData.r78 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched79 : Agree q79 FR7022ScalarTable.q79 FR7022CompactData.r79 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched80 : Agree q80 FR7022ScalarTable.q80 FR7022CompactData.r80 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched81 : Agree q81 FR7022ScalarTable.q81 FR7022CompactData.r81 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched82 : Agree q82 FR7022ScalarTable.q82 FR7022CompactData.r82 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched83 : Agree q83 FR7022ScalarTable.q83 FR7022CompactData.r83 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched84 : Agree q84 FR7022ScalarTable.q84 FR7022CompactData.r84 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched85 : Agree q85 FR7022ScalarTable.q85 FR7022CompactData.r85 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched86 : Agree q86 FR7022ScalarTable.q86 FR7022CompactData.r86 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched87 : Agree q87 FR7022ScalarTable.q87 FR7022CompactData.r87 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched88 : Agree q88 FR7022ScalarTable.q88 FR7022CompactData.r88 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched89 : Agree q89 FR7022ScalarTable.q89 FR7022CompactData.r89 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched90 : Agree q90 FR7022ScalarTable.q90 FR7022CompactData.r90 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched91 : Agree q91 FR7022ScalarTable.q91 FR7022CompactData.r91 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched92 : Agree q92 FR7022ScalarTable.q92 FR7022CompactData.r92 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched93 : Agree q93 FR7022ScalarTable.q93 FR7022CompactData.r93 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched94 : Agree q94 FR7022ScalarTable.q94 FR7022CompactData.r94 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched95 : Agree q95 FR7022ScalarTable.q95 FR7022CompactData.r95 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched96 : Agree q96 FR7022ScalarTable.q96 FR7022CompactData.r96 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched97 : Agree q97 FR7022ScalarTable.q97 FR7022CompactData.r97 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched98 : Agree q98 FR7022ScalarTable.q98 FR7022CompactData.r98 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched99 : Agree q99 FR7022ScalarTable.q99 FR7022CompactData.r99 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched100 : Agree q100 FR7022ScalarTable.q100 FR7022CompactData.r100 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched101 : Agree q101 FR7022ScalarTable.q101 FR7022CompactData.r101 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched102 : Agree q102 FR7022ScalarTable.q102 FR7022CompactData.r102 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched103 : Agree q103 FR7022ScalarTable.q103 FR7022CompactData.r103 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched104 : Agree q104 FR7022ScalarTable.q104 FR7022CompactData.r104 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem matched105 : Agree q105 FR7022ScalarTable.q105 FR7022CompactData.r105 := by constructor <;> first | rfl | exact Finset.mem_Icc.mpr ⟨by decide,by decide⟩
theorem all_aligned : aligned coveredRows FR7022ScalarTable.pricedRows FR7022CompactData.rows := ⟨matched2,matched4,matched6,matched8,matched10,matched12,matched14,matched16,matched18,matched20,matched22,matched24,matched26,matched28,matched30,matched32,matched34,matched36,matched38,matched40,matched42,matched44,matched46,matched48,matched50,matched52,matched53,matched54,matched55,matched56,matched57,matched58,matched59,matched60,matched61,matched62,matched63,matched64,matched65,matched66,matched67,matched68,matched69,matched70,matched71,matched72,matched73,matched74,matched75,matched76,matched77,matched78,matched79,matched80,matched81,matched82,matched83,matched84,matched85,matched86,matched87,matched88,matched89,matched90,matched91,matched92,matched93,matched94,matched95,matched96,matched97,matched98,matched99,matched100,matched101,matched102,matched103,matched104,matched105,True.intro⟩
end FR7022Join
namespace FR7022Join
open Finset FR7022TwoStage FR7022ProgressionTail
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem complete_row (p : Packed) (hp : p∈coveredRows) :
    Nonempty (FR7022TwoStageBridge.Row p.params.q (10^16) 368640 (26/25) (96/10000)) := by
  obtain ⟨s,hs,t,ht,H⟩ := aligned_exists _ _ _ all_aligned p hp
  obtain ⟨check,k0,k1,hq,hφ⟩ := FR7022ScalarTable.prices_mem _ FR7022ScalarTable.pricedRows_pass s hs
  have ends := FR7022FastTail.harmonic_and_mass s t k0 k1
    (H.qScalar.trans H.qTail.symm) (H.lowScalar.trans H.lowTail.symm)
    (H.highScalar.trans H.highTail.symm) check
  have mass := FR7022ScalarTable.massGood_mem _ FR7022ScalarTable.price_masses s hs
  have eqm : (FR7022ScalarTable.evaluate s).mass=t.mass := mass.trans H.mass
  have ct := FR7022CompactData.all_certified_of_scalars t ht
    ⟨FR7022FastTail.slope_pos t H.qBounds, ends.1, ends.2.1,
      ends.2.2.trans (congrArg (fun n : ℕ => (n:ℤ)) eqm)⟩
  have setEq : t.S = unitsDomain p.params.q := by
    rw [←H.qTail]
    rfl
  have pp := all_pairs p hp
  have hscale : 0<p.params.scale := by rw [H.scale]; decide
  have coeffBounds : ∀ k∈unitsDomain p.params.q,
      (coeff FR7022Second.sign p.params.alphaLo k:ℝ)≤1292000*t.c k ∧
      1292000*t.c k≤(coeff FR7022Second.sign p.params.alphaHi k:ℝ) := by
    intro k hk
    rw [←H.lowTail,←H.highTail]
    exact FR7022CompactTail.between t ct k (by simpa only [H.qTail] using hk)
  apply FR7022SecondJumps.of_field p (FR7022SecondJumps.priced_of_mem FR7022SecondJumps.checked_rows hp)
    (unitsDomain p.params.q) t.c
  · intro k hk
    have h := mem_Icc.mp (mem_filter.mp hk).1
    exact ⟨h.1,by omega⟩
  · intro k hk; exact (mem_filter.mp hk).2
  · rw [←H.qTail]
    exact FR7022CompactTail.cancellation t ct
  · intro a u ha hu hB
    apply finite_real p FR7022Second.sign t.c hscale pp.1 pp.2 _ u a hu hB ha
    rw [H.scale]
    exact coeffBounds
  · intro a u ha
    have e := FR7022CompactTail.infinite_tail t ct a u (by simpa only [H.qTail] using ha)
    rw [setEq,H.qTail,H.cap] at e
    simpa only [H.scale,Nat.cast_ofNat] using e
  · have b := FR7022ScalarTable.budget_for_field s FR7022ScalarTable.frozen_powers check k0 k1 hq hφ t.c
    rw [H.qScalar,H.finiteCost,H.tailCost,H.lowScalar,H.highScalar] at b
    exact b coeffBounds
end FR7022Join
theorem PEqualNP.Outside.L_goldbach_finite_fixed_progression_unit_error :
  ∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/100 :=
  FR7022SecondJumps.frozen_of_covered FR7022Join.complete_row
