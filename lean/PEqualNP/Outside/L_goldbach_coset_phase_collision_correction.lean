import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Order.Interval.Finset.Nat

private theorem geom_root (L : ℕ) (y : ℂ) (hy : y^L = 1) :
    ∑ j ∈ Finset.range L, y^j = if y = 1 then (L:ℂ) else 0 := by
  by_cases h : y = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hy, sub_self, zero_div]

private theorem conj_root (L : ℕ) (hL : 0 < L) (z : ℂ) (hz : IsPrimitiveRoot z L) :
    (starRingEnd ℂ) z = z⁻¹ := by
  have h1 : ‖z‖ ^ L = 1 := by rw [← norm_pow, hz.pow_eq_one, norm_one]
  have h2 : ‖z‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg z) hL.ne').1 h1
  have h3 : Complex.normSq z = 1 := by rw [← Complex.sq_norm, h2]; norm_num
  rw [Complex.inv_def, h3]
  simp

private theorem cross_one (L : ℕ) (z : ℂ) (hz : IsPrimitiveRoot z L) (r r' : ℕ)
    (hr : r < L) (hr' : r' < L) :
    ∑ j ∈ Finset.range L, (z^j)^r * ((z^j)⁻¹)^r' = if r = r' then (L:ℂ) else 0 := by
  have hzL : z^L = 1 := hz.pow_eq_one
  have hz0 : z ≠ 0 := hz.ne_zero (by omega)
  have e : ∀ j, (z^j)^r * ((z^j)⁻¹)^r' = (z^r * (z^r')⁻¹)^j := fun j => by
    rw [inv_pow, pow_right_comm z j r, pow_right_comm z j r', mul_pow, inv_pow]
  have hy : (z^r * (z^r')⁻¹)^L = 1 := by
    rw [mul_pow, inv_pow, pow_right_comm z r L, pow_right_comm z r' L, hzL]
    simp
  simp_rw [e]
  rw [geom_root L _ hy]
  have hne : z^r' ≠ 0 := pow_ne_zero _ hz0
  have : z^r * (z^r')⁻¹ = 1 ↔ r = r' := by
    rw [mul_inv_eq_one₀ hne]
    constructor
    · intro H
      exact hz.pow_inj hr hr' H
    · intro H; rw [H]
  simp only [this]

private theorem parseval_full (s : ℕ → ℝ) (L : ℕ) (z : ℂ) (hL : 0 < L) (hz : IsPrimitiveRoot z L) :
    (∑ j ∈ Finset.range L, ‖∑ r ∈ Finset.range L, (s r : ℂ) * (z^j)^r‖^2) =
      (L:ℝ) * ∑ r ∈ Finset.range L, (s r)^2 := by
  have h1 : ∀ j : ℕ, (((‖∑ r ∈ Finset.range L, (s r : ℂ) * (z^j)^r‖^2 : ℝ)) : ℂ) =
      ∑ r ∈ Finset.range L, ∑ r' ∈ Finset.range L,
        ((s r : ℂ) * (z^j)^r) * ((s r' : ℂ) * ((z^j)⁻¹)^r') := by
    intro j
    rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Finset.sum_mul_sum]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    simp only [map_mul, map_pow, map_inv₀, Complex.conj_ofReal, conj_root L hL z hz, inv_pow, inv_inv]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have hr : ∀ r ∈ Finset.range L, ∑ j ∈ Finset.range L, ∑ r' ∈ Finset.range L,
        ((s r : ℂ) * (z^j)^r) * ((s r' : ℂ) * ((z^j)⁻¹)^r') = (L:ℂ) * ((s r : ℂ)^2) := by
    intro r hrr
    rw [Finset.sum_comm]
    have : ∀ r' ∈ Finset.range L, ∑ j ∈ Finset.range L,
        ((s r : ℂ) * (z^j)^r) * ((s r' : ℂ) * ((z^j)⁻¹)^r') =
        ((s r : ℂ) * (s r' : ℂ)) * (if r = r' then (L:ℂ) else 0) := by
      intro r' hr'
      rw [← cross_one L z hz r r' (Finset.mem_range.1 hrr) (Finset.mem_range.1 hr'), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl this]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [hrr, if_true]
    ring
  rw [Finset.sum_congr rfl hr, ← Finset.mul_sum]
  push_cast
  rfl

private theorem icc_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (H : ℕ) :
    ∑ h ∈ Finset.Icc 1 H, f h = ∑ k ∈ Finset.range H, f (k+1) := by
  induction H with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private theorem reindex (a b : ℕ → ℂ) (x : ℂ) (hx : x ≠ 0) (H : ℕ) :
    (a 0 + ∑ h ∈ Finset.Icc 1 H, (a h * x^h + b h * (x⁻¹)^h)) * x^H =
      ∑ i ∈ Finset.range (2*H+1), (if H ≤ i then a (i-H) else b (H-i)) * x^i := by
  have e2 : 2*H+1 = H + (H+1) := by ring
  rw [e2, Finset.sum_range_add]
  have hA : ∑ i ∈ Finset.range H, (if H ≤ i then a (i-H) else b (H-i)) * x^i =
      ∑ k ∈ Finset.range H, b (k+1) * x^(H-1-k) := by
    refine (Finset.sum_range_reflect (fun i => (if H ≤ i then a (i-H) else b (H-i)) * x^i) H).symm.trans ?_
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < H := Finset.mem_range.1 hk
    have h1 : ¬ H ≤ H - 1 - k := by omega
    have h2 : H - (H - 1 - k) = k + 1 := by omega
    simp only [if_neg h1, h2]
  have hB : ∑ k ∈ Finset.range (H+1), (if H ≤ H + k then a (H + k - H) else b (H - (H + k))) * x^(H+k) =
      a 0 * x^H + ∑ k ∈ Finset.range H, a (k+1) * x^(H+(k+1)) := by
    rw [Finset.sum_range_succ', add_comm]
    simp
  have hLs : (a 0 + ∑ h ∈ Finset.Icc 1 H, (a h * x^h + b h * (x⁻¹)^h)) * x^H =
      a 0 * x^H + ∑ k ∈ Finset.range H, a (k+1) * x^(H+(k+1)) +
        ∑ k ∈ Finset.range H, b (k+1) * x^(H-1-k) := by
    rw [icc_range (fun h => a h * x^h + b h * (x⁻¹)^h), add_mul, Finset.sum_mul]
    have : ∀ k ∈ Finset.range H, (a (k+1) * x^(k+1) + b (k+1) * (x⁻¹)^(k+1)) * x^H =
        a (k+1) * x^(H+(k+1)) + b (k+1) * x^(H-1-k) := by
      intro k hk
      have hk' : k < H := Finset.mem_range.1 hk
      have hH : x^H = x^(k+1) * x^(H-1-k) := by rw [← pow_add]; congr 1; omega
      have hinv : (x⁻¹)^(k+1) * x^(k+1) = 1 := by
        rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero _ hx)
      have hb : (x⁻¹)^(k+1) * x^H = x^(H-1-k) := by
        rw [hH, ← mul_assoc, hinv, one_mul]
      calc (a (k+1) * x^(k+1) + b (k+1) * (x⁻¹)^(k+1)) * x^H
          = a (k+1) * (x^(k+1) * x^H) + b (k+1) * ((x⁻¹)^(k+1) * x^H) := by ring
        _ = _ := by rw [hb, ← pow_add, add_comm (k+1) H]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    ring
  rw [hLs, hA, hB]
  ring

private theorem bucket (f : ℕ → ℂ) (x : ℂ) (L N : ℕ) (hL : 0 < L) (hx : x^L = 1) :
    ∑ i ∈ Finset.range N, f i * x^i =
      ∑ r ∈ Finset.range L, (∑ i ∈ (Finset.range N).filter (fun i => i % L = r), f i) * x^r := by
  have h1 : ∀ i, x^i = x^(i % L) := by
    intro i
    conv_lhs => rw [← Nat.div_add_mod i L, pow_add, pow_mul, hx, one_pow, one_mul]
  have h2 : ∑ i ∈ Finset.range N, f i * x^i = ∑ i ∈ Finset.range N, f i * x^(i % L) :=
    Finset.sum_congr rfl (fun i _ => by rw [h1 i])
  rw [h2, ← Finset.sum_fiberwise_of_maps_to (s := Finset.range N) (t := Finset.range L)
    (g := fun i => i % L) (fun i _ => Finset.mem_range.2 (Nat.mod_lt i hL))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [(Finset.mem_filter.1 hi).2]

theorem PEqualNP.Outside.L_goldbach_coset_phase_collision_correction :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q L : ℕ) (z : ℂ), 0<q → 0<L → IsPrimitiveRoot z L → let H := n/q; let c := fun i : ℕ => if H ≤ i then B n (n+(i-H)*q) else B n (n-(H-i)*q); (∑ j ∈ Finset.range L, ‖Y n q (z^j)‖^2)/(L:ℝ) = ∑ r ∈ Finset.range L, (∑ i ∈ (Finset.range (2*H+1)).filter (fun i => i % L=r), c i)^2 := by
  intro w B Y n q L z hq hL hz H c
  have hLr : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hn1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one hL.ne'
  set S : ℕ → ℝ := fun r => ∑ i ∈ (Finset.range (2*H+1)).filter (fun i => i % L=r), c i with hS
  have hj : ∀ j : ℕ, ‖Y n q (z^j)‖ = ‖∑ r ∈ Finset.range L, (S r : ℂ) * (z^j)^r‖ := by
    intro j
    have hx0 : z^j ≠ 0 := pow_ne_zero _ (hz.ne_zero hL.ne')
    have hxn : ‖z^j‖ = 1 := by rw [norm_pow, hn1, one_pow]
    have hxL : (z^j)^L = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    have h1 := reindex (fun h => (B n (n+h*q) : ℂ)) (fun h => (B n (n-h*q) : ℂ)) (z^j) hx0 H
    have h2 : Y n q (z^j) * (z^j)^H = ∑ i ∈ Finset.range (2*H+1), (c i : ℂ) * (z^j)^i := by
      have e : (B n n : ℂ) = (fun h => (B n (n+h*q) : ℂ)) 0 := by simp
      show ((B n n : ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*(z^j)^h + (B n (n-h*q):ℂ)*((z^j)⁻¹)^h)) * (z^j)^H = _
      rw [e]
      refine h1.trans (Finset.sum_congr rfl (fun i _ => ?_))
      simp only [c]
      split_ifs <;> simp
    have h3 := bucket (fun i => (c i : ℂ)) (z^j) L (2*H+1) hL hxL
    have h4 : ∑ r ∈ Finset.range L, (∑ i ∈ (Finset.range (2*H+1)).filter (fun i => i % L = r), (c i : ℂ)) * (z^j)^r
        = ∑ r ∈ Finset.range L, (S r : ℂ) * (z^j)^r := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [hS]
      push_cast
      rfl
    rw [← h4, ← h3, ← h2, norm_mul, norm_pow, hxn, one_pow, mul_one]
  have hP := parseval_full S L z hL hz
  simp_rw [hj]
  rw [hP, mul_div_cancel_left₀ _ hLr]
