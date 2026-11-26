import Mathlib

/- The large-sieve, separation and reciprocal-totient steps adapt the documented sources from muxkin, goldbach-proofs contribution 1708, c56bb450d43259dd871d29020d53facb6e5de557 (Apache-2.0). Separation adapts wzhxzkk’s frontier calculation; the sharp kernel is from OpenAI, openai/math, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
section

namespace GoldbachEstermann
open Finset

/-- Each divisor has totient at most that of the ambient integer. Summing over
divisors and using Gauss's identity gives a divisor-count majorant. -/
private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹) := by
  have hφ := Nat.totient_pos.mpr hq
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum (fun d hd =>
        Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  calc
    _ ≤ (q.divisors.card : ℝ) / q := (div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hq)).mpr
      (by rw [one_mul]; exact_mod_cast hcount)
    _ = ∑ _ ∈ q.divisorsAntidiagonal, (q:ℝ)⁻¹ := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (q:ℝ)⁻¹)]; simp [div_eq_mul_inv]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, mul_inv]

/-- A finite reciprocal-totient bound with constant one. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ)) ≤ (1 + Real.log Q)^2 := by
  let S := Icc 1 Q
  let w := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hf := Nat.fst_mem_divisors_of_mem_antidiagonal hab
      have hs := Nat.snd_mem_divisors_of_mem_antidiagonal hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ hf,hm _ hs⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hab
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hab).2,by omega⟩
  have hsum : (∑ i ∈ S, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
    simpa only [S,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log Q
  calc
    _ ≤ ∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab :=
      sum_le_sum (fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1)
    _ = ∑ q ∈ S, ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w ab :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w ab :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ ab ∈ S ×ˢ S, w ab := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ S, (i:ℝ)⁻¹)^2 := by rw [sq,sum_product,sum_mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hsum 2

end GoldbachEstermann

end

section

/- The sharp separated additive large sieve and its auxiliary proofs are adapted from
OpenAI, openai/math, revision 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/NumberTheory/Ostmann/Preliminaries (Apache License 2.0). -/
namespace GoldbachBDHSharp

-- Upstream module CosecantKernel
namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

noncomputable def cosecantKernel (x y : ℝ) : ℝ := (Real.sin (Real.pi * (x - y)))⁻¹
noncomputable def cotangentKernel (x y : ℝ) : ℝ :=
  Real.cos (Real.pi * (x - y)) / Real.sin (Real.pi * (x - y))

@[simp] theorem cosecantKernel_self (x : ℝ) : cosecantKernel x x = 0 := by
  simp [cosecantKernel]

@[simp] theorem cotangentKernel_self (x : ℝ) : cotangentKernel x x = 0 := by
  simp [cotangentKernel]

theorem cosecantKernel_skew (x y : ℝ) : cosecantKernel x y = -cosecantKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cosecantKernel, he]

theorem cotangentKernel_skew (x y : ℝ) : cotangentKernel x y = -cotangentKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cotangentKernel, he, div_neg]

theorem cosecantKernel_triple (x y z : ℝ)
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0)
    (hxz : Real.sin (Real.pi * (x - z)) ≠ 0)
    (hyz : Real.sin (Real.pi * (y - z)) ≠ 0) :
    cosecantKernel x y * cosecantKernel x z =
      cosecantKernel y z * (cotangentKernel x y - cotangentKernel x z) := by
  have he : Real.pi * (y - z) = Real.pi * (x - z) - Real.pi * (x - y) := by ring
  have hs := Real.sin_sub (Real.pi * (x - z)) (Real.pi * (x - y))
  rw [← he] at hs
  unfold cosecantKernel cotangentKernel
  field_simp
  nlinarith

theorem cos_quartic_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have ht0 : 0 ≤ t := (Set.mem_Ici.mp (interior_subset ht))
    have hs := Real.sin_ge_sub_cube ht0
    linarith
  have hh := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  simpa [f] using hh

theorem sine_cosecant_majorant {x : ℝ} (hx : 0 < x) (hxp : x ≤ Real.pi / 2) :
    1 / (Real.sin x) ^ 2 + 2 * |Real.cos x / (Real.sin x) ^ 2| ≤ 3 / x ^ 2 := by
  have hx2 : x < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxp⟩
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hxSq hx.le
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq := mul_self_le_mul_self hl hsin
  have hcos := mul_le_mul_of_nonneg_left (cos_quartic_upper hx.le) (sq_nonneg x)
  have hpoly : (1 + 2 * Real.cos x) * x ^ 2 ≤ 3 * (Real.sin x) ^ 2 := by nlinarith
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  have he : 1 / (Real.sin x) ^ 2 + 2 * (Real.cos x / (Real.sin x) ^ 2) =
      (1 + 2 * Real.cos x) / (Real.sin x) ^ 2 := by ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx)).mpr hpoly

end Ostmann

end OAI

-- Upstream module SieveGeometricKernel
namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

noncomputable def sieveHalfPhase (t : ℝ) : ℂ :=
  Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem sieveHalfPhase_zero : sieveHalfPhase 0 = 1 := by simp [sieveHalfPhase]

 theorem sieveHalfPhase_add (s t : ℝ) :
    sieveHalfPhase (s + t) = sieveHalfPhase s * sieveHalfPhase t := by
  simp only [sieveHalfPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem sieveHalfPhase_norm (t : ℝ) : ‖sieveHalfPhase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

 theorem sieveHalfPhase_sine (t : ℝ) :
    (2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ) =
      sieveHalfPhase t - sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem sieveHalfPhase_two_step (s t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) * sieveHalfPhase s =
      sieveHalfPhase (s + t) - sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_sine, sieveHalfPhase_add, sub_eq_add_neg s t, sieveHalfPhase_add]
  ring

 theorem sieve_geometric_kernel_mul (M : ℕ) (J t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) *
      (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
        sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hs := sieveHalfPhase_two_step (2 * (J + M) * t) t
    rw [show 2 * (J + (M : ℝ)) * t + t = (2 * (J + (M + 1 : ℕ)) - 1) * t by
      push_cast; ring,
      show 2 * (J + (M : ℝ)) * t - t = (2 * (J + M) - 1) * t by ring] at hs
    rw [hs]
    ring

 theorem sieve_geometric_kernel (M : ℕ) (J t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
      ((sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) /
        ((2 : ℂ) * Complex.I)) * (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
  have hs := sieve_geometric_kernel_mul M J t
  have htC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hfactor htC))
  rw [hs, div_eq_mul_inv]
  symm
  calc
    _ = (((2 : ℂ) * Complex.I) * ((2 : ℂ) * Complex.I)⁻¹) *
        ((Real.sin (Real.pi * t) : ℂ) * (Real.sin (Real.pi * t) : ℂ)⁻¹) *
          (sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, mul_inv_cancel₀ htC]; ring

end Ostmann

end OAI

-- Upstream module SeparatedInverseSquares
namespace OAI

/-! # The one-sided inverse-square estimate for separated sample points -/

namespace Ostmann

open scoped BigOperators

 theorem ordered_separated_lower {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    ∀ i, δ * (i.val + 1) ≤ x i := by
  have hi : ∀ k : ℕ, ∀ hk : k < n, δ * ((k : ℝ) + 1) ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hg := hgap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact hi i.val i.isLt

 theorem finite_positive_inverse_squares (n : ℕ) :
    (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have he : (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), 1 / (j : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) n,
      Finset.sum_range_succ']
    simp
  rw [he, ← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum _ (fun j _ => by positivity)

 theorem ordered_separated_inverse_squares {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hx := ordered_separated_lower x δ hfirst hgap
  have hb (i : Fin n) : 1 / (x i) ^ 2 ≤
      (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := by
    have hi : 0 < (i.val : ℝ) + 1 := by positivity
    have hxi : 0 < x i := lt_of_lt_of_le hδ (hfirst i)
    have hs : (δ * ((i.val : ℝ) + 1)) ^ 2 ≤ (x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hx i) 2
    calc
      _ ≤ 1 / (δ * ((i.val : ℝ) + 1)) ^ 2 := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by simp only [mul_pow, one_div, mul_inv]
  calc
    _ ≤ ∑ i : Fin n, (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (δ ^ 2)⁻¹ * ∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ 2)⁻¹ * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (finite_positive_inverse_squares n) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI

-- Upstream module SeparatedSetSquares
namespace OAI

/-! # The inverse-square row sum for a finite separated set -/

namespace Ostmann

open scoped BigOperators

 theorem positive_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  let e := S.orderEmbOfFin rfl
  have he (i : Fin S.card) : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hg (i j : Fin S.card) (hij : i < j) : δ ≤ e j - e i := by
    have hij' : e i < e j := e.strictMono hij
    have hh := hsep (e j) (he j) (e i) (he i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at hh
  have hh := ordered_separated_inverse_squares (fun i => e i) δ hδ
    (fun i => hfirst _ (he i)) hg
  have hs : (∑ x ∈ S, 1 / x ^ 2) = ∑ i : Fin S.card, 1 / (e i) ^ 2 := by
    conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  rwa [hs]

 theorem separated_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ |x|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let P := S.filter (fun x => 0 < x)
  let N := S.filter (fun x => ¬0 < x)
  let R := N.image (fun x => -x)
  have hP := positive_set_inverse_squares P δ hδ
    (fun x hx => by
      have h := Finset.mem_filter.mp hx
      simpa only [abs_of_pos h.2] using hfirst x h.1)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hRfirst (x : ℝ) (hx : x ∈ R) : δ ≤ x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_filter.mp hy
    simpa only [abs_of_nonpos (le_of_not_gt hy'.2)] using hfirst y hy'.1
  have hRsep (x : ℝ) (hx : x ∈ R) (y : ℝ) (hy : y ∈ R) (hxy : x ≠ y) : δ ≤ |x - y| := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hh := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun hab => hxy (congrArg Neg.neg hab))
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hR := positive_set_inverse_squares R δ hδ hRfirst hRsep
  have hsum : (∑ x ∈ P, 1 / x ^ 2) + (∑ x ∈ N, 1 / x ^ 2) = ∑ x ∈ S, 1 / x ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have he : (∑ x ∈ R, 1 / x ^ 2) = ∑ x ∈ N, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    · simp
    · exact fun _ _ _ _ hab => neg_injective hab
  rw [he] at hR
  rw [← hsum]
  have hid : Real.pi ^ 2 / (3 * δ ^ 2) = 2 * (Real.pi ^ 2 / (6 * δ ^ 2)) := by ring
  rw [hid]
  linarith

end Ostmann

end OAI

-- Upstream module CosecantDistanceBound
namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

noncomputable def cosecantRowWeight (t : ℝ) : ℝ :=
  1 / Real.sin (Real.pi * t) ^ 2 +
    2 * |Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ^ 2|

 theorem cosecantRowWeight_eq (x y : ℝ) :
    cosecantKernel x y ^ 2 + 2 * |cosecantKernel x y * cotangentKernel x y| =
      cosecantRowWeight (x - y) := by
  unfold cosecantKernel cotangentKernel cosecantRowWeight
  congr 1
  · ring
  · congr 2
    ring

 theorem cosecantRowWeight_shift (t : ℝ) (m : ℤ) :
    cosecantRowWeight (t - m) = cosecantRowWeight t := by
  have he : Real.pi * (t - m) = Real.pi * t - (m : ℝ) * Real.pi := by ring
  have hs : |Real.sin (Real.pi * (t - m))| = |Real.sin (Real.pi * t)| := by
    rw [he, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hc : |Real.cos (Real.pi * (t - m))| = |Real.cos (Real.pi * t)| := by
    rw [he, Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  simp only [sq_abs] at hs2
  unfold cosecantRowWeight
  rw [hs2, abs_div, abs_div, hc]

 theorem cosecantRowWeight_abs (t : ℝ) : cosecantRowWeight |t| = cosecantRowWeight t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp [cosecantRowWeight, Real.sin_neg, Real.cos_neg]

 theorem cosecantRowWeight_bound (t d : ℝ) (m : ℤ)
    (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (he : |t - m| = d) :
    cosecantRowWeight t ≤ 3 / (Real.pi ^ 2 * d ^ 2) := by
  rw [← cosecantRowWeight_shift t m, ← cosecantRowWeight_abs, he]
  have hp : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hh : Real.pi * d ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hb := sine_cosecant_majorant hp hh
  simpa only [cosecantRowWeight, mul_pow] using hb

end Ostmann

end OAI

-- Upstream module CircleSeparatedPoints
namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

noncomputable def centeredCircleRemainder (t : ℝ) : ℝ := t - (⌊t + 1 / 2⌋ : ℤ)

def CircleSeparated {ι : Type*} (x : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ s t, s ≠ t → ∀ m : ℤ, δ ≤ |x s - x t - m|

 theorem centeredCircleRemainder_bounds (t : ℝ) :
    -(1 / 2) ≤ centeredCircleRemainder t ∧ centeredCircleRemainder t < 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  dsimp [centeredCircleRemainder]
  constructor <;> linarith

 theorem circleSeparated_sine_ne_zero {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) {s t : ι} (hst : s ≠ t) :
    Real.sin (Real.pi * (x s - x t)) ≠ 0 := by
  intro hz
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hz
  have he : x s - x t - (m : ℝ) = 0 := by nlinarith [Real.pi_pos]
  have hh := hx s t hst m
  rw [he, abs_zero] at hh
  linarith

 theorem circleSeparated_remainders {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hx : CircleSeparated x δ) (center s t : ι) (hst : s ≠ t) :
    δ ≤ |centeredCircleRemainder (x s - x center) -
      centeredCircleRemainder (x t - x center)| := by
  have hh := hx s t hst (⌊x s - x center + 1 / 2⌋ - ⌊x t - x center + 1 / 2⌋)
  push_cast at hh
  convert hh using 1; congr 1; dsimp [centeredCircleRemainder]; ring

 theorem circleSeparated_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s ∈ Finset.univ.erase center,
      1 / centeredCircleRemainder (x s - x center) ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  let S := F.image r
  have hfirst (s : ι) (hs : s ∈ F) : δ ≤ |r s| :=
    hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
  have hinj : Set.InjOn r F := by
    intro s hs t ht he
    by_contra hst
    have hb := circleSeparated_remainders x δ hx center s t hst
    change δ ≤ |r s - r t| at hb
    rw [he, sub_self, abs_zero] at hb
    linarith
  have hb := separated_set_inverse_squares S δ hδ (by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact hfirst s hs) (by
    intro y hy z hz hyz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact circleSeparated_remainders x δ hx center s t (fun hst => hyz (congrArg r hst)))
  have he : (∑ y ∈ S, 1 / y ^ 2) = ∑ s ∈ F, 1 / (r s) ^ 2 := by
    exact Finset.sum_image hinj
  rwa [he] at hb

end Ostmann

end OAI

-- Upstream module CosecantRowSum
namespace OAI

/-! # The sharp row budget for the cosecant matrix -/

namespace Ostmann

open scoped BigOperators

 theorem cosecant_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s, cosecantKernel (x s) (x center) ^ 2) +
        2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| ≤
      1 / δ ^ 2 := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  have he (s : ι) : cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s) =
      cosecantKernel (x s) (x center) * cotangentKernel (x s) (x center) := by
    rw [cosecantKernel_skew (x center) (x s), cotangentKernel_skew (x center) (x s)]
    ring
  have hsum : (∑ s, cosecantKernel (x s) (x center) ^ 2) +
      2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| =
        ∑ s ∈ F, cosecantRowWeight (x s - x center) := by
    simp_rw [he]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [cosecantRowWeight_eq]
    apply (Finset.sum_erase_add _ _ (Finset.mem_univ center)).symm.trans ?_
    simp [cosecantRowWeight, F]
  have hb (s : ι) (hs : s ∈ F) :
      cosecantRowWeight (x s - x center) ≤ 3 / (Real.pi ^ 2 * (r s) ^ 2) := by
    have hd := hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
    change δ ≤ |r s| at hd
    have hhalf : |r s| ≤ 1 / 2 := abs_le.mpr
      ⟨(centeredCircleRemainder_bounds _).1, (centeredCircleRemainder_bounds _).2.le⟩
    have hh := cosecantRowWeight_bound (x s - x center) |r s|
      ⌊x s - x center + 1 / 2⌋ (lt_of_lt_of_le hδ hd) hhalf rfl
    simpa only [sq_abs] using hh
  rw [hsum]
  calc
    _ ≤ ∑ s ∈ F, 3 / (Real.pi ^ 2 * (r s) ^ 2) := Finset.sum_le_sum hb
    _ = (3 / Real.pi ^ 2) * ∑ s ∈ F, 1 / (r s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (circleSeparated_inverse_square_row x δ hδ hx center) (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI

-- Upstream module SkewKernelSquare
namespace OAI

/-! # A finite algebraic identity for the large-sieve kernel

This is the cancellation underlying Montgomery--Vaughan's equation (3.6).
The diagonal correction is retained explicitly before any norm estimate.
-/

namespace Ostmann

open scoped BigOperators

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

 theorem skew_kernel_square_entry (h k : ι → ι → K)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (∑ r, h r s * h r t) =
      (if s = t then ∑ r, h r s ^ 2 else 0) +
        h s t * ((∑ r, k r s) - ∑ r, k r t) + 2 * h s t * k s t := by
  by_cases hst : s = t
  · subst t
    simp [hdiag, sq]
  · have he (r : ι) : h r s * h r t = h s t * (k r s - k r t) +
        (if r = s then h s t * k s t else 0) +
        (if r = t then h s t * k s t else 0) := by
      by_cases hrs : r = s
      · subst r
        simp [hdiag, kdiag, hst]
      · by_cases hrt : r = t
        · subst r
          rw [hdiag, kdiag, kskew t s]
          simp only [hrs, ↓reduceIte]
          ring
        · simp only [hrs, hrt, ↓reduceIte, add_zero]
          exact htriple r s t hrs hrt hst
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hst, ↓reduceIte, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end

end Ostmann

end OAI

-- Upstream module HermitianEigenvector
namespace OAI

/-! # Finite Hermitian eigenvector cancellation -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem hermitian_eigenvector_left {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) (v : ι → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * (star u ⬝ᵥ v) := by
  have h := hA.star_dotProduct_mulVec_comm u v
  rw [heig, dotProduct_smul] at h
  apply star_injective
  rw [h]
  simp [dotProduct, mul_comm]

theorem hermitian_eigenvector_commutator {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (D : Matrix ι ι ℂ) (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) :
    star u ⬝ᵥ ((D * A - A * D) *ᵥ u) = 0 := by
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
    heig, mulVec_smul, dotProduct_smul, hermitian_eigenvector_left hA u μ heig]
  simp only [smul_eq_mul, sub_self]

end Ostmann

end OAI

-- Upstream module CosecantMatrix
namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def imaginaryKernelMatrix (h : ι → ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of (fun s t => Complex.I * (h s t : ℂ))

omit [Fintype ι] [DecidableEq ι] in
 theorem imaginaryKernelMatrix_hermitian (h : ι → ι → ℝ)
    (hskew : ∀ s t, h s t = -h t s) : (imaginaryKernelMatrix h).IsHermitian := by
  ext s t
  simp only [imaginaryKernelMatrix, conjTranspose_apply, Matrix.of_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [hskew t s]
  push_cast
  ring

 theorem imaginaryKernelMatrix_square_entry (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (imaginaryKernelMatrix h * imaginaryKernelMatrix h) s t =
      (if s = t then ((∑ r, h r s ^ 2 : ℝ) : ℂ) else 0) +
        (h s t : ℂ) * ((∑ r, k r s : ℝ) - ∑ r, k r t) +
          2 * (h s t : ℂ) * (k s t : ℂ) := by
  have he (r : ι) : imaginaryKernelMatrix h s r * imaginaryKernelMatrix h r t =
      ((h r s * h r t : ℝ) : ℂ) := by
    dsimp [imaginaryKernelMatrix]
    rw [hskew s r]
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * ((h r s : ℂ) * (h r t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum, skew_kernel_square_entry h k hdiag kdiag kskew htriple]
  push_cast
  by_cases hst : s = t <;> simp [hst]

 theorem imaginaryKernelMatrix_square (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) :
    let A : Matrix ι ι ℂ := imaginaryKernelMatrix h
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
    A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
      (Complex.I • (D * A - A * D) : Matrix ι ι ℂ) +
        (2 : ℂ) • Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ)) := by
  dsimp only
  ext s t
  rw [imaginaryKernelMatrix_square_entry h k hdiag kdiag hskew kskew htriple]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    imaginaryKernelMatrix, Matrix.of_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Ostmann

end OAI

-- Upstream module SymmetricQuadraticBound
namespace OAI

/-! # The finite quadratic bound for the cosecant row estimate -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem real_symmetric_quadratic_upper (v : ι → ι → ℝ)
    (hv : ∀ s t, v s t = v t s) (u : ι → ℂ) :
    ‖star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u)‖ ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
  have he : star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u) =
      ∑ s, ∑ t, star (u s) * (v s t : ℂ) * u t := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hswap : (∑ s, ∑ t, |v s t| * ‖u t‖ ^ 2) =
      ∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t s]
  have hfactor : (∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, mul_comm]
  have havg : (∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    rw [hfactor]
    ring
  rw [he]
  calc
    _ ≤ ∑ s, ‖∑ t, star (u s) * (v s t : ℂ) * u t‖ := norm_sum_le _ _
    _ ≤ ∑ s, ∑ t, ‖star (u s) * (v s t : ℂ) * u t‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ = ∑ s, ∑ t, |v s t| * ‖u s‖ * ‖u t‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hh := mul_le_mul_of_nonneg_left (sq_nonneg (‖u s‖ - ‖u t‖)) (abs_nonneg (v s t))
      nlinarith
    _ = _ := havg

end Ostmann

end OAI

-- Upstream module KernelEigenvalueBound
namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_diagonal_quadratic (d : ι → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Matrix.diagonal (fun s => (d s : ℂ))) *ᵥ u) =
      ((∑ s, d s * ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [show star (u s) * ((d s : ℂ) * u s) = (d s : ℂ) * (star (u s) * u s) by ring,
    Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

 theorem kernel_eigenvalue_bound (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t))
    (B μ : ℝ) (hrow : ∀ s, (∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r| ≤ B)
    (u : ι → ℂ) (hu : 0 < ∑ s, ‖u s‖ ^ 2)
    (heig : imaginaryKernelMatrix h *ᵥ u = (μ : ℂ) • u) : μ ^ 2 ≤ B := by
  let A := imaginaryKernelMatrix h
  let D := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
  let V : Matrix ι ι ℂ := Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ))
  have hA : A.IsHermitian := imaginaryKernelMatrix_hermitian h hskew
  have hcomm := hermitian_eigenvector_commutator hA D u μ heig
  have hsq : star u ⬝ᵥ ((A * A) *ᵥ u) =
      ((μ ^ 2 * ∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mulVec_mulVec, heig, mulVec_smul, heig, smul_smul, dotProduct_smul,
      complex_self_quadratic]
    push_cast
    simp only [smul_eq_mul, pow_two]
  have hidentity := imaginaryKernelMatrix_square h k hdiag kdiag hskew kskew htriple
  change A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
    Complex.I • (D * A - A * D) + (2 : ℂ) • V at hidentity
  rw [hidentity, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hcomm, smul_zero, sub_zero, smul_mulVec, dotProduct_smul,
    complex_diagonal_quadratic] at hsq
  have hreal := congrArg Complex.re hsq
  have htwo (z : ℂ) : ((2 : ℂ) • z).re = 2 * z.re := by simp [smul_eq_mul, Complex.mul_re]
  simp only [Complex.add_re, Complex.ofReal_re, htwo] at hreal
  have hsym : ∀ s t, h s t * k s t = h t s * k t s := by
    intro s t
    rw [hskew s t, kskew s t]
    ring
  have hv := real_symmetric_quadratic_upper (fun s t => h s t * k s t) hsym u
  have hvr : (star u ⬝ᵥ (V *ᵥ u)).re ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |h s t * k s t| :=
    (Complex.re_le_norm _).trans hv
  have hsum : (∑ s, (∑ r, h r s ^ 2) * ‖u s‖ ^ 2) +
      2 * (∑ s, ‖u s‖ ^ 2 * ∑ r, |h s r * k s r|) ≤
        B * ∑ s, ‖u s‖ ^ 2 := by
    calc
      _ = ∑ s, ‖u s‖ ^ 2 * ((∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro s _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * B := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hfinal : μ ^ 2 * (∑ s, ‖u s‖ ^ 2) ≤ B * (∑ s, ‖u s‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hu).mp hfinal

end Ostmann

end OAI

-- Upstream module HermitianNormBound
namespace OAI

/-! # Passing a finite Hermitian eigenvalue bound to its quadratic form -/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem hermitian_norm_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : ℝ) (hB : 0 ≤ B) (heig : ∀ i, |hA.eigenvalues i| ≤ B) : ‖A‖ ≤ B := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs] using heig i

 theorem matrix_quadratic_norm_bound (A : Matrix ι ι ℂ) (B : ℝ)
    (hB : ‖A‖ ≤ B) (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ B * ∑ i, ‖u i‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let w : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ u)
  have hinner : inner ℂ v w = star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hv : ‖v‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hw : ‖w‖ ≤ B * ‖v‖ := (Matrix.l2_opNorm_mulVec A v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  rw [← hinner]
  calc
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    _ = B * ∑ i, ‖u i‖ ^ 2 := by rw [← hv]; ring

end Ostmann

end OAI

-- Upstream module CosecantHilbertBound
namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cosecantMatrix (x : ι → ℝ) : Matrix ι ι ℂ :=
  imaginaryKernelMatrix (fun s t => cosecantKernel (x s) (x t))

omit [Fintype ι] [DecidableEq ι] in
 theorem cosecantMatrix_hermitian (x : ι → ℝ) : (cosecantMatrix x).IsHermitian :=
  imaginaryKernelMatrix_hermitian _ (fun _ _ => cosecantKernel_skew _ _)

 theorem cosecant_eigenvalue_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (μ : ℝ) (u : ι → ℂ)
    (hu : 0 < ∑ s, ‖u s‖ ^ 2) (heig : cosecantMatrix x *ᵥ u = (μ : ℂ) • u) :
    μ ^ 2 ≤ 1 / δ ^ 2 := by
  exact kernel_eigenvalue_bound
    (fun s t => cosecantKernel (x s) (x t))
    (fun s t => cotangentKernel (x s) (x t))
    (fun _ => cosecantKernel_self _) (fun _ => cotangentKernel_self _)
    (fun _ _ => cosecantKernel_skew _ _) (fun _ _ => cotangentKernel_skew _ _)
    (fun r s t hrs hrt hst => cosecantKernel_triple _ _ _
      (circleSeparated_sine_ne_zero x δ hδ hx hrs)
      (circleSeparated_sine_ne_zero x δ hδ hx hrt)
      (circleSeparated_sine_ne_zero x δ hδ hx hst))
    (1 / δ ^ 2) μ (cosecant_row_sum_bound x δ hδ hx) u hu heig

 theorem cosecantMatrix_norm_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) : ‖cosecantMatrix x‖ ≤ 1 / δ := by
  apply hermitian_norm_bound (cosecantMatrix_hermitian x) (1 / δ) (by positivity)
  intro i
  let hA := cosecantMatrix_hermitian x
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hu : 0 < ∑ s, ‖(hA.eigenvectorBasis i) s‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have hb := cosecant_eigenvalue_bound x δ hδ hx (hA.eigenvalues i)
    (hA.eigenvectorBasis i) hu (hA.mulVec_eigenvectorBasis i)
  have hinv : 0 < 1 / δ := by positivity
  have heq : 1 / δ ^ 2 = (1 / δ) ^ 2 := by ring
  rw [heq] at hb
  nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i)]

 theorem cosecant_hilbert_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (u : ι → ℂ) :
    ‖∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t‖ ≤
      (1 / δ) * ∑ s, ‖u s‖ ^ 2 := by
  have hb := matrix_quadratic_norm_bound (cosecantMatrix x) (1 / δ)
    (cosecantMatrix_norm_bound x δ hδ hx) u
  have he : star u ⬝ᵥ (cosecantMatrix x *ᵥ u) =
      Complex.I * (∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t) := by
    simp only [dotProduct, mulVec, Pi.star_apply, cosecantMatrix, imaginaryKernelMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end Ostmann

end OAI

-- Upstream module SievePhaseGram
namespace OAI

/-! # The exact finite Gram expansion of the large-sieve phase matrix -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_star (t : ℝ) : star (sieveHalfPhase t) = sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

 theorem sieveHalfPhase_difference (s t : ℝ) :
    sieveHalfPhase s * star (sieveHalfPhase t) = sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_star, ← sieveHalfPhase_add, sub_eq_add_neg]

 theorem finite_complex_norm_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ s, f s‖ ^ 2 : ℝ) : ℂ) = ∑ s, ∑ t, f s * star (f t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [← Complex.star_def, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

 theorem sieve_phase_gram {ι : Type*} [Fintype ι] (x : ι → ℝ) (b : ι → ℂ)
    (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, b s * star (b t) *
        ∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t)) := by
  simp only [Complex.ofReal_sum, finite_complex_norm_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul]
  rw [show 2 * (J + (n : ℝ)) * (x s - x t) =
    2 * (J + (n : ℝ)) * x s - 2 * (J + (n : ℝ)) * x t by ring,
    ← sieveHalfPhase_difference]
  ring

 theorem twisted_cosecant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (b : ι → ℂ) (L : ℝ) :
    ‖∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)‖ ≤ (1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  let u := fun s => star (b s * sieveHalfPhase (L * x s))
  have he : (∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)) =
      ∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    simp only [u, star_star, star_mul]
    rw [show L * (x s - x t) = L * x s - L * x t by ring,
      ← sieveHalfPhase_difference]
    ring
  rw [he]
  have hb := cosecant_hilbert_bound x δ hδ hx u
  simpa only [u, norm_star, norm_mul, sieveHalfPhase_norm, mul_one] using hb

end Ostmann

end OAI

-- Upstream module SieveDualEnergy
namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def twistedCosecantSum (x : ι → ℝ) (b : ι → ℂ) (L : ℝ) : ℂ :=
  ∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
    (cosecantKernel (x s) (x t) : ℂ)

omit [Fintype ι] in
 theorem sieve_pair_kernel (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (s t : ι) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t))) =
      (if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ) := by
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst, zero_add]
    simpa only [cosecantKernel, Complex.ofReal_inv] using
      sieve_geometric_kernel M J (x s - x t) (circleSeparated_sine_ne_zero x δ hδ hx hst)

 theorem sieve_dual_energy_identity (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)) := by
  rw [sieve_phase_gram]
  simp_rw [sieve_pair_kernel x δ hδ hx M J]
  have he (s t : ι) : b s * star (b t) *
      ((if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ)) =
      (if s = t then (M : ℂ) * ((‖b s‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (b s * star (b t) * sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ) -
            b s * star (b t) * sieveHalfPhase ((2 * J - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ)) := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, sub_self, mul_zero, sieveHalfPhase_zero,
        cosecantKernel_self, Complex.ofReal_zero, mul_one, add_zero]
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      ring
    · simp only [hst, ↓reduceIte, zero_add, div_eq_mul_inv]
      ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_mul, twistedCosecantSum]

 theorem sieve_dual_energy_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    (∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  have hi := sieve_dual_energy_identity x δ hδ hx b M J
  have htop := twisted_cosecant_bound x δ hδ hx b (2 * (J + M) - 1)
  have hbottom := twisted_cosecant_bound x δ hδ hx b (2 * J - 1)
  change ‖twistedCosecantSum x b (2 * (J + M) - 1)‖ ≤ _ at htop
  change ‖twistedCosecantSum x b (2 * J - 1)‖ ≤ _ at hbottom
  have htri := norm_add_le (((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) : ℂ)
    (((2 : ℂ) * Complex.I)⁻¹ *
      (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)))
  have hdiff := norm_sub_le (twistedCosecantSum x b (2 * (J + M) - 1))
    (twistedCosecantSum x b (2 * J - 1))
  rw [← hi] at htri
  have hE : 0 ≤ ∑ s, ‖b s‖ ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hN : 0 ≤ ∑ n ∈ Finset.range M,
      ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hE),
    norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I] at htri
  norm_num at htri
  nlinarith

end Ostmann

end OAI

-- Upstream module FiniteMatrixDuality
namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI

-- Upstream module SeparatedAdditiveSieve
namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

noncomputable def sievePhaseMatrix {ι : Type*} (x : ι → ℝ) (M : ℕ) (J : ℝ) :
    Matrix ι (Fin M) ℂ :=
  Matrix.of (fun s n => sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s))

 theorem sievePhaseMatrix_adjoint {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (J : ℝ) (b : ι → ℂ) (n : Fin M) :
    ((sievePhaseMatrix x M J)ᴴ *ᵥ b) n =
      star (∑ s, star (b s) * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)) := by
  simp only [mulVec, dotProduct, conjTranspose_apply, sievePhaseMatrix, Matrix.of_apply,
    star_sum, star_mul, star_star]

 theorem separated_additive_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (c : Fin M → ℂ) :
    (∑ s, ‖∑ n, c n * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ n, ‖c n‖ ^ 2 := by
  have hdual (b : ι → ℂ) :
      (∑ n, ‖((sievePhaseMatrix x M J)ᴴ *ᵥ b) n‖ ^ 2) ≤
        ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
    simp only [sievePhaseMatrix_adjoint, norm_star]
    have hb := sieve_dual_energy_bound x δ hδ hx (fun s => star (b s)) M J
    rw [← Fin.sum_univ_eq_sum_range] at hb
    simpa only [norm_star] using hb
  have hK : 0 ≤ (M : ℝ) + 1 / δ := by positivity
  have h := finite_matrix_duality (sievePhaseMatrix x M J) ((M : ℝ) + 1 / δ) hK hdual c
  simpa only [mulVec, dotProduct, sievePhaseMatrix, Matrix.of_apply, mul_comm] using h

end Ostmann

end OAI


end GoldbachBDHSharp

end

section

theorem GoldbachBDH.farey_sep :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q → Nat.Coprime b r → (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ, 1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq hqQ hr hrQ ha hb hdistinct m
  let d : ℤ := a * (r : ℤ) - b * (q : ℤ) - m * q * r
  have hd : d ≠ 0 := by
    intro heq
    change (a : ℤ) * r - b * q - m * q * r = 0 at heq
    have hqr : q ∣ a * r := by
      have : (q : ℤ) ∣ (a : ℤ) * r := ⟨b + m * r, by linarith only [heq]⟩
      exact_mod_cast this
    have hrq : r ∣ b * q := by
      have : (r : ℤ) ∣ (b : ℤ) * q := ⟨a - m * q, by linarith only [heq]⟩
      exact_mod_cast this
    have hsame := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hqr) (hb.symm.dvd_of_dvd_mul_left hrq)
    subst r
    have hqi : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have he : ((a : ℤ) - b - m * q) * q = 0 := by linarith only [heq]
    have hab := (mul_eq_zero.mp he).resolve_right hqi
    have hmod : (a : ℤ) ≡ b [ZMOD (q : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-m, by linarith only [hab]⟩
    exact hdistinct.elim (fun h => h rfl) (fun h => h (Int.natCast_modEq_iff.mp hmod))
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hD : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast (show (1 : ℤ) ≤ |d| by have := abs_pos.mpr hd; omega)
  have hden : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by rw [sq]; exact_mod_cast Nat.mul_le_mul hqQ hrQ
  calc 1 / (Q : ℝ)^2 ≤ 1 / ((q : ℝ) * r) := one_div_le_one_div_of_le (mul_pos hq' hr') hden
    _ ≤ |(d : ℝ)| / ((q : ℝ) * r) := div_le_div_of_nonneg_right hD (mul_pos hq' hr').le
    _ = _ := by
      rw [← abs_of_pos (mul_pos hq' hr'), ← abs_div]
      congr 1
      dsimp [d]; push_cast; field_simp

end

open Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Summing primitive roots over the divisors recovers all roots. Möbius inversion
then gives the sum at each exact order. -/
private theorem sumPrimitive (n : ℕ) :
    (∑ z ∈ primitiveRoots n ℂ, z) = (μ n : ℂ) := by
  classical
  let F : ArithmeticFunction ℂ := ⟨fun k => ∑ z ∈ primitiveRoots k ℂ, z, by simp⟩
  have hF : F * (ζ : ArithmeticFunction ℂ) = 1 := by
    ext k
    by_cases hk : k = 0
    · subst k; simp
    let : NeZero k := ⟨hk⟩
    have hk' := Nat.pos_of_ne_zero hk
    let z := Complex.exp (2 * Real.pi * Complex.I / k)
    have hz : IsPrimitiveRoot z k := Complex.isPrimitiveRoot_exp k hk
    rw [coe_mul_zeta_apply]
    change (∑ i ∈ k.divisors, ∑ t ∈ primitiveRoots i ℂ, t) = _
    rw [← Finset.sum_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    have hall : (∑ j ∈ Finset.range k, z ^ j) = ∑ t ∈ nthRootsFinset k (1 : ℂ), t := by
      apply Finset.sum_bij (fun j _ => z ^ j)
      · intro j _; apply (mem_nthRootsFinset hk' _).mpr
        rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
      · intro i hi j hj eq; exact hz.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) eq
      · intro x hx
        obtain ⟨j,hj,he⟩ := hz.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hk' _).mp hx)
        exact ⟨j,Finset.mem_range.mpr hj,he⟩
      · intros; rfl
    rw [← hall]
    by_cases h : k = 1
    · subst k; simp
    · rw [hz.geom_sum_eq_zero (by omega)]; simp [h]
  have hμ : F = (μ : ArithmeticFunction ℂ) := by
    calc F = (F * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) := by
            rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
         _ = _ := by rw [hF, one_mul]
  exact congrArg (fun f : ArithmeticFunction ℂ => f n) hμ

/-- A coprime frequency permutes the primitive roots of the given order. -/
theorem bandRamanujan (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / q : ℝ) : ℂ) * Complex.I)) = (μ q : ℂ) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / q)
  have hz : IsPrimitiveRoot (Complex.exp θ) q := Complex.isPrimitiveRoot_exp_of_coprime a q hq.ne' ha
  rw [← sumPrimitive q]
  apply Finset.sum_bij (fun i _ => Complex.exp θ ^ i)
  · intro i hi; exact (mem_primitiveRoots hq).mpr (hz.pow_of_coprime i (Finset.mem_filter.mp hi).2)
  · intro i hi j hj; exact hz.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  · intro x hx
    obtain ⟨i,hi,hc,he⟩ := hz.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hx)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hc⟩,he⟩
  · intro i _; rw [← Complex.exp_nat_mul]; congr 1; dsimp [θ]; push_cast; ring

namespace GoldbachMajorArc
open Finset
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
def primeSum (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (n+1), (primeWeight k:ℂ)*phase ((k:ℝ)*t)
@[simp] lemma bandPhase_norm (x : ℝ) : ‖phase x‖=1 := Complex.norm_exp_ofReal_mul_I _
end
end GoldbachMajorArc
namespace GoldbachBDH
open Finset
def num (q : ℕ) := (range q).filter (fun a => a.Coprime q)
end GoldbachBDH
namespace GoldbachBDH
open Finset GoldbachMajorArc GoldbachBDHSharp.OAI.Ostmann
noncomputable section

def spectrum (n d : ℕ) : ℝ := ∑ a ∈ num d, ‖primeSum n ((a:ℝ)/d)‖^2

lemma spectrum_nonneg (n d : ℕ) : 0 ≤ spectrum n d := sum_nonneg fun _ _ => sq_nonneg _

def weightEnergy (n : ℕ) : ℝ := ∑ k ∈ range (n+1), (primeWeight k)^2

lemma energy_bound (n : ℕ) (hn : 1≤n) : weightEnergy n ≤ Real.log 4 * n * Real.log n := by
  have hL := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
  have hpt (k : ℕ) (hk : k∈range (n+1)) : (primeWeight k)^2 ≤ primeWeight k*Real.log n := by
    unfold primeWeight
    split_ifs with hp
    · rw [sq]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show k≤n by simpa using hk)))
        (Real.log_nonneg (by exact_mod_cast hp.one_le))
    · simp
  have hs : (∑ k ∈ range (n+1), primeWeight k)=Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range,sum_filter]; rfl
  calc
    _ ≤ ∑ k ∈ range (n+1), primeWeight k*Real.log n := sum_le_sum hpt
    _ = Chebyshev.theta n*Real.log n := by rw [←sum_mul,hs]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) hL

lemma shifted_spectrum (n Y : ℕ) (hY : 0<Y) (β : ℝ) :
    (∑ d ∈ Icc 1 Y, ∑ a ∈ num d, ‖primeSum n (β+(a:ℝ)/d)‖^2) ≤ ((n:ℝ)+1+(Y:ℝ)^2)*weightEnergy n := by
  classical
  let pairs := (Icc 1 Y).sigma num
  let x : pairs → ℝ := fun p => β+(p.val.2:ℝ)/p.val.1
  let δ := 1/(Y:ℝ)^2
  have hd : 0<δ := by dsimp [δ]; positivity
  have hsep : CircleSeparated x δ := by
    rintro ⟨⟨d,a⟩,ha⟩ ⟨⟨e,b⟩,hb⟩ hne t
    obtain ⟨hd1,ha'⟩ := mem_sigma.mp ha
    obtain ⟨he1,hb'⟩ := mem_sigma.mp hb
    change δ ≤ |(β+(a:ℝ)/d)-(β+(b:ℝ)/e)-t|
    rw [add_sub_add_left_eq_sub]
    apply farey_sep Y a b d e (mem_Icc.mp hd1).1 (mem_Icc.mp hd1).2
      (mem_Icc.mp he1).1 (mem_Icc.mp he1).2 (mem_filter.mp ha').2 (mem_filter.mp hb').2 _ t
    by_contra! hh
    obtain ⟨de,numEq⟩ := hh
    rw [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha').1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hb').1)] at numEq
    subst e; change a=b at numEq; subst b; exact hne rfl
  have hs := separated_additive_sieve x δ hd hsep (n+1) 0 (fun k => (primeWeight k.val:ℂ))
  have hphase (k : Fin (n+1)) (p : pairs) :
      sieveHalfPhase (2*(0+(k.val:ℝ))*x p) = phase ((k.val:ℝ)*x p) := by
    unfold sieveHalfPhase phase; congr 2; ring
  simp_rw [hphase] at hs
  have hs1 (p : pairs) :
      (∑ k : Fin (n+1), (primeWeight k.val:ℂ)*phase ((k.val:ℝ)*x p))=primeSum n (x p) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => (primeWeight k:ℂ)*phase ((k:ℝ)*x p)) (n+1)
  simp_rw [hs1] at hs
  have he : (∑ k:Fin (n+1), ‖(primeWeight k.val:ℂ)‖^2) = weightEnergy n := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖(primeWeight k:ℂ)‖^2)]
    simp [weightEnergy,Real.norm_eq_abs]
  rw [he] at hs
  have hconst : (((n+1:ℕ):ℝ)+1/δ) = (n:ℝ)+1+(Y:ℝ)^2 := by dsimp [δ]; push_cast; field_simp
  rw [hconst] at hs
  calc
    _ = ∑ p ∈ pairs, ‖primeSum n (β+(p.2:ℝ)/p.1)‖^2 := by
      dsimp [pairs]; rw [sum_sigma']
    _ = ∑ p : pairs, ‖primeSum n (x p)‖^2 := (sum_attach pairs _).symm
    _ ≤ _ := hs
end
end GoldbachBDH

namespace FrontierBand
open Finset MeasureTheory GoldbachMajorArc GoldbachBDH

def bandSet (Q n A B : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, A<q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (Q:ℝ)/((q:ℝ)*n)}

noncomputable def actualBand (Q n A B : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (bandSet Q n A B).indicator
    (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t

private lemma actualIntegralBound (Q n A B : ℕ) (hA : 1≤A) (hB : 0<B) (hn : 2≤n) :
    ‖actualBand Q n A B‖ ≤
      2*((Q:ℝ)/((A:ℝ)*n))*(((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
  classical
  let g := fun t => ‖primeSum n t‖^2
  have cg : Continuous g := by dsimp [g,primeSum,phase]; fun_prop
  let R := (Q:ℝ)/((A:ℝ)*n)
  have hR : 0≤R := by dsimp [R]; positivity
  let center := fun q a : ℕ => (a:ℝ)/q
  let F := fun (q a : ℕ) => (Set.Icc (center q a-R) (center q a+R)).indicator g
  have hF (q a : ℕ) : Integrable (F q a) volume :=
    (cg.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hp (q a : ℕ) (t : ℝ) : 0≤F q a t := by
    by_cases h : t ∈ Set.Icc (center q a-R) (center q a+R)
    · simpa only [F, Set.indicator_of_mem h] using sq_nonneg ‖primeSum n t‖
    · simp [F,h]
  let G := fun t => ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, F q a t
  have hGi : Integrable G volume := integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun a _ => hF q a
  have hGp (t : ℝ) : 0≤G t := sum_nonneg fun q _ => sum_nonneg fun a _ => hp q a t
  have hdom (t : ℝ) : ‖(bandSet Q n A B).indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ ≤ G t := by
    by_cases ht : t∈bandSet Q n A B
    · rw [Set.indicator_of_mem ht,norm_mul,norm_pow,bandPhase_norm,mul_one]
      obtain ⟨q,a,haq,hqb,ha,hcop,hnear⟩ := ht
      have hq : q∈Finset.Icc 1 B := mem_Icc.mpr ⟨by omega,hqb⟩
      have ha' : a∈num q := by
        refine mem_filter.mpr ⟨mem_range.mpr ?_,hcop⟩
        by_contra! hh
        have heq := Nat.le_antisymm ha hh
        have := (Nat.coprime_self q).mp (heq ▸ hcop)
        omega
      have hrad : (Q:ℝ)/((q:ℝ)*n) ≤ R :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg Q) (by positivity) (by gcongr)
      have htF : t∈Set.Icc (center q a-R) (center q a+R) := by
        have h := abs_le.mp (hnear.trans hrad)
        change center q a-R ≤ t ∧ t ≤ center q a+R
        dsimp [center] at *
        constructor <;> linarith [h.1,h.2]
      change g t ≤ _
      calc
        _ = F q a t := (Set.indicator_of_mem htF g).symm
        _ ≤ ∑ b ∈ num q, F q b t := single_le_sum (fun b _ => hp q b t) ha'
        _ ≤ _ := single_le_sum (fun r _ => sum_nonneg fun b _ => hp r b t) hq
    · simpa [ht] using hGp t
  have htranslate (q a : ℕ) :
      (∫ t, F q a t) = ∫ β in -R..R, g (β+center q a) := by
    rw [intervalIntegral.integral_comp_add_right,intervalIntegral.integral_of_le (by linarith)]
    unfold F
    rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
    congr 1 <;> congr 1 <;> ring
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖(bandSet Q n A B).indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t, G t := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hGi.integrableOn (Filter.Eventually.of_forall hdom)).trans
        (setIntegral_le_integral hGi (Filter.Eventually.of_forall hGp))
    _ = ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, ∫ β in -R..R, g (β+center q a) := by
      unfold G
      rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun a _ => hF q a)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun a _ => hF q a)]
      simp_rw [htranslate]
    _ = ∫ β in -R..R, ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, g (β+center q a) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro q _
        rw [intervalIntegral.integral_finsetSum]
        exact fun a _ => (cg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
      · intro q _
        apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => cg.comp (continuous_id.add continuous_const)
    _ ≤ ∫ _β in -R..R, (((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
          cg.comp (continuous_id.add continuous_const)
      · exact continuous_const.intervalIntegrable _ _
      · exact fun t _ => shifted_spectrum n B hB t
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; dsimp [R]; ring

theorem actualBound (Q n A B : ℕ) (hA : 1≤A) (hB : 0<B) (hBn : B^2≤n) (hn : 2≤n) :
    ‖actualBand Q n A B‖ ≤ 24*(n:ℝ)*Q*(1+Real.log n)^2/A := by
  have h := actualIntegralBound Q n A B hA hB hn
  have he := energy_bound n (by omega)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  have hx : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : (0:ℝ)<A := by exact_mod_cast (show 0<A by omega)
  have hc : (n:ℝ)+1+(B:ℝ)^2 ≤ 3*n := by
    have hb : (B:ℝ)^2 ≤ n := by exact_mod_cast hBn
    linarith [show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)]
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have he' : weightEnergy n ≤ 3*n*Real.log n := he.trans (by gcongr)
  have he0 : 0≤weightEnergy n := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ _ := h
    _ ≤ 2*((Q:ℝ)/((A:ℝ)*n))*((3*n)*(3*n*Real.log n)) := by
      gcongr
    _ = 18*(n:ℝ)*Q*Real.log n/A := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ha.le
      have he'' : 18*Real.log n ≤ 24*(1+Real.log n)^2 := by nlinarith [sq_nonneg (Real.log (n:ℝ))]
      nlinarith only [mul_le_mul_of_nonneg_left he'' (mul_nonneg hx.le (Nat.cast_nonneg Q))]
end FrontierBand

namespace FrontierBand
open Finset GoldbachMajorArc
noncomputable section

def modelBand (Q n A B : ℕ) : ℂ :=
  ∑ q ∈ Ioc A B, ∑ a ∈ (range (q+1)).filter (fun a => Nat.Coprime a q),
    intervalIntegral (fun t => (((∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
      phase ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) *
      (∑ k ∈ range (n+1), phase ((k:ℝ)*(t-(a:ℝ)/(q:ℝ)))))^2 * phase (-(n:ℝ)*t))
      ((a:ℝ)/(q:ℝ) - (Q:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume

private lemma ramNorm (q a : ℕ) (hq : 0<q) (ha : a.Coprime q) :
    ‖∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)‖ ≤ 1 := by
  have he : (∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) =
      (ArithmeticFunction.moebius q:ℂ) := by
    rw [← bandRamanujan q a hq ha]
    apply sum_congr rfl
    intro r _
    unfold phase
    congr 3
    ring
  rw [he,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=q)

private lemma modelOne (Q n A q a : ℕ) (hn : 2≤n) (hA : 1≤A) (haq : A<q) (ha : a.Coprime q) :
    ‖intervalIntegral (fun t => (((∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) / (q.totient:ℂ)) *
      (∑ k ∈ range (n+1), phase ((k:ℝ)*(t-(a:ℝ)/q))))^2 * phase (-(n:ℝ)*t))
      ((a:ℝ)/q - Q/((q:ℝ)*n)) ((a:ℝ)/q + Q/((q:ℝ)*n)) MeasureTheory.volume‖ ≤
    (16*(n:ℝ)*Q/A)/(q.totient:ℝ)^2 := by
  have hq : 0<q := by omega
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hA' : (0:ℝ)<A := by exact_mod_cast hA
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hQ : 0≤(Q:ℝ) := by positivity
  let R := (Q:ℝ)/((q:ℝ)*n)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have point (t : ℝ) :
      ‖(((∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) / (q.totient:ℂ)) *
        (∑ k ∈ range (n+1), phase ((k:ℝ)*(t-(a:ℝ)/q))))^2 * phase (-(n:ℝ)*t)‖ ≤
        ((n+1:ℝ)/(q.totient:ℝ))^2 := by
    simp only [norm_mul,norm_pow,norm_div,bandPhase_norm,mul_one,Complex.norm_natCast]
    have hK : ‖∑ k ∈ range (n+1), phase ((k:ℝ)*(t-(a:ℝ)/q))‖ ≤ (n:ℝ)+1 :=
      (norm_sum_le ..).trans (by simp)
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ ≤ (1/(q.totient:ℝ))*((n:ℝ)+1) := by gcongr; exact ramNorm q a hq ha
      _ = _ := by ring
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => point t)
      (a:=(a:ℝ)/q-R) (b:=(a:ℝ)/q+R)
  rw [show (a:ℝ)/q+R-((a:ℝ)/q-R)=2*R by ring,abs_of_nonneg (by positivity)] at hh
  apply hh.trans
  have hn1 : ((n:ℝ)+1)^2 ≤ 4*(n:ℝ)^2 := by nlinarith [show (1:ℝ) ≤ n by exact_mod_cast (show 1≤n by omega)]
  have hcut : (A:ℝ)≤q := by exact_mod_cast haq.le
  dsimp [R]
  field_simp
  calc
    _ ≤ (4*(n:ℝ)^2)*2*Q*A := by gcongr
    _ ≤ (4*(n:ℝ)^2)*2*Q*q := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (n:ℝ)) hQ) hq'.le]

theorem modelBound (Q n A B : ℕ) (hA : 1≤A) (hBn : B^2≤n) (hn : 2≤n) :
    ‖modelBand Q n A B‖ ≤ 16*(n:ℝ)*Q*(1+Real.log n)^2/A := by
  classical
  let C := 16*(n:ℝ)*Q/A
  have hC : 0≤C := by dsimp [C]; positivity
  have hb (q : ℕ) (hq : q∈Ioc A B) :
      ((range (q+1)).filter (fun a => Nat.Coprime a q)).card=q.totient := by
    have hq2 : 1<q := lt_of_le_of_lt hA (mem_Ioc.mp hq).1
    rw [range_add_one,filter_insert]
    simp [Nat.coprime_self,Nat.totient_eq_card_coprime,Nat.coprime_comm (n:=q),show q≠1 by omega]
  calc
    ‖modelBand Q n A B‖ ≤ ∑ q ∈ Ioc A B, C*(1/(q.totient:ℝ)) := by
      unfold modelBand
      refine (norm_sum_le ..).trans <| sum_le_sum fun q hq => ?_
      refine (norm_sum_le ..).trans ?_
      calc
        _ ≤ ∑ _a ∈ (range (q+1)).filter (fun a => Nat.Coprime a q), C/(q.totient:ℝ)^2 :=
          sum_le_sum fun a ha => modelOne Q n A q a hn hA (mem_Ioc.mp hq).1 (mem_filter.mp ha).2
        _ = _ := by
          have hφ : (q.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (show 0<q by have := (mem_Ioc.mp hq).1; omega)).ne'
          simp [hb q hq]
          field_simp
    _ ≤ C*∑ q ∈ Icc 1 B, 1/(q.totient:ℝ) := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ hC
      exact sum_le_sum_of_subset_of_nonneg (fun q hq => mem_Icc.mpr ⟨hA.trans (mem_Ioc.mp hq).1.le,(mem_Ioc.mp hq).2⟩) (fun _ _ _ => by positivity)
    _ ≤ C*(1+Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply (GoldbachEstermann.sum_inv_totient_le B).trans
      apply pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg B])
      apply add_le_add_right
      by_cases hB : B=0
      · simp [hB,Real.log_natCast_nonneg]
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hB) (by exact_mod_cast (show B≤n by nlinarith [Nat.mul_le_mul_left B (Nat.pos_of_ne_zero hB)]))
    _ = _ := by dsimp [C]; ring
end
end FrontierBand

open Filter

namespace FrontierBand

private theorem hpLog (n : ℕ) (hn : 2≤n) :
    (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
  have hb := Real.natLog_le_logb (n+2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2:ℝ)≤n := by exact_mod_cast hn
  have hh : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤(n:ℝ)-2 by linarith) (show 0≤(n:ℝ)+1 by linarith)]
  have hl := Real.log_le_log (by positivity : 0<(n:ℝ)+2) hh
  rw [Real.log_pow] at hl
  norm_num at hl
  have hx' := (le_div_iff₀ (by linarith : 0<Real.log 2)).mp hb
  have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_)
  linarith only [hl,hx',hm]

private theorem thresholdBudget (e u : ℝ) (n : ℕ) (he : 0<e) (hu : 2≤u) (hn : 2≤n)
    (hlog : 1≤Real.log n) (hsmall : (Real.log n)^4 ≤ (e/6000)*u) :
    40*(n:ℝ)*((Nat.log 2 (n+2))^2:ℕ)*(1+Real.log n)^2/(⌊u⌋₊:ℝ) ≤ e*n := by
  have hl := hpLog n hn
  have hp : (0:ℝ) < (⌊u⌋₊:ℕ) := by exact_mod_cast Nat.floor_pos.mpr (by linarith : 1≤u)
  have hf := Nat.lt_floor_add_one u
  have hfn : (1:ℝ) ≤ (⌊u⌋₊:ℕ) := by exact_mod_cast Nat.floor_pos.mpr (by linarith : 1≤u)
  have hu' : u ≤ 2*(⌊u⌋₊:ℕ) := by linarith
  have hQ := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_) hl 2
  have hL := pow_le_pow_left₀ (show 0≤1+Real.log n by linarith) (show 1+Real.log n≤2*Real.log n by linarith) 2
  have hmul := mul_le_mul hQ hL (sq_nonneg _) (sq_nonneg _)
  apply (div_le_iff₀ hp).2
  push_cast
  have he' := mul_le_mul_of_nonneg_left hu' he.le
  have hfac : 40*((Nat.log 2 (n+2):ℝ)^2*(1+Real.log n)^2) ≤ e*(⌊u⌋₊:ℕ) := by nlinarith only [hmul,hsmall,he',mul_nonneg he.le (by positivity : 0≤u)]
  nlinarith only [mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg n : (0:ℝ)≤_)]

theorem polynomialBudget (e : ℝ) (he : 0<e) : ∀ᶠ n : ℕ in atTop,
    40*(n:ℝ)*((Nat.log 2 (n+2))^2:ℕ)*(1+Real.log n)^2/(⌊(n:ℝ)^(1/10:ℝ)⌋₊:ℝ) ≤ e*n := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp ht
  have hc := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ)<1/10)).comp_tendsto ht).bound (by positivity : 0<e/6000)
  filter_upwards [eventually_ge_atTop (2:ℕ),(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,hpow.eventually_ge_atTop 2,hc] with n hn hlog hu hs
  apply thresholdBudget e ((n:ℝ)^(1/10:ℝ)) n he hu hn hlog
  change ‖Real.log n^(4:ℝ)‖ ≤ (e/6000)*‖(n:ℝ)^(1/10:ℝ)‖ at hs
  simpa only [Real.rpow_ofNat,Real.norm_of_nonneg (by positivity : 0≤(Real.log n)^4),
    Real.norm_of_nonneg (by positivity : 0≤(n:ℝ)^(1/10:ℝ))] using hs

theorem exponentialBudget (e : ℝ) (he : 0<e) : ∀ᶠ n : ℕ in atTop,
    40*(n:ℝ)*((Nat.log 2 (n+2))^2:ℕ)*(1+Real.log n)^2/(⌊Real.exp (Real.sqrt (Real.log (n:ℝ)))⌋₊:ℝ) ≤ e*n := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hr := Real.tendsto_sqrt_atTop.comp ht
  have hu := Real.tendsto_exp_atTop.comp hr
  have hc := ((isLittleO_rpow_exp_atTop 8).comp_tendsto hr).bound (by positivity : 0<e/6000)
  filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually_ge_atTop 1,hu.eventually_ge_atTop 2,hc] with n hn hlog hu' hs
  apply thresholdBudget e _ n he hu' hn hlog
  let t := Real.sqrt (Real.log (n:ℝ))
  change ‖t^(8:ℝ)‖ ≤ (e/6000)*‖Real.exp t‖ at hs
  rw [Real.rpow_ofNat,Real.norm_of_nonneg (by positivity : 0≤t^8),
    Real.norm_of_nonneg (Real.exp_pos _).le] at hs
  have hp : t^8 = (Real.log n)^4 := by
    rw [show t^8=(t^2)^4 by ring, Real.sq_sqrt (Real.log_natCast_nonneg n)]
  rwa [hp] at hs

theorem denomSquare (n : ℕ) (hn : 2≤n) (s : ℝ) (hs : s*2≤1) :
    ⌊(n:ℝ)^s⌋₊ ^2 ≤ n := by
  have hx : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hp := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n : (0:ℝ)≤_) s)
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊(n:ℝ)^s⌋₊ : (0:ℝ)≤_) hp 2
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)] at hh
  have hcap := Real.rpow_le_rpow_of_exponent_le hx hs
  rw [Real.rpow_one] at hcap
  exact_mod_cast hh.trans hcap
end FrontierBand

namespace FrontierBand
theorem differenceBound (Q n A B : ℕ) (hA : 1≤A) (hB : 0<B) (hBn : B^2≤n) (hn : 2≤n) :
    ‖actualBand Q n A B-modelBand Q n A B‖ ≤ 40*(n:ℝ)*Q*(1+Real.log n)^2/A := by
  calc
    _ ≤ ‖actualBand Q n A B‖+‖modelBand Q n A B‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (actualBound Q n A B hA hB hBn hn) (modelBound Q n A B hA hBn hn)
    _ = _ := by ring
end FrontierBand

theorem PEqualNP.Outside.L_goldbach_frontier_medcore_bv_band :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Qzf := fun n : ℕ => ⌊(n:ℝ)^(1/10:ℝ)⌋₊; let K := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.range (n+1), E ((k:ℝ)*β); let medCoreBand := fun (n A B : ℕ) => intervalIntegral (fun t => {u : ℝ | ∃ q a : ℕ, A < q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧ |u - (a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let modelBand := fun (n A B : ℕ) => ∑ q ∈ Finset.Ioc A B, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), intervalIntegral (fun t => (((∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) * K n (t - (a:ℝ)/(q:ℝ)))^2 * E (-(n:ℝ)*t)) ((a:ℝ)/(q:ℝ) - (Q n:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q n:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qzf n) (Q₁ n) - modelBand n (Qzf n) (Q₁ n)‖ ≤ e * (n : ℝ) := by
  intro w E S Q f A₀ B₀ K actual model e he
  have ht : Filter.Tendsto (fun n : ℕ => (n:ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [Filter.eventually_ge_atTop (2:ℕ),FrontierBand.polynomialBudget e he] with n hn hlim
  intro heven
  let A : ℕ := B₀ n
  let B : ℕ := A₀ n
  have hx : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hA : 1≤A := Nat.floor_pos.mpr (Real.one_le_rpow hx (by norm_num))
  have hB : 0<B := Nat.floor_pos.mpr (Real.one_le_rpow hx (by norm_num))
  have hBn : B^2≤n := FrontierBand.denomSquare n hn _ (by norm_num)
  change ‖FrontierBand.actualBand (Q n) n A B - FrontierBand.modelBand (Q n) n A B‖ ≤ _
  exact (FrontierBand.differenceBound _ _ _ _ hA hB hBn hn).trans hlim
