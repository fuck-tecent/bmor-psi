import Mathlib

/-!
# A common short-window criterion for the full low-modulus skirt

The full range q ≤ log₂(n+2)² and the cube-root outer radius both vary with n.
Theorem 1.2 of D. Koukoulopoulos, Primes in short arithmetic progressions, enters only through the explicit real-integral hypothesis below, with A=18 and epsilon=1/16. Discretization, dyadic summation, all moduli and endpoints, the common short window, and the transfer to the full frozen target are proved here.
The displayed implication takes the short-interval prime distribution estimate as its explicit hypothesis.

The circle-method model, arc geometry and Gallagher estimates below adapt unconditional components
from LogTruSoul, goldbach-proofs PR 2829, cfde193e18afc4e0ffac53868d514142e908cd36,
and its Apache-2.0 source PR 2486, f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f.
The moving-window variance criterion and its specialization to the full skirt are new here.
-/

section GoldbachDeepFourthPrimeDenominator

namespace GoldbachFourthMoment
open Finset

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- Finite character calculation adapted from DFQDZZ, goldbach-proofs PR 316.
theorem full_phase_sum (q h : ℕ) (hq : 0 < q) :
    (∑ a ∈ range q, phase ((h : ℝ) * a / q)) = if q ∣ h then (q : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
      apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
      · intro a ha
        exact mem_univ _
      · intro a ha b hb hab
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
          ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
      · intro x _
        exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
      · intro a _
        have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
        rw [cast_eq, ZMod.stdAddChar_coe]
        dsimp [phase]
        congr 1
        push_cast
        ring
    _ = _ := by
      by_cases hd : q ∣ h
      · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
        simp [hd, hz, ZMod.card]
      · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
        rw [ite_eq_right hd]
        exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)

theorem prime_phase_sum {q : ℕ} (hq : q.Prime) (h : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)) =
      (if q ∣ h then (q : ℂ) else 0) - 1 := by
  have hF : (range q).filter (fun a => a.Coprime q) = range q \ {0} := by
    ext a
    simp only [mem_filter, mem_sdiff, mem_singleton]
    constructor
    · rintro ⟨ha, hc⟩
      refine ⟨ha, ?_⟩
      rintro rfl
      exact hq.ne_one (by simpa using hc)
    · rintro ⟨ha, hz⟩
      refine ⟨ha, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
      exact fun hd => hz (Nat.eq_zero_of_dvd_of_lt hd (mem_range.mp ha))
  have hsub : ({0} : Finset ℕ) ⊆ range q := by simpa using hq.pos
  rw [hF]
  calc
    _ = (∑ a ∈ range q, phase ((h : ℝ) * a / q)) -
        (∑ a ∈ ({0} : Finset ℕ), phase ((h : ℝ) * a / q)) :=
      eq_sub_of_add_eq (sum_sdiff hsub)
    _ = _ := by rw [full_phase_sum q h hq.pos]; simp [phase]

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

noncomputable def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

theorem sum_prime_centers {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n) (β : ℝ) :
    ∑ a ∈ (range q).filter (fun a => a.Coprime q), primeSum n ((a : ℝ) / q + β) =
      -primeSum n β + (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β) := by
  let centers := (range q).filter (fun a => a.Coprime q)
  let term (k : ℕ) := (primeWeight k : ℂ) * phase ((k : ℝ) * β)
  have hphase (k a : ℕ) : (primeWeight k : ℂ) * phase ((k : ℝ) * (a / q + β)) =
      term k * phase ((k : ℝ) * a / q) := by
    rw [show (k : ℝ) * (a / q + β) = (k : ℝ) * a / q + k * β by ring, phase_add]
    dsimp [term]
    ring
  have hterm (k : ℕ) :
      term k * (∑ a ∈ centers, phase ((k : ℝ) * a / q)) =
        -term k + if k = q then (q : ℂ) * term q else 0 := by
    rw [prime_phase_sum hq]
    by_cases hk : k.Prime
    · have hd : q ∣ k ↔ k = q := by
        constructor
        · intro h
          exact ((Nat.dvd_prime hk).mp h).resolve_left hq.ne_one |>.symm
        · rintro rfl
          exact dvd_refl _
      by_cases h : k = q
      · subst k
        rw [ite_eq_left (dvd_refl _), ite_eq_left rfl]
        ring
      · rw [ite_eq_right (fun hh => h (hd.mp hh)), ite_eq_right h]
        ring
    · have hne : k ≠ q := by
        rintro rfl
        exact hk hq
      simp [term, primeWeight, hk, hne]
  unfold primeSum
  simp_rw [hphase]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ k ∈ range (n + 1), term k * ∑ a ∈ centers, phase ((k : ℝ) * a / q)) = _
  simp_rw [hterm, sum_add_distrib, sum_neg_distrib]
  have hqmem : q ∈ range (n + 1) := mem_range.mpr (by omega)
  simp [hqmem, term, primeWeight, hq, mul_assoc]

theorem fourth_power_of_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  let x := ∑ i ∈ s, ‖f i‖
  let y := ∑ i ∈ s, ‖f i‖ ^ 2
  let z := ∑ i ∈ s, ‖f i‖ ^ 4
  let k : ℝ := s.card
  have hx : ‖∑ i ∈ s, f i‖ ≤ x := norm_sum_le _ _
  have h₁ : x ^ 2 ≤ k * y := by
    simpa [x, y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have h₂ : y ^ 2 ≤ k * z := by
    calc
      y ^ 2 ≤ k * ∑ i ∈ s, (‖f i‖ ^ 2) ^ 2 := by
        simpa [y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖ ^ 2)
      _ = k * z := by
        congr 1
        exact sum_congr rfl (fun i _ => by ring)
  change _ ≤ k ^ 3 * z
  calc
    _ ≤ x ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hx 4
    _ = (x ^ 2) ^ 2 := by ring
    _ ≤ (k * y) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = k ^ 2 * y ^ 2 := by ring
    _ ≤ k ^ 2 * (k * z) := mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring


theorem reduced_eq_Ico {q : ℕ} (hq : q.Prime) :
    (range q).filter (fun a => a.Coprime q) = Ico 1 q := by
  ext a
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨?_, ha⟩
    by_contra! hz
    obtain rfl : a = 0 := by omega
    exact hq.ne_one (by simpa using hc)
  · rintro ⟨ha₁, ha₂⟩
    refine ⟨ha₂, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
    intro hd
    have := Nat.eq_zero_of_dvd_of_lt hd ha₂
    omega

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem primeSum_re (n : ℕ) (β : ℝ) : (primeSum n β).re =
    ∑ k ∈ range (n + 1), primeWeight k * Real.cos (2 * Real.pi * (k : ℝ) * β) := by
  unfold primeSum
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    phase, Complex.exp_ofReal_mul_I_re, mul_assoc]

theorem one_prime_denominator {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n)
    (β : ℝ) (hβ : |β| ≤ 1 / (20 * (n : ℝ)))
    (hθ : (n : ℝ) / 4 ≤ ∑ k ∈ range (n + 1), primeWeight k)
    (hsmall : (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) :
    ((n : ℝ) / 16) ^ 4 / (q : ℝ) ^ 3 ≤
      ∑ a ∈ Ico 1 q, ‖primeSum n ((a : ℝ) / q + β)‖ ^ 4 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hq.pos.trans_le hqn
  have hcos (k : ℕ) (hk : k ∈ range (n + 1)) :
      (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) * β) := by
    have hkN : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
    have hangle : |2 * Real.pi * (k : ℝ) * β| ≤ Real.pi / 3 := by
      calc
        _ = 2 * Real.pi * (k : ℝ) * |β| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 2 * Real.pi * (n : ℝ) * (1 / (20 * (n : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkN (by positivity)) hβ
            (abs_nonneg _) (by positivity)
        _ = Real.pi / 10 := by
          field_simp
          ring
        _ ≤ Real.pi / 3 := by linarith [Real.pi_pos]
    calc
      _ = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |2 * Real.pi * (k : ℝ) * β| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle
      _ = _ := Real.cos_abs _
  have hs : (n : ℝ) / 8 ≤ (primeSum n β).re := by
    rw [primeSum_re]
    calc
      _ ≤ (∑ k ∈ range (n + 1), primeWeight k) * (1 / 2 : ℝ) := by linarith
      _ = ∑ k ∈ range (n + 1), primeWeight k * (1 / 2 : ℝ) := by rw [sum_mul]
      _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hcos k hk) (primeWeight_nonneg k)
  let C := Ico 1 q
  let F (a : ℕ) := primeSum n ((a : ℝ) / q + β)
  let Z : ℂ := (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β)
  have hsum : (∑ a ∈ C, F a) = -primeSum n β + Z := by
    simpa only [C, F, ← reduced_eq_Ico hq, Z] using sum_prime_centers hq hqn β
  have hZ : ‖Z‖ = (q : ℝ) * Real.log q := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_le)
    have hphase : ‖phase ((q : ℝ) * β)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [Z, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, hphase, mul_one]
  have hback : ‖primeSum n β‖ ≤ ‖-primeSum n β + Z‖ + ‖Z‖ := by
    simpa only [add_sub_cancel_right, norm_neg] using norm_sub_le (-primeSum n β + Z) Z
  have hnorm : (n : ℝ) / 16 ≤ ‖∑ a ∈ C, F a‖ := by
    have hre : (primeSum n β).re ≤ ‖primeSum n β‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [hZ] at hback
    rw [hsum]
    linarith
  have hC : C.card ≤ q := by
    calc
      _ ≤ (range q).card := card_le_card fun a ha => mem_range.mpr (mem_Ico.mp ha).2
      _ = _ := card_range _
  have hnonneg : 0 ≤ ∑ a ∈ C, ‖F a‖ ^ 4 := sum_nonneg fun _ _ => by positivity
  apply (div_le_iff₀ (pow_pos hqR 3)).2
  change ((n : ℝ) / 16) ^ 4 ≤ (∑ a ∈ C, ‖F a‖ ^ 4) * (q : ℝ) ^ 3
  calc
    _ ≤ ‖∑ a ∈ C, F a‖ ^ 4 := pow_le_pow_left₀ (by positivity) hnorm 4
    _ ≤ (C.card : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 := fourth_power_of_sum_le C F
    _ ≤ (q : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hC) 3) hnonneg
    _ = _ := mul_comm _ _

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeDenominator

section GoldbachDeepFourthPrimeCount

open Filter Finset
open scoped BigOperators

namespace GoldbachFourthMoment

theorem theta_eq_prime_log_sum (n : ℕ) :
    Chebyshev.theta n =
      ∑ k ∈ Finset.range (n + 1), if Nat.Prime k then Real.log (k : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter,
    Nat.range_succ_eq_Icc_zero]

theorem eventually_theta_half : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have h := Chebyshev.isLittleO_psi_sub_theta_id.def (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [h.natCast_atTop, eventually_ge_atTop 7] with n hn h7
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hn'] at hn
  have hlog : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlo := mul_le_mul_of_nonneg_left hlog hn'
  linarith [Chebyshev.psi_ge_of_seven_le h7, (abs_le.mp hn).2]

theorem eventually_theta_quarter : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ Chebyshev.theta n := by
  filter_upwards [eventually_theta_half] with n hn
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem prime_denominators_log_floor :
    ∀ᶠ R : ℕ in atTop,
      (R : ℝ) / 2 ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_theta_half
  filter_upwards [eventually_ge_atTop N] with R hR
  have hR4 : R ≤ 4 * R := by omega
  have hhigh := hN (4 * R) (hR.trans hR4)
  push_cast at hhigh
  have hlow := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg R)
  have hlog : Real.log 4 ≤ (3 / 2 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hlow' := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg R : 0 ≤ (R : ℝ))
  have hsplit : Chebyshev.theta (R : ℝ) +
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) =
        Chebyshev.theta ((4 * R : ℕ) : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive
      (fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0) (Nat.zero_le R) hR4
  push_cast at hsplit
  have hupper :
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
    apply Real.log_le_log (by exact_mod_cast hpPrime.pos)
    exact_mod_cast (Finset.mem_Ioc.mp hpI).2
  linarith

private theorem eventually_log_le_mul_rpow (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_atTop hs).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
    using (le_abs_self (Real.log (n : ℝ))).trans hn

private theorem cube_root_floor_tendsto :
    Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_atTop.2 fun m =>
    ((tendsto_atTop.1 h) (m : ℝ)).mono fun n hn => Nat.le_floor hn

theorem eventually_many_prime_denominators : ∀ᶠ n : ℕ in atTop,
    let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (((Finset.Ioc R (4*R)).filter Nat.Prime).card : ℝ) := by
  filter_upwards [cube_root_floor_tendsto.eventually prime_denominators_log_floor,
    eventually_log_le_mul_rpow (1 / 12) (1 / 8) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hc hlog hn
  let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  change (R : ℝ) / 2 ≤ _ at hc
  change (n : ℝ) ^ (1 / 4 : ℝ) ≤ _
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa using Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 1/3))
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRlo : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (R : ℝ) := by
    have h := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 3 : ℝ))
    change (n : ℝ) ^ (1 / 3 : ℝ) < (R : ℝ) + 1 at h
    linarith
  have hRhi : (R : ℝ) ≤ (n : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hnPos.le _)
      _ ≤ _ := by simpa using
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1)
  have hlogR : Real.log (4 * (R : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith)
        (by nlinarith only [hRhi, hnR, sq_nonneg ((n : ℝ) - 4)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) =
      (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hnPos]
    congr 1
    norm_num
  apply le_of_mul_le_mul_right _ (Real.log_pos (by linarith : 1 < 4 * (R : ℝ)))
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogR (Real.rpow_nonneg hnPos.le _)
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * ((1 / 8 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = (n : ℝ) ^ (1 / 3 : ℝ) / 4 := by rw [← hpow]; ring
    _ ≤ (R : ℝ) / 2 := by linarith
    _ ≤ _ := hc

theorem eventually_small_denominator_log : ∀ᶠ n : ℕ in atTop,
    ∀ q : ℕ, q ≤ 4 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ →
      (q : ℝ) * Real.log (q : ℝ) ≤ (n : ℝ) / 16 := by
  filter_upwards [eventually_log_le_mul_rpow (2 / 3) (1 / 128) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hlog hn
  intro q hq
  rcases q.eq_zero_or_pos with rfl | hqPos
  · simp
    positivity
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hqPos' : 0 < (q : ℝ) := by exact_mod_cast hqPos
  have hqHi : (q : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 3 : ℝ) := calc
    _ ≤ 4 * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hq
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hnPos.le _)) (by norm_num)
  have hqHi' : (q : ℝ) ≤ 4 * (n : ℝ) := hqHi.trans <|
    mul_le_mul_of_nonneg_left
      (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1))
      (by norm_num)
  have hlogq : Real.log (q : ℝ) ≤ 2 * Real.log (n : ℝ) := calc
    _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hqPos'
      (by nlinarith only [hqHi', hnR, sq_nonneg ((n : ℝ) - 4)])
    _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnPos]
    norm_num
  calc
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * Real.log (n : ℝ)) := by
      apply mul_le_mul hqHi hlogq
      · exact Real.log_nonneg (by exact_mod_cast hqPos)
      · positivity
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * ((1 / 128 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) / 16 := by ring
    _ = _ := congrArg (fun x : ℝ => x / 16) hpow

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeCount

section GoldbachWideArcSeparation

open Filter
open scoped Topology

namespace GoldbachWideArcs

/-- The triangle inequality and spacing of rational centers give this general width condition.
    This uses the rational-separation argument from goldbach-proofs PR 153. -/
theorem reduced_centers_eq_of_common_point {n H B q r a b : ℕ} {t : ℝ}
    (hn : 2 * H * B < n) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqB : q ≤ B) (hrB : r ≤ B)
    (hca : a.Coprime q) (hcb : b.Coprime r)
    (ha : |t - (a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n))
    (hb : |t - (b : ℝ)/r| ≤ (H : ℝ)/((r : ℝ)*n)) : q = r ∧ a = b := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H*r + H*q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left H hrB, Nat.mul_le_mul_left H hqB]
  have hradii : (H : ℝ)/(q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r - b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r - b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

theorem eventually_wide_arc_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * Q₁ < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/512 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/512 := hN n hnN
  have hscaled : 512 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 512)).1
      (show Real.log (n : ℝ)^2 < c^2*z/512 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (512 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (512 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 512 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 512 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * Q₁ < n
  rw [show 2 * (256 * Q₁ * Q) * Q₁ = 512 * Q * Q₁^2 by ring]
  exact hnat

end GoldbachWideArcs

end GoldbachWideArcSeparation

section GoldbachDeepFourthGeometry

open Filter
open scoped Topology

private theorem eventuallyExtendedBudget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * (4*Q₁) < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/2048 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/2048 := hN n hnN
  have hscaled : 2048 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2048)).1
      (show Real.log (n : ℝ)^2 < c^2*z/2048 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (2048 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (2048 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 2048 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 2048 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * (4*Q₁) < n
  rw [show 2 * (256 * Q₁ * Q) * (4*Q₁) = 2048 * Q * Q₁^2 by ring]
  exact hnat

open Set

namespace GoldbachFourthGeometry

noncomputable def strip (n q a : ℕ) : Set ℝ :=
  Set.Icc ((a:ℝ)/q - 1/(20*(n:ℝ))) ((a:ℝ)/q + 1/(20*(n:ℝ)))

noncomputable def wide (n R H : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤R ∧ a≤q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}

theorem mem_strip {n q a : ℕ} {t : ℝ} :
    t ∈ strip n q a ↔ |t-(a:ℝ)/q| ≤ 1/(20*(n:ℝ)) := by
  unfold strip
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem center_coprime {q a : ℕ} (hq : q.Prime) (ha : a ∈ Finset.Ico 1 q) :
    a.Coprime q := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha₀ ha₁)).symm

theorem bigger_radius {n q H : ℕ} (hn : 0 < n) (hq : 0 < q) (hqH : q ≤ H) :
    1/(20*(n:ℝ)) ≤ (H:ℝ)/((q:ℝ)*n) := by
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq' : (q:ℝ) ≤ (H:ℝ) := by exact_mod_cast hqH
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hs := mul_le_mul_of_nonneg_right hq' hnr.le
  nlinarith only [hs, mul_nonneg (Nat.cast_nonneg H) hnr.le]

theorem point_in_unit {n q a : ℕ} (hn : 0 < n) (hqn : q ≤ n) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqn' : (q:ℝ) ≤ (n:ℝ) := by exact_mod_cast hqn
  have hδ : 1/(20*(n:ℝ)) ≤ 1/(q:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hq).2
    linarith
  have hlow : 1/(q:ℝ) ≤ (a:ℝ)/q :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₀) hq.le
  have hhigh : (a:ℝ)/q ≤ 1-1/(q:ℝ) := by
    have ht : (a:ℝ)+1≤(q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt ha₁
    calc
      _ ≤ ((q:ℝ)-1)/q := div_le_div_of_nonneg_right (by linarith) hq.le
      _ = _ := by rw [sub_div, div_self hq.ne']
  obtain ⟨h₁,h₂⟩ := abs_le.mp (mem_strip.mp ht)
  exact ⟨by linarith, by linarith⟩

theorem point_outside_wide {n R H q a : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hqR : R < q) (hq4 : q ≤ 4*R) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ (wide n R H)ᶜ := by
  intro hw
  obtain ⟨r,b,hr,hrR,_,hcb,hradius⟩ := hw
  have hnr : 0 < n := by omega
  have hqa := center_coprime hq ha
  have hδ := (mem_strip.mp ht).trans (bigger_radius hnr hq.pos (hq4.trans hH))
  have ⟨heq,_⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr
    hq4 (hrR.trans (by omega)) hqa hcb hδ hradius
  omega

theorem strip_index_unique {n R H q r a b : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hr : r.Prime) (hq4 : q ≤ 4*R) (hr4 : r ≤ 4*R)
    (ha : a ∈ Finset.Ico 1 q) (hb : b ∈ Finset.Ico 1 r) {t : ℝ}
    (htq : t ∈ strip n q a) (htr : t ∈ strip n r b) : q=r ∧ a=b := by
  have hnr : 0 < n := by omega
  exact GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr.pos hq4 hr4
    (center_coprime hq ha) (center_coprime hr hb)
    ((mem_strip.mp htq).trans (bigger_radius hnr hq.pos (hq4.trans hH)))
    ((mem_strip.mp htr).trans (bigger_radius hnr hr.pos (hr4.trans hH)))

theorem eventually_strip_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let R := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      let H := 256 * R * (Nat.log 2 (n+2))^2
      2*H*(4*R) < n ∧ 4*R ≤ H ∧ 4*R ≤ n := by
  obtain ⟨N,hN⟩ := eventuallyExtendedBudget
  refine ⟨N, ?_⟩
  intro n hn R H
  have hbudget : 2*H*(4*R) < n := hN n hn
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hH : 4*R ≤ H := calc
    _ ≤ 256*R := Nat.mul_le_mul_right _ (by decide)
    _ = 256*R*1 := by simp
    _ ≤ H := Nat.mul_le_mul_left _ (by
      have hx := Nat.pow_le_pow_left hlog 2
      simpa using hx)
  have hsize : 4*R ≤ n := by
    by_cases hzero : R=0
    · simp [hzero]
    · have hHp : 1 ≤ H := by omega
      exact (Nat.le_mul_of_pos_left _ (show 0<2*H by omega)).trans hbudget.le
  exact ⟨hbudget,hH,hsize⟩

end GoldbachFourthGeometry

end GoldbachDeepFourthGeometry

section GoldbachDiscreteWindowEstimate

open Finset MeasureTheory
open scoped ComplexConjugate Interval

namespace GoldbachWindow

open GoldbachFourthMoment (phase phase_add)

/-- The finite Fourier series with coefficient list indexed by `range N`. -/
noncomputable def poly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range N, b j * phase ((j : ℝ) * t)

private theorem phase_cont : Continuous phase := by unfold phase; fun_prop

private theorem poly_cont (N : ℕ) (b : ℕ → ℂ) : Continuous (poly N b) := by
  unfold poly
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (phase_cont.comp (by fun_prop))

private theorem phase_int (m : ℤ) : phase (m : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

-- The mode integral uses the same orthogonality as Clrs17, Goldbach PR 158.
private theorem mode_integral (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

private theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem parseval (N : ℕ) (b : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖poly N b t‖^2) = ∑ k ∈ range N, ‖b k‖^2 := by
  let term (k j : ℕ) (t : ℝ) :=
    (conj (b k) * b j) * phase ((((j : ℤ) - (k : ℤ)) : ℝ) * t)
  let cross (t : ℝ) := ∑ k ∈ range N, ∑ j ∈ range N, term k j t
  have hc (k j : ℕ) : Continuous (term k j) := by
    unfold term phase
    fun_prop
  have hcross : Continuous cross := continuous_finsetSum _ fun k _ =>
    continuous_finsetSum _ fun j _ => hc k j
  have hexpand (t : ℝ) : ((‖poly N b t‖^2 : ℝ) : ℂ) = cross t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [poly, cross, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [term]
    simp only [map_mul, phase_conj]
    simp only [Int.cast_natCast]
    rw [show ((j : ℝ) - (k : ℝ)) * t =
      -((k : ℝ) * t) + (j : ℝ) * t by ring, phase_add]
    ring
  have hint : (∫ t in (0 : ℝ)..1, cross t) = (↑(∑ k ∈ range N, ‖b k‖^2) : ℂ) := by
    dsimp only [cross]
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (continuous_finsetSum _ fun j _ => hc k j).intervalIntegrable _ _),
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc k j).intervalIntegrable _ _]
    have hmode (j : ℕ) : (∫ t in (0 : ℝ)..1, term k j t) =
        (conj (b k) * b j) * (if j = k then 1 else 0) := by
      have hm : (∫ t in (0 : ℝ)..1, phase (((j : ℝ) - (k : ℝ)) * t)) =
          if j = k then 1 else 0 := by
        simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Int.ofNat_inj]
          using mode_integral ((j : ℤ) - (k : ℤ))
      unfold term
      rw [intervalIntegral.integral_const_mul]
      exact congrArg ((conj (b k) * b j) * ·) hm
    simp only [hmode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    · intro j _ hne
      simp [hne]
  have hre :
      (∫ t in (0 : ℝ)..1, (cross t).re) = (∫ t in (0 : ℝ)..1, cross t).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_re (hcross.intervalIntegrable (0 : ℝ) 1).1
  calc
    _ = ∫ t in (0 : ℝ)..1, (cross t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hexpand t)
    _ = _ := by rw [hre, hint, Complex.ofReal_re]

/-- The coefficient at frequency `m` after multiplying by the length-`h` box. -/
noncomputable def moving (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ ((range N) ×ˢ (range h)).filter (fun x => x.1 + x.2 = m), b x.1

theorem moving_eq_sum (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) :
    moving N h b m = ∑ k ∈ (range N).filter (fun k => m + 1 - h ≤ k ∧ k ≤ m), b k := by
  classical
  unfold moving
  refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    obtain ⟨⟨hk, hj⟩, heq⟩ := (Finset.mem_filter.mp hx).imp (fun hp => Finset.mem_product.mp hp) id
    have hj' := mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨hk, by omega, by omega⟩
  · intro x hx y hy hxy
    have heqx := (Finset.mem_filter.mp hx).2
    have heqy := (Finset.mem_filter.mp hy).2
    exact Prod.ext hxy (by omega)
  · intro k hk
    obtain ⟨hk', hlo, hhi⟩ := Finset.mem_filter.mp hk
    refine ⟨(k, m - k), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk', mem_range.mpr (by omega)⟩, by omega⟩

theorem poly_moving_mul (N h : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    poly (N + h) (moving N h b) t = poly N b t * poly h (fun _ => 1) t := by
  unfold poly
  have hmaps (x : ℕ × ℕ) (hx : x ∈ (range N) ×ˢ (range h)) :
      x.1 + x.2 ∈ range (N + h) := by
    obtain ⟨hk, hj⟩ := Finset.mem_product.mp hx
    simp only [Finset.mem_range] at hk hj
    exact mem_range.mpr (by omega)
  calc
    _ = ∑ m ∈ range (N + h), ∑ x ∈ ((range N) ×ˢ (range h)).filter
        (fun x => x.1 + x.2 = m), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [moving, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hsum := (Finset.mem_filter.mp hx).2
      have hsumR : (x.1 : ℝ) + x.2 = m := by exact_mod_cast hsum
      rw [← add_mul, hsumR]
    _ = ∑ x ∈ (range N) ×ˢ (range h), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = _ := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
      simp only [one_mul, phase_add, mul_assoc]

private theorem box_lower {h : ℕ} {t : ℝ} (ht : 6 * (h : ℝ) * |t| ≤ 1) :
    (h : ℝ) / 2 ≤ ‖poly h (fun _ => 1) t‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  unfold poly
  simp only [one_mul, Complex.re_sum, phase, Complex.exp_ofReal_mul_I_re]
  calc
    _ = ∑ _ ∈ range h, (1 / 2 : ℝ) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (mem_range.mp hj).le
      have hfac := mul_le_mul_of_nonneg_right hjh (abs_nonneg t)
      have hangle : |2 * Real.pi * ((j : ℝ) * t)| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_mul,
          abs_of_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ))]
        calc
          _ ≤ (2 * Real.pi) * ((h : ℝ) * |t|) := mul_le_mul_of_nonneg_left hfac (by positivity)
          _ ≤ _ := by
            have h' : (h : ℝ) * |t| ≤ 1 / 6 := by linarith only [ht]
            have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ 2 * Real.pi by positivity)
            linarith only [h'']
      rw [← Real.cos_pi_div_three, ← Real.cos_abs (2 * Real.pi * ((j : ℝ) * t))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle

set_option maxHeartbeats 600000 in
/-- A finite version of the low-frequency window estimate, using exact Parseval on one period. -/
theorem low_frequency_le (N h : ℕ) (b : ℕ → ℂ) (δ : ℝ)
    (hpos : 0 < h) (hδ : 0 ≤ δ) (hwidth : 6 * (h : ℝ) * δ ≤ 1) :
    (h : ℝ)^2 / 4 * (∫ t in (-δ)..δ, ‖poly N b t‖^2) ≤
      ∑ m ∈ range (N + h), ‖moving N h b m‖^2 := by
  have hδsmall : δ ≤ 1 / 2 := by
    have hh : (1 : ℝ) ≤ h := by exact_mod_cast hpos
    have hmul := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hmul, hwidth]
  have hre : -δ ≤ δ := by linarith
  have hline (t : ℝ) (ht : t ∈ Set.Icc (-δ) δ) :
      (h : ℝ)^2 / 4 * ‖poly N b t‖^2 ≤ ‖poly (N + h) (moving N h b) t‖^2 := by
    have ht' : |t| ≤ δ := abs_le.mpr ht
    have hb := box_lower ((mul_le_mul_of_nonneg_left ht'
      (by positivity : 0 ≤ 6 * (h : ℝ))).trans hwidth)
    rw [poly_moving_mul, norm_mul, mul_pow]
    have hb' := pow_le_pow_left₀ (by positivity : 0 ≤ (h : ℝ) / 2) hb 2
    rw [show (h : ℝ)^2 / 4 = ((h : ℝ) / 2)^2 by ring, mul_comm]
    exact mul_le_mul_of_nonneg_left hb' (by positivity)
  let F (t : ℝ) := ‖poly (N + h) (moving N h b) t‖^2
  have hF : Continuous F := (poly_cont _ _).norm.pow 2
  have hpolyper : Function.Periodic (poly (N + h) (moving N h b)) 1 := by
    intro t
    unfold poly
    apply Finset.sum_congr rfl
    intro m _
    have hm : phase (m : ℝ) = 1 := by
      simpa only [Int.cast_natCast] using phase_int (m : ℤ)
    rw [mul_add, phase_add, mul_one, hm, mul_one]
  have hper : Function.Periodic F 1 := by
    intro t
    dsimp only [F]
    rw [hpolyper t]
  calc
    _ = ∫ t in (-δ)..δ, (h : ℝ)^2 / 4 * ‖poly N b t‖^2 :=
      (intervalIntegral.integral_const_mul _ (fun t : ℝ => ‖poly N b t‖^2)).symm
    _ ≤ ∫ t in (-δ)..δ, F t :=
      intervalIntegral.integral_mono_on hre
        ((continuous_const.mul ((poly_cont _ _).norm.pow 2)).intervalIntegrable _ _)
        (hF.intervalIntegrable _ _) hline
    _ ≤ ∫ t in (-(1/2):ℝ)..(-(1/2)+1), F t :=
      intervalIntegral.integral_mono_interval (by linarith) hre (by linarith)
        (Filter.Eventually.of_forall (fun _ => by dsimp [F]; positivity)) (hF.intervalIntegrable _ _)
    _ = ∫ t in (0 : ℝ)..1, F t := by
      simpa only [zero_add] using hper.intervalIntegral_add_eq (-(1/2)) 0
    _ = _ := parseval _ _

end GoldbachWindow

end GoldbachDiscreteWindowEstimate

section GoldbachMinorArcAbelTail

open scoped BigOperators

theorem goldbach_geometric_sum_le_inv_twice_round_distance (θ : ℝ) (K : ℕ)
    (hθ : 0 < |θ - (round θ : ℝ)|) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * |θ - (round θ : ℝ)|) := by
  let k : ℤ := round θ
  let d : ℝ := θ - (k : ℝ)
  let z : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
  have hpos : 0 < |d| := hθ
  have habs : |d| ≤ 1 / 2 := abs_sub_round θ
  have hphase : z = Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) := by
    have hsplit :
        (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((2 * Real.pi * d : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [d]
      push_cast
      ring
    dsimp only [z]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  have hsin : 2 * |d| ≤ |Real.sin (Real.pi * d)| := calc
    _ = 2 / Real.pi * |Real.pi * d| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hdenom : 4 * |d| ≤ ‖z - 1‖ := by
    rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d) / 2 = Real.pi * d by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hsin]
  have hunit : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : ‖∑ j ∈ Finset.range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hunit]
  have hscaled : ‖∑ j ∈ Finset.range K, z ^ j‖ * (4 * |d|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)).trans hprod
  have hterm (j : ℕ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) = z^j := by
    have he : (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    simpa only [z, he] using Complex.exp_nat_mul
      ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) j
  simp_rw [hterm]
  change ‖∑ j ∈ Finset.range K, z ^ j‖ ≤ 1 / (2 * |d|)
  apply (le_div_iff₀ (mul_pos (by norm_num) hpos)).2
  nlinarith only [hscaled]


open MeasureTheory

theorem goldbach_periodic_integral_mul_nat
    (g : ℝ → ℝ) (hg : Function.Periodic g 1)
    (hi : IntervalIntegrable g volume 0 1) (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, g ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hg.intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (fun a b => hg.intervalIntegrable₀ (by norm_num) hi a b)
  have hscaled : (∫ t in (0 : ℝ)..(m : ℝ), g t) =
      (m : ℝ) * ∫ t in (0 : ℝ)..1, g t := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] using hperiod
  rw [intervalIntegral.integral_comp_mul_left g hmR, mul_zero, mul_one, hscaled,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmR, one_mul]


open Set

noncomputable def goldbach_round_tail (δ x : ℝ) : ℝ :=
  if δ ≤ |x - (round x : ℝ)| then 1 / |x - (round x : ℝ)| ^ 2 else 0

theorem goldbach_round_tail_periodic (δ : ℝ) : Function.Periodic (goldbach_round_tail δ) 1 := by
  intro x
  simp only [goldbach_round_tail, round_add_one, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]

theorem goldbach_round_tail_integral (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    IntervalIntegrable (goldbach_round_tail δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, goldbach_round_tail δ x) = 2 / δ - 4 := by
  let g := goldbach_round_tail δ
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℤ)
  have hr {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : round x = 0 :=
    round_eq_zero_iff.2 ⟨hx.1.le, hx.2⟩
  have hpow (x : ℝ) : f x = 1 / |x| ^ 2 := by
    simp [f, zpow_neg, sq_abs, one_div]
  have heL : (Ioo (-(1 / 2 : ℝ)) (-δ)).EqOn g f := by
    intro x hx
    have hxr : x < 1 / 2 := by linarith only [hx.2, hδ]
    have hx0 : x < 0 := by linarith only [hx.2, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_neg hx0]; linarith only [hx.2]
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hx.1,hxr⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heR : (Ioo δ (1 / 2 : ℝ)).EqOn g f := by
    intro x hx
    have hxl : -(1 / 2 : ℝ) < x := by linarith only [hx.1, hδ]
    have hx0 : 0 < x := by linarith only [hx.1, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_pos hx0]; exact hx.1.le
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hxl,hx.2⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heC : (Ioo (-δ) δ).EqOn g (fun _ : ℝ => (0 : ℝ)) := by
    intro x hx
    have hx₁ : -(1 / 2 : ℝ) < x := by linarith only [hd, hx.1]
    have hx₂ : x < (1 / 2 : ℝ) := hx.2.trans_le hd
    have hxd : |x| < δ := abs_lt.2 ⟨hx.1, hx.2⟩
    simp only [g, goldbach_round_tail, hr ⟨hx₁,hx₂⟩, Int.cast_zero, sub_zero,
      ite_eq_right hxd.not_ge]
  have hAway (l r : ℝ) (hab : l ≤ r) (h0 : (0 : ℝ) ∉ Icc l r) (he : (Ioo l r).EqOn g f) :
      IntervalIntegrable g volume l r ∧ (∫ x in l..r, g x) = l⁻¹ - r⁻¹ := by
    have hz : (0 : ℝ) ∉ uIcc l r := by simpa only [uIcc_of_le hab] using h0
    have hIf : IntervalIntegrable f volume l r :=
      intervalIntegral.intervalIntegrable_zpow (n := -2) (Or.inr hz)
    refine ⟨hIf.congr_uIoo (by simpa only [uIoo_of_le hab] using he.symm), ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hab he]
    change (∫ x in l..r, x ^ (-2 : ℤ)) = _
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  obtain ⟨hIL,hVL⟩ := hAway (-(1/2)) (-δ) (by linarith only [hd])
    (by intro hz; have hh := (mem_Icc.mp hz).2; linarith only [hh,hδ]) heL
  obtain ⟨hIR,hVR⟩ := hAway δ (1/2) hd
    (by intro hz; have hh := (mem_Icc.mp hz).1; linarith only [hh,hδ]) heR
  have hcent : -δ ≤ δ := by linarith only [hδ]
  have hIC : IntervalIntegrable g volume (-δ) δ :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-δ) δ).congr_uIoo
      (by simpa only [uIoo_of_le hcent] using heC.symm)
  have hVC : (∫ x in -δ..δ, g x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcent heC]
    exact intervalIntegral.integral_zero
  have hp := goldbach_round_tail_periodic δ
  have hiBase : IntervalIntegrable g volume (-(1/2)) (1/2) := hIL.trans (hIC.trans hIR)
  have hBaseEnd : -(1/2 : ℝ) + 1 = 1/2 := by norm_num
  have hInt : IntervalIntegrable g volume 0 1 :=
    hp.intervalIntegrable (by norm_num) (t := -(1/2 : ℝ)) (by simpa only [hBaseEnd] using hiBase) 0 1
  refine ⟨hInt, ?_⟩
  have hperiod := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [show (∫ x in (0 : ℝ)..1, g x) = ∫ x in (-(1/2 : ℝ))..(1/2), g x by
      simpa only [hBaseEnd, zero_add] using hperiod.symm,
      ← intervalIntegral.integral_add_adjacent_intervals hIL (hIC.trans hIR),
      ← intervalIntegral.integral_add_adjacent_intervals hIC hIR,
      hVL, hVC, hVR]
  norm_num [inv_neg, div_eq_mul_inv]
  ring

theorem goldbach_sum_Icc_one_eq_shifted_range {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, f j) = ∑ j ∈ Finset.range K, f (j+1) := by
  symm
  refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro j hj
    obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
    exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rfl

theorem goldbach_exponential_shifted_range_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * ((j+1 : ℕ) : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  have hshift (j : ℕ) : e (j+1) = e 1 * e j := by
    dsimp [e]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hunit : ‖e 1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hs : (∑ j ∈ Finset.range K, e (j+1)) = e 1 * (∑ j ∈ Finset.range K, e j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hshift j)
  change ‖∑ j ∈ Finset.range K, e (j+1)‖ = ‖∑ j ∈ Finset.range K, e j‖
  rw [hs, norm_mul, hunit, one_mul]

theorem goldbach_positive_exponential_prefix_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  rw [goldbach_sum_Icc_one_eq_shifted_range]
  exact goldbach_exponential_shifted_range_norm θ K

theorem goldbach_norm_weighted_prefix_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Monotone w) (hw₀ : ∀ j, 0 ≤ w j) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K, ‖∑ j ∈ Finset.range n, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, w j • a j‖ ≤ 2 * w (K-1) * B := by
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hlead :
      ‖w (K-1) • (∑ j ∈ Finset.range K, a j)‖ ≤ w (K-1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw₀ _)]
    exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (hw₀ _)
  have hrest :
      ‖∑ j ∈ Finset.range (K-1), (w (j+1) - w j) • (∑ i ∈ Finset.range (j+1), a i)‖
        ≤ (w (K-1)-w 0) * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1),
          ‖(w (j+1)-w j) • (∑ i ∈ Finset.range (j+1), a i)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1)-w j)*B := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        have hdiff : 0 ≤ w (j+1)-w j := sub_nonneg.mpr (hw (Nat.le_succ j))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (hprefix (j+1) hj') hdiff
      _ = _ := by rw [← Finset.sum_mul, htel]
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ w (K-1)*B + (w (K-1)-w 0)*B := by exact add_le_add hlead hrest
    _ = (2*w (K-1)-w 0)*B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ (hw₀ 0)) hB

theorem goldbach_log_exponential_prefix_bound (θ B : ℝ) (K : ℕ) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K,
      ‖∑ j ∈ Finset.range n, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖∑ j ∈ Finset.Icc 1 K,
      (Real.log (j : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 * Real.log (K : ℝ) * B := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  let w : ℕ → ℝ := fun j => Real.log ((j+1 : ℕ) : ℝ)
  have hw : Monotone w := by
    intro i j hij
    dsimp [w]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hw₀ (j : ℕ) : 0 ≤ w j :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j + 1))
  have hshifted (n : ℕ) (hn : n ≤ K) :
      ‖∑ j ∈ Finset.range n, e (j+1)‖ ≤ B := by
    calc
      _ = ‖∑ j ∈ Finset.range n, e j‖ := goldbach_exponential_shifted_range_norm θ n
      _ ≤ _ := hprefix n hn
  have hreindex :
      (∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j) =
        ∑ j ∈ Finset.range K, w j • e (j+1) := by
    simpa only [w, Complex.real_smul] using
      goldbach_sum_Icc_one_eq_shifted_range (fun j => (Real.log (j : ℝ) : ℂ) * e j) K
  change ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j‖ ≤ _
  rw [hreindex]
  by_cases hK : K = 0
  · simp [hK]
  · have hterm : w (K-1) = Real.log (K : ℝ) := by
      dsimp [w]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ K)]
    simpa only [hterm] using
      goldbach_norm_weighted_prefix_le (fun j => e (j+1)) w K B hw hw₀ hB hshifted

theorem goldbach_truncated_square_comparison (F : ℝ → ℝ) (hF : Continuous F)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      F t ≤ A * (1 / |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| ^ 2)) :
    (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
  let g := goldbach_round_tail δ
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hiind : IntervalIntegrable (s.indicator F) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi).indicator hs
  obtain ⟨hiUnit, hvalue⟩ := goldbach_round_tail_integral δ hδ hd
  have hp := goldbach_round_tail_periodic δ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiWide : IntervalIntegrable g volume 0 (m : ℝ) :=
    hp.intervalIntegrable₀ one_ne_zero hiUnit 0 (m : ℝ)
  have hiScaled : IntervalIntegrable (fun t => g ((m : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hmR] using hiWide.comp_mul_left (c := (m : ℝ))
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp [g, goldbach_round_tail]; split <;> positivity
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, A * g ((m : ℝ)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hiind (hiScaled.const_mul A)
      intro t ht
      by_cases hb : t ∈ s
      · rw [indicator_of_mem hb]
        dsimp [g]
        rw [goldbach_round_tail, ite_eq_left (hcut t ht hb)]
        exact hpoint t ht hb
      · rw [indicator_of_notMem hb]
        exact mul_nonneg hA (hnonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        goldbach_periodic_integral_mul_nat g hp hiUnit m hm, hvalue]

theorem goldbach_geometric_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.range K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ (1/4 : ℝ) * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF (1/4) (by norm_num) m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    have hgeo := goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) K hpos
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    calc
      _ ≤ (1 / (2 * d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = (1/4 : ℝ) * (1 / d^2) := by
        field_simp [hn.ne']
        ring
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  have hEq : (1/4 : ℝ) * (2/δ - 4) = 1/(2*δ) - 1 := by
    field_simp [hδ.ne']
    ring
  rw [hEq] at hI
  linarith only [hI]

theorem goldbach_positive_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  simp_rw [goldbach_positive_exponential_prefix_norm]
  exact goldbach_geometric_tail_l2 K m hm δ hδ hd s hs hcut

theorem goldbach_log_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 2 * Real.log (K : ℝ)^2 / δ := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  let A : ℝ := Real.log (K : ℝ)^2
  have hA : 0 ≤ A := sq_nonneg _
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF A hA m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    have hgeo := goldbach_log_exponential_prefix_bound ((m : ℝ)*t) (1/(2*d)) K
      (by positivity) (fun n _ => goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) n hpos)
    have hEq : 2 * Real.log (K : ℝ) * (1/(2*d)) = Real.log (K : ℝ)/d := by
      field_simp [hn.ne']
    rw [hEq] at hgeo
    calc
      _ ≤ (Real.log (K : ℝ)/d)^2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = A * (1/d^2) := by dsimp [A]; rw [div_pow,one_div,div_eq_mul_inv]
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  calc
    _ ≤ A * (2/δ - 4) := hI
    _ ≤ A * (2/δ) := mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hA
    _ = _ := by dsimp [A]; ring

end GoldbachMinorArcAbelTail

section FrontierMedcoreModelHelpers

open scoped BigOperators ComplexConjugate

theorem frontierMedcoreWeightedPrefixLower (a w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Antitone w) (hw₀ : ∀ j, 0 ≤ w j)
    (hPrefix : ∀ m ≤ K, -B ≤ ∑ j ∈ Finset.range m, a j) :
    -(B * w 0) ≤ ∑ j ∈ Finset.range K, w j * a j := by
  have hTel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hLast : -B * w (K-1) ≤ w (K-1) * (∑ j ∈ Finset.range K, a j) := by
    rw [mul_comm (-B)]
    exact mul_le_mul_of_nonneg_left (hPrefix K le_rfl) (hw₀ _)
  have hRest :
      (∑ j ∈ Finset.range (K-1),
        (w (j+1) - w j) * (∑ i ∈ Finset.range (j+1), a i)) ≤ (w (K-1) - w 0) * -B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1) - w j) * -B := by
        apply Finset.sum_le_sum
        intro j hj
        have hjK : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        exact mul_le_mul_of_nonpos_left (hPrefix (j+1) hjK)
          (sub_nonpos.mpr (hw (Nat.le_succ j)))
      _ = _ := by rw [← Finset.sum_mul, hTel]
  change -(B * w 0) ≤ ∑ j ∈ Finset.range K, w j • a j
  rw [Finset.sum_range_by_parts]
  simp only [smul_eq_mul]
  calc
    _ = -B * w (K-1) - (w (K-1) - w 0) * -B := by ring
    _ ≤ _ := sub_le_sub hLast hRest

private noncomputable def frontierMedcorePhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem frontierMedcoreKernelReflection (n : ℕ) (β : ℝ) :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let K := ∑ k ∈ Finset.range (n+1), E ((k : ℝ) * β)
    K^2 * E (-(n : ℝ) * β) = (Complex.normSq K : ℂ) := by
  dsimp only
  let F : ℕ → ℂ := fun k => frontierMedcorePhase ((k : ℝ) * β)
  change (∑ k ∈ Finset.range (n+1), F k)^2 * frontierMedcorePhase (-(n : ℝ) * β) =
    (Complex.normSq (∑ k ∈ Finset.range (n+1), F k) : ℂ)
  have hPhaseAdd (x y : ℝ) : frontierMedcorePhase (x + y) =
      frontierMedcorePhase x * frontierMedcorePhase y := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPhaseConj (x : ℝ) : conj (frontierMedcorePhase x) = frontierMedcorePhase (-x) := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hConj : (∑ k ∈ Finset.range (n+1), F k) * frontierMedcorePhase (-(n : ℝ) * β) =
      conj (∑ k ∈ Finset.range (n+1), F k) := by
    rw [Finset.sum_mul, map_sum, ← Finset.sum_range_reflect (fun k => F k * _)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hIdx : n + 1 - 1 - k = n - k := by omega
    rw [hIdx]
    dsimp only [F]
    rw [← hPhaseAdd, hPhaseConj, Nat.cast_sub hk']
    congr 1
    ring
  rw [pow_two, mul_assoc, hConj, Complex.normSq_eq_conj_mul_self, mul_comm]

end FrontierMedcoreModelHelpers

section GoldbachGRHWindowParseval

open scoped BigOperators ComplexConjugate
open Finset

namespace GoldbachGRHWindow

noncomputable section

private theorem norm_energy_of_columns {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

variable {q : ℕ} [NeZero q]

local instance : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

theorem additive_energy (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ r : ZMod q, f r * ZMod.stdAddChar (a * r)‖ ^ 2) =
      (q : ℝ) * ∑ r : ZMod q, ‖f r‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply norm_energy_of_columns (fun r a => ZMod.stdAddChar (a * r)) (fun _ => (q : ℝ))
  intro r s
  have hc (z : ZMod q) : conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [AddChar.map_neg_eq_inv]
    exact (Complex.inv_eq_conj (by simp [ZMod.stdAddChar_apply])).symm
  simp only [hc, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  by_cases h : r = s
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    have hne : -r + s ≠ 0 := by
      simpa only [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr (fun he : s = r => h he.symm) : s - r ≠ 0)
    calc
      _ = ∑ a : ZMod q, ZMod.stdAddChar ((-r + s) * a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm]
      _ = 0 := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hne)

omit [NeZero q] in
private theorem char_conj_of_unit (χ : DirichletCharacter ℂ q) {r : ZMod q}
    (hr : IsUnit r) : conj (χ r) = χ r⁻¹ := by
  have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
  have hi : χ r⁻¹ = (χ r)⁻¹ := by
    calc
      _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr, mul_one]
      _ = _ := by rw [← mul_assoc, ← map_mul, ZMod.inv_mul_of_unit r hr, map_one, one_mul]
  exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)

theorem multiplicative_energy (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2) =
      (q.totient : ℝ) * ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖f r‖ ^ 2 := by
  rw [Finset.sum_filter, Finset.mul_sum]
  have hParseval := norm_energy_of_columns (fun r (χ : DirichletCharacter ℂ q) => χ r)
    (fun r : ZMod q => if IsUnit r then (q.totient : ℝ) else 0)
    (f := f) (by
      intro r s
      by_cases hr : IsUnit r
      · simp only [char_conj_of_unit _ hr, ite_eq_left hr, Complex.ofReal_natCast]
        exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s
      · simp [hr, MulChar.map_nonunit _ hr])
  rw [hParseval]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r <;> simp [hr]

/-- The additive coefficient of the unit-uniform residue distribution. -/
noncomputable def additiveModel (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) / (q.totient : ℂ)

private noncomputable def residueSum (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k

private noncomputable def residueError (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  residueSum I w r - if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0

private theorem sum_residueSum_mul (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, residueSum I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [residueSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _

private theorem sum_if_isUnit (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

private theorem residueError_character (I : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q, residueError I w r * χ r) =
      (∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0) := by
  classical
  unfold residueError
  simp only [sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  have hs : (∑ r : ZMod q, (if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0) * χ r) =
      ((I.card : ℂ) / (q.totient : ℂ)) * (∑ r : ZMod q, χ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : IsUnit r
    · simp [hr]
    · simp [hr, MulChar.map_nonunit χ hr]
  rw [hs]
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, ite_eq_left rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  · rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem residueError_additive (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ r : ZMod q, residueError I w r * ZMod.stdAddChar (a * r)) =
      ∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a) := by
  classical
  simp only [residueError, sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  calc
    _ = ((I.card : ℂ) / (q.totient : ℂ)) *
        (∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a * r) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : IsUnit r <;> simp [hr]
    _ = _ := by
      rw [sum_if_isUnit, Finset.sum_const, nsmul_eq_mul]
      unfold additiveModel
      simp only [div_eq_mul_inv]
      ring

/-- Squared short-window error at all additive numerators, from uniform
    individual character bounds and an absolute mass bound at nonunits. -/
theorem sum_additive_window_error_sq_le (I : Finset ℕ) (w : ℕ → ℂ)
    (B P : ℝ) (_hB : 0 ≤ B) (_hP : 0 ≤ P)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0)‖ ≤ B)
    (hnon : (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖) ≤ P) :
    (∑ a : ZMod q,
      ‖∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a)‖ ^ 2) ≤
      (q : ℝ) * (B ^ 2 + P ^ 2) := by
  classical
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hCard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hUnit : (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖residueError I w r‖ ^ 2) ≤
      B ^ 2 := by
    apply le_of_mul_le_mul_left _ hφ
    rw [← multiplicative_energy]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, B ^ 2 := by
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [residueError_character]
        exact pow_le_pow_left₀ (norm_nonneg _) (hχ χ) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hCard]
  let V : Finset (ZMod q) := univ.filter (fun r => ¬ IsUnit r)
  have hV : (∑ r ∈ V, ‖residueError I w r‖) ≤ P := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr' : ¬ IsUnit r := (Finset.mem_filter.mp hr).2
        simpa [residueError, hr', residueSum] using
          norm_sum_le (I.filter (fun k : ℕ => (k : ZMod q) = r)) w
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
        simp [V]
      _ ≤ _ := hnon
  have hNonUnit : (∑ r ∈ V, ‖residueError I w r‖ ^ 2) ≤ P ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  simp_rw [← residueError_additive]
  rw [additive_energy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (univ : Finset (ZMod q))) (p := IsUnit)]
  exact add_le_add hUnit hNonUnit

/-- The additive kernel written with the phase convention used in the frozen theorem. -/
theorem stdAddChar_mul_nat (a : ZMod q) (k : ℕ) :
    ZMod.stdAddChar (a * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((k : ℝ) * ((a.val : ℝ) / (q : ℝ))) : ℝ) : ℂ) *
        Complex.I) := by
  have ha : (↑(a.val * k) : ZMod q) = a * (k : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (↑(a.val * k) : ℂ) / q) := by
      rw [← ha]
      simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (a.val * k : ℕ)
    _ = _ := by
      congr 1
      push_cast
      ring

/-- Write the character of two natural residues without reducing either natural number. -/
theorem stdAddChar_nat_pair (a k : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (k : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * k : ℕ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- Express the unit-model coefficient as the exact reduced numerator sum
    occurring in the major-arc statements. -/
theorem additiveModel_eq_reduced_sum (a : ℕ) :
    additiveModel q (a : ZMod q) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (((2 * Real.pi * ((a : ℝ) * (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
          Complex.I)) / (q.totient : ℂ) := by
  unfold additiveModel
  congr 1
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hrunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hrunit.unit, Finset.mem_univ _, by
      rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rw [← stdAddChar_nat_pair (q := q) a ((u : ZMod q).val), ZMod.natCast_zmod_val]

/-- A reduced numerator changes only the order of the same unit residues. -/
theorem additiveModel_of_unit (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = additiveModel q 1 := by
  unfold additiveModel
  apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.mulLeft ha.unit
  refine Fintype.sum_equiv e (fun u => ZMod.stdAddChar (a * (u : ZMod q)))
    (fun u => ZMod.stdAddChar (1 * (u : ZMod q))) ?_
  intro u
  change ZMod.stdAddChar (a * (u : ZMod q)) =
    ZMod.stdAddChar (1 * (((ha.unit * u) : (ZMod q)ˣ) : ZMod q))
  rw [one_mul, Units.val_mul, IsUnit.unit_spec]

/-- Prime-logarithmic weights, represented in the complex field. -/
noncomputable def primeLog (k : ℕ) : ℂ :=
  ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ)

/-- A prime in a nonunit residue must divide the modulus. Its total
    logarithmic mass in any window is at most the logarithm of the modulus. -/
theorem primeLog_nonunit_mass_le (I : Finset ℕ) :
    (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖) ≤
      Real.log (q : ℝ) := by
  let J := I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q))
  change (∑ k ∈ J, ‖primeLog k‖) ≤ _
  have hsub : J.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hkJ, hp⟩ := Finset.mem_filter.mp hk
    have hnu := (Finset.mem_filter.mp hkJ).2
    have hd : k ∣ q := by
      by_contra hnd
      exact hnu ((ZMod.isUnit_iff_coprime k q).mpr ((hp.coprime_iff_not_dvd).mpr hnd))
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
  calc
    _ = ∑ k ∈ J.filter Nat.Prime, Real.log (k : ℝ) := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : Nat.Prime k
      · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hp.pos)
        simp only [primeLog, ite_eq_left hp, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hk)]
      · simp [primeLog, hp]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ _ := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

end

end GoldbachGRHWindow

end GoldbachGRHWindowParseval

section GoldbachGRHBandBase

/- The arithmetic foundation is adapted from muxkin's goldbach-proofs PR #2458,
   commit 25c1ef60495052eb22212b5560f90bbc6a4a0917 (Apache-2.0).
   Its source notes attributing earlier components are retained below. -/

/- The finite Ramanujan identities, kernel identities, CRT and prime-power computations
used below adapt DFQDZZ's goldbach-proofs PR #316, commit
e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). Original credits are
retained with the corresponding sections. The multiplicative averaging, sieve estimates,
convolution bounds and the moving-modulus-window argument are derived below. -/

section

/-!
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT
namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor

open Finset

noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]


end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor
noncomputable section

private theorem coprime_prod_factors {p : ℕ} {s : Finset ℕ} (hp : p.Prime)
    (hs : ∀ r∈s, r.Prime) (hps : p∉s) : p.Coprime (∏ r∈s, r) :=
  Nat.coprime_prod_right_iff.mpr (fun r hr => (Nat.coprime_primes hp (hs r hr)).mpr (fun e => hps (e ▸ hr)))

theorem coeff_norm_le (q n : ℕ) (hq : 0<q) :
    ‖coefficient q n‖ ≤ 1/(q.totient:ℝ) := by
  by_cases hsf : Squarefree q
  · suffices H : ∀ s : Finset ℕ, (∀ p∈s, p.Prime) →
        ‖coefficient (∏ p∈s, p) n‖ ≤ 1/((∏ p∈s, p).totient:ℝ) by
      simpa only [Nat.prod_primeFactors_of_squarefree hsf] using H q.primeFactors
        (fun _ h => Nat.prime_of_mem_primeFactors h)
    intro s
    induction s using Finset.induction_on with
    | empty => simp [coefficient_one]
    | @insert p s hp ih =>
      intro hs
      have hprime := hs p (mem_insert_self ..)
      have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
      have hc := coprime_prod_factors hprime hs' hp
      have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).pos
      rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,Nat.cast_mul,norm_mul,
        coefficient_prime hprime, Complex.norm_real,Real.norm_eq_abs]
      have hR : (2:ℝ)≤p := by exact_mod_cast hprime.two_le
      have hp1 : 0≤(p:ℝ)-1 := by linarith
      have hf : |localCoefficient p n| ≤ 1/(p.totient:ℝ) := by
        rw [Nat.totient_prime hprime,Nat.cast_sub hprime.one_le,Nat.cast_one]
        dsimp [localCoefficient]
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_neg,abs_of_nonneg (by positivity)]
          apply one_div_le_one_div_of_le (by linarith)
          nlinarith [mul_nonneg (show 0≤(p:ℝ)-1 by linarith) (show 0≤(p:ℝ)-2 by linarith)]
      exact (mul_le_mul hf (ih hs') (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [coefficient_not_squarefree n hq hsf, norm_zero]; positivity

theorem coeff_bad_prime (p r n : ℕ) (hp : p.Prime) (hpn : ¬p∣n) (hr : 0<r) :
    ‖coefficient (p*r) n‖ ≤ 1/((p:ℝ)-1)^2 * (1/(r.totient:ℝ)) := by
  by_cases hc : p.Coprime r
  · rw [coefficient_mul hp.pos hr hc,norm_mul,coefficient_prime hp,Complex.norm_real,Real.norm_eq_abs,
      localCoefficient,if_neg hpn,abs_neg,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (coeff_norm_le r n hr) (by positivity)
  · have hpr : p∣r := by simpa [hp.coprime_iff_not_dvd] using hc
    have hsf : ¬Squarefree (p*r) := fun h =>
      Nat.squarefree_iff_prime_squarefree.mp h p hp (Nat.mul_dvd_mul_left _ hpr)
    rw [coefficient_not_squarefree n (Nat.mul_pos hp.pos hr) hsf,norm_zero]
    positivity

theorem good_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ p∣n) :
    coefficient (∏ p∈s, p) n = ((1/((∏ p∈s, p).totient:ℝ):ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_pos hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,←Complex.ofReal_mul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem bad_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ ¬p∣n) :
    coefficient (∏ p∈s, p) n =
      (((ArithmeticFunction.moebius (∏ p∈s, p):ℝ)/((∏ p∈s, p).totient:ℝ)^2:ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_neg hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,ArithmeticFunction.moebius_apply_prime hprime,←Complex.ofReal_mul]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem coefficient_factorization (q n : ℕ) (hsq : Squarefree q) (hn : 0<n) :
    ∃ d m : ℕ, q=d*m ∧ d∣n ∧ m.Coprime n ∧
      coefficient q n = (((ArithmeticFunction.moebius m:ℝ)/((d.totient:ℝ)*(m.totient:ℝ)^2):ℝ):ℂ) := by
  classical
  let G := q.primeFactors.filter (fun p => p∣n)
  let B := q.primeFactors \ G
  let d := ∏ p∈G, p
  let m := ∏ p∈B, p
  have hG (p : ℕ) (hp : p∈G) : p.Prime ∧ p∣n := by
    obtain ⟨h1,h2⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,h2⟩
  have hB (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,fun hd => h2 (mem_filter.mpr ⟨h1,hd⟩)⟩
  have hqm : q=d*m := by
    have h := Finset.prod_sdiff (f:=id) (s₁:=G) (s₂:=q.primeFactors) (Finset.filter_subset ..)
    simpa [d,m,B,Nat.prod_primeFactors_of_squarefree hsq,mul_comm] using h.symm
  have hdn : d∣n := by
    have hsub : G ⊆ n.primeFactors := fun p hp => Nat.mem_primeFactors.mpr ⟨(hG p hp).1,(hG p hp).2,hn.ne'⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset G n.primeFactors id hsub) (Nat.prod_primeFactors_dvd n)
  have hmn : m.Coprime n := Nat.coprime_prod_left_iff.mpr fun p hp => (hB p hp).1.coprime_iff_not_dvd.mpr (hB p hp).2
  refine ⟨d,m,hqm,hdn,hmn,?_⟩
  rw [hqm,coefficient_mul (prod_pos (fun p hp => (hG p hp).1.pos)) (prod_pos (fun p hp => (hB p hp).1.pos))
    (hmn.of_dvd_right hdn).symm, show coefficient d n = _ from good_product hG,
    show coefficient m n = _ from bad_product hB,←Complex.ofReal_mul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring
end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction GoldbachExplicitModeledMajor
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section

def smooth (n k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p∣n
instance smoothDec (n k : ℕ) : Decidable (smooth n k) := by unfold smooth; infer_instance

def g (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k=0 then 0 else if smooth n k then 1 else 0,by simp⟩

@[simp] theorem g_one (n : ℕ) : g n 1=1 := by simp [g,smooth]
theorem g_mul (n a b : ℕ) : g n (a*b)=g n a*g n b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : smooth n (a*b) ↔ smooth n a ∧ smooth n b := by
    simp only [smooth,Nat.primeFactors_mul ha hb,mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp),fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x,y⟩ p (h|h)
      · exact x p h
      · exact y p h
  simp only [g,coe_mk, mul_ne_zero ha hb,ha,hb,ite_false]
  by_cases h1 : smooth n a <;> by_cases h2 : smooth n b <;> simp [hs,h1,h2]
theorem g_mult (n : ℕ) : IsMultiplicative (g n) := ⟨g_one n, fun {_ _} _ => g_mul n _ _⟩
theorem g_prime (n p : ℕ) (hp : p.Prime) : g n p=if p∣n then 1 else 0 := by
  simp [g,smooth,hp.ne_zero,hp.primeFactors]

def F (n : ℕ) : ArithmeticFunction ℝ := ⟨fun q => (q:ℝ)*(coefficient q n).re,by simp⟩

theorem coeff_real {q : ℕ} (hq : 0<q) (n : ℕ) : coefficient q n = (((coefficient q n).re:ℝ):ℂ) := by
  by_cases hsf : Squarefree q
  · have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [coefficient_not_squarefree n hq hsf]; simp
theorem F_mult (n : ℕ) : IsMultiplicative (F n) := by
  refine ⟨by simp [F,coefficient_one],fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (coefficient a n).im=0 := by rw [coeff_real ha.bot_lt n]; rfl
  simp [F,coefficient_mul ha.bot_lt hb.bot_lt hab,Complex.mul_re,hzero]
  ring
theorem F_prime (n p : ℕ) (hp : p.Prime) : F n p=(p:ℝ)*localCoefficient p n := by simp [F,coefficient_prime hp]
theorem F_higher (n p j : ℕ) (hp : p.Prime) : F n (p^(j+2))=0 := by simp [F,coefficient_higher_power hp j n]

def invG (n : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (g n)
def h (n : ℕ) : ArithmeticFunction ℝ := invG n * F n

theorem h_mult (n : ℕ) : IsMultiplicative (h n) :=
  (isMultiplicative_moebius.intCast.pmul (g_mult n)).mul (F_mult n)

theorem inverse_id (n : ℕ) : g n * invG n = 1 := by
  ext k
  have heq : (g n*invG n) k = g n k * (((ζ : ArithmeticFunction ℝ)*μ) k) := by
    simp only [ArithmeticFunction.mul_apply,Finset.mul_sum,invG,pmul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    have h0 : 0<ab.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)
    have hG : g n k=g n ab.1*g n ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ g_mul n ab.1 ab.2
    rw [hG]
    simp [zeta_apply,h0.ne']; ring
  rw [heq,coe_zeta_mul_coe_moebius]
  by_cases hk : k=1 <;> simp [ArithmeticFunction.one_apply,hk]
theorem convolution (n : ℕ) : F n = g n*h n := by rw [h,←mul_assoc,inverse_id,one_mul]

theorem h_prime_recurrence (n p j : ℕ) (hp : p.Prime) :
    h n (p^(j+1))=F n (p^(j+1))-g n p*F n (p^j) := by
  let q := p^(j+1)
  have hq : q≠0 := pow_ne_zero _ hp.ne_zero
  let v := fun d : ℕ => invG n d * F n (q/d)
  have hv : h n q = ∑ d ∈ q.divisors, v d := by
    rw [h,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => invG n a * F n b)]
  have h1 : ({1,p}:Finset ℕ) ⊆ q.divisors := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ (by omega),hq⟩
  have hsum : ∑ d ∈ q.divisors,v d = ∑ d ∈ ({1,p}:Finset ℕ),v d := by
    symm; apply sum_subset h1
    intro d hd hn
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    by_cases hi0 : i=0
    · exfalso; apply hn; simp [he,hi0]
    by_cases hi1 : i=1
    · exfalso; apply hn; simp [he,hi1]
    have hm : μ d=0 := by rw [he, moebius_apply_prime_pow hp hi0,if_neg hi1]
    simp [v,invG,pmul_apply,intCoe_apply,hm]
  have hdiv : q/p=p^j := by dsimp [q]; rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
  change h n q = _
  rw [hv,hsum,Finset.sum_insert (by simpa using hp.ne_one.symm : (1:ℕ)∉({p}:Finset ℕ)),Finset.sum_singleton]
  simp [v,invG,pmul_apply,intCoe_apply,moebius_apply_prime hp,hdiv,q]
  ring

theorem h_prime (n p : ℕ) (hp : p.Prime) : h n p =
    if p∣n then 1/((p:ℝ)-1) else -(p:ℝ)/((p:ℝ)-1)^2 := by
  have he := h_prime_recurrence n p 0 hp
  have he1 : F n 1=1 := (F_mult n).map_one
  simp only [Nat.zero_add,pow_one,pow_zero,he1,F_prime n p hp,g_prime n p hp,mul_one] at he
  rw [he]; dsimp [localCoefficient]
  have hr1 : (p:ℝ)-1≠0 := by
    have ht : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  split_ifs <;> field_simp <;> ring
theorem h_square (n p : ℕ) (hp : p.Prime) : h n (p^2) =
    if p∣n then -(p:ℝ)/((p:ℝ)-1) else 0 := by
  have he := h_prime_recurrence n p 1 hp
  rw [F_higher n p 0 hp,pow_one,g_prime n p hp,F_prime n p hp] at he
  rw [he]; dsimp [localCoefficient]; split_ifs <;> ring
theorem h_cube (n p j : ℕ) (hp : p.Prime) : h n (p^(j+3))=0 := by
  have he := h_prime_recurrence n p (j+2) hp
  rw [F_higher n p j hp,show j+2+1=(j+1)+2 by omega,F_higher n p (j+1) hp] at he
  simpa [show j+2+1=j+3 by omega] using he

end
end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

private theorem pairPos {q : ℕ} {v : ℕ × ℕ} (hv : v ∈ q.divisorsAntidiagonal) : 0<v.1 ∧ 0<v.2 :=
  ⟨Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hv),
   Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)⟩

theorem unpair (U : ℕ) (F : ℕ×ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ q ∈ Icc 1 U, ∑ v ∈ q.divisorsAntidiagonal, F v) ≤
      ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := by
  classical
  let S := Icc 1 U
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro h; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp h).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), F v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), F v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ v ∈ S ×ˢ S, F v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => hF v)
    _ = _ := Finset.sum_product _ _ _

theorem invSquares (U : ℕ) : (∑ k ∈ Icc 1 U, ((k:ℝ)^2)⁻¹) ≤ 2 := by
  rcases U with _ | u
  · simp
  · have hUU : 1≤u+1 := by omega
    have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) (by decide : 1 ≠ 0) hUU
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hUU]
    norm_num at H ⊢
    linarith [show 0 ≤ ((u:ℝ)+1)⁻¹ by positivity]

theorem scaledInvSquares (X v U : ℕ) (hv : 0<v) :
    (X:ℝ) * (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2*v := by
  by_cases h : X<v
  · have hc : (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2 :=
      (sum_le_sum fun k _ => by split_ifs <;> first | rfl | positivity).trans (invSquares U)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans (by exact_mod_cast (by omega : X*2 ≤ 2*v))
  have hm : 0<X/v := Nat.div_pos (by omega) hv
  have he : ∑ k ∈ Icc 1 U, (if X<v*k then ((k:ℝ)^2)⁻¹ else 0) =
      ∑ k ∈ Ioc (X/v) U, ((k:ℝ)^2)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter,mem_Icc,mem_Ioc,Nat.div_lt_iff_lt_mul hv]
    constructor <;> rintro h
    · exact ⟨by simpa [mul_comm] using h.2,h.1.2⟩
    · exact ⟨⟨by cases k <;> simp_all, h.2⟩,by simpa [mul_comm] using h.1⟩
  rw [he]
  by_cases hU : X/v≤U
  · have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) hm.ne' hU
    have hc := H.trans (sub_le_self _ (by positivity))
    have hlim := Nat.div_add_mod X v
    have hmod := Nat.mod_lt X hv
    have hle : X ≤ 2*v*(X/v) := by nlinarith only [hlim,hmod,Nat.mul_le_mul_left v hm]
    have hr : 0<((X/v:ℕ):ℝ) := by exact_mod_cast hm
    refine (mul_le_mul_of_nonneg_left hc (by positivity : 0≤(X:ℝ))).trans ?_
    rw [←div_eq_mul_inv,div_le_iff₀ hr]
    exact_mod_cast hle
  · simp [Finset.Ioc_eq_empty_of_le (by omega : U≤X/v)]

theorem totient_series (U : ℕ) : (∑ q ∈ Icc 1 U, 1/((q:ℝ)*q.totient)) ≤ 4 := by
  let F := fun ab : ℕ×ℕ => ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹
  calc
    _ ≤ ∑ q ∈ Icc 1 U, ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
      apply sum_le_sum
      intro q hq
      have hq0 := (mem_Icc.mp hq).1
      have hφ := Nat.totient_pos.mpr hq0
      have hcount : q ≤ q.divisors.card*q.totient := calc
        _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
        _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum fun d hd => Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
        _ = _ := by simp
      calc
        _ ≤ (q.divisors.card:ℝ)/(q:ℝ)^2 := by
          have hr : (0:ℝ)<q := by exact_mod_cast hq0
          have hφr : (0:ℝ)<q.totient := by exact_mod_cast hφ
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hc : (q:ℝ)≤q.divisors.card*q.totient := by exact_mod_cast hcount
          nlinarith only [mul_le_mul_of_nonneg_left hc hr.le]
        _ = ∑ ab ∈ q.divisorsAntidiagonal, ((q:ℝ)^2)⁻¹ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => ((q:ℝ)^2)⁻¹)]; simp [div_eq_mul_inv]
        _ = _ := by
          apply sum_congr rfl; intro ab hab
          dsimp [F]
          rw [←(Nat.mem_divisorsAntidiagonal.mp hab).1,Nat.cast_mul,mul_pow,mul_inv]
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := unpair U F (by intro x; dsimp [F]; positivity)
    _ = (∑ a ∈ Icc 1 U, ((a:ℝ)^2)⁻¹)^2 := by dsimp [F]; rw [sq,Finset.sum_mul_sum]
    _ ≤ 4 := by
      have h := pow_le_pow_left₀ (by exact sum_nonneg (fun _ _ => by positivity)) (invSquares U) 2
      norm_num at h ⊢; exact h

theorem totient_tail (X v U : ℕ) (hv : 0<v) :
    (X:ℝ)*(∑ q ∈ Icc 1 U, if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ 8*v := by
  let F := fun ab : ℕ×ℕ => (1 / ((ab.1:ℝ)^2*ab.1.totient)) *
      (if X<v*ab.1*ab.2 then ((ab.2:ℝ)^2)⁻¹ else 0)
  have hF (x : ℕ×ℕ) : 0≤F x := by dsimp [F]; split_ifs <;> positivity
  have hh (q : ℕ) (hq : q ∈ Icc 1 U) :
      (if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    by_cases h : X<v*q
    · rw [if_pos h]
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hφR : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have he : ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ) = (q:ℝ) := by
        exact_mod_cast (by rw [Nat.sum_divisorsAntidiagonal (fun (_ : ℕ) (b : ℕ) => b.totient), Nat.sum_div_divisors]; exact Nat.sum_totient q : ∑ ab ∈ q.divisorsAntidiagonal, ab.2.totient=q)
      calc
        _ = (∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ))/((q:ℝ)^2*q.totient) := by rw [he]; field_simp
        _ = ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ)/((q:ℝ)^2*q.totient) := Finset.sum_div _ _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro ab hab
          obtain ⟨ha,hb⟩ := pairPos hab
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
          have habR : (ab.1:ℝ)*ab.2=q := by exact_mod_cast hprod
          have hφa : (0:ℝ)<ab.1.totient := by exact_mod_cast Nat.totient_pos.mpr ha
          have hbR : (0:ℝ)<ab.2 := by exact_mod_cast hb
          have haR : (0:ℝ)<ab.1 := by exact_mod_cast ha
          have hs := Nat.totient_super_multiplicative ab.1 ab.2
          rw [hprod] at hs
          have hs' : (ab.1.totient:ℝ)*ab.2.totient≤q.totient := by exact_mod_cast hs
          dsimp [F]
          rw [mul_assoc,hprod,if_pos h]
          rw [←habR,mul_pow]
          field_simp
          nlinarith only [hs']
    · rw [if_neg h]; exact sum_nonneg fun ab _ => hF ab
  calc
    _ ≤ (X:ℝ)*(∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b)) :=
      mul_le_mul_of_nonneg_left ((sum_le_sum hh).trans (unpair U F hF)) (by positivity)
    _ = ∑ a ∈ Icc 1 U, (1 / ((a:ℝ)^2*a.totient)) *
        ((X:ℝ) * ∑ b ∈ Icc 1 U, if X<(v*a)*b then ((b:ℝ)^2)⁻¹ else 0) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl; intro a _
      dsimp [F]
      rw [←Finset.mul_sum]; ring
    _ ≤ ∑ a ∈ Icc 1 U, 2*(v:ℝ)*(1/((a:ℝ)*a.totient)) := by
      apply sum_le_sum; intro a ha
      have ha0 := (Finset.mem_Icc.mp ha).1
      have hs := scaledInvSquares X (v*a) U (Nat.mul_pos hv ha0)
      refine (mul_le_mul_of_nonneg_left hs (by positivity : 0≤1/((a:ℝ)^2*a.totient))).trans_eq ?_
      push_cast
      have haR : (0:ℝ)<a := by exact_mod_cast ha0
      have hφR : (0:ℝ)<a.totient := by exact_mod_cast Nat.totient_pos.mpr ha0
      field_simp
    _ = 2*(v:ℝ)*(∑ a ∈ Icc 1 U, 1/((a:ℝ)*a.totient)) := (Finset.mul_sum ..).symm
    _ ≤ 8*v := by nlinarith only [mul_le_mul_of_nonneg_left (totient_series U) (show 0≤(v:ℝ) by positivity)]

end
end BandTail

end

section

/- The finite phase and Ramanujan identities in this section are adapted from
DFQDZZ's Apache-2.0 proof in goldbach-proofs PR #316,
commit e4ab24712555ae8c2c926adf19d368a9fb392c35. -/
namespace GoldbachExplicitModeledMajor
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

private theorem windowPhaseAdd (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem windowConjPhase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Centering the square of the geometric sum makes its phase cancel exactly. -/
theorem windowKernelSquare (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel
    rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (n + 1), conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [windowConjPhase, ← windowPhaseAdd, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem windowRamPower {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem windowRamUnit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [windowRamPower hp k h hc', windowRamPower hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

def windowAvg (q a : ℕ) : ℂ := (∑ r ∈ (range q).filter (fun r => r.Coprime q),
  phase ((r:ℝ)*a/q))/(q.totient:ℂ)

private theorem avg_const (q a : ℕ) (ha : a.Coprime q) :
    windowAvg q a = ram q 1/(q.totient:ℂ) := by
  have hm : (∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) = ram q a := by
    unfold ram; apply sum_congr rfl; intro r _; congr 1; ring
  rw [windowAvg,hm,windowRamUnit q a ha]

def windowModel (n A B : ℕ) : ℂ :=
  ∑ q ∈ Ioc A B, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
    ∫ t in (a:ℝ)/q-width n q..(a:ℝ)/q+width n q,
      (windowAvg q a * kernel n (t-(a:ℝ)/q))^2 * phase (-(n:ℝ)*t)

private theorem windowIntegral (n : ℕ) (c b : ℝ) (z : ℂ) :
    (∫ t in c-b..c+b, (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) =
      z^2*phase (-(n:ℝ)*c)*(kernelMass n b:ℂ) := by
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) (a := -b) (b := b) c
  rw [sub_eq_add_neg,← ht]
  calc
    _ = ∫ x in -b..b, (z^2*phase (-(n:ℝ)*c))*((‖kernel n x‖^2:ℝ):ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [add_sub_cancel_left,mul_add,windowPhaseAdd,← windowKernelSquare]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]; rfl

theorem windowModel_re (n A B : ℕ) (hA : 1≤A) :
    (windowModel n A B).re = ∑ q ∈ Ioc A B, (coefficient q n).re * kernelMass n (width n q) := by
  unfold windowModel
  simp_rw [windowIntegral]
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro q hq
  have hq' : 1<q := lt_of_le_of_lt hA (mem_Ioc.mp hq).1
  have hrange : (range (q+1)).filter (fun a => a.Coprime q) = (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      have hne : a ≠ q := by
        rintro rfl
        simp [Nat.Coprime] at hc
        omega
      exact ⟨by omega,hc⟩
    · rintro ⟨ha,hc⟩; exact ⟨by omega,hc⟩
  rw [hrange,← sum_mul]
  have hc : (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      windowAvg q a ^ 2 * phase (-(n:ℝ)*((a:ℝ)/q))) = coefficient q n := by
    unfold coefficient ram
    rw [map_sum,mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [avg_const _ _ (mem_filter.mp ha).2,windowConjPhase]
    congr 2
    ring
  rw [hc,Complex.mul_re]; simp

end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor MeasureTheory Filter Topology
noncomputable section

private theorem mass_nonneg (n q : ℕ) : 0 ≤ kernelMass n (width n q) := by
  apply intervalIntegral.integral_nonneg
  · linarith only [width_nonneg n q]
  · intro t _; positivity

theorem mass_upper (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    kernelMass n (width n q) ≤ 8*(n:ℝ)*(cutoff n:ℝ)/q := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hK (x : ℝ) : ‖kernel n x‖ ≤ (n:ℝ)+1 := by
    unfold kernel
    exact (norm_sum_le ..).trans (by simp [phase,Complex.norm_exp])
  have hnn := mass_nonneg n q
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(width n q)) (b := width n q)
    (f := fun x : ℝ => ‖kernel n x‖^2) (C := ((n:ℝ)+1)^2) (fun t _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK t) 2)
  change |kernelMass n (width n q)| ≤ _ at h
  rw [abs_of_nonneg hnn,abs_of_nonneg (by linarith only [width_nonneg n q])] at h
  refine h.trans ?_
  unfold width
  have hnpos : (0:ℝ) < n := by linarith
  have hQ : 0 ≤ (cutoff n:ℝ) := by positivity
  have hsq : ((n:ℝ)+1)^2 ≤ 4*(n:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (show 0 ≤ 3*(n:ℝ)+1 by positivity)]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hsq hQ]

private def bandWeight (n q : ℕ) : ℝ := kernelMass n (width n q)/(q:ℝ)

private theorem weight_mono (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : bandWeight n j ≤ bandWeight n i := by
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have hj' : (0:ℝ) < j := by exact_mod_cast hi.trans hij
  have hr : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hw : width n j ≤ width n i := by
    by_cases hn : n=0
    · simp [width,hn]
    · unfold width
      gcongr
  unfold bandWeight
  apply div_le_div₀ (mass_nonneg n i) (kernelMass_mono (width_nonneg n j) hw n) hi' hr

theorem weighted_prefix_lower (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]

theorem model_from_prefix (n B R : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hprefix : ∀ i ≥ cutoff n,i ≤ R*cutoff n → -(δ*(cutoff n:ℝ)) ≤ ∑ q ∈ Ioc (cutoff n) i, F n q) :
    -((8*δ + 64/(R:ℝ))*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  let A := cutoff n
  have ha : 1 ≤ A := cutoff_positive n
  have ha' : (0:ℝ) < A := by exact_mod_cast ha
  have hr' : (0:ℝ) < R := by exact_mod_cast hR
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [windowModel_re _ _ _ ha]
  change _ ≤ ∑ q ∈ Ioc A B, _
  by_cases hab : A ≤ B
  · let T := min B (R*A)
    have hT : A ≤ T := le_min hab (by dsimp [A]; nlinarith [Nat.mul_le_mul_right (cutoff n) hR])
    have hind := weighted_prefix_lower A T (F n) (bandWeight n) (δ*(A:ℝ)) hT (by positivity)
      (fun i _ => div_nonneg (mass_nonneg n i) (by positivity)) (fun i hi => weight_mono n _ _ (ha.trans hi) (by omega))
      (fun i hi hmax => hprefix i hi (hmax.trans (min_le_right _ _)))
    have hweight : bandWeight n A ≤ 8*(n:ℝ)/A := by
      have h := mass_upper n A hn ha
      change kernelMass n (width n A) ≤ 8*(n:ℝ)*A/A at h
      rw [mul_div_cancel_right₀ _ ha'.ne'] at h
      exact div_le_div_of_nonneg_right h ha'.le
    have hs : -(8*δ*(n:ℝ)) ≤ ∑ q ∈ Ioc A T, (coefficient q n).re * kernelMass n (width n q) := by
      calc
        _ ≤ -(δ*(A:ℝ)*bandWeight n A) := by
          have h := mul_le_mul_of_nonneg_left hweight (show 0 ≤ δ*(A:ℝ) by positivity)
          field_simp at h
          nlinarith only [h]
        _ ≤ _ := hind
        _ = _ := sum_congr rfl (fun q hq => by
          have hq' : (q:ℝ)≠0 := by exact_mod_cast (show q≠0 by have := (mem_Ioc.mp hq).1; omega)
          change (q:ℝ)*_ * (_/(q:ℝ)) = _
          field_simp)
    have ht : -(64*(n:ℝ)/R) ≤ ∑ q ∈ Ioc T B, (coefficient q n).re * kernelMass n (width n q) := by
      by_cases hB : B ≤ R*A
      · simp [T,min_eq_left hB]; positivity
      · rw [show T = R*A from min_eq_right (by omega)]
        have hsum := totient_tail (R*A) 1 B (by decide)
        let S := Ioc (R*A) B
        have he : ∑ q ∈ S, 1/((q:ℝ)*q.totient) ≤
          ∑ q ∈ Icc 1 B, if R*A < 1*q then 1/((q:ℝ)*q.totient) else 0 := by
          rw [← sum_filter]
          apply le_of_eq
          congr 1
          ext q; simp only [S,mem_Ioc,mem_filter,mem_Icc,one_mul]
          constructor <;> rintro h <;> omega
        have hsz : ((R:ℝ)*A)*(∑ q ∈ S,1/((q:ℝ)*q.totient)) ≤ 8 := by
          push_cast at hsum
          exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa only [Nat.cast_one,mul_one] using hsum)
        have hterm (q : ℕ) (hq : q∈S) : -((8*(n:ℝ)*A)*(1/((q:ℝ)*q.totient))) ≤
            (coefficient q n).re * kernelMass n (width n q) := by
          have hq0 : 1 ≤ q := by have := (mem_Ioc.mp hq).1; omega
          have hq' : (0:ℝ) < q := by exact_mod_cast hq0
          have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
          have hc := (Complex.abs_re_le_norm (coefficient q n)).trans (coeff_norm_le q n hq0)
          have hmass := mass_upper n q hn hq0
          have hprod := mul_le_mul hc hmass (mass_nonneg n q) (by positivity)
          have habs : |(coefficient q n).re * kernelMass n (width n q)| ≤ (1/(q.totient:ℝ))*(8*(n:ℝ)*(cutoff n:ℝ)/q) := by
            simpa only [abs_mul,abs_of_nonneg (mass_nonneg n q)] using hprod
          have hneg := (neg_le_of_abs_le habs)
          convert hneg using 1 <;> dsimp [A] <;> ring
        have hsum' := sum_le_sum hterm
        rw [sum_neg_distrib,← mul_sum] at hsum'
        refine le_trans ?_ hsum'
        apply neg_le_neg
        apply (le_div_iff₀ hr').mpr
        nlinarith only [mul_le_mul_of_nonneg_left hsz (show 0 ≤ 8*(n:ℝ) by positivity)]
    rw [← sum_Ioc_consecutive _ hT (min_le_left _ _)]
    have hid : 64*(n:ℝ)/R = (64/(R:ℝ))*(n:ℝ) := by ring
    linarith
  · simp [Ioc_eq_empty (by omega : ¬ A < B)]
    positivity

end
end BandTail

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor Filter Topology
noncomputable section

theorem floor_from_uniform
    (uniform : ∀ R : ℕ, 1 ≤ R → ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℕ,
      ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A → -(δ*(A:ℝ)) ≤ ∑ q ∈ Ioc A i, F n q) :
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ B : ℕ,
      -(e*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  intro e he
  let R : ℕ := ⌈128/e⌉₊+1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hlarge : 128 / e ≤ (R:ℝ) := by
    dsimp [R]; push_cast; linarith only [Nat.le_ceil (128/e)]
  have hratio : 64/(R:ℝ) ≤ e/2 := (div_le_iff₀ hR').mpr (by
    have h := (div_le_iff₀ he).mp hlarge
    linarith)
  obtain ⟨A₀,hA⟩ := uniform R hR (e/16) (by positivity)
  refine ⟨2^A₀+1,?_⟩
  intro n hn B
  have hn' : 1 ≤ n := (Nat.succ_le_succ (Nat.zero_le (2^A₀))).trans hn
  have hlog : A₀ ≤ Nat.log 2 (n+2) := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  have hl : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hc : A₀ ≤ cutoff n := hlog.trans (by
    dsimp [cutoff]; nlinarith [Nat.mul_le_mul_left (Nat.log 2 (n+2)) hl])
  apply le_trans _ (model_from_prefix n B R (e/16) hn' hR (by positivity) (hA _ hc n))
  have hk : 8*(e/16)+64/(R:ℝ) ≤ e := by linarith
  exact neg_le_neg (mul_le_mul_of_nonneg_right hk (by positivity))

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
noncomputable section
def w (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |h n d|/(d:ℝ)^(3/4:ℝ),by simp⟩
def z (n : ℕ) : ArithmeticFunction ℝ := ⟨fun d => h n d/(d:ℝ),by simp⟩
theorem w_mult (n : ℕ) : IsMultiplicative (w n) := by
  refine ⟨by simp [w,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp only [w,coe_mk,(h_mult n).map_mul_of_coprime hab,Nat.cast_mul,abs_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring
theorem z_mult (n : ℕ) : IsMultiplicative (z n) := by
  refine ⟨by simp [z,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp [z,(h_mult n).map_mul_of_coprime hab]; ring
theorem w_nonneg (n d : ℕ) : 0≤w n d := by dsimp [w]; positivity

theorem localReduce (f : ℕ → ℝ) (hf : ∀ j, f (j+3)=0) (k : ℕ) :
    (∑ i ∈ range (k+1), f i)=f 0 + (if k≥1 then f 1 else 0) + (if k≥2 then f 2 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    rcases k with _ | _ | j
    · simp
    · simp
    · simp [hf,show 2≤j+1+1 by omega,show 2≤j+1+1+1 by omega]

theorem wLocal (p n k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^k).divisors, w n d) ≤ 1+6/((p:ℝ)^(3/2:ℝ)) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hW1 : w n p ≤ 4/((p:ℝ)^(3/2:ℝ)) := by
    have h₁ : |h n p| ≤ 4/(p:ℝ) := by
      rw [h_prime n p hp]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]; field_simp; linarith
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg (sq_nonneg _)]
        field_simp
        nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤3*(p:ℝ)-2 by linarith)]
    dsimp [w]
    calc
      _ ≤ (4/(p:ℝ))/((p:ℝ)^(3/4:ℝ)) := div_le_div_of_nonneg_right h₁ (by positivity)
      _ = 4/(p:ℝ)^(1+(3/4):ℝ) := by rw [Real.rpow_add hpr,Real.rpow_one,div_div]
      _ ≤ _ := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hW2 : w n (p^2) ≤ 2/(p:ℝ)^(3/2:ℝ) := by
    have he : |h n (p^2)| ≤ 2 := by
      rw [h_square n p hp]; split_ifs
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg hp1.le]; apply (div_le_iff₀ hp1).mpr; linarith
      · norm_num
    change |h n (p^2)| / ((p^2:ℕ):ℝ)^(3/4:ℝ) ≤ _
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hpr.le,show (↑(2:ℕ):ℝ)*(3/4)=3/2 by norm_num]
    exact div_le_div_of_nonneg_right he (by positivity)
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => w n (p^j)) (fun j => by simp [w,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(w_mult n).map_one]
  simp only [div_eq_mul_inv] at hW1 hW2 ⊢
  split_ifs <;> linarith [w_nonneg n p,w_nonneg n (p^2)]

theorem zLocal (p n k : ℕ) (hp : p.Prime) : 0≤∑ d ∈ (p^k).divisors,z n d := by
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => z n (p^j)) (fun j => by simp [z,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(z_mult n).map_one]
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hsq : 1≤((p:ℝ)-1)^2 := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by linarith)]
  simp only [z,coe_mk,h_prime n p hp,h_square n p hp,Nat.cast_pow]
  by_cases hpn : p∣n
  · simp only [hpn,ite_true]
    split_ifs with hk hk2
    · field_simp; nlinarith [mul_pos hpr hp1]
    · positivity
    · omega
    · norm_num
  · simp only [hpn,ite_false,zero_div,ite_self,add_zero]
    split_ifs
    · field_simp; nlinarith [mul_le_mul_of_nonneg_right hsq hpr.le]
    · norm_num

def universal : ℝ := Real.exp (6*∑' j : ℕ, ((j:ℝ)^(3/2:ℝ))⁻¹)

theorem uniformDivisors (n M : ℕ) (hM : 0<M) :
    (∑ d ∈ M.divisors, w n d) ≤ universal := by
  let A : ArithmeticFunction ℝ := w n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (w_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,w n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  calc
    _ ≤ ∏ p ∈ M.factorization.support, Real.exp (6/((p:ℝ)^(3/2:ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · rw [he]; exact sum_nonneg fun d _ => w_nonneg n d
      · rw [he]
        have hh : p ∈ M.primeFactors := M.support_factorization ▸ hp
        exact (wLocal p n _ (Nat.prime_of_mem_primeFactors hh)).trans (by linarith [Real.add_one_le_exp (6/((p:ℝ)^(3/2:ℝ)))])
    _ ≤ universal := by
      rw [←Real.exp_sum,universal]
      apply Real.exp_le_exp.mpr
      simp_rw [div_eq_mul_inv,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<3/2)).sum_le_tsum _ (by intro _ _; positivity)

theorem signedDivisors (n M : ℕ) (hM : 0<M) :
    0 ≤ ∑ d ∈ M.divisors, z n d := by
  let A : ArithmeticFunction ℝ := z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,z n d := coe_mul_zeta_apply
  have hh := hA.multiplicative_factorization A hM.ne'
  rw [he] at hh
  rw [hh,Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hp
  rw [he]
  exact zLocal p n _ (Nat.prime_of_mem_primeFactors (M.support_factorization ▸ hp))

theorem prefixDiv (J : ℕ) : Icc 1 J ⊆ J.factorial.divisors := by
  intro d hd
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hd1 hdJ,J.factorial_pos.ne'⟩

theorem uniformPrefix (n J : ℕ) : (∑ d ∈ Icc 1 J, w n d)≤universal :=
  (sum_le_sum_of_subset_of_nonneg (prefixDiv J) (fun d _ _ => w_nonneg n d)).trans
    (uniformDivisors n _ J.factorial_pos)

theorem tailTerm (n J d : ℕ) (hJ : 0<J) (hJd : J≤d) :
    |z n d| ≤ w n d / ((J:ℝ)^(1/4:ℝ)) := by
  have hd : 0<(d:ℝ) := by exact_mod_cast hJ.trans_le hJd
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have he : (d:ℝ)^(3/4:ℝ)*(d:ℝ)^(1/4:ℝ)=d := by
    rw [←Real.rpow_add hd,show (3/4:ℝ)+1/4=1 by norm_num,Real.rpow_one]
  change |h n d / (d:ℝ)| ≤ |h n d| / _ / _
  rw [abs_div,abs_of_pos hd,div_div]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hJr _))
  apply le_trans _ he.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hJd) (by norm_num)) (by positivity)

theorem uniformTail (n J : ℕ) (s : Finset ℕ) (hJ : 0<J) (hs : ∀ d ∈ s,J≤d) :
    (∑ d ∈ s, |z n d|) ≤ universal / (J:ℝ)^(1/4:ℝ) := by
  have hb : s⊆Icc 1 (s.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨by have := hs d hd; omega, le_sup (f:=id) hd⟩
  calc
    _ ≤ ∑ d ∈ s, w n d / (J:ℝ)^(1/4:ℝ) := sum_le_sum fun d hd => tailTerm n J d hJ (hs d hd)
    _ = _ := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hb (fun d _ _ => w_nonneg n d)).trans (uniformPrefix n _)) (by positivity)

theorem signedPrefix (n J : ℕ) (hJ : 0<J) :
    -(universal / (J:ℝ)^(1/4:ℝ)) ≤ ∑ d ∈ Icc 1 J, z n d := by
  have hu := uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ (by
    intro d hd
    obtain ⟨hd,hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc,not_and] at hd'
    omega)
  have hh := signedDivisors n J.factorial J.factorial_pos
  rw [←sum_sdiff (s₁:=Icc 1 J) (s₂:=J.factorial.divisors) (prefixDiv J)] at hh
  have ht := sum_le_sum (s:=J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (z n d))
  linarith

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
noncomputable section

def gSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, g n k
def gAvg (n X : ℕ) : ℝ := gSum n X / X
def fSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, F n k

theorem g_sum_bounds (n X : ℕ) : 0≤gSum n X ∧ gSum n X≤X := by
  constructor
  · apply sum_nonneg
    intro k hk
    simp [g]; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ k ∈ Icc 1 X,(1:ℝ) := by
        apply sum_le_sum
        intro k hk
        simp [g]; split_ifs <;> norm_num
      _ = _ := by simp

theorem g_avg_bounds (n X : ℕ) : 0≤gAvg n X ∧ gAvg n X≤1 := by
  have hb := g_sum_bounds n X
  exact ⟨div_nonneg hb.1 (Nat.cast_nonneg _),div_le_one_of_le₀ hb.2 (Nat.cast_nonneg _)⟩

theorem fSum_convolution (n X : ℕ) :
    fSum n X = ∑ d ∈ Icc 1 X,h n d * gSum n (X/d) := by
  classical
  let S := Icc 1 X
  let f := fun v : ℕ × ℕ => h n v.1 * g n v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S,∑ v ∈ q.divisorsAntidiagonal,f v := by
      simp [fSum,S,convolution n,mul_comm (g n) (h n),ArithmeticFunction.mul_apply,f]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [f,gSum,mul_sum]
      rw [←sum_filter,hkd]

theorem prefix_split (f : ℕ→ℝ) {J X : ℕ} (hJX : J≤X) :
    (∑ d ∈ Icc 1 X,f d)=(∑ d ∈ Icc 1 J,f d)+(∑ d ∈ Ioc J X,f d) := by
  have he : Icc 1 X=Icc 1 J ∪ Ioc J X := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [he,sum_union (by rw [Finset.disjoint_left]; intro k hk hj; have := (mem_Icc.mp hk).2; have := (mem_Ioc.mp hj).1; omega)]

def scaleFactor (X d : ℕ) : ℝ := (d:ℝ)*(X/d:ℕ)/X

theorem scale_bounds (X d : ℕ) (hX : 0<X) (hd : 0<d) :
    0≤ scaleFactor X d ∧ scaleFactor X d ≤ 1 ∧ 1-scaleFactor X d ≤ (d:ℝ)/X := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hx0 : (d:ℝ)*(X/d:ℕ) ≤ X := by exact_mod_cast Nat.mul_div_le X d
  have hx1 : (X:ℝ) < (d:ℝ)*((X/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X hd
  unfold scaleFactor
  refine ⟨by positivity,(div_le_iff₀ hx).mpr (by linarith),?_⟩
  rw [sub_div' hx.ne',div_le_div_iff_of_pos_right hx]
  linarith

theorem scaled_piece (n X d : ℕ) (hd : 0<d) :
    h n d * gSum n (X/d) / X = z n d * (scaleFactor X d * gAvg n (X/d)) := by
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  by_cases hy : X/d=0
  · simp [gSum,gAvg,scaleFactor,hy]
  · have hyr : ((X/d:ℕ):ℝ)≠0 := by exact_mod_cast hy
    simp only [z,coe_mk,scaleFactor,gAvg]
    field_simp

theorem piece_approx (n X d : ℕ) (hX : 0<X) (hd : 0<d) (t e : ℝ)
    (he : |gAvg n (X/d)-t|≤e) (hdX : (d:ℝ)/X≤e) :
    |h n d * gSum n (X/d) / X - z n d * t| ≤ |z n d| *(2*e) := by
  obtain ⟨_,hs,hs'⟩ := scale_bounds X d hX hd
  have hg := g_avg_bounds n (X/d)
  have hc : |scaleFactor X d * gAvg n (X/d)-gAvg n (X/d)| ≤ e := by
    rw [←sub_one_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonneg hg.1]
    calc
      _ ≤ -(scaleFactor X d-1)*1 := mul_le_mul_of_nonneg_left hg.2 (by linarith)
      _ ≤ e := by linarith
  rw [scaled_piece n X d hd,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub_le _ (gAvg n (X/d)) _).trans (by linarith)

theorem dyadic_approx (n X J : ℕ) (hX : 0<X) (hJ : 0<J) (hJX : J≤X) (t e : ℝ) (he : 0≤e)
    (hne : ∀ d ∈ Icc 1 J,|gAvg n (X/d)-t|≤e) (hJr : (J:ℝ)/X ≤ e) :
    |fSum n X / X - (∑ d ∈ Icc 1 J,z n d)*t| ≤
      universal*(2*e)+universal/(J:ℝ)^(1/4:ℝ) := by
  let a := fun d => h n d * gSum n (X/d) / X
  have hsmall : |∑ d ∈ Icc 1 J,(a d-z n d*t)|≤universal*(2*e) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 J, |z n d| *(2*e) := by
        refine sum_le_sum fun d hd => piece_approx n X d hX (mem_Icc.mp hd).1 t e (hne _ hd) ?_
        exact (div_le_div_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) (Nat.cast_nonneg _)).trans hJr
      _ = _ := (sum_mul _ _ _).symm
      _ ≤ _ := by
        have hu := uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
        norm_num at hu
        exact mul_le_mul_of_nonneg_right hu (by positivity)
  have hlarge : |∑ d ∈ Ioc J X,a d| ≤ universal/(J:ℝ)^(1/4:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (uniformTail n J (Ioc J X) hJ (fun d hd => (mem_Ioc.mp hd).1.le))
    apply sum_le_sum
    intro d hd
    have hd0 : 0<d := hJ.trans (mem_Ioc.mp hd).1
    obtain ⟨hs,hs',_⟩ := scale_bounds X d hX hd0
    have hg := g_avg_bounds n (X/d)
    dsimp only [a]; rw [scaled_piece n X d hd0,abs_mul,abs_of_nonneg (mul_nonneg hs hg.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hs' hg.1 hg.2)
  have htotal : fSum n X / X = (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d) := by
    rw [fSum_convolution,sum_div]
    exact prefix_split a hJX
  rw [htotal,sum_mul]
  rw [show (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d)-(∑ d ∈ Icc 1 J,z n d*t)=
      (∑ d ∈ Icc 1 J,(a d-z n d*t))+(∑ d ∈ Ioc J X,a d) by rw [sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hsmall hlarge)

end
end BandTail

end

section

namespace GoldbachModelMean

open Finset Filter Topology

private def modProd (s : Finset Nat.Primes) : ℕ := ∏ p ∈ s, (p:ℕ)

private theorem modProd_pos (s : Finset Nat.Primes) : 0 < modProd s :=
  Finset.prod_pos (fun p _ => p.property.pos)

private theorem totientProd (s : Finset Nat.Primes) :
    ((modProd s).totient:ℝ)*(1+∑ p ∈ s, 1/(p:ℝ)) ≤ modProd s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modProd]
  | @insert p s hps ih =>
    have hcop : (p:ℕ).Coprime (modProd s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes p.property q.property).mpr
      intro h
      exact hps ((Subtype.ext h : p=q) ▸ hq)
    have heq : modProd (insert p s) = (p:ℕ)*modProd s := Finset.prod_insert hps
    have hp : (1:ℕ)≤p.val := p.property.one_lt.le
    have hp' : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hsum : 0 ≤ ∑ q ∈ s, (1:ℝ)/(q:ℝ) := sum_nonneg fun q _ => by positivity
    rw [heq,Nat.totient_mul hcop,Nat.totient_prime p.property,Finset.sum_insert hps]
    push_cast [Nat.cast_sub hp]
    calc
      _ ≤ (p:ℝ)*(((modProd s).totient:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ))) := by
        have : ((p:ℝ)-1)*(1+(1/(p:ℝ)+∑ q ∈ s, 1/(q:ℝ))) ≤ (p:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ)) := by
          field_simp
          nlinarith [mul_nonneg hp'.le hsum]
        nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (modProd s).totient (α:=ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih hp'.le

theorem exists_thin_modulus (e : ℝ) (he : 0<e) :
    ∃ D : ℕ, 0<D ∧ (D.totient:ℝ)/(D:ℝ)<e := by
  classical
  have hs : ∃ s : Finset Nat.Primes, (1/e:ℝ) < ∑ p ∈ s, 1/(p:ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s,hs⟩ := hs
  refine ⟨modProd s,modProd_pos s,(div_lt_iff₀ (by exact_mod_cast modProd_pos s)).mpr ?_⟩
  have h := totientProd s
  have ht : (0:ℝ) < (modProd s).totient := by exact_mod_cast Nat.totient_pos.mpr (modProd_pos s)
  have h1 := (div_lt_iff₀ he).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right h he.le,
    mul_lt_mul_of_pos_right h1 ht,mul_pos he ht]

def fewFactors (k X : ℕ) : Finset ℕ :=
  (range X).filter fun n => 0 < n ∧ n.primeFactorsList.length ≤ k

private theorem few_step (k X D : ℕ) (hD : 0<D) :
    (fewFactors (k+1) X).card ≤ D.totient*(X/D+1)+(D+1)*(fewFactors k X).card := by
  classical
  let R := (range X).filter fun n => D.Coprime n
  let cover := (range (D+1)).biUnion fun p => (fewFactors k X).image fun y => p*y
  have hsub : fewFactors (k+1) X ⊆ R ∪ cover := by
    intro x hx
    obtain ⟨hxX,hxp,hxk⟩ := mem_filter.mp hx
    by_cases hc : D.Coprime x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxX,hc⟩)
    obtain ⟨p,hp,hpd,hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨y,rfl⟩ := hpx
    have hy : y ≠ 0 := by intro hz; simp [hz] at hxp
    have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hy).length_eq
    simp [Nat.primeFactorsList_prime hp] at hlen
    have hyX : y < X := lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left y hp.pos) (mem_range.mp hxX)
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_range.mpr (by have := Nat.le_of_dvd hD hpd; omega),
      mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_range.mpr hyX,by omega,by omega⟩,rfl⟩⟩)
  have hR : R.card ≤ D.totient*(X/D+1) := by
    simpa only [R,zero_add,← range_eq_Ico] using Nat.Ico_filter_coprime_le 0 X hD.ne'
  have hc : cover.card ≤ (D+1)*(fewFactors k X).card := calc
    _ ≤ ∑ p ∈ range (D+1), ((fewFactors k X).image fun y => p*y).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range (D+1), (fewFactors k X).card := by exact Finset.sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hR hc))

theorem fewFactors_eventually (k : ℕ) (e : ℝ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ((fewFactors k X).card:ℝ) ≤ e*X := by
  induction k generalizing e with
  | zero =>
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/e)] with X hX
    have hsub : fewFactors 0 X ⊆ {1} := by
      intro x hx
      obtain ⟨_,hp,hl⟩ := mem_filter.mp hx
      have hn := (Nat.primeFactorsList_eq_nil x).mp (List.length_eq_zero_iff.mp (by omega))
      simp only [mem_singleton]
      omega
    have hc : (fewFactors 0 X).card ≤ 1 := by simpa using card_le_card hsub
    change 1/e ≤ (X:ℝ) at hX
    have hh := (div_le_iff₀ he).mp hX
    exact (by exact_mod_cast hc : ((fewFactors 0 X).card:ℝ) ≤ 1) |>.trans (by linarith)
  | succ k ih =>
    obtain ⟨D,hD,hphi⟩ := exists_thin_modulus (e/4) (by positivity)
    have hD' : (0:ℝ)<D := by exact_mod_cast hD
    filter_upwards [ih (e/(4*(D+1))) (by positivity),
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (4*(D.totient:ℝ)/e)] with X hprev hlarge
    change 4*(D.totient:ℝ)/e ≤ X at hlarge
    have hr := (div_le_iff₀ he).mp hlarge
    have hp := (div_lt_iff₀ hD').mp hphi
    have hquot : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D := by
      apply (le_div_iff₀ hD').mpr
      exact_mod_cast Nat.div_mul_le_self X D
    have h := few_step k X D hD
    have h' : ((fewFactors (k+1) X).card:ℝ) ≤ D.totient*(((X/D:ℕ):ℝ)+1)+((D:ℝ)+1)*(fewFactors k X).card := by exact_mod_cast h
    have hf : ((D:ℝ)+1)*((fewFactors k X).card:ℝ) ≤ (e/4)*X := by
      calc
        _ ≤ ((D:ℝ)+1)*(e/(4*(D+1))*X) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by field_simp
    have hg : (D.totient:ℝ)*((X/D:ℕ):ℝ) ≤ (e/4)*X := calc
      _ ≤ (D.totient:ℝ)*((X:ℝ)/D) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((D.totient:ℝ)/D)*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi.le (by positivity)
    nlinarith only [h',hf,hg,hr,mul_nonneg he.le (Nat.cast_nonneg X (α:=ℝ))]

end GoldbachModelMean

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

def product (s : Finset ℕ) := ∏ p ∈ s, p
def hits (P : Finset ℕ) (m : ℕ) := P.filter (fun p => p ∣ m)
def count (P : Finset ℕ) (X : ℕ) : ℝ := ∑ m ∈ Ioc 0 X, if (hits P m).card=0 then 1 else 0
def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p:ℝ)
def divisCount (P : Finset ℕ) (j X : ℕ) : ℝ :=
  ∑ s ∈ P.powersetCard j, ((X / product s : ℕ):ℝ)
def trunc (P : Finset ℕ) (r X : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (-1:ℝ)^j*divisCount P j X

lemma prodPos (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : 0<product s :=
  prod_pos (fun p h => (hp p h).pos)

lemma prodDvd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (m : ℕ) :
    product s ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (product s) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hp' (hs q hq)).mpr fun he => hps (he ▸ hq))
    rw [product,prod_insert hps,forall_mem_insert]
    change p*product s ∣ m ↔ _
    exact ⟨fun h => ⟨(dvd_mul_right p _).trans h,(ih hs).mp ((dvd_mul_left (product s) p).trans h)⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 ((ih hs).mpr h.2)⟩

lemma omegaProd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : (product s).primeFactorsList.length=s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have he := (Nat.perm_primeFactorsList_mul hp'.ne_zero (prodPos s hs).ne').length_eq
    change (∏ q ∈ insert p s,q).primeFactorsList.length=_
    rw [prod_insert hps,card_insert_of_notMem hps]
    change (p*product s).primeFactorsList.length=_
    simpa [Nat.primeFactorsList_prime hp',ih hs,Nat.add_comm] using he

theorem divisAsChoose (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (j X : ℕ) :
    divisCount P j X = ∑ m ∈ Ioc 0 X, (((hits P m).card.choose j:ℕ):ℝ) := by
  classical
  have hs (m : ℕ) :
      (P.powersetCard j).filter (fun s => product s ∣ m) = (hits P m).powersetCard j := by
    ext s
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hj⟩,hd⟩
      exact ⟨fun q hq => mem_filter.mpr ⟨hsub hq,(prodDvd s (fun p h => hp p (hsub h)) m).mp hd q hq⟩,hj⟩
    · rintro ⟨hsub,hj⟩
      have hP (q) (hq:q∈s) := (mem_filter.mp (hsub hq)).1
      exact ⟨⟨fun q hq => hP q hq,hj⟩,(prodDvd s (fun p h => hp p (hP p h)) m).mpr
        (fun q hq => (mem_filter.mp (hsub hq)).2)⟩
  unfold divisCount
  simp_rw [←Nat.Ioc_filter_dvd_card_eq_div, ←Finset.sum_boole]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Finset.sum_boole,hs,card_powersetCard]

private theorem localTrunc (k r : ℕ) :
    |(if k=0 then (1:ℝ) else 0) - ∑ j ∈ range (r+1), (-1:ℝ)^j*(k.choose j:ℕ)| ≤ k.choose r := by
  cases k with
  | zero =>
    have hy : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((0:ℕ).choose j):ℕ))=1 := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        have hh : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hh];simp
      · simp
    simp [hy]
  | succ k =>
    have hi := @Int.alternating_sum_range_choose_eq_choose k r
    have hr : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((k+1).choose j):ℕ))=(-1:ℝ)^r*(k.choose r:ℕ) := by exact_mod_cast hi
    rw [if_neg (by omega),zero_sub,abs_neg,hr,abs_mul,abs_pow]
    simpa using (show ((k.choose r:ℕ):ℝ) ≤ ((k+1).choose r:ℕ) by exact_mod_cast Nat.choose_le_succ k r)

theorem truncateError (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ divisCount P r X := by
  unfold count trunc
  simp_rw [divisAsChoose P hp,Finset.mul_sum]
  rw [Finset.sum_comm (s:=range (r+1)),←sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun m _ => localTrunc (hits P m).card r))

theorem reciprocalLayer (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r : ℕ) :
    (∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) ≤ Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ s ∈ P.powersetCard r, ∏ p ∈ s, (2/(p:ℝ)) := by
      apply sum_congr rfl
      intro s hs
      rw [prod_div_distrib,prod_const,(mem_powersetCard.mp hs).2]
      simp [product,div_eq_mul_inv,mul_comm]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (2/(p:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (mem_powersetCard.mp hs).1)
        (fun s _ _ => prod_nonneg (fun _ _ => by positivity))
    _ = ∏ p ∈ P, (1+2/(p:ℝ)) := (prod_one_add ..).symm
    _ ≤ ∏ p ∈ P, Real.exp (2/(p:ℝ)) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      simpa [add_comm] using (Real.add_one_le_exp (2/(p:ℝ)))
    _ = _ := by rw [←Real.exp_sum]; congr 1;unfold harmonic;rw [mul_sum];apply sum_congr rfl;intros;ring

theorem errorEnvelope (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ (X:ℝ)*Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (truncateError P hp r X).trans
  calc
    divisCount P r X ≤ (X:ℝ)*(∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) := by
      unfold divisCount
      rw [mul_sum]
      apply sum_le_sum
      intro s _
      simpa only [mul_one_div] using (Nat.cast_div_le (m:=X) (n:=product s) : ((X/product s:ℕ):ℝ)≤X/(product s:ℝ))
    _ ≤ (X:ℝ)*(Real.exp (2*harmonic P)/(2:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (reciprocalLayer P hp r) (Nat.cast_nonneg _)
    _ = _ := by ring
end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

private lemma floorIneq (m d : ℕ) (hd : 0<d) :
    (m:ℝ)/d-1 ≤ ((m/d:ℕ):ℝ) ∧ ((m/d:ℕ):ℝ) ≤ m/(d:ℝ) := by
  refine ⟨?_,Nat.cast_div_le⟩
  have h : (m:ℝ) < d * (((m/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hh : (m:ℝ)/d < ((m/d:ℕ):ℝ)+1 := (div_lt_iff₀ (by exact_mod_cast hd)).mpr (by linarith)
  linarith

private lemma floorDiff (X Y d : ℕ) (hd : 0<d) (hY : 0<Y) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/Y*((Y/d:ℕ):ℝ)| ≤ 1+(X:ℝ)/Y := by
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hpos : 0≤(X:ℝ)/Y := by positivity
  obtain ⟨a,b⟩ := floorIneq X d hd
  obtain ⟨c,e⟩ := floorIneq Y d hd
  have h : (X:ℝ)/Y*(Y/(d:ℝ))=X/(d:ℝ) := by field_simp
  have h1 := mul_le_mul_of_nonneg_left c hpos
  have h2 := mul_le_mul_of_nonneg_left e hpos
  rw [h] at h2
  rw [mul_sub,h,mul_one] at h1
  rw [abs_le]
  constructor <;> linarith

private lemma layerCard (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X : ℕ) (hj : j≤r) :
    ((P.powersetCard j).filter (fun s => product s ≤ X)).card ≤
      (GoldbachModelMean.fewFactors r (X+1)).card := by
  apply Finset.card_le_card_of_injOn product
  · intro s hs
    obtain ⟨hP,hX⟩ := mem_filter.mp hs
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    have hPrime (q) (hq:q∈s) := hp q (hsub hq)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),prodPos s hPrime,(omegaProd s hPrime).trans_le (hcard.trans_le hj)⟩
  · intro s hs t ht e
    have h1 := (mem_powersetCard.mp (mem_filter.mp hs).1).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp ht).1).1
    have hs' : (product s).primeFactors=s := Nat.primeFactors_prod (fun q hq => hp q (h1 hq))
    have ht' : (product t).primeFactors=t := Nat.primeFactors_prod (fun q hq => hp q (h2 hq))
    rw [←hs',e,ht']

private lemma layerDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X Y : ℕ)
    (hj : j≤r) (hY : 0<Y) (hYX : Y≤X) :
    |divisCount P j X-(X:ℝ)/Y*divisCount P j Y| ≤
      ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  classical
  unfold divisCount
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ P.powersetCard j, if product s≤X then 1+(X:ℝ)/Y else 0 := by
      apply sum_le_sum
      intro s hs
      split_ifs with h
      · exact floorDiff X Y (product s) (prodPos s (fun q hq => hp q ((mem_powersetCard.mp hs).1 hq))) hY
      · have hx : X<product s := by omega
        simp [Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (hYX.trans_lt hx)]
    _ = (((P.powersetCard j).filter (fun s => product s ≤ X)).card:ℝ)*(1+(X:ℝ)/Y) := by
      rw [←sum_filter];simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast layerCard P hp r j X hj) (by positivity)

theorem truncDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r X Y : ℕ)
    (hY : 0<Y) (hYX : Y≤X) :
    |trunc P r X-(X:ℝ)/Y*trunc P r Y| ≤
      ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  unfold trunc
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (r+1), ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
      apply sum_le_sum
      intro j hj
      have hh := layerDiff P hp r j X Y (by have := mem_range.mp hj;omega) hY hYX
      rw [show (X:ℝ)/Y*((-1:ℝ)^j*divisCount P j Y)=(-1:ℝ)^j*((X:ℝ)/Y*divisCount P j Y) by ring,
        ←mul_sub,abs_mul,abs_pow]
      simpa using hh
    _ = _ := by simp [mul_assoc]

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

theorem uniform_lowH (H C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ P : Finset ℕ, (∀ p∈P,p.Prime) → harmonic P≤H →
    |count P X/X - count P Y/Y| ≤ e := by
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt (4*Real.exp (2*H)/e) (show (1:ℝ)<2 by norm_num)
  let A : ℝ := ((r:ℝ)+1)*(1+C)
  have hA : 0<A := by dsimp [A];positivity
  have heps : 0<e/(4*A) := by positivity
  obtain ⟨x₀,hx⟩ := eventually_atTop.mp (GoldbachModelMean.fewFactors_eventually r (e/(4*A)) heps)
  filter_upwards [eventually_ge_atTop x₀,eventually_ge_atTop 1] with X hX hX1
  intro Y hY hYX hscale P hp hH
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hX' : (0:ℝ)<X := by exact_mod_cast hX1
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX1
  have hRatio : (X:ℝ)/Y≤C := (div_le_iff₀ hY').mpr hscale
  have hR : 0≤(X:ℝ)/Y := by positivity
  have hExp := Real.exp_le_exp.mpr (show 2*harmonic P≤2*H by linarith)
  have hcoeff : Real.exp (2*harmonic P)/(2:ℝ)^r ≤ e/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_lt_iff₀ he).mp hr
    nlinarith
  have err (W : ℕ) : |count P W-trunc P r W| ≤ (W:ℝ)*(e/4) := by
    refine (errorEnvelope P hp r W).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  have hf := hx (X+1) (by omega)
  push_cast at hf
  have hL : ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) ≤ (X:ℝ)*(e/2) := by
    calc
      _ ≤ ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+C) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = A*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ) := by dsimp [A];ring
      _ ≤ A*(e/(4*A)*((X:ℝ)+1)) := mul_le_mul_of_nonneg_left hf hA.le
      _ = e/4*((X:ℝ)+1) := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx1)]
  have ht := (truncDiff P hp r X Y hY hYX).trans hL
  have hE : |(X:ℝ)/Y*trunc P r Y-(X:ℝ)/Y*count P Y| ≤ (X:ℝ)*(e/4) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR,abs_sub_comm]
    calc
      _ ≤ ((X:ℝ)/Y)*(Y*(e/4)) := mul_le_mul_of_nonneg_left (err _) hR
      _ = _ := by field_simp
  have hT := abs_sub_le (count P X) (trunc P r X) ((X:ℝ)/Y*count P Y)
  have hU := abs_sub_le (trunc P r X) ((X:ℝ)/Y*trunc P r Y) ((X:ℝ)/Y*count P Y)
  have hab : |count P X-(X:ℝ)/Y*count P Y|≤e*X := by linarith [err X]
  rw [show count P X/(X:ℝ)-count P Y/Y=(count P X-(X:ℝ)/Y*count P Y)/X by field_simp,
    abs_div,abs_of_pos hX']
  exact (div_le_iff₀ hX').mpr hab

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

def exceptionalPrimes (n X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p => p.Prime ∧ ¬p∣n)
def meanG (n X : ℕ) : ℝ := (∑ k ∈ Icc 1 X,g n k)/X

theorem count_eq_g (n X T : ℕ) (hT : T≤X) :
    count (exceptionalPrimes n X) T = ∑ k ∈ Icc 1 T,g n k := by
  unfold count
  have hset : Ioc 0 T=Icc 1 T := by ext k;simp;omega
  rw [hset]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk1,hkT⟩ := mem_Icc.mp hk
  have h0 : k≠0 := by omega
  have he : (hits (exceptionalPrimes n X) k).card=0 ↔ smooth n k := by
    rw [Finset.card_eq_zero]
    constructor
    · intro h p hp
      by_contra hn
      obtain ⟨hp',hpk,_⟩ := Nat.mem_primeFactors.mp hp
      have hpX := (Nat.le_of_dvd (by omega : 0<k) hpk).trans (hkT.trans hT)
      have hmem : p ∈ hits (exceptionalPrimes n X) k := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.one_lt.le,hpX⟩,hp',hn⟩,hpk⟩
      simp [h] at hmem
    · intro hs
      apply eq_empty_iff_forall_notMem.mpr
      intro p hpm
      obtain ⟨hP,hpk⟩ := mem_filter.mp hpm
      obtain ⟨_,hp,hn⟩ := mem_filter.mp hP
      exact hn (hs p (Nat.mem_primeFactors.mpr ⟨hp,hpk,h0⟩))
  simp [g,h0,he]

theorem meanG_nonneg (n X : ℕ) : 0≤ meanG n X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro k _
  simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num

theorem meanG_le_one (n X : ℕ) : meanG n X≤1 := by
  rcases eq_or_ne X 0 with rfl|hx
  · simp [meanG]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hx)).mpr
    calc
      _ ≤ ∑ k ∈ Icc 1 X, (1:ℝ) := by
        apply sum_le_sum
        intro k _
        simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num
      _ = _ := by simp

end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

def frequency (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
def hit (p k : ℕ) : ℝ := if p ∣ k then 1 else 0
def hitCount (P : Finset ℕ) (k : ℕ) : ℝ := ∑ p ∈ P, hit p k

theorem hit_sum (p X : ℕ) : (∑ k ∈ Icc 1 X, hit p k) = (X/p : ℕ) := by
  have he : Icc 1 X=Ioc 0 X := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold hit
  rw [he,Finset.sum_boole,Nat.Ioc_filter_dvd_card_eq_div]

theorem firstMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, 0<p) :
    (X:ℝ)*frequency P-P.card ≤ ∑ k ∈ Icc 1 X,hitCount P k := by
  simp only [hitCount,Finset.sum_comm (s:=Icc 1 X) (t:=P),hit_sum]
  calc
    _ = ∑ p ∈ P, ((X:ℝ)*(p:ℝ)⁻¹-1) := by simp [frequency,mul_sum,sum_sub_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr : 0<(p:ℝ) := by exact_mod_cast hP p hp
      have hc : (X:ℝ) < (p:ℝ)*((X/p:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X (hP p hp)
      have hh : (X:ℝ)/(p:ℝ) ≤ ((X/p:ℕ):ℝ)+1 := (div_le_iff₀ hpr).mpr (by linarith)
      linarith [show (X:ℝ)*(p:ℝ)⁻¹ = X/p by rw [div_eq_mul_inv]]

theorem hitPair (X p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (∑ k ∈ Icc 1 X,hit p k * hit r k) ≤
      (X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹) + (if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0) := by
  by_cases he : p=r
  · subst r
    have hh (k : ℕ) : hit p k*hit p k=hit p k := by by_cases hk : p∣k <;> simp [hit,hk]
    simp only [hh,hit_sum,ite_true]
    exact (Nat.cast_div_le (α:=ℝ)).trans (by rw [div_eq_mul_inv]; exact le_add_of_nonneg_left (by positivity))
  · have hh (k : ℕ) : hit p k*hit r k=hit (p*r) k := by
      have hc := (Nat.coprime_primes hp hr).mpr he
      have eqv : p*r∣k ↔ p∣k ∧ r∣k := ⟨fun hk => ⟨(dvd_mul_right p r).trans hk,(dvd_mul_left r p).trans hk⟩,fun hk => hc.mul_dvd_of_dvd_of_dvd hk.1 hk.2⟩
      by_cases ha : p∣k <;> by_cases hb : r∣k <;> simp [hit,eqv,ha,hb]
    simp only [hh,hit_sum,if_neg he,add_zero]
    exact (Nat.cast_div_le (α:=ℝ)).trans_eq (by simp [div_eq_mul_inv,mul_comm])

theorem secondMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ Icc 1 X,(hitCount P k)^2) ≤ (X:ℝ)*(frequency P)^2+X*frequency P := by
  have hswap (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ k ∈ Icc 1 X,∑ p ∈ P,∑ r ∈ P,f k p r)=∑ p ∈ P,∑ r ∈ P,∑ k ∈ Icc 1 X,f k p r := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  simp only [hitCount,sq,sum_mul_sum,hswap]
  calc
    _ ≤ ∑ p ∈ P,∑ r ∈ P, ((X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹)+(if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun r hr => hitPair X p r (hP p hp) (hP r hr)
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
      unfold frequency
      congr 1
      · rw [←Finset.sum_mul]
      · rw [mul_sum]
        exact sum_congr rfl fun p hp => by simp [hp]

theorem highH (n X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p∣n) :
    frequency P * (∑ k ∈ Icc 1 X, g n k) ≤ (X:ℝ) + 2*P.card := by
  let H := frequency P
  have hH : 0≤H := sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  rcases hH.eq_or_lt with hz | hpos
  · change H*_ ≤ _
    rw [←hz,zero_mul]; positivity
  have h1 := firstMoment P X (fun p hp => (hP p hp).1.pos)
  have h2 := secondMoment P X (fun p hp => (hP p hp).1)
  have hdom : (∑ k ∈ Icc 1 X, g n k * H^2) ≤ ∑ k ∈ Icc 1 X, (hitCount P k-H)^2 := by
    apply sum_le_sum
    intro k hk
    have hk0 : k≠0 := by have := (mem_Icc.mp hk).1; omega
    by_cases hsm : smooth n k
    · have h0 : hitCount P k=0 := by
        apply sum_eq_zero
        intro p hp
        have hn := (hP p hp).2
        have hpk : ¬p∣k := fun hpk => hn (hsm p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hpk,hk0⟩))
        simp [hit,hpk]
      simp [g,hk0,hsm,h0]
    · simp [g,hk0,hsm,sq_nonneg]
  have he (k : ℕ) : (hitCount P k-H)^2=(hitCount P k)^2 - hitCount P k*(2*H)+ H^2 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,←sum_mul,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hdom
  change (X:ℝ)*H-_≤_ at h1
  change _≤(X:ℝ)*H^2+X*H at h2
  have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hpos.le)
  apply le_of_mul_le_mul_right (a:=H) _ hpos
  nlinarith only [hdom,h3,h2]
end
end BandTail

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

theorem mean_slow (C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ n, |meanG n X-meanG n Y|≤e := by
  let H : ℝ := (1+2*C)/e
  have hHpos : 0<H := by dsimp [H];positivity
  filter_upwards [uniform_lowH H C e hC he] with X hlow
  intro Y hY hYX hscale n
  let P := exceptionalPrimes n X
  have hprime (p) (hp : p∈P) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hh : harmonic P=frequency P := by simp [GoldbachModelMean.Brun.harmonic,frequency,one_div]
  by_cases hc : harmonic P≤H
  · have hh := hlow Y hY hYX hscale P (fun p h => (hprime p h).1) hc
    rwa [count_eq_g n X X le_rfl,count_eq_g n X Y hYX] at hh
  · have hPH := lt_of_not_ge hc
    rw [hh] at hPH
    have hPcard : P.card≤X := (card_filter_le ..).trans_eq (by simp)
    have hX' : (0:ℝ)<X := by exact_mod_cast hY.trans_le hYX
    have hyp : (0:ℝ)<Y := by exact_mod_cast hY
    have hscaleX : (X:ℝ)≤C*X := by simpa using (mul_le_mul_of_nonneg_right hC hX'.le)
    have hb (T : ℕ) (ht : (0:ℝ)<T) (hscaleT : (X:ℝ)≤C*T) : meanG n T≤e := by
      have hcard' : (P.card:ℝ) ≤ C*T := (show (P.card:ℝ)≤X by exact_mod_cast hPcard).trans hscaleT
      have hbound := highH n T P hprime
      have hp : 0≤∑ k ∈ Icc 1 T,g n k := by
        have hh := meanG_nonneg n T
        unfold meanG at hh
        simpa [ht.ne'] using mul_nonneg hh ht.le
      have hlo := mul_le_mul_of_nonneg_right hPH.le hp
      have hHS : H*(∑ k ∈ Icc 1 T,g n k) ≤ (1+2*C)*T := by linarith
      have hid : (1+2*C)*T=H*(e*T) := by dsimp [H];field_simp
      rw [hid] at hHS
      exact (div_le_iff₀ ht).mpr ((mul_le_mul_iff_right₀ hHpos).mp hHS)
    have hx := hb X hX' hscaleX
    have hy := hb Y hyp hscale
    rw [abs_le]
    constructor <;> linarith [meanG_nonneg n X, meanG_nonneg n Y]

end BandTail

end

section

namespace BandTail
open Finset Filter
noncomputable section

theorem uniform_prefix_floor (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ : 0<δ) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A →
      -(δ*(A:ℝ))  ≤  ∑ q ∈ Finset.Ioc A i,F n q := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hu : 0<universal := Real.exp_pos _
  let τ : ℝ := δ/(8*((R:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  let e : ℝ := τ/(universal+1)
  have he : 0<e := by dsimp [e]; positivity
  have heu : universal*e  ≤  τ := by
    have heq : e*(universal+1)=τ := by dsimp [e]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_ge (universal/τ)
  let J := (N+1)^4
  have hJ : 0<J := by dsimp [J]; positivity
  have hj : (J:ℝ)^(1/4:ℝ)=(N:ℝ)+1 := by
    dsimp [J]; push_cast
    rw [←Real.rpow_natCast_mul (by positivity),show (↑(4:ℕ):ℝ)*(1/4)=1 by norm_num,Real.rpow_one]
  have ht : universal/(J:ℝ)^(1/4:ℝ)  ≤  τ := by
    rw [hj]
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_le_iff₀ hτ).mp hN
    nlinarith
  let C : ℝ := 2*(R:ℝ)*J
  have hjr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_le_mul hr hjr (by norm_num) (by positivity)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (mean_slow C e hC he)
  obtain ⟨L,hL⟩ := exists_nat_ge ((J:ℝ)/e)
  refine ⟨max J (max M L),?_⟩
  intro A hA n i hAi hiA
  have hJA : J ≤ A := by omega
  have hA0 : 0<A := hJ.trans_le hJA
  have hAr : (0:ℝ)<A := by exact_mod_cast hA0
  have hi0 : 0 < i := hA0.trans_le hAi
  have hir : (0:ℝ) < i := by exact_mod_cast hi0
  have hscale : (i:ℝ) ≤ R*(A:ℝ) := by exact_mod_cast hiA
  let t := gAvg n i
  let Z := ∑ d ∈ Icc 1 J,z n d
  have ht01 : 0 ≤ t ∧ t ≤ 1 := g_avg_bounds n i
  have hz : -τ ≤ Z := by have hz' := signedPrefix n J hJ; dsimp [Z]; linarith
  have hlin (X : ℕ) (hAX : A ≤ X) (hXi : X ≤ i) :
      |fSum n X-(X:ℝ)*(Z*t)|  ≤  X*(3*τ) := by
    have hX : 0<X := hA0.trans_le hAX
    have hxr : (0:ℝ)<X := by exact_mod_cast hX
    have hjx : (J:ℝ)/X ≤ e := by
      apply (div_le_iff₀ hxr).mpr
      have hLX : (L:ℝ) ≤ X := by exact_mod_cast (show L ≤ X by omega)
      have := (div_le_iff₀ he).mp (hL.trans hLX)
      linarith
    have hnear (d : ℕ) (hd : d∈Icc 1 J) : |gAvg n (X/d)-t| ≤ e := by
      obtain ⟨hd0,hdJ⟩ := mem_Icc.mp hd
      have hdX : d ≤ X := by omega
      have hy : 0<X/d := Nat.div_pos hdX hd0
      have hii : i ≤ R*X := hiA.trans (Nat.mul_le_mul_left R hAX)
      have hratio : X ≤ (2*J)*(X/d) := by
        calc
          X  ≤  d*(X/d+1) := (Nat.lt_mul_div_succ X hd0).le
          _  ≤  J*(2*(X/d)) := Nat.mul_le_mul hdJ (by omega)
          _ = _ := by ring
      have hcxy : (i:ℝ) ≤ C*(X/d:ℕ) := by
        dsimp [C]
        exact_mod_cast (show i ≤ 2*R*J*(X/d) from hii.trans (by calc
          R*X  ≤  R*((2*J)*(X/d)) := Nat.mul_le_mul_left R hratio
          _ = _ := by ring))
      rw [abs_sub_comm]
      exact hM i (by omega) (X/d) hy ((Nat.div_le_self X d).trans hXi) hcxy n
    have h := dyadic_approx n X J hX hJ (by omega) t e he.le hnear hjx
    have ha : |fSum n X / X - Z*t| ≤ 3*τ := h.trans (by linarith)
    have eqv : fSum n X-(X:ℝ)*(Z*t)=(X:ℝ)*(fSum n X/X-Z*t) := by field_simp
    rw [eqv,abs_mul,abs_of_pos hxr]
    exact mul_le_mul_of_nonneg_left ha hxr.le
  have ha := abs_le.mp (hlin A le_rfl hAi)
  have hb := abs_le.mp (hlin i hAi le_rfl)
  have htZ : -τ  ≤  Z*t := by
    calc
      -τ  ≤  -τ*t := by nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr ht01.2)]
      _  ≤  _ := mul_le_mul_of_nonneg_right hz ht01.1
  have hia : (A:ℝ) ≤ i := by exact_mod_cast hAi
  have hdiff := mul_le_mul_of_nonneg_left htZ (sub_nonneg.mpr hia)
  have heqτ : (8*((R:ℝ)+1))*τ=δ := by dsimp [τ]; field_simp
  have htot : (i:ℝ)*τ  ≤  R*A*τ := mul_le_mul_of_nonneg_right hscale hτ.le
  have hgood : -(δ*(A:ℝ)) ≤ fSum n i-fSum n A := by
    have δeq : δ*(A:ℝ)=(8*((R:ℝ)+1))*τ*A := by rw [heqτ]
    nlinarith only [ha.1,ha.2,hb.1,hb.2,hdiff,htot,δeq,
      mul_nonneg (Nat.cast_nonneg R) (mul_nonneg hAr.le hτ.le),mul_nonneg hAr.le hτ.le]
  have hsplit := prefix_split (fun q => F n q) hAi
  change fSum n i=fSum n A+_ at hsplit
  linarith

end
end BandTail

end

end
end
end
end
end

end GoldbachGRHBandBase

section GoldbachGRHRamanujanMobius

open scoped BigOperators

namespace GoldbachExplicitModeledMajor

/-- The reduced-residue exponential sum at numerator one is the Möbius value. -/
theorem ram_one_eq_moebius (q : ℕ) :
    ram q 1 = (ArithmeticFunction.moebius q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hd (a : ℕ) : ¬ p ^ (a + 1) ∣ 1 := by
        intro ha
        exact (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt).ne' (Nat.dvd_one.mp ha)
      rw [ram_primePower p k 1 hp,
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero k), ite_eq_right (hd k)]
      cases k with
      | zero => norm_num
      | succ k => simp [hd k]
  | coprime q r hq hr hqr iq ir =>
    rw [ram_mul (by omega) (by omega) hqr, iq, ir,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr, Int.cast_mul]

end GoldbachExplicitModeledMajor


namespace GoldbachGRHWindow

/-- A reduced additive numerator has the exact Möbius/totient model. -/
theorem additiveModel_eq_moebius {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) := by
  rw [additiveModel_of_unit a ha]
  have h := additiveModel_eq_reduced_sum (q := q) 1
  have hr : additiveModel q 1 =
      GoldbachExplicitModeledMajor.ram q 1 / (q.totient : ℂ) := by
    simpa only [Nat.cast_one, GoldbachExplicitModeledMajor.ram,
      GoldbachExplicitModeledMajor.phase] using h
  rw [hr, GoldbachExplicitModeledMajor.ram_one_eq_moebius]

end GoldbachGRHWindow

end GoldbachGRHRamanujanMobius

section GoldbachGRHKernel

open MeasureTheory Set Finset
open scoped Interval

namespace GoldbachGRHKernel

open GoldbachFourthMoment (phase phase_add)

noncomputable def kernel (n : ℕ) : ℝ → ℂ :=
  GoldbachWindow.poly (n + 1) fun _ => 1

noncomputable def mass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-r)..r, ‖kernel n t‖ ^ 2

theorem kernel_eq_sum (n : ℕ) (t : ℝ) :
    kernel n t = ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) := by
  simp [kernel, GoldbachWindow.poly]

theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)

theorem kernel_periodic (n : ℕ) : Function.Periodic (kernel n) 1 := by
  intro t
  simp only [kernel_eq_sum, mul_add, mul_one, phase_add, phase_nat, mul_one]

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by
  rw [show kernel n = fun t => ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) from
    funext (kernel_eq_sum n)]
  unfold phase
  fun_prop

theorem reflect (n : ℕ) (t : ℝ) :
    kernel n t ^ 2 * phase (-(n : ℝ) * t) = (↑(‖kernel n t‖ ^ 2) : ℂ) := by
  simp only [kernel_eq_sum, ← Complex.normSq_eq_norm_sq]
  exact frontierMedcoreKernelReflection n t

theorem full_parseval (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖kernel n t‖ ^ 2) = (n : ℝ) + 1 := by
  simpa [kernel] using GoldbachWindow.parseval (n + 1) (fun _ => (1 : ℂ))

theorem mass_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ mass n r :=
  intervalIntegral.integral_nonneg_of_forall (by linarith) fun _ => sq_nonneg _

theorem mass_mono (n : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    mass n r ≤ mass n s := by
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hrs
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact ((kernel_continuous n).norm.pow 2).intervalIntegrable _ _

theorem mass_loss (n : ℕ) {r : ℝ} (hr : 0 < r) (hh : r ≤ 1 / 2) :
    0 ≤ (n : ℝ) + 1 - mass n r ∧
      (n : ℝ) + 1 - mass n r ≤ 1 / (2 * r) := by
  let F : ℝ → ℝ := fun t => ‖kernel n t‖ ^ 2
  have hF : Continuous F := (kernel_continuous n).norm.pow 2
  have hp : Function.Periodic F 1 := by
    intro t
    simp only [F, kernel_periodic n t]
  have hfull : (∫ t in (-r)..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := hp.intervalIntegral_add_eq (-r) 0
    rw [show -r + 1 = 1 - r by ring, zero_add] at h
    exact h.trans (full_parseval n)
  have hsplit :
      mass n r + (∫ t in r..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (-r) r) (hF.intervalIntegrable r (1 - r))
    exact h.trans hfull
  have htail : (n : ℝ) + 1 - mass n r = ∫ t in r..(1 - r), F t := by
    linarith only [hsplit]
  have hordered : r ≤ 1 - r := by linarith only [hh]
  have hrepr : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) =
      ∫ t in r..(1 - r), F t := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hordered,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr (Ioc_subset_Ioc hr.le (by linarith only [hr]))]
  have hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioc r (1 - r) →
      r ≤ |(1 : ℝ) * t - (round ((1 : ℝ) * t) : ℝ)| := by
    intro t ht hz
    rw [one_mul]
    by_cases hhalf : t < 1 / 2
    · have hround : round t = 0 :=
        round_eq_zero_iff.mpr ⟨by linarith only [ht.1], hhalf⟩
      simp only [hround, Int.cast_zero, sub_zero, abs_of_nonneg ht.1]
      exact hz.1.le
    · have hround : round t = 1 := round_eq_iff.mpr (by
        change ((1 : ℤ) : ℝ) - 1 / 2 ≤ t ∧ t < ((1 : ℤ) : ℝ) + 1 / 2
        push_cast
        constructor <;> linarith only [hhalf, ht.2])
      simp only [hround, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith only [hz.2]
  have hbound := goldbach_geometric_tail_l2 (n + 1) 1 Nat.one_pos r hr hh
    (Ioc r (1 - r)) measurableSet_Ioc hcut
  simp only [Nat.cast_one, one_mul] at hbound
  have hboundF : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) ≤ 1 / (2 * r) := by
    simpa only [F, kernel_eq_sum, phase, mul_assoc] using hbound
  rw [hrepr] at hboundF
  rw [htail]
  exact ⟨intervalIntegral.integral_nonneg_of_forall hordered (fun _ => sq_nonneg _), hboundF⟩

end GoldbachGRHKernel

end GoldbachGRHKernel

section GoldbachGRHArcs

open Finset MeasureTheory Set
open scoped Interval

namespace GoldbachGRHArcs

noncomputable abbrev cap := GoldbachFourthGeometry.wide

/-- Indices of reduced fractions in the closed unit interval. The two endpoints are both
present when the denominator is one. -/
def centers (U : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 U) ×ˢ (Finset.range (U+1))).filter
    (fun i => i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1)

theorem mem_centers {U : ℕ} {i : ℕ × ℕ} :
    i ∈ centers U ↔ 1 ≤ i.1 ∧ i.1 ≤ U ∧ i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1 := by
  simp only [centers, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, _⟩, h₃, h₄⟩
    exact ⟨h₁,h₂,h₃,h₄⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨⟨h₁,h₂⟩, by omega⟩,h₃,h₄⟩

theorem centers_mono {Q U : ℕ} (h : Q ≤ U) : centers Q ⊆ centers U := by
  intro i hi
  obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
  exact mem_centers.mpr ⟨h₁,h₂.trans h,h₃,h₄⟩

noncomputable def radius (n H q : ℕ) : ℝ := (H : ℝ) / ((q : ℝ) * (n : ℝ))

noncomputable def center (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) / (i.1 : ℝ)

noncomputable def arc (n H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ radius n H i.1}

theorem measurable_arc (n H : ℕ) (i : ℕ × ℕ) : MeasurableSet (arc n H i) := by
  unfold arc
  exact measurableSet_le (show Continuous (fun t : ℝ => |t - center i|) by fun_prop).measurable
    measurable_const

theorem arc_eq_Icc (n H : ℕ) (i : ℕ × ℕ) :
    arc n H i = Set.Icc (center i - radius n H i.1) (center i + radius n H i.1) := by
  ext t
  change |t - center i| ≤ radius n H i.1 ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem mem_cap {n U H : ℕ} {t : ℝ} :
    t ∈ cap n U H ↔ ∃ i ∈ centers U, t ∈ arc n H i := by
  constructor
  · rintro ⟨q,a,h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨(q,a),mem_centers.mpr ⟨h₁,h₂,h₃,h₄⟩,h₅⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
    exact ⟨q,a,h₁,h₂,h₃,h₄,ht⟩

theorem measurable_cap (n U H : ℕ) : MeasurableSet (cap n U H) := by
  have h : cap n U H = ⋃ i ∈ centers U, arc n H i := by
    ext t
    rw [mem_cap]
    simp only [Set.mem_iUnion]
    constructor <;> rintro ⟨i,hi,ht⟩ <;> exact ⟨i,hi,ht⟩
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurable_arc n H i

theorem arc_mono {n R H : ℕ} (h : R ≤ H) (i : ℕ × ℕ) : arc n R i ⊆ arc n H i := by
  intro t ht
  change |t - center i| ≤ radius n R i.1 at ht
  change |t - center i| ≤ radius n H i.1
  exact ht.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

theorem cap_mono {n Q U R H : ℕ} (hQ : Q ≤ U) (hH : R ≤ H) :
    cap n Q R ⊆ cap n U H := by
  intro t ht
  obtain ⟨i,hi,hit⟩ := mem_cap.mp ht
  exact mem_cap.mpr ⟨i,centers_mono hQ hi,arc_mono hH i hit⟩

theorem common_arc_unique {n U H : ℕ} (hbudget : 2 * H * U < n)
    {i j : ℕ × ℕ} (hi : i ∈ centers U) (hj : j ∈ centers U) {t : ℝ}
    (hti : t ∈ arc n H i) (htj : t ∈ arc n H j) : i = j := by
  obtain ⟨hi₁,hi₂,_,hi₄⟩ := mem_centers.mp hi
  obtain ⟨hj₁,hj₂,_,hj₄⟩ := mem_centers.mp hj
  obtain ⟨h₁,h₂⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point
    hbudget hi₁ hj₁ hi₂ hj₂ hi₄ hj₄ hti htj
  exact Prod.ext h₁ h₂

/-- A wide arc clipped to the unit interval, with its narrow interval removed when appropriate. -/
noncomputable def cell (n Q H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  (arc n H i \ (if i.1 ≤ Q then arc n Q i else ∅)) ∩ Set.Ioc 0 1

theorem measurable_cell (n Q H : ℕ) (i : ℕ × ℕ) : MeasurableSet (cell n Q H i) := by
  unfold cell
  apply MeasurableSet.inter _ measurableSet_Ioc
  apply (measurable_arc n H i).diff
  split
  · exact measurable_arc n Q i
  · exact MeasurableSet.empty

theorem cell_disjoint {n Q U H : ℕ} (hbudget : 2 * H * U < n) :
    (↑(centers U) : Set (ℕ × ℕ)).PairwiseDisjoint (cell n Q H) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  exact hij (common_arc_unique hbudget hi hj hti.1.1 htj.1.1)

theorem cells_eq {n Q U H : ℕ} (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) :
    (⋃ i ∈ centers U, cell n Q H i) = (cap n U H \ cap n Q Q) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨⟨mem_cap.mpr ⟨i,hi,ht.1.1⟩,?_⟩, ht.2⟩
    intro hN
    obtain ⟨j,hj,htj⟩ := mem_cap.mp hN
    have he := common_arc_unique hbudget hi (centers_mono hQ hj) ht.1.1 (arc_mono hH j htj)
    subst j
    apply ht.1.2
    rw [ite_eq_left (mem_centers.mp hj).2.1]
    exact htj
  · rintro ⟨⟨ht,hnot⟩,hunit⟩
    obtain ⟨i,hi,hti⟩ := mem_cap.mp ht
    refine ⟨i,hi,⟨⟨hti,?_⟩,hunit⟩⟩
    by_cases hic : i.1 ≤ Q
    · rw [ite_eq_left hic]
      intro hnarrow
      apply hnot
      obtain ⟨h₁,_,h₃,h₄⟩ := mem_centers.mp hi
      exact mem_cap.mpr ⟨i,mem_centers.mpr ⟨h₁,hic,h₃,h₄⟩,hnarrow⟩
    · simp [hic]

theorem integrate_difference_eq_sum {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t) =
      ∑ i ∈ centers U, ∫ t in cell n Q H i, F t := by
  have hm := (measurable_cap n U H).diff (measurable_cap n Q Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    inter_comm, ← cells_eq hQ hH hbudget]
  exact integral_biUnion_finset (centers U) (fun i _ => measurable_cell n Q H i)
    (cell_disjoint hbudget) (fun i _ => hint.mono_set inter_subset_right)

theorem integrate_middle_split {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U Q \ cap n Q Q).indicator F t) +
      (∫ t in (0 : ℝ)..1, (cap n U H \ cap n U Q).indicator F t) =
        ∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t := by
  let L := cap n Q Q
  let M := cap n U Q
  let W := cap n U H
  have hLM : L ⊆ M := cap_mono hQ le_rfl
  have hMW : M ⊆ W := cap_mono le_rfl hH
  have hm := (measurable_cap n U Q).diff (measurable_cap n Q Q)
  have hw := (measurable_cap n U H).diff (measurable_cap n U Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  have hmi : IntervalIntegrable ((M \ L).indicator F) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint.indicator hm)
  have hwi : IntervalIntegrable ((W \ M).indicator F) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint.indicator hw)
  change (∫ t in (0 : ℝ)..1, (M \ L).indicator F t) +
    (∫ t in (0 : ℝ)..1, (W \ M).indicator F t) =
    ∫ t in (0 : ℝ)..1, (W \ L).indicator F t
  rw [← intervalIntegral.integral_add hmi hwi]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases hl : t ∈ L
  · have hmt := hLM hl
    simp [hl, hmt]
  · by_cases hmt : t ∈ M
    · have hwt := hMW hmt
      simp [hl, hmt, hwt]
    · by_cases hwt : t ∈ W <;> simp [hl, hmt, hwt]

end GoldbachGRHArcs

end GoldbachGRHArcs

section GoldbachGRHCenterSums

open scoped BigOperators

namespace GoldbachGRHArcs

/-- Group the reduced arc centers by denominator. -/
theorem sum_centers_eq (U : ℕ) {A : Type*} [AddCommMonoid A] (F : ℕ × ℕ → A) :
    (∑ i ∈ centers U, F i) =
      ∑ q ∈ Finset.Icc 1 U, ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
        F (q, a) := by
  rw [centers, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  change (∑ a ∈ Finset.range (U + 1), if a ≤ q ∧ a.Coprime q then F (q, a) else 0) = _
  rw [← Finset.sum_filter]
  have hqU := (Finset.mem_Icc.mp hq).2
  have hs : (Finset.range (U + 1)).filter (fun a => a ≤ q ∧ a.Coprime q) =
      (Finset.range (q + 1)).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, ha, hcop⟩
      exact ⟨Nat.lt_succ_of_le ha, hcop⟩
    · rintro ⟨ha, hcop⟩
      exact ⟨by omega, by omega, hcop⟩
  rw [hs]

/-- The least nonnegative representatives enumerate all residues once. -/
theorem sum_range_natCast_zmod (q : ℕ) [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : ZMod q → A) :
    (∑ a ∈ Finset.range q, f (a : ZMod q)) = ∑ a : ZMod q, f a := by
  apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hab
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro a _
    rfl

/-- Restrict to the reduced numerators of the closed unit interval. The factor
    two allows the endpoints \(0/1\) and \(1/1\) to share their residue. -/
theorem sum_numerators_le_real (q : ℕ) [NeZero q] (f : ZMod q → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q), f (a : ZMod q)) ≤
      2 * (∑ a : ZMod q, f a) := by
  calc
    _ ≤ ∑ a ∈ Finset.range (q + 1), f (a : ZMod q) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hf a)
    _ = (∑ a ∈ Finset.range q, f (a : ZMod q)) + f (q : ZMod q) :=
      Finset.sum_range_succ _ _
    _ = (∑ a : ZMod q, f a) + f 0 := by
      rw [sum_range_natCast_zmod, ZMod.natCast_self]
    _ ≤ _ := by
      have hzero : f 0 ≤ ∑ a : ZMod q, f a :=
        Finset.single_le_sum (fun a _ => hf a) (Finset.mem_univ 0)
      linarith

end GoldbachGRHArcs

end GoldbachGRHCenterSums

section GoldbachGRHArcTransport

open MeasureTheory
open Set hiding center
open scoped Interval

namespace GoldbachGRHArcTransport

open GoldbachGRHArcs

private theorem radius_nonnegative (n H q : ℕ) : 0 ≤ radius n H q := by
  unfold radius
  positivity

private theorem continuous_translate {E : Type*} [TopologicalSpace E]
    {G : ℝ → E} (hG : Continuous G) (c : ℝ) : Continuous (fun t => G (t - c)) :=
  hG.comp (continuous_id.sub continuous_const)

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_integral (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  have hr := radius_nonnegative n H i.1
  rw [arc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hr] :
      center i - radius n H i.1 ≤ center i + radius n H i.1),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

private theorem clipped_arc_integral_closed (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in arc n H i ∩ Icc 0 1, G (t - center i) := by
  apply setIntegral_congr_set
  have h : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
  filter_upwards [h] with t ht
  simp only [mem_inter_iff, ht]

theorem clipped_arc_integral_of_interior (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E)
    (hleft : radius n H i.1 ≤ center i) (hright : center i + radius n H i.1 ≤ 1) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [clipped_arc_integral_closed, inter_eq_left.mpr, arc_integral]
  rw [arc_eq_Icc]
  exact Icc_subset_Icc (sub_nonneg.mpr hleft) hright

theorem clipped_arc_integral_zero (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 0) ∩ Ioc 0 1, G (t - center (1, 0))) =
      ∫ t in (0 : ℝ)..(radius n H 1), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 0) = 0 by norm_num [center], zero_sub, zero_add, sub_zero]
  rw [Icc_inter_Icc, sup_eq_right.mpr (neg_nonpos.mpr hnonneg), inf_eq_left.mpr hr,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hnonneg]

theorem clipped_arc_integral_one (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 1) ∩ Ioc 0 1, G (t - center (1, 1))) =
      ∫ t in (-(radius n H 1))..(0 : ℝ), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 1) = 1 by norm_num [center] ]
  rw [Icc_inter_Icc, sup_eq_left.mpr (sub_nonneg.mpr hr),
    inf_eq_right.mpr (by linarith only [hnonneg] : (1 : ℝ) ≤ 1 + radius n H 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hnonneg] :
      1 - radius n H 1 ≤ 1), intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem cell_integral_eq_clipped_sub {n Q H : ℕ} (hQH : Q ≤ H) (i : ℕ × ℕ)
    (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H i, G (t - center i)) =
      (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) -
        if i.1 ≤ Q then (∫ t in arc n Q i ∩ Ioc 0 1, G (t - center i)) else 0 := by
  by_cases hq : i.1 ≤ Q
  · simp only [cell, ite_eq_left hq]
    rw [show (arc n H i \ arc n Q i) ∩ Ioc (0 : ℝ) 1 =
        (arc n H i ∩ Ioc 0 1) \ (arc n Q i ∩ Ioc 0 1) by
      ext t
      simp only [mem_inter_iff, mem_sdiff]
      tauto]
    apply setIntegral_sdiff ((measurable_arc n Q i).inter measurableSet_Ioc)
    · exact ((continuous_translate hG (center i)).intervalIntegrable 0 1).1.mono_set inter_subset_right
    · exact inter_subset_inter_left _ (arc_mono hQH i)
  · simp [cell, hq]

end Integral

/-- A nonnegative translated integrand on the clipped cell is bounded by its full window. -/
theorem cell_l2_le (n Q H : ℕ) (i : ℕ × ℕ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) :
    (∫ t in cell n Q H i, G (t - center i)) ≤
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [← arc_integral]
  apply setIntegral_mono_set
  · rw [arc_eq_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
    exact ((continuous_translate hG (center i)).intervalIntegrable _ _).1
  · exact Filter.Eventually.of_forall fun t => hG0 (t - center i)
  · exact (show cell n Q H i ⊆ arc n H i from fun _ ht => ht.1.1).eventuallySubset

theorem arc_interior_bounds {n H q a : ℕ} (hH : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) :
    radius n H q ≤ center (q, a) ∧ center (q, a) + radius n H q ≤ 1 := by
  have ha0 : 1 ≤ a := by
    by_contra! hn
    have ha' : a = 0 := by omega
    subst a
    have h := (Nat.coprime_zero_left q).mp hcop
    omega
  have haq : a + 1 ≤ q := by
    by_contra! hn
    have ha' : a = q := by omega
    subst a
    have h : q = 1 := by simpa [Nat.Coprime] using hcop
    omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr : radius n H q ≤ 1 / (q : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [radius]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hHn : (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hH
    unfold radius
    apply (div_le_iff₀ (mul_pos hqR hnR)).mpr
    rw [← mul_assoc, one_div_mul_cancel hqR.ne', one_mul]
    exact hHn
  refine ⟨hr.trans ?_, (add_le_add_right hr (center (q, a))).trans ?_⟩
  · unfold center
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le
  · unfold center
    rw [← add_div]
    apply (div_le_iff₀ hqR).mpr
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using (show ((a + 1 : ℕ) : ℝ) ≤ q by
      exact_mod_cast haq)

theorem radius_one_le {n H : ℕ} (hH : H ≤ n) : radius n H 1 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [radius]
  · simpa [radius] using (div_le_one (by exact_mod_cast hn : (0:ℝ) < n)).mpr
      (show (H : ℝ) ≤ n by exact_mod_cast hH)


theorem cell_integral_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (q, a), G (t - center (q, a))) =
      (∫ t in (-(radius n H q))..(radius n H q), G t) -
        if q ≤ Q then (∫ t in (-(radius n Q q))..(radius n Q q), G t) else 0 := by
  obtain ⟨hHl, hHr⟩ := arc_interior_bounds hHn hq ha hcop
  obtain ⟨hQl, hQr⟩ := arc_interior_bounds (hQH.trans hHn) hq ha hcop
  rw [cell_integral_eq_clipped_sub hQH (q, a) G hG,
    clipped_arc_integral_of_interior n H (q, a) G hHl hHr,
    clipped_arc_integral_of_interior n Q (q, a) G hQl hQr]

/-- The two denominator-one cells assemble to a full translated window. -/
theorem cell_integral_endpoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (1, 0), G (t - center (1, 0))) +
      (∫ t in cell n Q H (1, 1), G (t - center (1, 1))) =
      (∫ t in (-(radius n H 1))..(radius n H 1), G t) -
        if 1 ≤ Q then (∫ t in (-(radius n Q 1))..(radius n Q 1), G t) else 0 := by
  have hQn := hQH.trans hHn
  have hfull (R : ℕ) :
      (∫ t in (0 : ℝ)..(radius n R 1), G t) +
        (∫ t in (-(radius n R 1))..(0 : ℝ), G t) =
          ∫ t in (-(radius n R 1))..(radius n R 1), G t := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  simp only [cell_integral_eq_clipped_sub hQH _ G hG,
    clipped_arc_integral_zero n H G (radius_one_le hHn),
    clipped_arc_integral_zero n Q G (radius_one_le hQn),
    clipped_arc_integral_one n H G (radius_one_le hHn),
    clipped_arc_integral_one n Q G (radius_one_le hQn)]
  by_cases h : 1 ≤ Q
  · simp only [ite_eq_left h]
    rw [← hfull H, ← hfull Q]
    abel
  · simpa only [ite_eq_right h, sub_zero] using hfull H

theorem cell_kernel_interior {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hcop : Nat.Coprime a q) :
    (∫ t in cell n Q H (q, a), ‖GoldbachGRHKernel.kernel n (t - center (q, a))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H q) -
        if q ≤ Q then GoldbachGRHKernel.mass n (radius n Q q) else 0 :=
  cell_integral_interior hQH hHn hq ha hcop _
    ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

theorem cell_kernel_endpoints {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∫ t in cell n Q H (1, 0), ‖GoldbachGRHKernel.kernel n (t - center (1, 0))‖ ^ 2) +
      (∫ t in cell n Q H (1, 1), ‖GoldbachGRHKernel.kernel n (t - center (1, 1))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H 1) -
        if 1 ≤ Q then GoldbachGRHKernel.mass n (radius n Q 1) else 0 :=
  cell_integral_endpoints hQH hHn _ ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

end GoldbachGRHArcTransport

end GoldbachGRHArcTransport

section GoldbachGRHModelDef

namespace GoldbachGRHModel

/-- The principal model on a single reduced rational arc. -/
noncomputable def model (n : ℕ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius i.1 : ℂ) / (i.1.totient : ℂ)) *
    GoldbachGRHKernel.kernel n (t - GoldbachGRHArcs.center i)

theorem model_continuous (n : ℕ) (i : ℕ × ℕ) : Continuous (model n i) :=
  continuous_const.mul ((GoldbachGRHKernel.kernel_continuous n).comp
    (continuous_id.sub continuous_const))

end GoldbachGRHModel

end GoldbachGRHModelDef

section GoldbachGRHModelAssembly

open Finset MeasureTheory
open scoped ComplexConjugate

namespace GoldbachGRHModelAssembly

open GoldbachGRHArcs (cell centers center radius)
open GoldbachGRHKernel (kernel mass)
open GoldbachFourthMoment (phase phase_add)
open GoldbachGRHModel (model)
open GoldbachExplicitModeledMajor (coefficient ram ram_one_eq_moebius)

noncomputable def massDifference (n Q H q : ℕ) : ℝ :=
  mass n (radius n H q) - if q ≤ Q then mass n (radius n Q q) else 0

noncomputable def signedFactor (n q a : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
    phase (-(n : ℝ) * center (q, a))

private theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  symm
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem signedFactor_zero (n : ℕ) : signedFactor n 1 0 = 1 := by
  simp [signedFactor, center, phase]

private theorem signedFactor_one (n : ℕ) : signedFactor n 1 1 = 1 := by
  simp [signedFactor, center, phase_neg, GoldbachGRHKernel.phase_nat]

theorem model_square_eq (n q a : ℕ) (t : ℝ) :
    model n (q, a) t ^ 2 * phase (-(n : ℝ) * t) =
      signedFactor n q a * (↑(‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  have hphase : -(n : ℝ) * t =
      -(n : ℝ) * center (q, a) + -(n : ℝ) * (t - center (q, a)) := by ring
  rw [← GoldbachGRHKernel.reflect n (t - center (q, a)), model, hphase, phase_add]
  unfold signedFactor
  ring

theorem cell_model_integral (n Q H q a : ℕ) :
    (∫ t in cell n Q H (q, a), model n (q, a) t ^ 2 * phase (-(n : ℝ) * t)) =
      signedFactor n q a *
        (↑(∫ t in cell n Q H (q, a), ‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  simp_rw [model_square_eq]
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]

theorem sum_signedFactor (n q : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), signedFactor n q a) =
      coefficient q n := by
  rw [coefficient, ram_one_eq_moebius, ram, map_sum, Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  unfold signedFactor
  congr 1
  have h : -(n : ℝ) * center (q, a) = -((n : ℝ) * a / q) := by
    simp only [center, ← mul_div_assoc, neg_mul, neg_div]
  rw [h, phase_neg]
  rfl

/-- Grouping the centered kernels by denominator recovers the exact Ramanujan model. -/
theorem sum_cell_model {n Q H U : ℕ} (_hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)) =
      ∑ q ∈ Icc 1 U, coefficient q n * (massDifference n Q H q : ℂ) := by
  classical
  rw [GoldbachGRHArcs.sum_centers_eq]
  refine sum_congr rfl fun q hq => ?_
  have hq1 := (mem_Icc.mp hq).1
  by_cases hqOne : q = 1
  · subst q
    have hf : ((range (1 + 1)).filter (fun a : ℕ => Nat.Coprime a 1)) =
        ({0, 1} : Finset ℕ) := by
      ext a
      simp only [mem_filter, mem_range, Nat.coprime_one_right_iff, and_true,
        mem_insert, mem_singleton]
      omega
    rw [hf, sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [cell_model_integral, signedFactor_zero, signedFactor_one, one_mul,
      ← Complex.ofReal_add, GoldbachGRHArcTransport.cell_kernel_endpoints hQH hHn,
      GoldbachExplicitModeledMajor.coefficient_one, massDifference]
  · have hq2 : 2 ≤ q := by omega
    have hf : ((range (q + 1)).filter (fun a => Nat.Coprime a q)) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨haq, hcop⟩
        have hne : a ≠ q := by
          intro heq
          subst a
          have h : q = 1 := by simpa [Nat.Coprime] using hcop
          exact hqOne h
        exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne, hcop⟩
      · rintro ⟨haq, hcop⟩
        exact ⟨haq.trans (Nat.lt_succ_self q), hcop⟩
    rw [hf, ← sum_signedFactor, Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    rw [cell_model_integral, GoldbachGRHArcTransport.cell_kernel_interior hQH hHn hq2
      (mem_range.mp haq).le hcop, massDifference]

theorem sum_cell_model_re {n Q H U : ℕ} (hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)).re =
      ∑ q ∈ Icc 1 U, (coefficient q n).re * massDifference n Q H q := by
  rw [sum_cell_model hU hQH hHn, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end GoldbachGRHModelAssembly

end GoldbachGRHModelAssembly

section GoldbachGRHWindowEnergy

open Finset MeasureTheory
open scoped Interval

namespace GoldbachGRHWindowEnergy

open GoldbachWindow

/-- The low-frequency estimate summed over a finite family with a common window length. -/
theorem sum_low_frequency_le {ι : Type*} (s : Finset ι) (N h : ℕ)
    (b : ι → ℕ → ℂ) (δ C : ℝ) (hh : 0 < h) (hδ : 0 ≤ δ)
    (hwidth : 6 * (h : ℝ) * δ ≤ 1)
    (hwindow : ∀ m ∈ range (N + h), ∑ i ∈ s, ‖moving N h (b i) m‖^2 ≤ C) :
    (h : ℝ)^2 / 4 * (∑ i ∈ s, ∫ t in (-δ)..δ, ‖poly N (b i) t‖^2) ≤
      ((N + h : ℕ) : ℝ) * C := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ s, ∑ m ∈ range (N + h), ‖moving N h (b i) m‖^2 :=
      Finset.sum_le_sum fun i _ => low_frequency_le N h (b i) δ hh hδ hwidth
    _ = ∑ m ∈ range (N + h), ∑ i ∈ s, ‖moving N h (b i) m‖^2 := Finset.sum_comm
    _ ≤ ∑ _ ∈ range (N + h), C := Finset.sum_le_sum hwindow
    _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-- Choose the integer window by rounding down the reciprocal of the frequency width. -/
theorem sum_low_frequency_width_le {ι : Type*} (s : Finset ι) (N : ℕ)
    (b : ι → ℕ → ℂ) (δ C : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/24)
    (hlarge : 1 ≤ (N : ℝ) * δ) (hC : 0 ≤ C)
    (hwindow : ∀ m : ℕ, ∑ i ∈ s,
      ‖moving N ⌊1 / (12 * δ)⌋₊ (b i) m‖^2 ≤ C) :
    (∑ i ∈ s, ∫ t in (-δ)..δ, ‖poly N (b i) t‖^2) ≤ 4608 * (N : ℝ) * δ^2 * C := by
  let h := ⌊1 / (12 * δ)⌋₊
  have hz : 0 < 12 * δ := by positivity
  have hrec : 2 ≤ 1 / (12 * δ) := (le_div_iff₀ hz).2 (by linarith)
  have hh : 0 < h := lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_floor (by simpa using hrec))
  have hhlo : 1 / (24 * δ) ≤ (h : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (1 / (12 * δ))
    change 1 / (12 * δ) < (h : ℝ) + 1 at hfloor
    have heq : 1 / (24 * δ) = (1 / (12 * δ)) / 2 := by ring
    rw [heq]
    linarith
  have hhhi : (h : ℝ) ≤ 1 / (12 * δ) := Nat.floor_le (by positivity)
  have hwidth : 6 * (h : ℝ) * δ ≤ 1 := by
    have h := (le_div_iff₀ hz).1 hhhi
    nlinarith only [h]
  have hhN : (h : ℝ) ≤ (N : ℝ) := hhhi.trans <|
    (div_le_iff₀ hz).2 (by nlinarith only [hlarge])
  have hb := sum_low_frequency_le s N h b δ C hh hδ.le hwidth (fun m _ => hwindow m)
  let E := ∑ i ∈ s, ∫ t in (-δ)..δ, ‖poly N (b i) t‖^2
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro i hi
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hhscale : 1 ≤ (24 * δ) * (h : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < 24 * δ)).1 hhlo
    simpa [mul_comm] using h
  have hEbound : (h : ℝ)^2 / 4 * E ≤ 2 * (N : ℝ) * C := by
    exact hb.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith) hC)
  have hsq := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hhscale 2
  calc
    E ≤ ((24 * δ) * (h : ℝ))^2 * E := by
      simpa only [one_pow, one_mul] using (mul_le_mul_of_nonneg_right hsq hE)
    _ = (4 * (24 * δ)^2) * ((h : ℝ)^2 / 4 * E) := by ring
    _ ≤ (4 * (24 * δ)^2) * (2 * (N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hEbound (by positivity)
    _ = _ := by ring

/-- Young's inequality written with the energy of the original sum. -/
private theorem norm_square_sub_square_le (z w : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖z^2 - w^2‖ ≤ (1 + 1/η) * ‖z-w‖^2 + η * ‖z‖^2 := by
  have hfactor : z^2 - w^2 = (2 : ℂ) * z * (z-w) - (z-w)^2 := by ring
  have hmain :
      2 * ‖z‖ * ‖z - w‖ ≤ (1 / η) * ‖z - w‖^2 + η * ‖z‖^2 := by
    apply (le_of_mul_le_mul_right ?_ hη)
    have hsq := sq_nonneg (η * ‖z‖ - ‖z-w‖)
    field_simp
    nlinarith only [hsq]
  calc
    _ ≤ ‖(2 : ℂ) * z * (z-w)‖ + ‖(z-w)^2‖ := hfactor ▸ norm_sub_le _ _
    _ = 2 * ‖z‖ * ‖z-w‖ + ‖z-w‖^2 := by simp [norm_pow]
    _ ≤ _ := by linarith [hmain]

set_option maxHeartbeats 1500000 in
/-- On disjoint sets, compare the squared model with the original squared sum using its
global energy. The factors of modulus at most one can encode any target frequency. -/
theorem sum_setIntegral_square_difference_le {ι : Type*} (s : Finset ι)
    (D : ι → Set ℝ) (hD : ∀ i ∈ s, MeasurableSet (D i))
    (hsub : ∀ i ∈ s, D i ⊆ Set.Ioc 0 1)
    (hdisj : (↑s : Set ι).PairwiseDisjoint D) (S : ℝ → ℂ) (M : ι → ℝ → ℂ)
    (osc : ℝ → ℂ) (hS : Continuous S) (hM : ∀ i ∈ s, Continuous (M i))
    (hosc : Continuous osc) (hnorm : ∀ t, ‖osc t‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    (∑ i ∈ s, ‖∫ t in D i, (S t ^ 2 - M i t ^ 2) * osc t‖) ≤
      (1 + 1/η) * (∑ i ∈ s, ∫ t in D i, ‖S t - M i t‖^2) +
      η * (∫ t in (0 : ℝ)..1, ‖S t‖^2) := by
  let A (t : ℝ) := ‖S t‖^2
  let C (i : ι) (t : ℝ) := ‖S t - M i t‖^2
  have hA : Continuous A := hS.norm.pow 2
  have hAI : IntegrableOn A (Set.Ioc 0 1) volume := (hA.intervalIntegrable 0 1).1
  have hAi (i : ι) (hi : i ∈ s) : IntegrableOn A (D i) volume := hAI.mono_set (hsub i hi)
  have hUsed : (⋃ i ∈ s, D i) ⊆ Set.Ioc 0 1 := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨i, hi, ht⟩ := ht
    exact hsub i hi ht
  have htotal : (∑ i ∈ s, ∫ t in D i, A t) ≤ ∫ t in (0 : ℝ)..1, A t := by
    rw [← integral_biUnion_finset s hD hdisj hAi,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact setIntegral_mono_set hAI (Filter.Eventually.of_forall (fun _ => by positivity))
      hUsed.eventuallySubset
  have hlocal (i : ι) (hi : i ∈ s) :
      ‖∫ t in D i, (S t ^ 2 - M i t ^ 2) * osc t‖ ≤
        (1+1/η) * (∫ t in D i, C i t) + η * (∫ t in D i, A t) := by
    have hCt : Continuous (C i) := ((hS.sub (hM i hi)).norm.pow 2)
    have hCi : IntegrableOn (C i) (D i) volume :=
      (hCt.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    have hF : Continuous fun t => (S t ^ 2 - M i t ^ 2) * osc t :=
      ((hS.pow 2).sub ((hM i hi).pow 2)).mul hosc
    have hFi : IntegrableOn (fun t => ‖(S t ^ 2 - M i t ^ 2) * osc t‖) (D i) volume :=
      (hF.norm.intervalIntegrable 0 1).1.mono_set (hsub i hi)
    calc
      _ ≤ ∫ t in D i, ‖(S t ^ 2 - M i t ^ 2) * osc t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in D i, (1+1/η) * C i t + η * A t := by
        apply integral_mono hFi ((hCi.const_mul _).add ((hAi i hi).const_mul _))
        intro t
        change ‖(S t ^ 2 - M i t ^ 2) * osc t‖ ≤
          (1+1/η) * ‖S t - M i t‖^2 + η * ‖S t‖^2
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hnorm t)).trans
          (norm_square_sub_square_le (S t) (M i t) hη)
      _ = _ := by rw [integral_add (hCi.const_mul _) ((hAi i hi).const_mul _),
        integral_const_mul, integral_const_mul]
  calc
    _ ≤ ∑ i ∈ s, ((1+1/η) * (∫ t in D i, C i t) + η * (∫ t in D i, A t)) :=
      Finset.sum_le_sum hlocal
    _ = (1+1/η) * (∑ i ∈ s, ∫ t in D i, C i t) + η * (∑ i ∈ s, ∫ t in D i, A t) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left htotal hη.le)

end GoldbachGRHWindowEnergy

end GoldbachGRHWindowEnergy

section GoldbachGRHAnalytic

open Finset
open scoped Interval Classical

namespace GoldbachGRHAnalytic

open GoldbachFourthMoment (phase phase_add primeSum primeWeight)
open GoldbachWindow (poly moving)
open GoldbachGRHWindow (additiveModel primeLog)
open GoldbachGRHKernel (kernel)

/-- Fourier coefficients of the deviation from the principal local model. -/
noncomputable def errorCoeff {q : ℕ} [NeZero q] (a : ZMod q) (k : ℕ) : ℂ :=
  primeLog k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a

theorem shifted_error_eq {q : ℕ} [NeZero q] (n a : ℕ) (β : ℝ) :
    poly (n+1) (errorCoeff (a : ZMod q)) β =
      primeSum n ((a : ℝ) / (q:ℝ) + β) -
        additiveModel q (a : ZMod q) * kernel n β := by
  unfold kernel poly errorCoeff primeSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sub_mul, one_mul, GoldbachGRHWindow.stdAddChar_nat_pair]
  change (primeWeight k : ℂ) * phase ((a:ℝ)*(k:ℝ)/(q:ℝ)) * phase ((k:ℝ)*β) -
    additiveModel q (a : ZMod q) * phase ((k:ℝ)*β) =
      (primeWeight k : ℂ) * phase ((k:ℝ)*((a:ℝ)/(q:ℝ)+β)) -
        additiveModel q (a : ZMod q) * phase ((k:ℝ)*β)
  rw [mul_assoc, ← phase_add]
  congr 3
  ring

theorem prime_sum_energy_le (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in (0:ℝ)..1, ‖primeSum n t‖^2) ≤ ((n:ℝ)+1)*(Real.log (n:ℝ))^2 := by
  change (∫ t in (0:ℝ)..1, ‖poly (n+1) (fun k => (primeWeight k:ℂ)) t‖^2) ≤ _
  rw [GoldbachWindow.parseval]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  calc
    _ ≤ ∑ k ∈ range (n+1), (Real.log (n:ℝ))^2 := by
      apply Finset.sum_le_sum
      intro k hk
      unfold primeWeight
      by_cases hp : k.Prime
      · rw [ite_eq_left hp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
          (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
        exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
          (Real.log_le_log (by exact_mod_cast hp.pos)
            (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk))) _
      · simpa [hp] using (sq_nonneg (Real.log (n:ℝ)))
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]


end GoldbachGRHAnalytic
end GoldbachGRHAnalytic

section GoldbachGRHBudget

open Filter Finset
open scoped Topology

namespace GoldbachGRHBudget

def narrow (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * narrow n

private theorem log_nat_le (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnon : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hpow : (2:ℝ)^(Nat.log 2 (n+2)) ≤ ((n+2 : ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n:ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0≤(_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm, hraw, hlog]

theorem eventually_log_pow_le (k : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n:ℝ))^k ≤ c * (n:ℝ)^a := by
  have h := (isLittleO_log_rpow_rpow_atTop (s:=a) k ha).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)]
    using (le_abs_self ((Real.log (n:ℝ))^(k:ℝ))).trans hn

theorem eventual_geometry :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ narrow n ∧ narrow n ≤ cutoff n ∧ cutoff n ≤ n ∧
      24 * width n ≤ n ∧ 2 * width n * cutoff n < n := by
  obtain ⟨N,hN⟩ := GoldbachFourthGeometry.eventually_strip_budget
  have hroot : ∀ᶠ n : ℕ in atTop, (3:ℝ) ≤ (n:ℝ)^(1/3:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (eventually_ge_atTop (3:ℝ))
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2:ℕ), hroot,
    eventually_log_pow_le 2 (1/3) (1/32) (by norm_num) (by norm_num)] with n hnN hn h3 hlog
  obtain ⟨hU,hH,hNn⟩ := hN n hnN
  change 2 * width n * (4 * cutoff n) < n at hU
  have hQ₀ : 1 ≤ narrow n := by
    unfold narrow
    exact Nat.pow_pos (Nat.log_pos (by decide) (by omega))
  have hQ : narrow n ≤ cutoff n := by
    apply Nat.le_floor
    calc
      (narrow n : ℝ) ≤ (4 * Real.log (n:ℝ))^2 := by
        unfold narrow
        push_cast
        exact pow_le_pow_left₀ (by positivity) (log_nat_le n hn) _
      _ = 16 * Real.log (n:ℝ)^2 := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) := by
        have ht := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤16 by norm_num)
        nlinarith only [ht, Real.rpow_nonneg (Nat.cast_nonneg n) (1/3:ℝ)]
  have hU3 : 3 ≤ cutoff n := Nat.le_floor (by exact h3)
  have hW : 24 * width n ≤ n := by
    have ht := Nat.mul_le_mul_left (2*width n) (show 12 ≤ 4*cutoff n by omega)
    omega
  have hBudget : 2 * width n * cutoff n < n := by
    have ht := Nat.mul_le_mul_left (2*width n) (show cutoff n ≤ 4*cutoff n by omega)
    exact ht.trans_lt hU
  exact ⟨hn,hQ₀,hQ,(by change 4 * cutoff n ≤ n at hNn; omega),hW,hBudget⟩

theorem width_ge_cutoff (n : ℕ) (h : 1 ≤ narrow n) : cutoff n ≤ width n := by
  unfold width
  have hh := Nat.mul_le_mul_left (256 * cutoff n) h
  omega

end GoldbachGRHBudget
end GoldbachGRHBudget

section GoldbachGRHSignedModel

open Filter
open scoped Topology BigOperators ComplexConjugate

namespace GoldbachGRHSignedModel

open Finset

theorem weighted_suffix_lower (f : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m A : ℕ) (w : ℕ → ℝ), Monotone w → (∀ q ≥ A, 0 ≤ w q) →
      (∀ k, A ≤ k → k ≤ A+m → -ε ≤ ∑ q ∈ Ioc k (A+m), f q) →
      -(ε * w (A+m)) ≤ ∑ q ∈ Ioc A (A+m), f q * w q := by
  intro m
  induction m with
  | zero =>
    intro A w _ hw _
    simpa using neg_nonpos.mpr (mul_nonneg hε (hw A le_rfl))
  | succ m ih =>
    intro A w hw hw₀ hfloor
    let B := A + (m+1)
    let v : ℕ → ℝ := fun q => w q-w (A+1)
    have hB : A+1+m=B := by dsimp [B]; omega
    have hv : Monotone v := by
      intro i j hij
      exact sub_le_sub_right (hw hij) _
    have hv₀ (q : ℕ) (hq : A+1 ≤ q) : 0 ≤ v q := sub_nonneg.mpr (hw hq)
    have hsub : -(ε * v B) ≤ ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [← hB]
      apply ih (A+1) v hv hv₀
      intro k hk hkB
      simpa only [hB] using hfloor k (by omega) (show k ≤ B from hB ▸ hkB)
    have hs : Ioc A B = insert (A+1) (Ioc (A+1) B) := by
      ext k
      have hAB : A+1 ≤ B := by dsimp [B]; omega
      simp only [mem_Ioc, mem_insert]
      omega
    have hnin : A+1 ∉ Ioc (A+1) B := by simp
    have hsum :
        (∑ q ∈ Ioc A B, f q * w q) =
          w (A+1) * (∑ q ∈ Ioc A B, f q) +
            ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [hs]
      simp only [sum_insert hnin, v, mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    have hf := hfloor A le_rfl (by omega)
    have hfirst : -(ε * w (A+1)) ≤ w (A+1) * (∑ q ∈ Ioc A B, f q) := by
      simpa [B, mul_comm] using mul_le_mul_of_nonneg_left hf (hw₀ (A+1) (by omega))
    change -(ε * w B) ≤ ∑ q ∈ Ioc A B, f q * w q
    rw [hsum]
    dsimp [v] at hsub
    calc
      _ = -(ε*w (A+1)) + -(ε*(w B-w (A+1))) := by ring
      _ ≤ _ := add_le_add hfirst hsub

theorem weighted_suffix_lower_of_le_one (f w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    {A B : ℕ} (hAB : A ≤ B) (hw : Monotone w) (hw₀ : ∀ q ≥ A, 0 ≤ w q) (hwend : w B ≤ 1)
    (hfloor : ∀ k, A ≤ k → k ≤ B → -ε ≤ ∑ q ∈ Ioc k B, f q) :
    -ε ≤ ∑ q ∈ Ioc A B, f q * w q := by
  have hlen : A+(B-A)=B := Nat.add_sub_of_le hAB
  have hh := weighted_suffix_lower f ε hε (B-A) A w hw hw₀
  rw [hlen] at hh
  exact (by nlinarith [mul_le_mul_of_nonneg_left hwend hε] : -ε ≤ -(ε * w B)).trans (hh hfloor)

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta

private theorem inverse_squares_ge_two_le (X : ℕ) :
    (∑ j ∈ Icc 2 X, ((j : ℝ)^2)⁻¹) ≤ 3/4 := by
  by_cases hX : 2 ≤ X
  · rw [← sum_Ioc_add_eq_sum_Icc hX]
    have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2 : ℕ) ≠ 0) hX
    norm_num at hh ⊢
    linarith [show 0 ≤ ((X : ℝ))⁻¹ by positivity]
  · norm_num [Icc_eq_empty_of_lt (lt_of_not_ge hX)]

private theorem product_one_sub_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have haF := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [sum_insert ha, prod_insert ha]
    have hsum : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => (hs i hi).1
    have hh := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr haF.2)
    nlinarith only [hh, mul_nonneg haF.1 hsum]

private noncomputable def correctionLoss (n p : ℕ) : ℝ :=
  if p ∣ n then 0 else (((p : ℝ)-1)^2)⁻¹

private theorem odd_prime_ge_three {n p : ℕ} (hn : Even n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) : 3 ≤ p := by
  have hp2 := hp.two_le
  by_contra! hh
  have hp₂ : p = 2 := by omega
  apply hpn
  rw [hp₂]
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, by omega⟩

private theorem correctionLoss_bounds {n p : ℕ} (hn : Even n) (hp : p.Prime) :
    0 ≤ correctionLoss n p ∧ correctionLoss n p ≤ 1 := by
  unfold correctionLoss
  by_cases hpN : p ∣ n
  · simp [hpN]
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast odd_prime_ge_three hn hp hpN
    rw [ite_eq_right hpN]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((p:ℝ)-2)])⟩

private theorem local_correction_floor (n p k : ℕ) (hp : p.Prime) :
    1 - correctionLoss n p ≤ ∑ d ∈ (p^k).divisors, BandTail.z n d := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [Nat.sum_divisors_prime_pow hp,
    BandTail.localReduce (fun j => BandTail.z n (p^j))
      (fun j => by simp [BandTail.z,BandTail.h_cube n p j hp])]
  simp only [pow_zero,pow_one,(BandTail.z_mult n).map_one]
  simp only [correctionLoss,BandTail.z,ArithmeticFunction.coe_mk,
    BandTail.h_prime n p hp,BandTail.h_square n p hp,Nat.cast_pow]
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true, sub_zero]
    have hpos : 0 ≤ (1 / ((p : ℝ)-1)) / (p : ℝ) := by positivity
    have hcancel : (1 / ((p : ℝ)-1)) / (p : ℝ) +
        (-(p : ℝ) / ((p : ℝ)-1)) / (p : ℝ)^2 = 0 := by
      field_simp; ring
    split_ifs <;> first | omega | linarith only [hpos,hcancel]
  · simp only [hpn, ite_false, zero_div, ite_self, add_zero]
    have hneg : (-(p : ℝ) / ((p : ℝ)-1)^2) / (p : ℝ) = -(((p : ℝ)-1)^2)⁻¹ := by
      field_simp
    rw [hneg]
    split_ifs <;> linarith [show 0 ≤ (((p : ℝ)-1)^2)⁻¹ by positivity]

theorem signed_divisors_quarter (n M : ℕ) (hn : Even n) (hM : 0 < M) :
    (1/4 : ℝ) ≤ ∑ d ∈ M.divisors, BandTail.z n d := by
  classical
  let s := M.factorization.support
  let P := s.filter (fun p => ¬ p ∣ n)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    Nat.prime_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp))
  have hle (p : ℕ) (hp : p ∈ s) : p ≤ M :=
    Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp)))
  have hM' (p : ℕ) (hp : p ∈ P) : 3 ≤ p :=
    odd_prime_ge_three hn (hprime p (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have h1 := hM' p hp
    have h2 := hM' q hq
    change p - 1 = q - 1 at he
    omega
  have himage : P.image (fun p => p-1) ⊆ Icc 2 M := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have h1 := hM' p hp
    have h2 := hle p (mem_filter.mp hp).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ p ∈ s, correctionLoss n p) ≤ 3/4 := by
    calc
      _ = ∑ p ∈ P, (((p : ℝ)-1)^2)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro p hp
        by_cases hpN : p ∣ n <;> simp [correctionLoss,hpN]
      _ = ∑ p ∈ P, ((((p-1 : ℕ) : ℝ)^2))⁻¹ := by
        apply sum_congr rfl
        intro p hp
        rw [Nat.cast_sub (by have := hM' p hp; omega)]
        norm_cast
      _ = ∑ j ∈ P.image (fun p : ℕ => p-1), ((j : ℝ)^2)⁻¹ := by rw [sum_image hinj]
      _ ≤ ∑ j ∈ Icc 2 M, ((j : ℝ)^2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ ≤ _ := inverse_squares_ge_two_le M
  let A : ArithmeticFunction ℝ := BandTail.z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (BandTail.z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,BandTail.z n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  change _ ≤ ∏ p ∈ s, A (p^M.factorization p)
  calc
    _ ≤ 1 - ∑ p ∈ s, correctionLoss n p := by linarith
    _ ≤ ∏ p ∈ s, (1 - correctionLoss n p) :=
      product_one_sub_ge s _ (fun p hp => correctionLoss_bounds hn (hprime p hp))
    _ ≤ _ := by
      apply prod_le_prod₀
      · exact fun p hp => sub_nonneg.mpr (correctionLoss_bounds hn (hprime p hp)).2
      · intro p hp
        rw [he]
        exact local_correction_floor n p _ (hprime p hp)

theorem correction_prefix_eighth :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, Even n →
      (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop (8 * BandTail.universal)]
    with J hJ hlarge
  refine ⟨hJ, ?_⟩
  intro n hn
  have hJ' : 0 < J := hJ
  have hu := BandTail.uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ' (by
    intro d hd
    obtain ⟨hd, hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc, not_and] at hd'
    omega)
  have hh := signed_divisors_quarter n J.factorial hn J.factorial_pos
  rw [← sum_sdiff (s₁ := Icc 1 J) (s₂ := J.factorial.divisors) (BandTail.prefixDiv J)] at hh
  have ht := sum_le_sum (s := J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (BandTail.z n d))
  have hsmall : BandTail.universal / (J : ℝ)^(1/4 : ℝ) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change 8 * BandTail.universal ≤ (J : ℝ)^(1/4 : ℝ) at hlarge
    linarith
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology

noncomputable def harmonicG (n X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, BandTail.g n k / (k : ℝ)

noncomputable def harmonicF (n X : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 X, BandTail.F n q / (q : ℝ)

theorem g_unit_interval (n k : ℕ) : 0 ≤ BandTail.g n k ∧ BandTail.g n k ≤ 1 := by
  simp [BandTail.g]
  split_ifs <;> norm_num

private theorem harmonicG_sub (n : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    harmonicG n B - harmonicG n A =
      ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) := by
  have h := BandTail.prefix_split (fun k => BandTail.g n k / (k : ℝ)) hAB
  unfold harmonicG
  linarith

theorem harmonicG_mono (n : ℕ) : Monotone (harmonicG n) := by
  intro A B hAB
  have h := harmonicG_sub n hAB
  have hn : 0 ≤ ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) :=
    sum_nonneg fun k _ => div_nonneg (g_unit_interval n k).1 (Nat.cast_nonneg _)
  linarith

theorem g_boundary_le_mean (n X d : ℕ) (hX : 0 < X) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ (d : ℝ) * BandTail.gAvg n X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hsub : Ioc (X/d) X ⊆ Icc 1 X := by
    intro k hk
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (X/d)).trans_lt (mem_Ioc.mp hk).1), (mem_Ioc.mp hk).2⟩
  rw [harmonicG_sub n (Nat.div_le_self X d)]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, BandTail.g n k * ((d : ℝ)/X) := by
      apply sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt (mem_Ioc.mp hk).1
      have hxk := (Nat.div_lt_iff_lt_mul hd).mp (mem_Ioc.mp hk).1
      have hxkR : (X : ℝ) ≤ k * d := by exact_mod_cast hxk.le
      have hcoeff : (1 : ℝ)/(k : ℝ) ≤ (d : ℝ)/X :=
        (div_le_div_iff₀ hkR hXR).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hcoeff (g_unit_interval n k).1
    _ ≤ ∑ k ∈ Icc 1 X, BandTail.g n k * ((d : ℝ)/X) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (g_unit_interval n k).1 (by positivity))
    _ = _ := by
      rw [← sum_mul]
      unfold BandTail.gAvg BandTail.gSum
      ring

theorem g_boundary_le_log (n X d : ℕ) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ 1 + Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  by_cases hX : X = 0
  · simp [hX, harmonicG]
    positivity
  have hXR : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hfloor := Nat.div_le_self X d
  have hQ : (0 : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by positivity
  have hdiv : (X : ℝ) / (((X / d : ℕ) : ℝ) + 1) ≤ d := by
    apply (div_le_iff₀ hQ).mpr
    exact_mod_cast (Nat.lt_mul_div_succ X hd).le
  have hlogs : Real.log (X : ℝ) - Real.log (((X / d : ℕ) : ℝ) + 1) ≤ Real.log d := by
    rw [← Real.log_div hXR.ne' hQ.ne']
    exact Real.log_le_log (div_pos hXR hQ) hdiv
  have hH := harmonic_le_one_add_log X
  have hL := log_add_one_le_harmonic (X/d)
  have hsum : (∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹) =
      (harmonic X:ℝ) - (harmonic (X/d):ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hp := BandTail.prefix_split (fun k : ℕ => (k : ℝ)⁻¹) hfloor
    linarith
  rw [harmonicG_sub n hfloor]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k _
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k)) (g_unit_interval n k).2
    _ = _ := hsum
    _ ≤ _ := by
      rw [Nat.cast_add, Nat.cast_one] at hL
      linarith

theorem harmonic_doubling_lower (n A : ℕ) (hA : 0 < A) (t η : ℝ)
    (hlo : |BandTail.gAvg n A - t| ≤ η)
    (hhi : |BandTail.gAvg n (2*A) - t| ≤ η) :
    t/2 - (3/2)*η ≤ harmonicG n (2*A) - harmonicG n A := by
  have hAB : A ≤ 2*A := by omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBA := BandTail.prefix_split (BandTail.g n) hAB
  change BandTail.gSum n (2*A) = BandTail.gSum n A + _ at hBA
  have hweak : BandTail.gAvg n (2*A) - BandTail.gAvg n A / 2 ≤
      harmonicG n (2*A) - harmonicG n A := by
    rw [harmonicG_sub n hAB]
    calc
      _ = (∑ j ∈ Ioc A (2*A), BandTail.g n j) / ((2*A : ℕ) : ℝ) := by
        unfold BandTail.gAvg
        rw [← sub_eq_of_eq_add hBA]
        push_cast
        field_simp; ring
      _ ≤ _ := by
        rw [sum_div]
        apply sum_le_sum
        intro k hk
        apply div_le_div_of_nonneg_left (g_unit_interval n k).1
        · exact_mod_cast hA.trans (mem_Ioc.mp hk).1
        · exact_mod_cast (mem_Ioc.mp hk).2
  linarith [(abs_le.mp hlo).2, (abs_le.mp hhi).1]

theorem harmonic_dyadic_lower (n : ℕ) (t η : ℝ) :
    ∀ (L A : ℕ), 0 < A →
      (∀ j ≤ L, |BandTail.gAvg n (2^j*A) - t| ≤ η) →
      (L : ℝ) * (t/2 - (3/2)*η) ≤ harmonicG n (2^L*A) - harmonicG n A := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    intro A hA hnear
    have hm := ih A hA (fun j hj => hnear j (by omega))
    have ht : 0 < 2^L*A := Nat.mul_pos (pow_pos (by decide) _) hA
    have hh := harmonic_doubling_lower n (2^L*A) ht t η (hnear L (by omega)) (by
      simpa only [pow_succ', mul_assoc] using hnear (L+1) le_rfl)
    push_cast
    rw [pow_succ', mul_assoc]
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology

private theorem sum_divisors_reindex (X : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v) =
      ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := by
  classical
  let S := Icc 1 X
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      rw [←sum_filter,hkd]

theorem harmonicF_convolution (n X : ℕ) :
    harmonicF n X = ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (X/d) := by
  let f := fun v : ℕ × ℕ => BandTail.z n v.1 * (BandTail.g n v.2 / (v.2 : ℝ))
  calc
    _ = ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_congr rfl
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply,sum_div]
      apply sum_congr rfl
      intro v hv
      change BandTail.h n v.1*BandTail.g n v.2/(q:ℝ) =
        (BandTail.h n v.1/(v.1:ℝ))*(BandTail.g n v.2/(v.2:ℝ))
      rw [←(Nat.mem_divisorsAntidiagonal.mp hv).1, Nat.cast_mul,div_eq_mul_inv,mul_inv]
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ = _ := by simp [f,harmonicG,mul_sum]

theorem absolute_prefix_le (n X : ℕ) :
    (∑ q ∈ Icc 1 X, |BandTail.F n q|) ≤ BandTail.universal * (X:ℝ) := by
  classical
  let f : ℕ × ℕ → ℝ := fun v => |BandTail.h n v.1|
  calc
    _ ≤ ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_le_sum
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro v _
      rw [abs_mul,abs_of_nonneg (g_unit_interval n v.2).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (g_unit_interval n v.2).2
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ ≤ ∑ d ∈ Icc 1 X, |BandTail.z n d| * (X:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdR : (0:ℝ)<d := by exact_mod_cast hd0
      have hdiv : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ hdR).2
        exact_mod_cast Nat.div_mul_le_self X d
      calc
        _ = ((X/d:ℕ):ℝ)*|BandTail.h n d| := by
          simp [f,Nat.card_Icc,nsmul_eq_mul]
        _ ≤ ((X:ℝ)/(d:ℝ))*|BandTail.h n d| := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
        _ = _ := by
          rw [BandTail.z,ArithmeticFunction.coe_mk,abs_div,abs_of_pos hdR]
          ring
    _ = (∑ d ∈ Icc 1 X, |BandTail.z n d|) * (X:ℝ) := (sum_mul ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using BandTail.uniformTail n 1 (Icc 1 X) (by decide) (fun d hd => (mem_Icc.mp hd).1)

theorem harmonic_convolution_interval (n K X : ℕ) (hKX : K ≤ X) :
    (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) =
      ∑ d ∈ Icc 1 X, BandTail.z n d * (harmonicG n (X/d)-harmonicG n (K/d)) := by
  have hsub := BandTail.prefix_split (fun q => BandTail.F n q / (q:ℝ)) hKX
  have hsub' : (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) = harmonicF n X-harmonicF n K := by
    unfold harmonicF
    linarith
  have hK :
      ∑ d ∈ Icc 1 K, BandTail.z n d * harmonicG n (K/d) =
        ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (K/d) := by
    apply sum_subset (Icc_subset_Icc_right hKX)
    intro d hd hnot
    have hdK : K<d := by
      simp only [mem_Icc,not_and] at hnot
      have hd' := mem_Icc.mp hd
      omega
    simp [Nat.div_eq_of_lt hdK,harmonicG]
  rw [hsub',harmonicF_convolution n X,harmonicF_convolution n K,hK,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  ring

theorem uniform_log_tail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, J ≤ d) →
      (∑ d ∈ s, |BandTail.z n d| *(1+Real.log d)) ≤ ε := by
  have hC : 0 < BandTail.universal := Real.exp_pos _
  let τ := ε/(2*BandTail.universal)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hc := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hm := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/4)).comp_tendsto hc).bound hτ
  have hlog := (Real.tendsto_log_atTop.comp hc).eventually_ge_atTop (1:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.and hlog)
  filter_upwards [eventually_ge_atTop (max N 1)] with J hJ
  have hJ' : 0<J := lt_of_lt_of_le (by decide : 0<1) ((le_max_right N 1).trans hJ)
  refine ⟨hJ',?_⟩
  intro n s hs
  have hbound (d : ℕ) (hd : d ∈ s) : |BandTail.z n d| *(1+Real.log d) ≤
      (ε/BandTail.universal)*BandTail.w n d := by
    have hdJ := hs d hd
    have hd0 := hJ'.trans_le hdJ
    have hz : (0:ℝ)<(d:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd0) _
    obtain ⟨ha,hb⟩ := hN d ((le_max_left N 1).trans (hJ.trans hdJ))
    change ‖(Real.log (d:ℝ))^(1:ℝ)‖ ≤ τ*‖(d:ℝ)^(1/4:ℝ)‖ at ha
    change 1 ≤ Real.log (d:ℝ) at hb
    rw [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log (d:ℝ)),
      Real.norm_eq_abs,abs_of_pos hz] at ha
    have hh : 1+Real.log (d:ℝ) ≤ (ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ) := by
      have hτ' : 2*τ=ε/BandTail.universal := by dsimp [τ]; ring
      rw [←hτ',mul_assoc]
      linarith
    calc
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*(1+Real.log d) :=
        mul_le_mul_of_nonneg_right (BandTail.tailTerm n d d hd0 le_rfl) (by linarith)
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*((ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (BandTail.w_nonneg n d) hz.le)
      _ = _ := by field_simp
  have hu : ∑ d ∈ s, BandTail.w n d ≤ BandTail.universal := by
    apply le_trans _ (BandTail.uniformPrefix n (s.sup id))
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨hJ'.trans_le (hs d hd),le_sup (f:=id) hd⟩
    · intro d _ _
      exact BandTail.w_nonneg n d
  calc
    _ ≤ ∑ d ∈ s, (ε/BandTail.universal)*BandTail.w n d := sum_le_sum hbound
    _ = (ε/BandTail.universal)*(∑ d ∈ s,BandTail.w n d) := (mul_sum ..).symm
    _ ≤ (ε/BandTail.universal)*BandTail.universal := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by field_simp

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter
open scoped Topology

private theorem harmonic_diff_boundary (n K X d : ℕ) :
    harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K) =
      (harmonicG n K - harmonicG n (K/d)) -
      (harmonicG n X - harmonicG n (X/d)) := by ring

private theorem harmonic_diff_abs (n K X d : ℕ) :
    |harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K)| ≤
      (harmonicG n K - harmonicG n (K/d)) +
      (harmonicG n X - harmonicG n (X/d)) := by
  rw [harmonic_diff_boundary]
  have hK := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self K d))
  have hX := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self X d))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem gAvg_nonneg (n X : ℕ) : 0 ≤ BandTail.gAvg n X := by
  unfold BandTail.gAvg BandTail.gSum
  exact div_nonneg (sum_nonneg fun k _ => (g_unit_interval n k).1) (by positivity)

theorem harmonic_convolution_lower (n K X J : ℕ) (hK : 0 < K) (hKX : K ≤ X)
    (hJX : J ≤ X) (e : ℝ)
    (hZ : (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 X, BandTail.z n d)
    (hlog : (∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d)) ≤ e) :
    (1/8 : ℝ) * (harmonicG n X - harmonicG n K) -
      (J : ℝ) * BandTail.universal * (BandTail.gAvg n K + BandTail.gAvg n X) - 2*e ≤
      ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  let A := harmonicG n X - harmonicG n K
  let D (d : ℕ) := harmonicG n (X/d) - harmonicG n (K/d) - A
  let t := BandTail.gAvg n K + BandTail.gAvg n X
  have ht := add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X)
  have hpos := sub_nonneg.mpr (harmonicG_mono n hKX)
  have hlow (d : ℕ) : -(abs (BandTail.z n d) * abs (D d)) ≤ BandTail.z n d * D d := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hsmall : -((J : ℝ) * BandTail.universal * t) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Icc 1 J) : |D d| ≤ (J : ℝ) * t := by
      have hd0 := (mem_Icc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (d : ℝ) * t := by
          dsimp [t]
          rw [mul_add]
          exact add_le_add (g_boundary_le_mean n K d hK hd0)
            (g_boundary_le_mean n X d (hK.trans_le hKX) hd0)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) ht
    have hU : (∑ d ∈ Icc 1 J, |BandTail.z n d|) ≤ BandTail.universal := by
      simpa using BandTail.uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
    calc
      _ = -(BandTail.universal * ((J : ℝ) * t)) := by ring
      _ ≤ -((∑ d ∈ Icc 1 J, |BandTail.z n d|) * ((J : ℝ) * t)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hU (mul_nonneg (Nat.cast_nonneg J) ht))
      _ = ∑ d ∈ Icc 1 J, -(|BandTail.z n d| * ((J : ℝ) * t)) := by rw [sum_neg_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hlarge : -(2*e) ≤ ∑ d ∈ Ioc J X, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Ioc J X) : |D d| ≤ 2 * (1 + Real.log d) := by
      have hd0 := (Nat.zero_le J).trans_lt (mem_Ioc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (1 + Real.log d) + (1 + Real.log d) := by
          exact add_le_add (g_boundary_le_log n K d hd0) (g_boundary_le_log n X d hd0)
        _ = _ := by ring
    calc
      _ ≤ -(2*(∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlog (by norm_num))
      _ = ∑ d ∈ Ioc J X, -(|BandTail.z n d| * (2 * (1 + Real.log d))) := by
        rw [sum_neg_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hsplit := BandTail.prefix_split (fun d => BandTail.z n d * D d) hJX
  rw [harmonic_convolution_interval n K X hKX]
  have hrewrite : (∑ d ∈ Icc 1 X, BandTail.z n d *
      (harmonicG n (X/d) - harmonicG n (K/d))) =
      (∑ d ∈ Icc 1 X, BandTail.z n d) * A + ∑ d ∈ Icc 1 X, BandTail.z n d * D d := by
    rw [sum_mul, ←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    dsimp [D]
    ring
  rw [hrewrite, hsplit]
  change (1/8 : ℝ) * A - (J : ℝ)*BandTail.universal*t - 2*e ≤ _
  linarith [mul_le_mul_of_nonneg_right hZ hpos]

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter
open scoped Topology

theorem harmonic_suffix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ n X : ℕ, Even n → K ≤ X →
      -ε ≤ ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (correction_prefix_eighth.and (uniform_log_tail (ε/4) (by positivity)))
  obtain ⟨hJ₀,_⟩ := (hJ J le_rfl).1
  obtain ⟨m,hm⟩ := exists_nat_ge (16 * ((J:ℝ) * BandTail.universal))
  let L := m+1
  let T : ℕ := 2^L
  have hT : 0 < T := pow_pos (by decide) _
  have hC : (1:ℝ) ≤ 2*(T:ℝ) := by
    have ht' : (1:ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hL : (0:ℝ) < L := by exact_mod_cast (Nat.zero_lt_succ m)
  have hLJ : (J:ℝ)*BandTail.universal ≤ (L:ℝ)/16 := by
    change (J:ℝ)*BandTail.universal ≤ ((m+1:ℕ):ℝ)/16
    push_cast
    linarith
  let η := ε/(L:ℝ)
  have hη : 0 < η := div_pos hε hL
  have hLη : (L:ℝ)*η=ε := by dsimp [η]; field_simp
  obtain ⟨M,hM⟩ := eventually_atTop.mp (BandTail.mean_slow (2*(T:ℝ)) η hC hη)
  have hR : 1 ≤ T*T := Nat.mul_pos hT hT
  obtain ⟨N,hN⟩ := BandTail.uniform_prefix_floor (T*T) hR ε hε
  refine ⟨max J (max M N),?_⟩
  intro K hK₀ n X hn hKX
  have hJK : J ≤ K := (le_max_left J (max M N)).trans hK₀
  have hMK : M ≤ K := ((le_max_left M N).trans (le_max_right J (max M N))).trans hK₀
  have hNK : N ≤ K := ((le_max_right M N).trans (le_max_right J (max M N))).trans hK₀
  have hK : 0 < K := hJ₀.trans_le hJK
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  by_cases hnear : X ≤ (T*T)*K
  · have hh := BandTail.weighted_prefix_lower K X (BandTail.F n)
      (fun q => (q:ℝ)⁻¹) (ε*(K:ℝ)) hKX (by positivity)
      (fun i _ => by positivity)
      (fun i hi => by
        apply inv_anti₀
        · exact_mod_cast hK.trans_le hi
        · exact_mod_cast Nat.le_succ i)
      (fun i hi hiX => hN K hNK n i hi (hiX.trans hnear))
    have hEq : -(ε*(K:ℝ)*(K:ℝ)⁻¹) = -ε := by field_simp
    rw [hEq] at hh
    simpa [div_eq_mul_inv] using hh
  · let B := X/T
    have hfar : (T*T)*K ≤ X := le_of_lt (lt_of_not_ge hnear)
    have hKB : T*K ≤ B := by
      apply (Nat.le_div_iff_mul_le hT).2
      calc
        T*K*T = (T*T)*K := by ring
        _ ≤ X := hfar
    have hB : 0<B := (Nat.mul_pos hT hK).trans_le hKB
    have hBX : T*B ≤ X := Nat.mul_div_le X T
    have hXT : X ≤ 2*T*B := by
      have hmod := Nat.mod_lt X hT
      have hdiv : X % T + T * B = X := Nat.mod_add_div X T
      have hTB : T ≤ T*B := by
        simpa using Nat.mul_le_mul_left T (show 1≤B from hB)
      have he : 2*T*B=T*B+T*B := by ring
      rw [he]
      omega
    have hdT (j : ℕ) (hj : j≤L) : (2:ℕ)^j≤T := Nat.pow_le_pow_right (by decide) hj
    have hd1 (j : ℕ) : 1≤(2:ℕ)^j := pow_pos (by decide : 0<(2:ℕ)) j
    have hKm (j : ℕ) : K ≤ 2^j*K := by simpa using Nat.mul_le_mul_right K (hd1 j)
    have hBm (j : ℕ) : B ≤ 2^j*B := by simpa using Nat.mul_le_mul_right B (hd1 j)
    have hslowK (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*K)-BandTail.gAvg n K| ≤ η := by
      apply hM (2^j*K) (hMK.trans (hKm j)) K hK (hKm j) _ n
      have hx : (2:ℕ)^j*K≤T*K := Nat.mul_le_mul_right K (hdT j hj)
      have hx' : (((2:ℕ)^j*K : ℕ):ℝ) ≤ (T:ℝ)*(K:ℝ) := by exact_mod_cast hx
      nlinarith [show (0:ℝ)≤(T:ℝ)*(K:ℝ) by positivity]
    have hslowX (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*B)-BandTail.gAvg n X| ≤ η := by
      rw [abs_sub_comm]
      apply hM X (hMK.trans hKX) (2^j*B) (hB.trans_le (hBm j))
        ((Nat.mul_le_mul_right B (hdT j hj)).trans hBX) _ n
      have hXj : X ≤ 2*T*(2^j*B) := hXT.trans (Nat.mul_le_mul_left (2*T) (hBm j))
      exact_mod_cast hXj
    have hnearK := harmonic_dyadic_lower n (BandTail.gAvg n K) η L K hK hslowK
    have hnearX := harmonic_dyadic_lower n (BandTail.gAvg n X) η L B hB hslowX
    have hmid := harmonicG_mono n hKB
    have hlast := harmonicG_mono n hBX
    change (L:ℝ)*(BandTail.gAvg n K/2 - (3/2)*η) ≤ harmonicG n (T*K)-harmonicG n K at hnearK
    change (L:ℝ)*(BandTail.gAvg n X/2 - (3/2)*η) ≤ harmonicG n (T*B)-harmonicG n B at hnearX
    have hlong : ((L:ℝ)/2)*(BandTail.gAvg n K+BandTail.gAvg n X)-3*ε ≤
      harmonicG n X-harmonicG n K := by linarith
    have hJX := hJK.trans hKX
    have hZ := (hJ X hJX).1.2 n hn
    have hlog := (hJ J le_rfl).2.2 n (Ioc J X) (fun d hd => (mem_Ioc.mp hd).1.le)
    have hlower := harmonic_convolution_lower n K X J hK hKX hJX (ε/4) hZ hlog
    have hdom := mul_le_mul_of_nonneg_right hLJ
      (add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X))
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset

theorem coefficient_re_eq (n q : ℕ) (hq : 0 < q) :
    (GoldbachExplicitModeledMajor.coefficient q n).re = BandTail.F n q / (q:ℝ) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [BandTail.F,hqR]

/-- A monotone weight that is at most q/Q near the origin preserves the asymptotic
lower floor of the full initial Ramanujan sum. -/
theorem harmonic_tapered_prefix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n : ℕ, Even n → ∀ w : ℕ → ℝ, Monotone w →
      (∀ q, 0 ≤ w q) → w Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, w q ≤ (q:ℝ)/(Q:ℝ)) →
      -ε ≤ ∑ q ∈ Icc 1 Q, (BandTail.F n q / (q:ℝ)) * w q := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨K₀,hK₀⟩ := harmonic_suffix_floor (ε/4) hδ
  let K := max K₀ 1
  have hK₁ : 1 ≤ K := le_max_right _ _
  obtain ⟨M,hM⟩ := exists_nat_ge (2 * (BandTail.universal * (K:ℝ)) / ε)
  refine ⟨max K M, ?_⟩
  intro Q hQ n hn w hw hw₀ hwQ hweight
  have hKQ : K ≤ Q := (le_max_left _ _).trans hQ
  have hMQ : M ≤ Q := (le_max_right _ _).trans hQ
  have hQR : (0:ℝ) < Q := by exact_mod_cast hK₁.trans hKQ
  have hQM : 2 * (BandTail.universal * (K:ℝ)) / ε ≤ (Q:ℝ) :=
    hM.trans (by exact_mod_cast hMQ)
  have hcut : BandTail.universal * (K:ℝ) / (Q:ℝ) ≤ ε/2 := by
    have hs := (div_le_iff₀ hε).1 hQM
    apply (div_le_iff₀ hQR).2
    linarith
  have hterm (q : ℕ) (hq : q ∈ Icc 1 K) :
      -(|BandTail.F n q| / (Q:ℝ)) ≤ (BandTail.F n q / (q:ℝ)) * w q := by
    have hqR : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hh := hweight q ((Icc_subset_Icc_right hKQ) hq)
    calc
      _ = -((|BandTail.F n q| / (q:ℝ)) * ((q:ℝ)/(Q:ℝ))) := by field_simp
      _ ≤ -((|BandTail.F n q| / (q:ℝ)) * w q) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hh (div_nonneg (abs_nonneg _) hqR.le))
      _ ≤ _ := by
        have he : |(BandTail.F n q / (q:ℝ)) * w q| =
            (|BandTail.F n q| / (q:ℝ)) * w q := by
          rw [abs_mul, abs_div, abs_of_pos hqR, abs_of_nonneg (hw₀ q)]
        rw [←he]
        exact neg_abs_le _
  have hsmall :
      -(ε/2) ≤ ∑ q ∈ Icc 1 K, (BandTail.F n q / (q:ℝ)) * w q := by
    calc
      _ ≤ -(BandTail.universal * (K:ℝ) / (Q:ℝ)) := neg_le_neg hcut
      _ ≤ -((∑ q ∈ Icc 1 K, |BandTail.F n q|) / (Q:ℝ)) :=
        neg_le_neg (div_le_div_of_nonneg_right (absolute_prefix_le n K) hQR.le)
      _ = ∑ q ∈ Icc 1 K, -(|BandTail.F n q| / (Q:ℝ)) := by
        rw [sum_neg_distrib, sum_div]
      _ ≤ _ := sum_le_sum hterm
  have hlen : K+(Q-K)=Q := Nat.add_sub_of_le hKQ
  have htail := weighted_suffix_lower (fun q => BandTail.F n q/(q:ℝ)) (ε/4) hδ.le
    (Q-K) K w hw (fun q _ => hw₀ q)
  rw [hlen] at htail
  have hrest := htail (fun k hk hkQ => hK₀ k ((le_max_left _ _).trans hk) n Q hn hkQ)
  have hrest' : -(ε/2) ≤ ∑ q ∈ Ioc K Q, (BandTail.F n q/(q:ℝ))*w q := by
    exact (by linarith [mul_le_mul_of_nonneg_left hwQ hδ.le] : -(ε/2) ≤ -(ε/4 * w Q)).trans hrest
  rw [BandTail.prefix_split (fun q => (BandTail.F n q/(q:ℝ))*w q) hKQ]
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset

/-- Uniform lower floor for the two model sums after separating the common kernel
mass, the low-denominator taper, and a uniformly small truncation error. -/
theorem medium_model_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n U : ℕ, Even n → Q ≤ U →
      ∀ mass defect : ℝ, mass ∈ Set.Icc 0 2 → 0 ≤ defect →
      defect * (BandTail.universal * (U:ℝ)) ≤ ε/4 →
      ∀ wide taper : ℕ → ℝ, Monotone taper → (∀ q, 0 ≤ taper q) → taper Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ)) →
      (∀ q ∈ Icc 1 U, |wide q-mass| ≤ defect*(q:ℝ)) →
      -ε ≤ (∑ q ∈ Ioc Q U, (GoldbachExplicitModeledMajor.coefficient q n).re * wide q) +
        ∑ q ∈ Icc 1 Q, (GoldbachExplicitModeledMajor.coefficient q n).re *
          (wide q-mass+taper q) := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨Q₁,hQ₁⟩ := harmonic_suffix_floor (ε/4) hδ
  obtain ⟨Q₂,hQ₂⟩ := harmonic_tapered_prefix_floor (ε/4) hδ
  refine ⟨max Q₁ Q₂,?_⟩
  intro Q hQ n U hn hQU mass defect hmass hdefect hcost wide taper hmono hnonneg
    hcap hscale hwide
  let a (q : ℕ) := (GoldbachExplicitModeledMajor.coefficient q n).re
  have hite (q : ℕ) (hq : q ∈ Ioc Q U) : 0 < q := (Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1
  have hlarge : -(ε/4) ≤ ∑ q ∈ Ioc Q U, a q := by
    have hh := hQ₁ Q ((le_max_left _ _).trans hQ) n U hn hQU
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact (coefficient_re_eq n q (hite q hq)).symm
  have hmain : -(ε/2) ≤ (∑ q ∈ Ioc Q U, a q)*mass := by
    exact (by linarith [mul_le_mul_of_nonneg_left hmass.2 hδ.le] :
      -(ε/2) ≤ -(ε/4)*mass).trans (mul_le_mul_of_nonneg_right hlarge hmass.1)
  have hsmall : -(ε/4) ≤ ∑ q ∈ Icc 1 Q, a q*taper q := by
    have hh := hQ₂ Q ((le_max_right _ _).trans hQ) n hn taper hmono hnonneg hcap hscale
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact congrArg (fun x : ℝ => x*taper q) (coefficient_re_eq n q (mem_Icc.mp hq).1).symm
  have herror : -(ε/4) ≤ ∑ q ∈ Icc 1 U, a q*(wide q-mass) := by
    have hterm (q : ℕ) (hq : q ∈ Icc 1 U) :
        -(defect*|BandTail.F n q|) ≤ a q*(wide q-mass) := by
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hAbs : |a q*(wide q-mass)| ≤ defect*|BandTail.F n q| := by
        dsimp [a]
        rw [abs_mul, coefficient_re_eq n q hq0, abs_div, abs_of_pos hqR]
        calc
          _ ≤ (|BandTail.F n q|/(q:ℝ))*(defect*(q:ℝ)) :=
            mul_le_mul_of_nonneg_left (hwide q hq) (div_nonneg (abs_nonneg _) hqR.le)
          _ = _ := by field_simp
      exact (neg_le_neg hAbs).trans (neg_abs_le _)
    calc
      _ ≤ -(defect*(BandTail.universal*(U:ℝ))) := neg_le_neg hcost
      _ ≤ -(defect*(∑ q ∈ Icc 1 U, |BandTail.F n q|)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left (absolute_prefix_le n U) hdefect)
      _ = ∑ q ∈ Icc 1 U, -(defect*|BandTail.F n q|) := by rw [sum_neg_distrib,mul_sum]
      _ ≤ _ := sum_le_sum hterm
  change -ε ≤ (∑ q ∈ Ioc Q U, a q * wide q) +
    ∑ q ∈ Icc 1 Q, a q * (wide q-mass+taper q)
  have H :
      (∑ q ∈ Ioc Q U, a q * wide q) =
        (∑ q ∈ Ioc Q U, a q)*mass + ∑ q ∈ Ioc Q U, a q*(wide q-mass) := by
    rw [sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro q _
    ring
  have E := BandTail.prefix_split (fun q => a q*(wide q-mass)) hQU
  rw [H]
  simp only [mul_add,sum_add_distrib]
  linarith

end GoldbachGRHSignedModel

end GoldbachGRHSignedModel

section GoldbachGRHConcreteFloor

open Filter Finset MeasureTheory
open scoped Topology Interval Classical

namespace GoldbachGRHConcreteFloor

open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (radius centers cell)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)

theorem eventually_narrow_ge (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)

noncomputable def normalized (n T q : ℕ) : ℝ :=
  mass n (radius n T (max 1 q)) / (n:ℝ)

theorem normalized_loss (n T q : ℕ) (hn : 0 < n) (hT : 0 < T) (hbudget : 24*T≤n) :
    0 ≤ ((n:ℝ)+1)/(n:ℝ)-normalized n T q ∧
     ((n:ℝ)+1)/(n:ℝ)-normalized n T q ≤ (max 1 q:ℕ)/(2*(T:ℝ)) := by
  let r := radius n T (max 1 q)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hTR : 0 < (T:ℝ) := by exact_mod_cast hT
  have hqR : (1:ℝ) ≤ (max 1 q:ℕ) := by exact_mod_cast le_max_left 1 q
  have hqpos : (0:ℝ) < ((max 1 q:ℕ):ℝ) := by linarith
  have hbn : 24*(T:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbudget
  have hqp := mul_le_mul_of_nonneg_right hqR hnR.le
  have hr : 0 < r := by unfold r radius; positivity
  have hr' : r ≤ 1/2 := by
    apply (div_le_iff₀ (mul_pos hqpos hnR)).2
    nlinarith only [hqp,hbn,hTR]
  have hmass := GoldbachGRHKernel.mass_loss n hr hr'
  change 0 ≤ ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ∧
    ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ≤ _
  rw [← sub_div]
  constructor
  · exact div_nonneg hmass.1 hnR.le
  · calc
      _ ≤ (1/(2*r))/(n:ℝ) := div_le_div_of_nonneg_right hmass.2 hnR.le
      _ = _ := by
        unfold r radius
        field_simp [hnR.ne',hqpos.ne',hTR.ne']

end GoldbachGRHConcreteFloor
end GoldbachGRHConcreteFloor

namespace GoldbachGRHApproximation
open GoldbachFourthMoment (phase primeSum)
noncomputable def integrand (n : ℕ) (t : ℝ) : ℂ := primeSum n t ^ 2 * phase (-(n:ℝ)*t)
end GoldbachGRHApproximation

open Filter Finset MeasureTheory
open scoped Topology Interval Classical

namespace GoldbachLowSkirt7

open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (radius centers cell cap)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)
open GoldbachGRHConcreteFloor (normalized normalized_loss)
open GoldbachFourthMoment (phase primeSum primeWeight)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHApproximation (integrand)

theorem eventually_narrow_ge (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)

theorem eventual_low_model_floor (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n →
      -ε * (n:ℝ) ≤
      (∑ i ∈ centers (narrow n), ∫ t in cell n (narrow n) (width n) i,
        GoldbachGRHModel.model n i t^2 * GoldbachFourthMoment.phase (-(n:ℝ)*t)).re := by
  obtain ⟨Q₀,hfloor⟩ := GoldbachGRHSignedModel.medium_model_floor ε hε
  obtain ⟨P,hP⟩ := exists_nat_ge (4*(|BandTail.universal|+1)/ε)
  filter_upwards [GoldbachGRHBudget.eventual_geometry, eventually_narrow_ge Q₀,
    eventually_narrow_ge P] with n hgeo hQ₀ hQP
  intro hEven
  obtain ⟨hn,hQ,hQU,_,hbudget,_⟩ := hgeo
  let Q := narrow n
  let U := cutoff n
  let H := width n
  let full := ((n:ℝ)+1)/(n:ℝ)
  let d := 1/(2*(H:ℝ))
  let wide := normalized n H
  let taper (q : ℕ) := full - normalized n Q q
  have hn₀ : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn₀
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hU₀ : 1≤U := hQ.trans hQU
  have hUH : U≤H := GoldbachGRHBudget.width_ge_cutoff n hQ
  have hQH : Q≤H := hQU.trans hUH
  have hH₀ : 0<H := hU₀.trans hUH
  have hHn : H≤n := by change 24*H≤n at hbudget; omega
  have hH' : 0 < (H:ℝ) := by exact_mod_cast hH₀
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hU' : 0 < (U:ℝ) := by exact_mod_cast hU₀
  have hQbudget : 24*Q≤n := (Nat.mul_le_mul_left 24 hQH).trans hbudget
  have hfull : full ∈ Set.Icc 0 2 := ⟨by unfold full; positivity,
    (div_le_iff₀ hnR).2 (by linarith)⟩
  have hcost : d*(BandTail.universal*(U:ℝ)) ≤ ε/4 := by
    have hhQ : (4*(|BandTail.universal|+1)/ε : ℝ) ≤ (Q:ℝ) :=
      hP.trans (by exact_mod_cast hQP)
    have hv := (div_le_iff₀ hε).1 hhQ
    have hconst : BandTail.universal ≤ (ε/4)*(512*(Q:ℝ)) := by
      have hnon := mul_nonneg hε.le hQ'.le
      nlinarith [le_abs_self BandTail.universal]
    have hval : d*(BandTail.universal*(U:ℝ)) = BandTail.universal/(512*(Q:ℝ)) := by
      unfold d H width
      push_cast
      change 1/(2*(256*(U:ℝ)*(Q:ℝ)))*(BandTail.universal*(U:ℝ)) = _
      field_simp [hU'.ne', hQ'.ne']
      ring
    rw [hval]
    exact (div_le_iff₀ (show 0 < 512*(Q:ℝ) by positivity)).2 hconst
  have htaper : ∀ q, 0≤taper q := fun q =>
    (normalized_loss n Q q hn₀ hQ hQbudget).1
  have hmono : Monotone taper := by
    intro q r hqr
    apply sub_le_sub_left
    unfold normalized
    apply div_le_div_of_nonneg_right _ hnR.le
    apply GoldbachGRHKernel.mass_mono
    · unfold radius
      positivity
    · unfold radius
      apply div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by exact_mod_cast (show 0 < max 1 q by omega)) hnR)
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast max_le_max (le_refl 1) hqr) hnR.le
  have htcap : taper Q≤2 := by
    have hnon : 0≤normalized n Q Q := by
      unfold normalized
      apply div_nonneg _ hnR.le
      exact GoldbachGRHKernel.mass_nonneg _ (by unfold radius; positivity)
    unfold taper
    linarith [hfull.2]
  have htbound : ∀ q∈Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ) := by
    intro q hq
    have hh := (normalized_loss n Q q hn₀ hQ hQbudget).2
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) hQ' (by linarith))
  have hwbound : ∀ q∈Icc 1 U, |wide q-full|≤d*(q:ℝ) := by
    intro q hq
    obtain ⟨h₁,h₂⟩ := normalized_loss n H q hn₀ hH₀ hbudget
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at h₂
    change 0≤full-wide q at h₁
    change full-wide q ≤ _ at h₂
    rw [abs_sub_comm, abs_of_nonneg h₁]
    unfold d
    exact h₂.trans_eq (by ring)
  have hCnon : 0 ≤ BandTail.universal := (Real.exp_pos _).le
  have hcostLow : d * (BandTail.universal * (Q : ℝ)) ≤ ε / 4 := by
    apply le_trans _ hcost
    apply mul_le_mul_of_nonneg_left _ (by unfold d; positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQU) hCnon
  have hwLow : ∀ q ∈ Icc 1 Q, |wide q-full| ≤ d*(q:ℝ) := by
    intro q hq
    exact hwbound q (mem_Icc.mpr ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2.trans hQU⟩)
  have hm := hfloor Q hQ₀ n Q hEven le_rfl full d hfull (by unfold d; positivity)
    hcostLow wide taper hmono htaper htcap htbound hwLow
  simp only [Finset.Ioc_self, Finset.sum_empty, zero_add] at hm
  rw [GoldbachGRHModelAssembly.sum_cell_model_re hQ hQH hHn]
  have hrew :
      (∑ q ∈ Icc 1 Q, (coefficient q n).re * GoldbachGRHModelAssembly.massDifference n Q H q)
      = (∑ q ∈ Icc 1 Q, (coefficient q n).re * (wide q-full+taper q)) * (n:ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hqL,hqU⟩ := Finset.mem_Icc.mp hq
    simp only [GoldbachGRHModelAssembly.massDifference, ite_eq_left hqU, taper,
      wide, normalized, max_eq_right hqL]
    field_simp [hnR.ne']
    ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hm hnR.le

noncomputable def lowIntegral (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1,
    (cap n (narrow n) (width n) \ cap n (narrow n) (narrow n)).indicator (integrand n) t

noncomputable def lowModel (n : ℕ) : ℂ :=
  ∑ i ∈ centers (narrow n), ∫ t in cell n (narrow n) (width n) i,
    model n i t ^ 2 * phase (-(n:ℝ)*t)

end GoldbachLowSkirt7

open Finset MeasureTheory Filter
open scoped BigOperators ComplexConjugate Interval Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHWindow (additiveModel primeLog)
open GoldbachGRHAnalytic (errorCoeff shifted_error_eq)
open GoldbachWindow (poly moving)
open GoldbachGRHArcs (radius center cell centers)
open GoldbachFourthMoment (primeSum phase)
open GoldbachGRHModel (model)
variable {q : ℕ} [NeZero q]

-- Finite Fourier identities from the project proof in #2829.
private noncomputable def residueSum (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k

noncomputable def residueError (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  residueSum I w r - if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0

private theorem sum_residueSum_mul (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, residueSum I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [residueSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _

private theorem sum_if_isUnit (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

private theorem residueError_additive (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ r : ZMod q, residueError I w r * ZMod.stdAddChar (a * r)) =
      ∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a) := by
  classical
  simp only [residueError, sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  calc
    _ = ((I.card : ℂ) / (q.totient : ℂ)) *
        (∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a * r) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : IsUnit r <;> simp [hr]
    _ = _ := by
      rw [sum_if_isUnit, Finset.sum_const, nsmul_eq_mul]
      unfold additiveModel
      simp only [div_eq_mul_inv]
      ring



def window (n h m : ℕ) := Icc (m+1-h) (min m n)

theorem moving_fourier (n h m : ℕ) (a : ZMod q) :
    moving (n+1) h (errorCoeff a) m =
      ∑ r : ZMod q, residueError (window n h m) primeLog r * ZMod.stdAddChar (a*r) := by
  rw [residueError_additive, GoldbachWindow.moving_eq_sum]
  have hI : (range (n+1)).filter (fun k => m+1-h≤k ∧ k ≤ m) = window n h m := by
    ext k
    simp only [mem_filter,mem_range,window,mem_Icc,le_min_iff]
    omega
  rw [hI]
  rfl

def windowEnergy (q n h : ℕ) [NeZero q] :=
  (q:ℝ) * ∑ m ∈ range (n+1+h), ∑ r : ZMod q, ‖residueError (window n h m) primeLog r‖^2

theorem denominator_bound (n h : ℕ) (δ : ℝ) (hh : 0<h) (hd : 0≤δ) (hw : 6*(h:ℝ)*δ≤1) :
    (h:ℝ)^2/4 * (∑ a : ZMod q, ∫ t in (-δ)..δ, ‖poly (n+1) (errorCoeff a) t‖^2) ≤
       windowEnergy q n h := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a : ZMod q, ∑ m ∈ range (n+1+h), ‖moving (n+1) h (errorCoeff a) m‖^2 :=
      sum_le_sum fun a _ => GoldbachWindow.low_frequency_le (n+1) h (errorCoeff a) δ hh hd hw
    _ = _ := by
      rw [sum_comm,windowEnergy,Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      simp_rw [moving_fourier]
      exact GoldbachGRHWindow.additive_energy _

def cellError (n Q H : ℕ) (i : ℕ × ℕ) :=
  ∫ t in cell n Q H i, ‖primeSum n t - model n i t‖^2

theorem cell_to_poly (n Q H a : ℕ) (ha : a.Coprime q) :
    cellError n Q H (q,a) ≤ ∫ t in -(radius n H q)..(radius n H q),
      ‖poly (n+1) (errorCoeff (a:ZMod q)) t‖^2 := by
  have hunit := (ZMod.isUnit_iff_coprime a q).2 ha
  let G (β : ℝ) := ‖poly (n+1) (errorCoeff (a : ZMod q)) β‖^2
  have hGc : Continuous G := by unfold G poly phase; fun_prop
  have hG₀ (t : ℝ) : 0 ≤ G t := by unfold G; positivity
  have ht (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
    unfold G
    rw [shifted_error_eq, GoldbachGRHWindow.additiveModel_eq_moebius _ hunit]
    unfold model
    have ha' : (a:ℝ)/q + (t-center (q,a)) = t := by unfold center; ring
    rw [ha']
  have hc := GoldbachGRHArcTransport.cell_l2_le n Q H (q,a) G hGc hG₀
  simpa only [ht, cellError, G] using hc

def mass (q n h : ℕ) : ℝ := if hq : q=0 then 0 else
  letI := NeZero.mk hq
  windowEnergy q n h

def variance (n Q h : ℕ) := ∑ q ∈ Icc 1 Q, mass q n h

theorem common_window (n Q H h : ℕ) (hn : 0<n) (hh : 0<h) (hw : 6*h*H ≤ n) :
    (h:ℝ)^2 * (∑ i ∈ centers Q, cellError n Q H i) ≤ 8*variance n Q h := by
  rw [GoldbachGRHArcs.sum_centers_eq, Finset.mul_sum,variance,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hpos := (mem_Icc.mp hq).1
  have hqn : q ≠ 0 := by omega
  letI : NeZero q := ⟨hqn⟩
  let δ := radius n H q
  let E (a : ZMod q) := ∫ t in (-δ)..δ, ‖poly (n+1) (errorCoeff a) t‖^2
  have hd : 0 ≤ δ := by dsimp [δ,radius]; positivity
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hqR : (1:ℝ)≤q := by exact_mod_cast hpos
  have hwidth : 6*(h:ℝ)*δ ≤ 1 := by
    dsimp [δ,radius]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0<(q:ℝ)*(n:ℝ)),one_mul]
    exact (by exact_mod_cast hw : 6*(h:ℝ)*H≤n).trans (by nlinarith only [mul_le_mul_of_nonneg_right hqR hnR.le])
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hcells : (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), cellError n Q H (q,a)) ≤
      2*∑ a : ZMod q, E a :=
    (sum_le_sum (fun a ha => cell_to_poly n Q H a (mem_filter.mp ha).2)).trans
      (GoldbachGRHArcs.sum_numerators_le_real q E hE)
  have hden := denominator_bound (q:=q) n h δ hh hd hwidth
  change (h:ℝ)^2/4 * (∑ a : ZMod q, E a) ≤ _ at hden
  rw [mass,dite_eq_right hqn]
  linarith only [mul_le_mul_of_nonneg_left hcells (sq_nonneg (h:ℝ)),hden]

end
end GBSkirtVariance

open Finset MeasureTheory Filter
open scoped Interval Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHBudget (narrow width cutoff)
open GoldbachGRHArcs (centers cell)
open GoldbachGRHModel (model model_continuous)
open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHApproximation (integrand)
open GoldbachLowSkirt7 (lowIntegral lowModel)

def length (n : ℕ) := n / (12 * width n)

theorem length_ok : ∀ᶠ n : ℕ in atTop, 0 < length n ∧ 6 * length n * width n ≤ n := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry] with n h
  obtain ⟨hn,hQ,hQU,_,hH,_⟩ := h
  have hw : 0 < width n := hQ.trans (hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ))
  have hd : 0 < 12*width n := by omega
  constructor
  · exact Nat.div_pos (by omega) hd
  · calc
      _ ≤ length n*(12*width n) := by nlinarith
      _ ≤ n := Nat.div_mul_le_self _ _

set_option maxHeartbeats 1200000 in
theorem signed_bound {n : ℕ} (hn : 2 ≤ n) (hQH : narrow n ≤ width n)
    (hbudgetLow : 2 * width n * narrow n < n) {η : ℝ} (hη : 0 < η) :
    ‖lowIntegral n - lowModel n‖ ≤ (1+1/η)*(∑ i ∈ centers (narrow n),
      cellError n (narrow n) (width n) i) + η*(((n:ℝ)+1)*(Real.log (n:ℝ))^2) := by
  let osc (t : ℝ) := phase (-(n:ℝ)*t)
  have hOsc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  have hF : Continuous (integrand n) := (hS.pow 2).mul hOsc
  rw [lowIntegral, GoldbachGRHArcs.integrate_difference_eq_sum le_rfl hQH hbudgetLow _ hF,
    lowModel, ← Finset.sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in cell n (narrow n) (width n) i, integrand n t) -
        (∫ t in cell n (narrow n) (width n) i, model n i t ^ 2 * osc t) =
      ∫ t in cell n (narrow n) (width n) i,
        (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : cell n (narrow n) (width n) i ⊆ Set.Ioc (0:ℝ) 1 :=
      Set.inter_subset_right
    have h₁ : IntegrableOn (integrand n) (cell n (narrow n) (width n) i) volume :=
      (hF.intervalIntegrable 0 1).1.mono_set hpart
    have hm : Continuous (fun t => model n i t ^ 2 * osc t) :=
      ((model_continuous n i).pow 2).mul hOsc
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t)
        (cell n (narrow n) (width n) i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  apply (GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (centers (narrow n)) (cell n (narrow n) (width n))
    (fun i _ => GoldbachGRHArcs.measurable_cell _ _ _ i)
    (fun _ _ => Set.inter_subset_right) (GoldbachGRHArcs.cell_disjoint hbudgetLow)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hOsc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n:ℝ)*t)))) hη).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le)

def ShortVariance : Prop := ∀ᶠ n : ℕ in atTop,
  variance n (narrow n) (length n) ≤ (n:ℝ)*(length n:ℝ)^2 / (Real.log (n:ℝ))^8

theorem eventual_error_of_variance (hv : ShortVariance) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖lowIntegral n - lowModel n‖ ≤ ε*(n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachGRHBudget.eventual_geometry, length_ok, hv,
    ht.eventually (eventually_ge_atTop (max 1 (18/ε)))] with n hg hl hvn hL
  obtain ⟨hn,hQ,hQU,_,_,hbudget⟩ := hg
  let L := Real.log (n:ℝ)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLe : 18/ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0<L := by linarith
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hh : 0 < (length n:ℝ) := by exact_mod_cast hl.1
  have hQH := hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ)
  have hbud := (Nat.mul_le_mul_left (2 * width n) hQU).trans_lt hbudget
  let D := ∑ i ∈ centers (narrow n), cellError n (narrow n) (width n) i
  have hD : D ≤ 8*(n:ℝ)/L^8 := by
    have hC := common_window n (narrow n) (width n) (length n) (by omega) hl.1 hl.2
    have h₁ := hC.trans (mul_le_mul_of_nonneg_left hvn (by norm_num : (0:ℝ)≤8))
    change (length n:ℝ)^2 * D ≤ 8*((n:ℝ)*(length n:ℝ)^2/L^8) at h₁
    apply le_of_mul_le_mul_left (a:=(length n:ℝ)^2) _ (by positivity)
    linarith only [show (length n:ℝ)^2 * D ≤ (length n:ℝ)^2 * (8*(n:ℝ)/L^8) from h₁.trans_eq (by ring)]
  have hη : 0<1/L^3 := by positivity
  have hS := signed_bound hn hQH hbud hη
  change ‖_‖ ≤ (1+1/(1/L^3))*D + (1/L^3)*(((n:ℝ)+1)*L^2) at hS
  calc
    _ ≤ _ := hS
    _ ≤ (1+1/(1/L^3))*(8*(n:ℝ)/L^8) + (1/L^3)*((n+1:ℝ)*L^2) := by
      gcongr
    _ ≤ 18*(n:ℝ)/L := by
      have hpow3 : 1≤L^3 := one_le_pow₀ hL1
      have hpow4 : 1≤L^4 := one_le_pow₀ hL1
      have hp : L^3≤L^7 := by
        calc
          _ = L^3*1 := by ring
          _ ≤ L^3*L^4 := by gcongr
          _ = _ := by ring
      have ha : (1+L^3)*(8*(n:ℝ)) ≤ (16*(n:ℝ))*L^7 := by
        nlinarith only [mul_le_mul_of_nonneg_right hpow3 (by positivity : 0≤(n:ℝ)),
          mul_le_mul_of_nonneg_right hp (by positivity : 0≤(n:ℝ))]
      have hb : (1+1/(1/L^3))*(8*(n:ℝ)/L^8) ≤ 16*(n:ℝ)/L := by
        rw [one_div_one_div, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hL0]
        convert mul_le_mul_of_nonneg_right ha hL0.le using 1 <;> ring
      have hc : (1/L^3)*((n+1:ℝ)*L^2) ≤ 2*(n:ℝ)/L := by
        have heq : (1/L^3)*((n+1:ℝ)*L^2) = ((n:ℝ)+1)/L := by field_simp <;> ring
        rw [heq]
        gcongr
        linarith
      exact (add_le_add hb hc).trans_eq (by ring)
    _ ≤ _ := by
      apply (div_le_iff₀ hL0).2
      have hε := (div_le_iff₀ he).1 hLe
      nlinarith only [mul_le_mul_of_nonneg_right hε (by positivity : 0≤(n:ℝ))]

theorem low_skirt_of_variance (hv : ShortVariance) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(ε*(n:ℝ)) ≤ (lowIntegral n).re := by
  intro ε he
  have ht := (eventual_error_of_variance hv (ε/2) (by positivity)).and
    (GoldbachLowSkirt7.eventual_low_model_floor (ε/2) (by positivity))
  apply eventually_atTop.mp
  filter_upwards [ht] with n h
  intro hEven
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans h.1)).1
  rw [Complex.sub_re] at hr
  have hm : -(ε/2)*(n:ℝ) ≤ (lowModel n).re := h.2 hEven
  linarith

end
end GBSkirtVariance

open Finset MeasureTheory Filter
open scoped Interval Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHWindow (primeLog)
variable {q : ℕ} [NeZero q]

def reducedMax (I : Finset ℕ) (q : ℕ) [NeZero q] : ℝ :=
  (univ : Finset (ZMod q)).sup' univ_nonempty
    (fun r => if IsUnit r then ‖residueError I primeLog r‖ else 0)

theorem reduced_le (I : Finset ℕ) (r : ZMod q) (hr : IsUnit r) :
    ‖residueError I primeLog r‖ ≤ reducedMax I q := by
  have h := Finset.le_sup' (f:=fun z : ZMod q => if IsUnit z then ‖residueError I primeLog z‖ else 0)
    (s:=univ) (mem_univ r)
  simpa only [if_pos hr,reducedMax] using h

theorem reduced_nonneg (I : Finset ℕ) : 0 ≤ reducedMax I q :=
  (norm_nonneg _).trans (reduced_le I (1:ZMod q) isUnit_one)

theorem card_window_le (n h m : ℕ) : (window n h m).card ≤ h := by
  simp only [window,Nat.card_Icc]
  omega

theorem trivial_window_error (n h m : ℕ) (hn : 2≤n) (r : ZMod q) :
    ‖residueError (window n h m) primeLog r‖ ≤ (h:ℝ)*(Real.log (n:ℝ)+1) := by
  let I := window n h m
  have hi : I.card ≤ h := card_window_le _ _ _
  have hL : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  have hprime (k : ℕ) (hk : k ∈ I) : ‖primeLog k‖ ≤ Real.log (n:ℝ) := by
    have hkn : k≤n := ((mem_Icc.mp hk).2.trans (min_le_right _ _))
    by_cases hp : k.Prime
    · simp only [primeLog,if_pos hp,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le : (1:ℝ)≤k))]
      exact Real.log_le_log (by exact_mod_cast hp.pos : 0<(k:ℝ)) (by exact_mod_cast hkn : (k:ℝ)≤n)
    · simpa [primeLog,hp] using hL
  let J := I.filter (fun k : ℕ => (k:ZMod q)=r)
  have hj : J.card ≤ h := (card_filter_le _ _).trans hi
  have hsum : ‖∑ k ∈ J, primeLog k‖ ≤ (h:ℝ)*Real.log (n:ℝ) := by
    apply (norm_sum_le J _).trans
    calc
      _ ≤ ∑ k ∈ J, Real.log (n:ℝ) := sum_le_sum fun k hk => hprime k (mem_filter.mp hk).1
      _ = (J.card:ℝ)*Real.log (n:ℝ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hL
  have hmodel : ‖if IsUnit r then (I.card:ℂ)/(q.totient:ℂ) else 0‖ ≤ (h:ℝ) := by
    split_ifs
    · simp only [norm_div,Complex.norm_natCast]
      have hφ : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
      exact (div_le_self (by positivity) hφ).trans (by exact_mod_cast hi)
    · simp
  change ‖(∑ k ∈ J, primeLog k) - (if IsUnit r then (I.card:ℂ)/(q.totient:ℂ) else 0)‖ ≤ _
  exact (norm_sub_le _ _).trans ((add_le_add hsum hmodel).trans_eq (by ring))

theorem classes_l1 (I : Finset ℕ) (B : ℝ) (hB : 0≤B)
    (htriv : ∀ r : ZMod q, ‖residueError I primeLog r‖ ≤ B) :
    (∑ r : ZMod q, ‖residueError I primeLog r‖^2) ≤
      (q:ℝ)*B*reducedMax I q + (Real.log (q:ℝ))^2 := by
  let U := (univ : Finset (ZMod q)).filter IsUnit
  let V := (univ : Finset (ZMod q)).filter (fun r => ¬IsUnit r)
  have hcard : U.card ≤ q := by simpa [ZMod.card] using (Finset.card_filter_le (s:=(univ : Finset (ZMod q))) IsUnit)
  have hU : (∑ r ∈ U, ‖residueError I primeLog r‖^2) ≤ (q:ℝ)*B*reducedMax I q := by
    calc
      _ ≤ ∑ r ∈ U, B*reducedMax I q := by
        apply sum_le_sum
        intro r hr
        rw [pow_two]
        exact mul_le_mul (htriv r) (reduced_le I r (mem_filter.mp hr).2) (norm_nonneg _) hB
      _ = (U.card:ℝ)*(B*reducedMax I q) := by simp
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hB (reduced_nonneg I))
  have hV : (∑ r ∈ V, ‖residueError I primeLog r‖) ≤ Real.log (q:ℝ) := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖primeLog k‖ := by
        refine sum_le_sum fun r hr => ?_
        have hr' : ¬ IsUnit r := (mem_filter.mp hr).2
        change ‖(∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=r), primeLog k) -
          (if IsUnit r then (I.card:ℂ)/(q.totient:ℂ) else 0)‖ ≤ _
        simpa only [if_neg hr',sub_zero] using norm_sum_le (I.filter (fun k : ℕ => (k:ZMod q)=r)) primeLog
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]; simp [V]
      _ ≤ _ := GoldbachGRHWindow.primeLog_nonunit_mass_le I
  have hV₂ := (Finset.sum_sq_le_sq_sum_of_nonneg (fun r (_ : r ∈ V) => norm_nonneg (residueError I primeLog r))).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (ZMod q))) (p := IsUnit)]
  exact add_le_add hU hV₂

end
end GBSkirtVariance

open Finset MeasureTheory Filter
open scoped Interval Topology Classical
namespace GBSkirtVariance
noncomputable section

def endpointSum (q n h : ℕ) : ℝ := if hq : q=0 then 0 else
  letI := NeZero.mk hq
  ∑ m ∈ range (n+1+h), reducedMax (window n h m) q

def clippedL1 (n Q h : ℕ) := ∑ q ∈ Icc 1 Q, endpointSum q n h

theorem variance_of_L1 (n Q h : ℕ) (hn : 2 ≤ n) (hQ : Q ≤ n) :
    variance n Q h ≤
      (Q:ℝ)^2 * ((h:ℝ)*(Real.log (n:ℝ)+1)) * clippedL1 n Q h +
      (Q:ℝ)^2 * ((n+1+h:ℕ):ℝ) * (Real.log (n:ℝ))^2 := by
  let B := (h:ℝ)*(Real.log (n:ℝ)+1)
  let L := Real.log (n:ℝ)
  let M := ((n+1+h:ℕ):ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq' (q : ℕ) (hq : q ∈ Icc 1 Q) :
      mass q n h ≤ (Q:ℝ)^2*B*endpointSum q n h + (Q:ℝ)*M*L^2 := by
    obtain ⟨hqpos,hqQ⟩ := mem_Icc.mp hq
    have hqn : q ≠ 0 := by omega
    letI : NeZero q := ⟨hqn⟩
    let E := ∑ m ∈ range (n+1+h), reducedMax (window n h m) q
    have hE : 0 ≤ E := sum_nonneg fun _ _ => reduced_nonneg _
    have hqQ' : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
    have hlog : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast hqpos)
    have hlog' : Real.log (q:ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast hqpos : 0<(q:ℝ)) (by exact_mod_cast hqQ.trans hQ)
    have hsum := sum_le_sum (s:=range (n+1+h)) (fun m _ =>
      classes_l1 (q:=q) (window n h m) B hB (trivial_window_error n h m hn))
    rw [mass,dite_eq_right hqn,endpointSum,dite_eq_right hqn,windowEnergy]
    calc
      _ ≤ (q:ℝ)*(((q:ℝ)*B)*E + M*(Real.log (q:ℝ))^2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
        convert hsum using 1
        simp [E,M,Finset.sum_add_distrib,Finset.mul_sum]
      _ = (q:ℝ)^2*B*E + (q:ℝ)*M*(Real.log (q:ℝ))^2 := by ring
      _ ≤ (Q:ℝ)^2*B*E + (Q:ℝ)*M*L^2 := by
        dsimp only [M]
        gcongr
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((Q:ℝ)^2*B*endpointSum q n h + (Q:ℝ)*M*L^2) := sum_le_sum hq'
    _ = _ := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      change _ + _ = (Q:ℝ)^2*B*clippedL1 n Q h + (Q:ℝ)^2*M*L^2
      congr 1
      simp [Nat.card_Icc]
      ring

end
end GBSkirtVariance

open Finset MeasureTheory Filter
open scoped Interval Topology Classical
namespace GBSkirtVariance
noncomputable section

def fullEndpointSum (q n h : ℕ) : ℝ := if hq : q=0 then 0 else
  letI := NeZero.mk hq
  ∑ y ∈ range (n+1), reducedMax (Icc (y+1) (y+h)) q

def fullL1 (n Q h : ℕ) := ∑ q ∈ Icc 1 Q, fullEndpointSum q n h

theorem clipped_to_full (n Q h : ℕ) (hn : 2≤n) (hhn : h≤n) :
    clippedL1 n Q h ≤ fullL1 n Q h + (Q:ℝ)*2*(h:ℝ)^2*(Real.log (n:ℝ)+1) := by
  let B := (h:ℝ)*(Real.log (n:ℝ)+1)
  have hL : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  have hB : 0≤B := by dsimp [B]; positivity
  have hq' (q : ℕ) (hq : q ∈ Icc 1 Q) :
      endpointSum q n h ≤ fullEndpointSum q n h + 2*(h:ℝ)*B := by
    have hp := (mem_Icc.mp hq).1
    have hqn : q ≠ 0 := by omega
    letI : NeZero q := ⟨hqn⟩
    let F := fun m => reducedMax (window n h m) q
    let G := fun y => reducedMax (Icc (y+1) (y+h)) q
    have hF (m : ℕ) : F m ≤ B := by
      apply Finset.sup'_le
      intro r _
      split_ifs
      · exact trivial_window_error n h m hn r
      · exact hB
    have cut (a : ℕ) : (∑ i ∈ range h, F (a+i)) ≤ (h:ℝ)*B :=
      (sum_le_sum (fun i (_ : i ∈ range h) => hF (a+i))).trans_eq (by simp)
    have start : (∑ m ∈ range h, F m) ≤ (h:ℝ)*B := by simpa using cut 0
    have middle : (∑ y ∈ range (n+1-h), F (h+y)) ≤ ∑ y ∈ range (n+1), G y := by
      calc
        _ = ∑ y ∈ range (n+1-h), G y := by
          apply sum_congr rfl
          intro y hy
          have hy' := mem_range.mp hy
          have hw : window n h (h+y) = Icc (y+1) (y+h) := by
            unfold window
            congr 1 <;> omega
          simp only [F,G,hw]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => reduced_nonneg _)
    have split' : (∑ m ∈ range (n+1), F m) =
        (∑ m ∈ range h, F m) + ∑ y ∈ range (n+1-h), F (h+y) := by
      have hs := Finset.sum_range_add F h (n+1-h)
      rwa [show h+(n+1-h) = n+1 by omega] at hs
    rw [endpointSum,dite_eq_right hqn,fullEndpointSum,dite_eq_right hqn]
    change (∑ m ∈ range (n+1+h), F m) ≤ (∑ y ∈ range (n+1), G y) + _
    rw [Finset.sum_range_add,split']
    linarith only [start,middle,cut (n+1)]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (fullEndpointSum q n h + 2*(h:ℝ)*B) := sum_le_sum hq'
    _ = _ := by
      rw [sum_add_distrib]
      congr 1
      simp [Nat.card_Icc,B]
      ring
end
end GBSkirtVariance

open Finset MeasureTheory Filter
open scoped Interval Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHBudget (narrow cutoff width)

private theorem log_nat_le (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnon : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hpow : (2:ℝ)^(Nat.log 2 (n+2)) ≤ ((n+2 : ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n:ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0≤(_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm, hraw, hlog]

theorem eventual_scales : ∀ᶠ n : ℕ in atTop,
    let L := Real.log (n:ℝ)
    16 ≤ L ∧ (narrow n:ℝ) ≤ 16*L^2 ∧ 1000000*L^20 ≤ (length n:ℝ) ∧
      1000000*L^20*(length n:ℝ) ≤ (n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachGRHBudget.eventual_geometry,GoldbachGRHBudget.eventually_log_pow_le 20
    (1/3) (1/24000000) (by norm_num) (by norm_num),ht.eventually (eventually_ge_atTop 16)]
    with n hg hpow hL
  obtain ⟨hn,hQ,hQU,_,_,hg⟩ := hg
  let L := Real.log (n:ℝ)
  change 16 ≤ L at hL
  have hL1 : 1≤L := by linarith
  have h20 : 1≤L^20 := one_le_pow₀ hL1
  have hlarge : 12000000*L^20 ≤ (cutoff n:ℝ) := by
    have hf := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    change _ < (cutoff n:ℝ)+1 at hf
    change L^20 ≤ _ at hpow
    linarith only [hf,hpow,h20]
  have hwidth := GoldbachGRHBudget.width_ge_cutoff n hQ
  have hw : 0<width n := hQ.trans (hQU.trans hwidth)
  have hu : cutoff n < 6*(length n+1) := by
    have hh := Nat.lt_mul_div_succ n (by positivity : 0<12*width n)
    apply Nat.lt_of_mul_lt_mul_left (a:=2*width n)
    exact (hg.trans hh).trans_eq (by unfold length; ring)
  have huc : length n * cutoff n ≤ n := by
    apply le_trans _ (Nat.div_mul_le_self n (12*width n))
    apply Nat.mul_le_mul_left
    omega
  refine ⟨hL,?_,?_,?_⟩
  · change (((Nat.log 2 (n+2))^2:ℕ):ℝ) ≤ 16*L^2
    push_cast
    calc
      _ ≤ (4*L)^2 := pow_le_pow_left₀ (by positivity) (log_nat_le n hn) 2
      _ = _ := by ring
  · have hu' : (cutoff n:ℝ)<6*((length n:ℝ)+1) := by exact_mod_cast hu
    linarith only [hlarge,hu',h20]
  · have hv : 1000000*L^20 ≤ (cutoff n:ℝ) := by linarith only [hlarge,h20]
    exact (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (length n))).trans
      (by rw [mul_comm]; exact_mod_cast huc)

theorem number_budget (N h Q L : ℝ) (hN : 1≤N) (hh : 1≤h) (hQ : 0≤Q)
    (hL : 16≤L) (hQN : Q≤16*L^2) (hb : 1000000*L^20 ≤ h) (hc : 1000000*L^20*h≤N) :
    Q^2*(h*(L+1))*(N*h/L^16 + Q*2*h^2*(L+1)) + Q^2*(3*N)*L^2 ≤ N*h^2/L^8 := by
  have hL1 : 1≤L := by linarith
  have hL0 : 0<L := by linarith
  have hhn : 0≤h := by linarith
  have hn : 0≤N := by linarith
  have hp : L+1 ≤ 2*L := by linarith
  have hmain : 3*Q^2*(L+1) ≤ L^8 := by
    calc
      _ ≤ 3*(16*L^2)^2*(2*L) := by gcongr
      _ = 1536*L^5 := by ring
      _ ≤ L^3*L^5 := by
        gcongr
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) hL 3
        norm_num at this
        linarith
      _ = _ := by ring
  have hbdy : 6*Q^3*(L+1)^2*L^8 ≤ 1000000*L^20 := by
    calc
      _ ≤ 6*(16*L^2)^3*(2*L)^2*L^8 := by gcongr
      _ = 98304*L^16 := by ring
      _ ≤ 1000000*L^20 := by
        gcongr <;> norm_num
  have hnon : 9*Q^2*L^10 ≤ h^2 := by
    calc
      _ ≤ 9*(16*L^2)^2*L^10 := by gcongr
      _ = 2304*L^14 := by ring
      _ ≤ 1000000*L^20 := by gcongr <;> norm_num
      _ ≤ h := hb
      _ ≤ h^2 := by nlinarith only [mul_le_mul_of_nonneg_right hh hhn]
  have a : 3*(Q^2*(h*(L+1))*(N*h/L^16))*L^8 ≤ N*h^2 := by
    have hx : 3*(Q^2*(h*(L+1))*(N*h/L^16))*L^8 = (3*Q^2*(L+1))*(N*h^2)/L^8 := by
      field_simp [hL0.ne'] <;> ring
    rw [hx,div_le_iff₀ (by positivity)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmain (by positivity : 0≤N*h^2)
  have b := (mul_le_mul_of_nonneg_right hbdy hhn).trans hc
  have b' := mul_le_mul_of_nonneg_right b (sq_nonneg h)
  have c := mul_le_mul_of_nonneg_right hnon hn
  apply (le_div_iff₀ (by positivity)).2
  ring_nf at a b' c ⊢
  linarith only [a,b',c]

def FullAverage : Prop := ∀ᶠ n : ℕ in atTop,
  fullL1 n (narrow n) (length n) ≤ (n:ℝ)*(length n:ℝ)/(Real.log (n:ℝ))^16

set_option maxHeartbeats 1200000 in
theorem variance_of_full_average (hA : FullAverage) : ShortVariance := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry,length_ok,eventual_scales,hA] with n hg hl hs hav
  obtain ⟨hn,hQ,hQU,hUn,_,_⟩ := hg
  obtain ⟨hL,hQN,hb,hc⟩ := hs
  have hnat : length n ≤ n := Nat.div_le_self _ _
  have hM : (((n+1+length n : ℕ):ℝ)) ≤ 3*(n:ℝ) := by exact_mod_cast (by omega : n+1+length n≤3*n)
  have hclip := (clipped_to_full n (narrow n) (length n) hn hnat).trans (add_le_add hav (le_refl _))
  have hV := variance_of_L1 n (narrow n) (length n) hn (hQU.trans hUn)
  have hlog : 0 ≤ Real.log (n:ℝ) := by linarith only [hL]
  have hx := number_budget (n:ℝ) (length n:ℝ) (narrow n:ℝ) (Real.log (n:ℝ))
    (by exact_mod_cast (by omega : 1≤n)) (by exact_mod_cast hl.1) (by positivity) hL hQN hb hc
  exact hV.trans ((add_le_add (mul_le_mul_of_nonneg_left hclip (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (sq_nonneg _)) (sq_nonneg _))).trans hx)

end
end GBSkirtVariance

open Finset Filter
open scoped Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHBudget (narrow cutoff width)

theorem dyadic_cover (f : ℕ → ℝ) (hf : ∀ y, 0≤f y) (n h : ℕ) (hh : 0<h)
    (K : ℝ) (hK : 0≤K)
    (localBound : ∀ x : ℕ, h≤x → x≤n → (∑ y ∈ Ico x (2*x), f y) ≤ (x:ℝ)*K) :
    (∑ y ∈ range (n+1), f y) ≤ (∑ y ∈ range (2*h), f y) + 2*((n+1:ℕ):ℝ)*K := by
  suffices aux : ∀ m : ℕ, m≤n+1 → (∑ y ∈ range m, f y) ≤
      (∑ y ∈ range (2*h), f y) + 2*(m:ℝ)*K by exact aux _ le_rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    by_cases small : m≤2*h
    · apply (sum_le_sum_of_subset_of_nonneg (range_mono small) (fun y _ _ => hf y)).trans
      linarith only [mul_nonneg (by positivity : 0≤2*(m:ℝ)) hK]
    let x := (m+1)/2
    have hxm : x < m := by dsimp [x]; omega
    have hxN : x ≤ n := by omega
    have hxH : h ≤ x := by dsimp [x]; omega
    have hx2 : m≤2*x := by dsimp [x]; omega
    have hx3 : 3*x≤2*m := by dsimp [x]; omega
    have hleft := ih x hxm (by omega)
    have hright : (∑ y ∈ Ico x m, f y) ≤ (x:ℝ)*K :=
      (sum_le_sum_of_subset_of_nonneg (fun y hy => mem_Ico.mpr
        ⟨(mem_Ico.mp hy).1,(mem_Ico.mp hy).2.trans_le hx2⟩) (fun y _ _ => hf y)).trans (localBound x hxH hxN)
    rw [← sum_range_add_sum_Ico f hxm.le]
    have hxr : 3*(x:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hx3
    linarith only [hleft,hright,mul_le_mul_of_nonneg_right hxr hK]

def pointError (q h y : ℕ) : ℝ := if hq : q=0 then 0 else
  letI := NeZero.mk hq
  reducedMax (Icc (y+1) (y+h)) q

def row (Q h y : ℕ) := ∑ q ∈ Icc 1 Q, pointError q h y

theorem row_nonneg (Q h y : ℕ) : 0 ≤ row Q h y := by
  apply sum_nonneg
  intro q _
  unfold pointError
  split
  · exact le_rfl
  · rename_i hq
    letI : NeZero q := ⟨hq⟩
    exact reduced_nonneg _

theorem fullL1_rows (n Q h : ℕ) : fullL1 n Q h = ∑ y ∈ range (n+1), row Q h y := by
  unfold fullL1 row
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  have hqn : q≠0 := by have := (mem_Icc.mp hq).1; omega
  simp only [fullEndpointSum,pointError,dite_eq_right hqn]

theorem initial_rows (n Q h : ℕ) (hn : 2≤n) (hh : h≤n) :
    (∑ y ∈ range (2*h), row Q h y) ≤ 2*(Q:ℝ)*(h:ℝ)^2*(Real.log (3*(n:ℝ))+1) := by
  have hB : 0 ≤ (h:ℝ)*(Real.log (3*(n:ℝ))+1) := by
    have hp : 1≤3*(n:ℝ) := by exact_mod_cast (by omega : 1≤3*n)
    have := Real.log_nonneg hp
    positivity
  have hy' (y : ℕ) (hy : y ∈ range (2*h)) :
      row Q h y ≤ (Q:ℝ)*((h:ℝ)*(Real.log (3*(n:ℝ))+1)) := by
    unfold row
    apply le_trans (sum_le_sum (g:=fun _ => (h:ℝ)*(Real.log (3*(n:ℝ))+1)) ?_) ?_
    · intro q hq
      have hqn : q≠0 := by have := (mem_Icc.mp hq).1; omega
      rw [pointError,dite_eq_right hqn]
      letI : NeZero q := ⟨hqn⟩
      apply Finset.sup'_le
      intro r _
      split_ifs
      · have hw : window (3*n) h (y+h) = Icc (y+1) (y+h) := by
          have hy' := mem_range.mp hy
          unfold window
          congr 1 <;> omega
        have hT := trivial_window_error (3*n) h (y+h) (by omega) r
        simpa only [hw,Nat.cast_mul,Nat.cast_ofNat] using hT
      · exact hB
    · simp [Nat.card_Icc]
  apply (sum_le_sum hy').trans_eq
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  ring

end
end GBSkirtVariance

open Finset Filter
open scoped Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHBudget (narrow cutoff width)

theorem paper_scales : ∀ᶠ n : ℕ in atTop,
    (n:ℝ)^(5/8:ℝ) ≤ (length n:ℝ) ∧
    (narrow n:ℝ)^2 * (n:ℝ)^(1/4:ℝ) ≤ (length n:ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry,eventual_scales,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/24) (1/100000) (by norm_num) (by norm_num),
    GoldbachGRHBudget.eventually_log_pow_le 4 (3/8) (1/256) (by norm_num) (by norm_num)]
    with n hg hs h₂ h₄
  obtain ⟨hn,hQ,hQU,_,_,_⟩ := hg
  let L := Real.log (n:ℝ)
  let A := (n:ℝ)^(5/8:ℝ)
  let R := (n:ℝ)^(1/3:ℝ)
  let Y := (n:ℝ)^(1/24:ℝ)
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hA : 1 ≤ A := Real.one_le_rpow hn1 (by norm_num)
  have hR : 0 ≤ R := Real.rpow_nonneg hn0.le _
  have hY : 0 ≤ Y := Real.rpow_nonneg hn0.le _
  have hU : (cutoff n:ℝ) ≤ R := Nat.floor_le hR
  have hid : R*Y*A = (n:ℝ) := by
    unfold R Y A; rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    norm_num
  have hw := hQ.trans (hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ))
  have hW : 0 < (width n:ℝ) := by exact_mod_cast hw
  have hqn : (narrow n:ℝ) ≤ 16*L^2 := hs.2.1
  have hh : 12*(width n:ℝ)*(2*A) ≤ (n:ℝ) := by
    calc
      _ = 98304*(cutoff n:ℝ)*((narrow n:ℝ)/16)*A := by
        unfold width; push_cast; ring
      _ ≤ 98304*R*(Y/100000)*A := by
        have hcut : (narrow n:ℝ)/16 ≤ Y/100000 := by change L^2 ≤ (1/100000:ℝ)*Y at h₂; linarith
        gcongr
      _ ≤ R*Y*A := by
        nlinarith only [mul_nonneg (mul_nonneg hR hY) (le_trans (by norm_num : (0:ℝ)≤1) hA)]
      _ = _ := hid
  have hlen : A ≤ (length n:ℝ) := by
    have hnat := Nat.lt_mul_div_succ n (by positivity : 0<12*width n)
    have hreal : (n:ℝ) < 12*(width n:ℝ)*((length n:ℝ)+1) := by exact_mod_cast hnat
    have := lt_of_mul_lt_mul_left (hh.trans_lt hreal) (by positivity : 0≤12*(width n:ℝ))
    linarith
  refine ⟨hlen,le_trans ?_ hlen⟩
  have hcoef : (narrow n:ℝ)^2 ≤ (n:ℝ)^(3/8:ℝ) := by
    have v := pow_le_pow_left₀ (Nat.cast_nonneg _) hqn 2
    change L^4 ≤ _ at h₄
    nlinarith only [v,h₄]
  calc
    _ ≤ (n:ℝ)^(3/8:ℝ)*(n:ℝ)^(1/4:ℝ) := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn0.le _)
    _ = _ := by unfold A; rw [← Real.rpow_add hn0]; norm_num

end
end GBSkirtVariance

open Finset Filter
open scoped Topology Classical
namespace GBSkirtVariance
noncomputable section
open GoldbachGRHBudget (narrow)

def IntegerDyadicAP : Prop := ∃ C : ℝ, 0 < C ∧ ∃ X : ℕ,
  ∀ x h Q : ℕ, X ≤ x → 1 ≤ Q → (x:ℝ)^(5/8:ℝ) ≤ (h:ℝ) → h ≤ x →
    (Q:ℝ)^2*(x:ℝ)^(1/4:ℝ) ≤ (h:ℝ) →
    (∑ y ∈ Ico x (2*x), row Q h y) ≤ C*(x:ℝ)*(h:ℝ)/(Real.log (x:ℝ))^18

theorem full_average_of_dyadic (hyp : IntegerDyadicAP) : FullAverage := by
  obtain ⟨C,hC,X,hX⟩ := hyp
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht' := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/8)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachGRHBudget.eventual_geometry,eventual_scales,paper_scales,length_ok,
    ht.eventually (eventually_ge_atTop (8*C*2^18)),
    ht'.eventually (eventually_ge_atTop (X:ℝ))] with n hg hs hscale hl hbig hX'
  let L := Real.log (n:ℝ)
  let H := (length n:ℝ)
  let Q := narrow n
  let K := C*(2:ℝ)^18*H/L^18
  obtain ⟨hn,hQ,_,_,_,_⟩ := hg
  obtain ⟨hL,hQN,_,hbudget⟩ := hs
  change 16 ≤ L at hL
  change (Q:ℝ) ≤ 16*L^2 at hQN
  change 1000000*L^20*H ≤ (n:ℝ) at hbudget
  change 8*C*2^18 ≤ L at hbig
  change (X:ℝ) ≤ (n:ℝ)^(5/8:ℝ) at hX'
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hL1 : 1≤L := by linarith
  have hL0 : 0<L := by linarith
  have hH : 0<H := by dsimp [H]; exact_mod_cast hl.1
  have hhn : length n ≤ n := Nat.div_le_self _ _
  have hK : 0≤K := by dsimp [K]; positivity
  have hlocal (x : ℕ) (hx : length n ≤ x) (hxn : x ≤ n) :
      (∑ y ∈ Ico x (2*x), row Q (length n) y) ≤ (x:ℝ)*K := by
    have hxr : (x:ℝ) ≤ n := by exact_mod_cast hxn
    have hhx : H ≤ (x:ℝ) := by dsimp [H]; exact_mod_cast hx
    have hxl : (n:ℝ)^(5/8:ℝ) ≤ (x:ℝ) := hscale.1.trans hhx
    have hlog : L ≤ 2*Real.log (x:ℝ) := by
      have ht := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hxl
      rw [Real.log_rpow hn0] at ht
      change (5/8:ℝ)*L ≤ _ at ht
      linarith
    have hxp : 0 < Real.log (x:ℝ) := by linarith
    have he := hX x (length n) Q (by exact_mod_cast hX'.trans hxl) hQ
      ((Real.rpow_le_rpow (by positivity) hxr (by norm_num)).trans hscale.1) hx
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hxr (by norm_num)) (sq_nonneg _)).trans hscale.2)
    have hpow := pow_le_pow_left₀ hL0.le hlog 18
    rw [mul_pow] at hpow
    apply he.trans
    change C*(x:ℝ)*H/(Real.log (x:ℝ))^18 ≤ (x:ℝ)*(C*2^18*H/L^18)
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hpow (by positivity : 0≤C*(x:ℝ)*H)]
  have ht := dyadic_cover (row Q (length n)) (row_nonneg Q _) n (length n) hl.1 K hK hlocal
  have hinit := initial_rows n Q (length n) hn hhn
  have hlog3 : Real.log (3*(n:ℝ))+1 ≤ 3*L := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have ha := Real.log_le_sub_one_of_pos (by norm_num : 0 < (3:ℝ))
    change Real.log 3 + L + 1 ≤ _
    linarith
  have hnon : 0 ≤ Real.log (3*(n:ℝ))+1 := by
    have := Real.log_nonneg (by linarith only [hn1] : 1≤3*(n:ℝ))
    linarith
  have hi : (∑ y ∈ range (2*length n), row Q (length n) y)*L^16 ≤ (n:ℝ)*H/2 := by
    have ha : (∑ y ∈ range (2*length n), row Q (length n) y) ≤ 96*H^2*L^3 := by
      apply hinit.trans
      calc
        _ ≤ 2*(16*L^2)*H^2*(3*L) := by gcongr
        _ = _ := by ring
    have hp19 : L^19 ≤ L^20 := pow_le_pow_right₀ hL1 (by decide)
    have hv : 192*L^19*H ≤ (n:ℝ) := by
      apply le_trans _ hbudget
      gcongr <;> norm_num
    nlinarith only [mul_le_mul_of_nonneg_right ha (by positivity : 0≤L^16),mul_le_mul_of_nonneg_right hv hH.le]
  have he : (2*((n+1:ℕ):ℝ)*K)*L^16 ≤ (n:ℝ)*H/2 := by
    have hcoeff : 8*C*2^18 ≤ L^2 := by nlinarith only [hbig,mul_le_mul_of_nonneg_right hL1 hL0.le]
    have hc : 2*((n+1:ℕ):ℝ) ≤ 4*(n:ℝ) := by push_cast; linarith
    have hx : (2*((n+1:ℕ):ℝ)*K)*L^16 ≤ (4*(n:ℝ)*K)*L^16 := by gcongr
    apply hx.trans
    have hid : (4*(n:ℝ)*K)*L^16 = (4*(n:ℝ)*C*2^18*H)/L^2 := by
      unfold K; field_simp [hL0.ne'] <;> ring
    rw [hid,div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff (by positivity : 0≤(n:ℝ)*H)]
  rw [fullL1_rows]
  apply (le_div_iff₀ (by positivity : 0<L^16)).2
  nlinarith only [mul_le_mul_of_nonneg_right ht (by positivity : 0≤L^16),hi,he]

end
end GBSkirtVariance

open Finset Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

def thetaClass (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) : ℝ :=
  ∑ k ∈ (Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊).filter (fun k : ℕ => (k:ZMod q)=r),
    if k.Prime then Real.log (k:ℝ) else 0

theorem theta_window_spec {y : ℝ} (hy : 0≤y) (h k : ℕ) :
    k ∈ Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ ↔ y < (k:ℝ) ∧ (k:ℝ) ≤ y+h := by
  rw [mem_Icc,Nat.le_floor_iff (by positivity)]
  exact and_congr_left fun _ => by rw [Nat.succ_le_iff,Nat.floor_lt hy]

def realError (q : ℕ) (h y : ℝ) : ℝ := if hq : q=0 then 0 else
  letI : NeZero q := ⟨hq⟩
  (univ : Finset (ZMod q)).sup' univ_nonempty (fun r =>
    if IsUnit r then |thetaClass q r y h - (h:ℝ)/(q.totient:ℝ)| else 0)

def realRow (Q : ℕ) (h y : ℝ) := ∑ q ∈ Icc 1 Q, realError q h y

theorem real_eq_integer (q h k : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    realError q h y = pointError q h k := by
  by_cases hq : q=0
  · simp only [realError,pointError,dite_eq_left hq]
  letI : NeZero q := ⟨hq⟩
  have hy₀ := (Nat.cast_nonneg k (α:=ℝ)).trans hy.1
  have hfloor : ⌊y⌋₊ = k := (Nat.floor_eq_iff hy₀).2 ⟨hy.1,by simpa using hy.2⟩
  have hcard : (Icc (k+1) (k+h)).card = h := by rw [Nat.card_Icc]; omega
  rw [realError,pointError,dite_eq_right hq,dite_eq_right hq,reducedMax]
  congr 1
  funext r
  split_ifs with hr
  · let J := (Icc (k+1) (k+h)).filter (fun j : ℕ => (j:ZMod q)=r)
    have hw : (∑ j ∈ J, GoldbachGRHWindow.primeLog j) =
        ((∑ j ∈ J, if j.Prime then Real.log (j:ℝ) else 0 : ℝ):ℂ) := by
      simp only [Complex.ofReal_sum,GoldbachGRHWindow.primeLog]
    change |thetaClass q r y h - (h:ℝ)/(q.totient:ℝ)| =
        ‖(∑ j ∈ J, GoldbachGRHWindow.primeLog j) -
            (if IsUnit r then ((Icc (k+1) (k+h)).card:ℂ)/(q.totient:ℂ) else 0)‖
    simp only [thetaClass,Nat.floor_add_natCast hy₀,hfloor,ite_eq_left hr,hcard,hw]
    change |(∑ j ∈ J, if j.Prime then Real.log (j:ℝ) else 0 : ℝ) - (h:ℝ)/(q.totient:ℝ)| = _
    rw [← Complex.ofReal_natCast h, ← Complex.ofReal_natCast q.totient, ← Complex.ofReal_div,
      ← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs]
  · rfl

theorem row_on_unit (Q h k : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    realRow Q h y = row Q h k := sum_congr rfl fun q _ => real_eq_integer q h k hy

theorem paper_integral (x Q h : ℕ) :
    (∫ y in (x:ℝ)..((2*x:ℕ):ℝ), realRow Q h y) =
      ∑ k ∈ Ico x (2*x), row Q h k := by
  let a (k : ℕ) := (k:ℝ)
  have hle (k : ℕ) : a k ≤ a (k+1) := by dsimp [a]; push_cast; linarith
  have hi (k : ℕ) : IntervalIntegrable (realRow Q h) volume (a k) (a (k+1)) := by
    apply (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).2
    have hc : IntegrableOn (fun _ : ℝ => row Q h k) (Set.Ico (a k) (a (k+1))) volume :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).1 intervalIntegrable_const
    apply hc.congr_fun _ measurableSet_Ico
    intro y hy
    exact (row_on_unit Q h k hy).symm
  have he (k : ℕ) : (∫ y in a k..a (k+1), realRow Q h y) = row Q h k := by
    rw [intervalIntegral.integral_of_le (hle k), ← integral_Ico_eq_integral_Ioc]
    calc
      _ = ∫ _y in Set.Ico (a k) (a (k+1)), row Q h k := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro y hy
        exact row_on_unit Q h k hy
      _ = _ := by simp [a,Real.volume_Ico]
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico (a:=a) (m:=x) (n:=2*x)
    (by omega) (fun k _ => hi k)
  exact ht.symm.trans (sum_congr rfl fun k _ => he k)

end
end GBSkirtVariance

open Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

/-- Fixed A=18 and ε=1/16 in the upper θ range in Theorem 1.2 of
D. Koukoulopoulos, Primes in short arithmetic progressions. -/
def PaperInput : Prop := ∃ C : ℝ, 0 < C ∧ ∃ X : ℕ,
  ∀ x θ : ℝ, (X:ℝ) ≤ x → 1 ≤ x → 5/8 ≤ θ → θ ≤ 1 → ∀ Q : ℕ, 1≤Q →
    (Q:ℝ)^2*x^((1-θ)/3+1/16) ≤ x^θ →
    (∫ y in x..2*x, realRow Q (x^θ) y) ≤ C*x*x^θ/(Real.log x)^18

theorem integer_of_paper (hyp : PaperInput) : IntegerDyadicAP := by
  obtain ⟨C,hC,X,hX⟩ := hyp
  refine ⟨C,hC,max 2 X,?_⟩
  intro x h Q hx hQ hh hhn hmod
  have hx2 := (le_max_left _ _).trans hx
  have hxX := (le_max_right _ _).trans hx
  have hx1 : (1:ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hx0 := lt_trans zero_lt_one hx1
  have hxp := Real.log_pos hx1
  have hhp := (Real.rpow_pos_of_pos hx0 (5/8:ℝ)).trans_le hh
  let θ := Real.log (h:ℝ)/Real.log (x:ℝ)
  have hθl : 5/8 ≤ θ := by
    apply (le_div_iff₀ hxp).2
    have hm := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hh
    rwa [Real.log_rpow hx0] at hm
  have hθu : θ ≤ 1 := by
    apply (div_le_iff₀ hxp).2
    simpa using (Real.log_le_log hhp (by exact_mod_cast hhn) : Real.log (h:ℝ) ≤ Real.log (x:ℝ))
  have hpow : (x:ℝ)^θ = (h:ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    unfold θ
    rw [show Real.log (x:ℝ)*(Real.log (h:ℝ)/Real.log (x:ℝ)) = Real.log (h:ℝ) by field_simp,Real.exp_log hhp]
  have hm : (Q:ℝ)^2*(x:ℝ)^((1-θ)/3+1/16) ≤ (x:ℝ)^θ := by
    rw [hpow]
    apply le_trans _ hmod
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have ht := hX (x:ℝ) θ (by exact_mod_cast hxX) hx1.le hθl hθu Q hQ hm
  rw [hpow] at ht
  rw [← paper_integral]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using ht

theorem low_skirt_of_paper (h : PaperInput) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(ε*(n:ℝ)) ≤ (GoldbachLowSkirt7.lowIntegral n).re :=
  low_skirt_of_variance (variance_of_full_average (full_average_of_dyadic (integer_of_paper h)))

end
end GBSkirtVariance

theorem Conjectures.Goldbach.LowSkirtFromShortProgressions :
(let theta := fun (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) => Finset.sum ((Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k:ZMod q)=r)) (fun k => if k.Prime then Real.log (k:ℝ) else 0); let E := fun (q : ℕ) (h y : ℝ) => if hq : q=0 then (0:ℝ) else (letI : NeZero q := ⟨hq⟩; (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r => if IsUnit r then |theta q r y h - h/(q.totient:ℝ)| else 0)); ∃ C : ℝ, 0<C ∧ ∃ X : ℕ, ∀ x t : ℝ, (X:ℝ)≤x → 1≤x → 5/8≤t → t≤1 → ∀ Q : ℕ, 1≤Q → (Q:ℝ)^2*x^((1-t)/3+1/16) ≤ x^t → intervalIntegral (fun y => Finset.sum (Finset.Icc 1 Q) (fun q => E q (x^t) y)) x (2*x) MeasureTheory.volume ≤ C*x*x^t/(Real.log x)^18) → let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  intro hv
  exact GBSkirtVariance.low_skirt_of_paper hv
