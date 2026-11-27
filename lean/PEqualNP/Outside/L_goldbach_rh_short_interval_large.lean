import Mathlib

/-!
# A sum of two odd primes in a short interval under RH

With δ = (123/2) (log x)² / x, the proof compares two bounds on the
second moment of ψ((1+δ)y) − ψ(y) − δy for x/100 ≤ y ≤ x.
If there is no admissible prime sum, one of two reflected intervals is
empty of primes. Removing the contribution of proper prime powers gives
the lower bound. For the upper bound we smooth the increment, move its
Perron contour to Re s = −1/2, and control the resulting critical-line
zero sum by the Poisson kernel 4/(4+t²). All zeros carry their analytic
multiplicities. The last theorem applies the two bounds at the same δ.
-/

namespace GoldbachShortInterval

section

noncomputable def relativeWidth (x : ℝ) : ℝ := (123/2) * (Real.log x)^2 / x

/-- A bound for the logarithm at the lower endpoint, certified by a rational
lower bound for the exponential. -/
theorem log_threshold_lt : Real.log 1100000000000000000 < 42 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h : (2.7 : ℝ)^42 ≤ (Real.exp 1)^42 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

/-- The same parameter lies in the permitted range of the moment estimate
and controls the total relative length lost to higher prime powers. -/
theorem relativeWidth_bounds {x : ℝ} (hx : 1100000000000000000 ≤ x) :
    1 ≤ Real.log x ∧ 0 < relativeWidth x ∧ relativeWidth x ≤ 1/10000000000000 ∧
      relativeWidth x * Real.sqrt x ≤ 11/100000 ∧
      0 ≤ Real.log (2.0001 / relativeWidth x) ∧
      Real.log (2.0001 / relativeWidth x) ≤ Real.log x := by
  let b : ℝ := 1100000000000000000
  have hb : 0 < b := by norm_num [b]
  have hbx : b ≤ x := hx
  have hxpos := hb.trans_le hbx
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 (by linarith [Real.exp_one_lt_d9])
  let r := Real.sqrt (Real.sqrt (x/b))
  have hratio : 1 ≤ x/b := (one_le_div hb).2 hbx
  have hr : 1 ≤ r := by
    have h₁ : 1 ≤ Real.sqrt (x/b) := by simpa using Real.sqrt_le_sqrt hratio
    simpa [r] using Real.sqrt_le_sqrt h₁
  have hrp : 0 < r := by linarith
  have hrsq : r^2 = Real.sqrt (x/b) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hr4 : r^4 = x/b := by
    rw [show r^4 = (r^2)^2 by ring, hrsq, Real.sq_sqrt (div_nonneg hxpos.le hb.le)]
  have hrep : b*r^4 = x := by rw [hr4]; field_simp
  have hlogrep : Real.log x = Real.log b + 4*Real.log r := by
    calc
      _ = Real.log (b*r^4) := by rw [hrep]
      _ = _ := by rw [Real.log_mul hb.ne' (pow_ne_zero _ hrp.ne'), Real.log_pow]; norm_num
  have hlogupper : Real.log x ≤ 42*r := by
    have hb42 : Real.log b < 42 := log_threshold_lt
    linarith [Real.log_le_sub_one_of_pos hrp]
  have hsq : (Real.log x)^2 ≤ 1764*r^2 := by
    calc
      _ ≤ (42*r)^2 := pow_le_pow_left₀ (by linarith) hlogupper 2
      _ = _ := by ring
  have hδ : 0 < relativeWidth x := by
    dsimp only [relativeWidth]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith))) hxpos
  have hr2 : 1 ≤ r^2 := one_le_pow₀ hr
  have hr24 : r^2 ≤ r^4 := by nlinarith [sq_nonneg (r^2-1)]
  have hsmall : relativeWidth x ≤ 1/10000000000000 := by
    apply (div_le_iff₀ hxpos).2
    have hrep' : 1100000000000000000*r^4 = x := hrep
    linarith only [hrep', hsq, hr24, hr2]
  have hsx : Real.sqrt x = Real.sqrt b * r^2 := by
    rw [← hrep, Real.sqrt_mul hb.le, show r^4=(r^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hsb : 1000000000 ≤ Real.sqrt b := by
    apply (Real.le_sqrt (by norm_num) hb.le).2
    norm_num [b]
  have hprod : relativeWidth x * Real.sqrt x ≤ 11/100000 := by
    have hrr := Real.mul_self_sqrt hxpos.le
    have hsr := Real.sqrt_pos.mpr hxpos
    have he : relativeWidth x * Real.sqrt x = (123/2)*(Real.log x)^2/Real.sqrt x := by
      dsimp only [relativeWidth]
      field_simp [hxpos.ne', hsr.ne']
      nlinarith only [hrr]
    rw [he, div_le_iff₀ hsr, hsx]
    have h := mul_le_mul_of_nonneg_right hsb (sq_nonneg r)
    linarith
  have he : relativeWidth x*x = (123/2)*(Real.log x)^2 := by
    exact div_mul_cancel₀ _ hxpos.ne'
  refine ⟨hlog,hδ,hsmall,hprod,Real.log_nonneg ((one_le_div hδ).2 (by linarith)),?_⟩
  apply Real.log_le_log (by positivity)
  apply (div_le_iff₀ hδ).2
  rw [mul_comm x,he]
  nlinarith [sq_nonneg (Real.log x - 1)]

end

section

open Chebyshev Set

/-- A prime-free interval contributes no increment to Chebyshev's theta. -/
theorem theta_eq_of_no_interval_prime {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hempty : ¬∃ p : ℕ, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b) :
    theta b = theta a := by
  have he : Nat.primesLE ⌊b⌋₊ = Nat.primesLE ⌊a⌋₊ := by
    ext p
    rw [Nat.mem_primesLE,Nat.mem_primesLE,Nat.le_floor_iff (ha.trans hab),Nat.le_floor_iff ha]
    constructor
    · rintro ⟨hp,hprime⟩
      exact ⟨le_of_not_gt (fun h => hempty ⟨p,hprime,h,hp⟩),hprime⟩
    · exact fun ⟨hp,hprime⟩ => ⟨hp.trans hab,hprime⟩
  rw [theta_eq_sum_primesLE,theta_eq_sum_primesLE,he]

/-- Choosing a prime in each of the two reflected intervals would give an odd-prime
pair with its sum in the target interval. -/
theorem reflected_intervals_no_prime {x h δ y : ℝ} (hx : 2 ≤ x/100) (hlen : δ*x ≤ h)
    (hy : y ∈ Icc (x/100) (x/2))
    (hno : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
       x < ((p+q : ℕ) : ℝ) ∧ ((p+q : ℕ) : ℝ) ≤ x+h) :
    (¬∃ p : ℕ, p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ (1+δ)*y) ∨
    (¬∃ q : ℕ, q.Prime ∧ x-y < (q : ℝ) ∧ (q : ℝ) ≤ (1+δ)*(x-y)) := by
  by_cases h₁ : ∃ p : ℕ, p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ (1+δ)*y
  · right
    obtain ⟨p,hp,hpy,hpδ⟩ := h₁
    rintro ⟨q,hq,hqy,hqδ⟩
    have hp2 : 2 < (p : ℝ) := by linarith [hy.1]
    have hq2 : 2 < (q : ℝ) := by linarith [hy.1,hy.2]
    refine hno ⟨p,q,hp,hq,hp.odd_of_ne_two ?_,hq.odd_of_ne_two ?_,?_,?_⟩
    · exact ne_of_gt (by exact_mod_cast hp2)
    · exact ne_of_gt (by exact_mod_cast hq2)
    · rw [Nat.cast_add]
      linarith
    · rw [Nat.cast_add]
      linarith only [add_le_add hpδ hqδ,hlen]
  · exact .inl h₁

/-- If the target interval contains no sum of odd primes, one of the two
centered theta increments equals minus its expected width. -/
theorem reflected_theta_sq_lower {x h δ y : ℝ} (hx : 2 ≤ x/100)
    (hδ : 0 ≤ δ) (hlen : δ*x ≤ h) (hy : y ∈ Icc (x/100) (x/2))
    (hno : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
       x < ((p+q : ℕ) : ℝ) ∧ ((p+q : ℕ) : ℝ) ≤ x+h) :
    δ^2*y^2 ≤ (theta ((1+δ)*y) - theta y - δ*y)^2 +
      (theta ((1+δ)*(x-y)) - theta (x-y) - δ*(x-y))^2 := by
  have hy₀ : 0 ≤ y := by linarith [hy.1]
  have hxy : y ≤ x-y := by linarith [hy.2]
  have hy' := hy₀.trans hxy
  have hgrow (t : ℝ) (ht : 0 ≤ t) : t ≤ (1+δ)*t := by
    linarith [mul_nonneg hδ ht]
  rcases reflected_intervals_no_prime hx hlen hy hno with hempty | hempty
  · rw [theta_eq_of_no_interval_prime hy₀ (hgrow _ hy₀) hempty]
    simp only [sub_self,zero_sub,neg_sq,mul_pow]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [theta_eq_of_no_interval_prime hy' (hgrow _ hy') hempty]
    simp only [sub_self,zero_sub,neg_sq,mul_pow]
    calc
      δ^2*y^2 ≤ δ^2*(x-y)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy₀ hxy 2) (sq_nonneg _)
      _ ≤ _ := le_add_of_nonneg_left (sq_nonneg _)

end

section

open MeasureTheory

/-- Integrating the reflected pair on the half-interval changes its second
term into the integral on the other half. Extending to the cutoff `x`
can only increase the integral of the square. -/
theorem reflected_second_moment_lower (e : ℝ → ℝ) (x δ : ℝ) (hx : 0 ≤ x)
    (hint : IntervalIntegrable (fun y => (e y)^2) volume (x/100) x)
    (hpair : ∀ y ∈ Set.Icc (x/100) (x/2), δ^2*y^2 ≤ (e y)^2 + (e (x-y))^2) :
    δ^2*x^3/3 * (1/8 - (1/100 : ℝ)^3) ≤ ∫ y in x/100..x, (e y)^2 := by
  let f (y : ℝ) := (e y)^2
  have hab : x/100 ≤ x/2 := by linarith
  have hbc : x/2 ≤ x-x/100 := by linarith
  have hcx : x-x/100 ≤ x := by linarith
  have hrestrict {a b : ℝ} (ha : x/100 ≤ a) (hab' : a ≤ b) (hb : b ≤ x) :
      IntervalIntegrable f volume a b := by
    apply hint.mono_set
    rw [Set.uIcc_of_le hab', Set.uIcc_of_le (by linarith : x/100 ≤ x)]
    exact Set.Icc_subset_Icc ha hb
  have hleft := hrestrict le_rfl hab (by linarith)
  have hright := hrestrict hab hbc hcx
  have href : IntervalIntegrable (fun y => f (x-y)) volume (x/100) (x/2) := by
    have h := hright.symm.comp_sub_left x
    rwa [sub_sub_cancel, show x - x/2 = x/2 by ring] at h
  have hpoly : IntervalIntegrable (fun y : ℝ => δ^2*y^2) volume (x/100) (x/2) :=
    (by fun_prop : Continuous (fun y : ℝ => δ^2*y^2)).intervalIntegrable _ _
  calc
    _ = ∫ y in x/100..x/2, δ^2*y^2 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    _ ≤ ∫ y in x/100..x/2, f y + f (x-y) :=
      intervalIntegral.integral_mono_on hab hpoly (hleft.add href) hpair
    _ = (∫ y in x/100..x/2, f y) + ∫ y in x/2..(x-x/100), f y := by
      rw [intervalIntegral.integral_add hleft href, intervalIntegral.integral_comp_sub_left f x,
        show x - x/2 = x/2 by ring]
    _ = ∫ y in x/100..(x-x/100), f y :=
      intervalIntegral.integral_add_adjacent_intervals hleft hright
    _ ≤ _ := intervalIntegral.integral_mono_interval le_rfl (hab.trans hbc) hcx
      (Filter.Eventually.of_forall fun y => sq_nonneg (e y)) hint

end

section

open Finset

/-- Proper prime powers below a real cutoff. -/
noncomputable def properPrimePowersLE (x : ℝ) : Finset ℕ := by
  classical
  exact (range (⌊x⌋₊ + 1)).filter (fun n => IsPrimePow n ∧ ¬n.Prime)

theorem mem_properPrimePowersLE {x : ℝ} (hx : 0 ≤ x) {n : ℕ} :
    n ∈ properPrimePowersLE x ↔ (n : ℝ) ≤ x ∧ IsPrimePow n ∧ ¬n.Prime := by
  classical
  simp only [properPrimePowersLE, mem_filter, mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hx]

/-- Group the exponents as `2j+2` and `2j+3`. For each exponent in that
pair the base is bounded by `√x / 2^j`, giving a convergent geometric sum. -/
theorem card_properPrimePowersLE {x : ℝ} (hx : 0 ≤ x) :
    ((properPrimePowersLE x).card : ℝ) ≤ 4 * Real.sqrt x := by
  classical
  let indices := range (⌊x⌋₊ + 1)
  let pairs (j : ℕ) := (Icc 1 ⌊Real.sqrt x / (2:ℝ)^j⌋₊) ×ˢ range 2
  let block (j : ℕ) := (pairs j).image (fun a : ℕ × ℕ => a.1 ^ (2*j+2+a.2))
  have hsub : properPrimePowersLE x ⊆ indices.biUnion block := by
    intro n hn
    obtain ⟨hnx, ⟨p,k,hp,hk,rfl⟩, hnprime⟩ := (mem_properPrimePowersLE hx).mp hn
    have hp' : p.Prime := hp.nat_prime
    have hk2 : 2 ≤ k := by
      by_contra! hh
      have hk1 : k = 1 := by omega
      exact hnprime (by simpa [hk1] using hp')
    let j := (k-2)/2
    let b := (k-2)%2
    have hkb : 2*j+2+b = k := by dsimp [j,b]; omega
    have hj : j ∈ indices := by
      apply mem_range.mpr
      have hjk : j ≤ k := by dsimp [j]; omega
      exact Nat.lt_succ_of_le ((hjk.trans (Nat.lt_pow_self hp'.one_lt).le).trans (Nat.le_floor hnx))
    have hj2 : (2:ℕ)^j ≤ p^j := Nat.pow_le_pow_left hp'.two_le _
    have hsq : (p*2^j)^2 ≤ p^k := calc
      (p*2^j)^2 ≤ (p*p^j)^2 := by gcongr
      _ = p^(2*j+2) := by rw [← pow_succ', ← pow_mul]; congr 1; omega
      _ ≤ p^k := Nat.pow_le_pow_right hp'.pos (by omega)
    have hsq' : ((p:ℝ) * (2:ℝ)^j)^2 ≤ x := by
      apply le_trans _ hnx
      exact_mod_cast hsq
    have hbase : (p:ℝ) ≤ Real.sqrt x / 2^j :=
      (le_div_iff₀ (by positivity)).mpr (Real.le_sqrt_of_sq_le hsq')
    apply mem_biUnion.mpr
    refine ⟨j, hj, mem_image.mpr ⟨(p,b), ?_, ?_⟩⟩
    · exact mem_product.mpr ⟨mem_Icc.mpr ⟨hp'.one_le, Nat.le_floor hbase⟩,
        mem_range.mpr (Nat.mod_lt _ (by norm_num))⟩
    · simp only [hkb]
  have hb (j : ℕ) : ((block j).card : ℝ) ≤ 2 * Real.sqrt x * (1/2 : ℝ)^j := by
    have hcard : (block j).card ≤ (pairs j).card := card_image_le
    have he : (pairs j).card = ⌊Real.sqrt x / (2:ℝ)^j⌋₊ * 2 := by simp [pairs]
    rw [he] at hcard
    calc
      _ ≤ (⌊Real.sqrt x / (2:ℝ)^j⌋₊ : ℝ) * 2 := by exact_mod_cast hcard
      _ ≤ (Real.sqrt x / (2:ℝ)^j) * 2 :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by norm_num)
      _ = _ := by rw [one_div, inv_pow]; ring
  have hgeom : ∑ j ∈ indices, (1/2 : ℝ)^j ≤ 2 := by
    have h := geom_sum_mul_neg (1/2 : ℝ) (⌊x⌋₊ + 1)
    change ∑ j ∈ range (⌊x⌋₊ + 1), (1/2 : ℝ)^j ≤ 2
    linarith [show 0 ≤ (1/2 : ℝ)^(⌊x⌋₊ + 1) by positivity]
  calc
    _ ≤ ((∑ j ∈ indices, (block j).card : ℕ) : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (card_biUnion_le (s:=indices) (t:=block))
    _ = ∑ j ∈ indices, ((block j).card : ℝ) := by simp
    _ ≤ ∑ j ∈ indices, 2 * Real.sqrt x * (1/2 : ℝ)^j := sum_le_sum fun j _ => hb j
    _ = (2 * Real.sqrt x) * (∑ j ∈ indices, (1/2 : ℝ)^j) := (mul_sum ..).symm
    _ ≤ (2 * Real.sqrt x) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- A single exceptional set controls every short interval below `2*x`. -/
theorem card_properPrimePowersLE_two_mul {x : ℝ} (hx : 0 ≤ x) :
    ((properPrimePowersLE (2*x)).card : ℝ) ≤ 6 * Real.sqrt x := by
  apply (card_properPrimePowersLE (mul_nonneg (by norm_num) hx)).trans
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have h : Real.sqrt 2 ≤ 3/2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  linarith only [mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg x)]

end

section

open Chebyshev MeasureTheory Set

/-- The exceptional values of the lower endpoint caused by the chosen integers,
including their reflections in the sum parameter. -/
noncomputable def primePowerCover (S : Finset ℕ) (x δ : ℝ) : Set ℝ :=
  ⋃ n ∈ S, Icc ((n : ℝ)/(1+δ)) n ∪ Icc (x-n) (x-(n : ℝ)/(1+δ))

theorem primePowerCover_isCompact (S : Finset ℕ) (x δ : ℝ) :
    IsCompact (primePowerCover S x δ) :=
  S.isCompact_biUnion fun _ _ => isCompact_Icc.union isCompact_Icc

/-- Each interval has length at most δx whenever the integer it covers is
at most (1+δ)x. Taking both reflections costs a factor of two. -/
theorem primePowerCover_volume_le (S : Finset ℕ) {x δ : ℝ}
    (hδ : 0 ≤ δ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (1+δ)*x) :
    volume.real (primePowerCover S x δ) ≤ 2*δ*x*(S.card : ℝ) := by
  let A (n : ℕ) := Icc ((n : ℝ)/(1+δ)) n
  let B (n : ℕ) := Icc (x-n) (x-(n : ℝ)/(1+δ))
  have hd : 0 < 1+δ := by linarith
  calc
    _ ≤ ∑ n ∈ S, volume.real (A n ∪ B n) :=
      measureReal_biUnion_finset_le S (fun n => A n ∪ B n)
    _ ≤ ∑ _n ∈ S, 2*δ*x := by
      apply Finset.sum_le_sum
      intro n hn
      have hlow : (n : ℝ)/(1+δ) ≤ n := div_le_self (Nat.cast_nonneg _) (by linarith)
      have ht : (n : ℝ)/(1+δ) ≤ x := (div_le_iff₀ hd).2 (by simpa [mul_comm] using hS n hn)
      have he : (n : ℝ) - n/(1+δ) = δ*(n/(1+δ)) := by field_simp; ring
      have hl := mul_le_mul_of_nonneg_left ht hδ
      apply (measureReal_union_le (A n) (B n)).trans
      rw [show A n = _ from rfl, Real.volume_real_Icc_of_le hlow,
        show B n = _ from rfl, Real.volume_real_Icc_of_le (by linarith)]
      linarith
    _ = _ := by simp [mul_comm]

theorem proper_power_cover_volume_le {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    let S := properPrimePowersLE ((1+δ)*x)
    volume.real (primePowerCover S x δ) ≤ 2*δ*x*(S.card : ℝ) := by
  intro S
  apply primePowerCover_volume_le S hδ
  exact fun n hn => ((mem_properPrimePowersLE (mul_nonneg (by linarith) hx)).1 hn).1

/-- The von Mangoldt sum is constant on an interval containing no prime powers. -/
theorem psi_eq_of_no_interval_prime_power {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hempty : ¬∃ n : ℕ, IsPrimePow n ∧ a < (n : ℝ) ∧ (n : ℝ) ≤ b) :
    psi b = psi a := by
  rw [psi_eq_sum_Icc,psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc (by rfl) (Nat.floor_mono hab))
  intro n hnb hna
  have hna' : ¬n ≤ ⌊a⌋₊ := by
    intro h
    exact hna (Finset.mem_Icc.mpr ⟨Nat.zero_le _,h⟩)
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr fun hp =>
    hempty ⟨n,hp,lt_of_not_ge (fun h => hna' ((Nat.le_floor_iff ha).2 h)),
      (Nat.le_floor_iff (ha.trans hab)).1 (Finset.mem_Icc.mp hnb).2⟩

/-- Outside the explicit cover, a prime power in either of the two short
intervals is itself prime. Consequently the reflected squared ψ errors have
the same pointwise lower bound as the θ errors. -/
theorem reflected_psi_sq_lower_off_cover {x h δ y : ℝ} (hx : 2 ≤ x/100)
    (hδ : 0 ≤ δ) (hlen : δ*x ≤ h) (hy : y ∈ Icc (x/100) (x/2))
    (hgood : y ∉ primePowerCover (properPrimePowersLE ((1+δ)*x)) x δ)
    (hno : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
       x < ((p+q : ℕ) : ℝ) ∧ ((p+q : ℕ) : ℝ) ≤ x+h) :
    δ^2*y^2 ≤ (psi ((1+δ)*y) - psi y - δ*y)^2 +
      (psi ((1+δ)*(x-y)) - psi (x-y) - δ*(x-y))^2 := by
  have hx₀ : 0 ≤ x := by linarith
  have hy₀ : 0 ≤ y := by linarith [hy.1]
  have hxy : y ≤ x-y := by linarith [hy.2]
  have hy' := hy₀.trans hxy
  have hd : 0 < 1+δ := by linarith
  have hgrow (t : ℝ) (ht : 0 ≤ t) : t ≤ (1+δ)*t := by linarith [mul_nonneg hδ ht]
  have extract {t : ℝ} (ht : t = y ∨ t = x-y) {n : ℕ}
      (hp : IsPrimePow n) (hl : t < (n : ℝ)) (hu : (n : ℝ) ≤ (1+δ)*t) : n.Prime := by
    by_contra hn
    have htx : t ≤ x := by rcases ht with rfl | rfl <;> linarith
    have hbound := hu.trans (mul_le_mul_of_nonneg_left htx hd.le)
    have hmem := (mem_properPrimePowersLE (mul_nonneg hd.le hx₀)).2 ⟨hbound,hp,hn⟩
    have hbase : (n : ℝ)/(1+δ) ≤ t := (div_le_iff₀ hd).2 (by rwa [mul_comm])
    apply hgood
    apply mem_iUnion.mpr
    refine ⟨n,mem_iUnion.mpr ⟨hmem,?_⟩⟩
    rcases ht with rfl | rfl
    · exact .inl ⟨hbase,hl.le⟩
    · exact .inr ⟨by linarith,by linarith⟩
  rcases reflected_intervals_no_prime hx hlen hy hno with h | h
  · have he := psi_eq_of_no_interval_prime_power hy₀ (hgrow _ hy₀) (by
      rintro ⟨n,hp,hl,hu⟩
      exact h ⟨n,extract (.inl rfl) hp hl hu,hl,hu⟩)
    rw [he]
    simp only [sub_self,zero_sub,neg_sq,mul_pow]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have he := psi_eq_of_no_interval_prime_power hy' (hgrow _ hy') (by
      rintro ⟨n,hp,hl,hu⟩
      exact h ⟨n,extract (.inr rfl) hp hl hu,hl,hu⟩)
    rw [he]
    simp only [sub_self,zero_sub,neg_sq,mul_pow]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy₀ hxy 2) (sq_nonneg δ)).trans
      (le_add_of_nonneg_left (sq_nonneg _))

end

section

open MeasureTheory Set Filter

/-- The reflected lower bound loses at most the measure of the exceptional
set times the largest possible lower-bound integrand on the half-interval. -/
theorem reflected_second_moment_lower_off_set (e : ℝ → ℝ) (x δ : ℝ) (hx : 0 ≤ x)
    (B : Set ℝ) (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤)
    (hint : IntervalIntegrable (fun y => (e y)^2) volume (x/100) x)
    (hpair : ∀ y ∈ Icc (x/100) (x/2), y ∉ B →
      δ^2*y^2 ≤ (e y)^2 + (e (x-y))^2) :
    δ^2*x^3/3 * (1/8 - (1/100 : ℝ)^3) - δ^2*(x/2)^2*volume.real B ≤
      ∫ y in x/100..x, (e y)^2 := by
  classical
  let f (y : ℝ) := (e y)^2
  let A := δ^2*(x/2)^2
  let penalty := B.indicator (fun _ => A)
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hp : Integrable penalty volume := (integrable_indicator_iff hB).mpr (integrableOn_const hBfin)
  have hp0 : ∀ y, 0 ≤ penalty y := fun y => indicator_nonneg (fun _ _ => hA) y
  have hab : x/100 ≤ x/2 := by linarith
  have hbc : x/2 ≤ x-x/100 := by linarith
  have hcx : x-x/100 ≤ x := by linarith
  have hrestrict {a b : ℝ} (ha : x/100 ≤ a) (hab' : a ≤ b) (hb : b ≤ x) :
      IntervalIntegrable f volume a b := by
    apply hint.mono_set
    rw [Set.uIcc_of_le hab', Set.uIcc_of_le (by linarith : x/100 ≤ x)]
    exact Icc_subset_Icc ha hb
  have hleft := hrestrict le_rfl hab (by linarith)
  have hright := hrestrict hab hbc hcx
  have href : IntervalIntegrable (fun y => f (x-y)) volume (x/100) (x/2) := by
    have h := hright.symm.comp_sub_left x
    rwa [sub_sub_cancel, show x - x/2 = x/2 by ring] at h
  have hpoly : IntervalIntegrable (fun y : ℝ => δ^2*y^2) volume (x/100) (x/2) :=
    (by fun_prop : Continuous (fun y : ℝ => δ^2*y^2)).intervalIntegrable _ _
  have hpt (y : ℝ) (hy : y ∈ Icc (x/100) (x/2)) :
      δ^2*y^2 ≤ (f y + f (x-y)) + penalty y := by
    by_cases h : y ∈ B
    · rw [show penalty y = A from indicator_of_mem h _]
      calc _ ≤ A := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hy.1]) hy.2 2) (sq_nonneg _)
           _ ≤ _ := le_add_of_nonneg_left (add_nonneg (sq_nonneg _) (sq_nonneg _))
    · simpa only [penalty, indicator_of_notMem h, add_zero, f] using hpair y hy h
  have hpen : (∫ y in x/100..x/2, penalty y) ≤ A*volume.real B := by
    rw [intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ y, penalty y := setIntegral_le_integral hp (Eventually.of_forall hp0)
      _ = _ := by rw [show penalty = _ from rfl, integral_indicator hB, setIntegral_const, smul_eq_mul, mul_comm]
  apply sub_le_iff_le_add.mpr
  calc
    _ = ∫ y in x/100..x/2, δ^2*y^2 := by rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring
    _ ≤ ∫ y in x/100..x/2, (f y + f (x-y)) + penalty y :=
      intervalIntegral.integral_mono_on hab hpoly ((hleft.add href).add hp.intervalIntegrable) hpt
    _ = (∫ y in x/100..(x-x/100), f y) + ∫ y in x/100..x/2, penalty y := by
      rw [intervalIntegral.integral_add (hleft.add href) hp.intervalIntegrable,
        intervalIntegral.integral_add hleft href, intervalIntegral.integral_comp_sub_left f x,
        show x - x/2 = x/2 by ring, intervalIntegral.integral_add_adjacent_intervals hleft hright]
    _ ≤ _ := add_le_add (intervalIntegral.integral_mono_interval le_rfl (hab.trans hbc) hcx
      (Eventually.of_forall fun y => sq_nonneg (e y)) hint) hpen

/-- Squared increments of any nonnegative monotone counting function are
integrable on finite intervals, for every real value of the increment parameter. -/
theorem counting_increment_sq_intervalIntegrable (F : ℝ → ℝ) (hF : Monotone F)
    (hF0 : ∀ y, 0 ≤ F y) (δ a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => (F ((1+δ)*y) - F y - δ*y)^2) volume a b := by
  let R := max |a| |b|
  let C := F (|1+δ| * R) + F R + |δ| * R
  have hR₁ : |a| ≤ R := le_max_left _ _
  have hR₂ : |b| ≤ R := le_max_right _ _
  have hmeas : Measurable (fun y : ℝ => (F ((1+δ)*y) - F y - δ*y)^2) :=
    (((hF.measurable.comp (measurable_const.mul measurable_id)).sub hF.measurable).sub
      (measurable_const.mul measurable_id)).pow_const _
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (M := C^2) measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_uIoc] with y hy
  have hyR : |y| ≤ R := by
    rcases mem_uIcc.mp (uIoc_subset_uIcc hy) with hy | hy <;> apply abs_le.mpr <;>
      constructor <;> linarith [neg_abs_le a, neg_abs_le b, le_abs_self a, le_abs_self b]
  have hf₁ : F ((1+δ)*y) ≤ F (|1+δ| * R) := hF (calc
    _ ≤ |(1+δ)*y| := le_abs_self _
    _ = |1+δ| * |y| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hyR (abs_nonneg _))
  have hf₂ : F y ≤ F R := hF ((le_abs_self y).trans hyR)
  have hval : |F ((1+δ)*y) - F y - δ*y| ≤ C := by
    apply (abs_sub ..).trans
    calc
      _ ≤ (|F ((1+δ)*y)| + |F y|) + |δ*y| := by linarith only [abs_sub (F ((1+δ)*y)) (F y)]
      _ ≤ C := by
        rw [abs_of_nonneg (hF0 _), abs_of_nonneg (hF0 _), abs_mul]
        exact add_le_add (add_le_add hf₁ hf₂) (mul_le_mul_of_nonneg_left hyR (abs_nonneg _))
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hval 2

theorem psi_increment_sq_intervalIntegrable (δ a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => (Chebyshev.psi ((1+δ)*y) - Chebyshev.psi y - δ*y)^2)
      volume a b :=
  counting_increment_sq_intervalIntegrable _ Chebyshev.psi_mono Chebyshev.psi_nonneg δ a b

theorem theta_increment_sq_intervalIntegrable (δ a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => (Chebyshev.theta ((1+δ)*y) - Chebyshev.theta y - δ*y)^2)
      volume a b :=
  counting_increment_sq_intervalIntegrable _ Chebyshev.theta_mono Chebyshev.theta_nonneg δ a b

end

section

open MeasureTheory Set Chebyshev

noncomputable def secondMoment (F : ℝ → ℝ) (x δ : ℝ) : ℝ :=
  ∫ y in (1:ℝ)..x, (F ((1+δ)*y) - F y - δ*y)^2

def primeSumInWindow (x : ℝ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
    x < ((p+q : ℕ) : ℝ) ∧ ((p+q : ℕ) : ℝ) ≤ x + 123 * (Real.log x)^2

private theorem enlarge_moment (F : ℝ → ℝ) {x δ : ℝ} (hx : 100 ≤ x)
    (hint : IntervalIntegrable (fun y => (F ((1+δ)*y)-F y-δ*y)^2) volume 1 x) :
    (∫ y in x/100..x, (F ((1+δ)*y)-F y-δ*y)^2) ≤ secondMoment F x δ :=
  intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint

private theorem relativeWidth_mul {x : ℝ} (hx : 0 < x) :
    relativeWidth x * x = (123/2) * (Real.log x)^2 := div_mul_cancel₀ _ hx.ne'

private theorem reflected_scale {x c K : ℝ} (hx : 0 < x) (hd : 0 < relativeWidth x)
    (hl : 1 ≤ Real.log x) (hc : K < c * (123/2)) :
    K * relativeWidth x * x^2 * (Real.log x)^2 < c * (relativeWidth x)^2 * x^3 := by
  let d := relativeWidth x
  have hscale := relativeWidth_mul hx
  calc
    _ = K * (d*x^2*(Real.log x)^2) := by ring
    _ < (c*(123/2)) * (d*x^2*(Real.log x)^2) :=
      mul_lt_mul_of_pos_right hc (by positivity [show 0 < d from hd,show 0 < Real.log x by linarith])
    _ = c*d^2*x^3 := by
      change d*x = (123/2)*(Real.log x)^2 at hscale
      linear_combination -(c*d*x^2)*hscale

/-- A theta mean square at the single width used for this cutoff suffices. -/
theorem primeSum_of_theta_moment {x : ℝ} (hx : 1100000000000000000 ≤ x)
    (hupper : secondMoment theta x (relativeWidth x) ≤
      2.56 * relativeWidth x * x^2 * (Real.log x)^2) : primeSumInWindow x := by
  by_contra hnone
  let d := relativeWidth x
  let e := fun y => theta ((1+d)*y)-theta y-d*y
  obtain ⟨hl,hd,_,_,_,_⟩ := relativeWidth_bounds hx
  have hxr : 0 < x := by linarith
  have hr := relativeWidth_mul hxr
  have hlen : d*x ≤ 123*(Real.log x)^2 := by dsimp [d]; linarith [sq_nonneg (Real.log x)]
  have h := reflected_second_moment_lower e x d hxr.le
    (theta_increment_sq_intervalIntegrable _ _ _) (fun _ hy =>
      reflected_theta_sq_lower (by linarith : 2 ≤ x/100) hd.le hlen hy hnone)
  have hbig := (h.trans (enlarge_moment theta (by linarith) (theta_increment_sq_intervalIntegrable _ _ _))).trans hupper
  have hlt := reflected_scale (c := (1/8-(1/100 : ℝ)^3)/3) (K := 2.56)
    hxr hd hl (by norm_num)
  dsimp only [d] at hbig
  linarith

/-- The prime-power cover occupies at most 0.00132 of the length x at
the chosen width, uniformly above the frozen cutoff. -/
theorem cover_relative_length {x : ℝ} (hx : 1100000000000000000 ≤ x) :
    let d := relativeWidth x
    volume.real (primePowerCover (properPrimePowersLE ((1+d)*x)) x d) ≤ 0.00132*x := by
  let d := relativeWidth x
  let S := properPrimePowersLE ((1+d)*x)
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨_,hd,hsmall,hroot,_,_⟩ := relativeWidth_bounds hx
  have hy : 0 ≤ (1+d)*x := mul_nonneg (by dsimp [d]; linarith) hx0
  have hmono : (1+d)*x ≤ 2*x := mul_le_mul_of_nonneg_right (by dsimp [d]; linarith) hx0
  have hsub : S ⊆ properPrimePowersLE (2*x) := by
    intro n hn
    obtain ⟨h,hnp,hnprime⟩ := (mem_properPrimePowersLE hy).1 hn
    exact (mem_properPrimePowersLE (by linarith)).2 ⟨h.trans hmono,hnp,hnprime⟩
  have hcard : (S.card : ℝ) ≤ 6*Real.sqrt x :=
    (show (S.card : ℝ) ≤ (properPrimePowersLE (2*x)).card by exact_mod_cast Finset.card_le_card hsub).trans
      (card_properPrimePowersLE_two_mul hx0)
  have hfactor : 0 ≤ 2*d*x := by positivity [show 0 < d from hd]
  calc
    _ ≤ 2*d*x*(S.card : ℝ) := proper_power_cover_volume_le hx0 hd.le
    _ ≤ 2*d*x*(6*Real.sqrt x) := mul_le_mul_of_nonneg_left hcard hfactor
    _ = 12*(d*Real.sqrt x)*x := by ring
    _ ≤ 12*(11/100000)*x := by gcongr
    _ = _ := by ring

/-- Sufficient condition directly in terms of the von Mangoldt function.
Prime powers of exponent at least two have already been accounted for. -/
theorem primeSum_of_local_psi_moment {x : ℝ} (hx : 1100000000000000000 ≤ x)
    (hupper : (∫ y in x/100..x, (psi ((1+relativeWidth x)*y)-psi y-relativeWidth x*y)^2) ≤
      2.54 * relativeWidth x * x^2 * (Real.log x)^2) : primeSumInWindow x := by
  by_contra hnone
  let d := relativeWidth x
  let e := fun y => psi ((1+d)*y)-psi y-d*y
  let B := primePowerCover (properPrimePowersLE ((1+d)*x)) x d
  obtain ⟨hl,hd,_,_,_,_⟩ := relativeWidth_bounds hx
  have hxr : 0 < x := by linarith
  have hr := relativeWidth_mul hxr
  have hlen : d*x ≤ 123*(Real.log x)^2 := by dsimp [d]; linarith [sq_nonneg (Real.log x)]
  have hc : IsCompact B := primePowerCover_isCompact _ _ _
  have h := reflected_second_moment_lower_off_set e x d hxr.le B
    hc.measurableSet hc.measure_lt_top.ne (psi_increment_sq_intervalIntegrable _ _ _)
    (fun _ hy hz => reflected_psi_sq_lower_off_cover (by linarith : 2 ≤ x/100) hd.le hlen hy hz hnone)
  have hbig := h.trans hupper
  have hvol : volume.real B ≤ 0.00132*x := cover_relative_length hx
  have hcvol := mul_le_mul_of_nonneg_left hvol (show 0 ≤ d^2*(x/2)^2 by positivity)
  have hlt := reflected_scale (c := (1/8-(1/100 : ℝ)^3)/3-0.00132/4)
    (K := 2.54) hxr hd hl (by norm_num)
  change 2.54*d*x^2*(Real.log x)^2 < _ * d^2*x^3 at hlt
  linarith

theorem primeSum_of_psi_moment {x : ℝ} (hx : 1100000000000000000 ≤ x)
    (hupper : secondMoment psi x (relativeWidth x) ≤
      2.54 * relativeWidth x * x^2 * (Real.log x)^2) : primeSumInWindow x :=
  primeSum_of_local_psi_moment hx
    ((enlarge_moment psi (by linarith) (psi_increment_sq_intervalIntegrable _ _ _)).trans hupper)

/-- Transfer the explicit Riemann-hypothesis mean-square estimate for psi
to the short interval statement. -/
theorem shortInterval_of_explicit_mean_square
    (hmean : RiemannHypothesis → ∀ x δ : ℝ, 10000000000000 ≤ x → 0 < δ →
      δ ≤ 1/10000000000000 → secondMoment psi x δ ≤
        2.2258*δ*(Real.log (2.0001/δ))^2*x^2) :
    RiemannHypothesis → ∀ x : ℝ, 1100000000000000000 ≤ x → primeSumInWindow x := by
  intro hrh x hx
  obtain ⟨_,hd,hsmall,_,hn,hlog⟩ := relativeWidth_bounds hx
  have hlog2 := pow_le_pow_left₀ hn hlog 2
  apply primeSum_of_psi_moment hx
  calc
    _ ≤ _ := hmean hrh x _ (by linarith) hd hsmall
    _ ≤ 2.54 * relativeWidth x * (Real.log x)^2 * x^2 := by gcongr; norm_num
    _ = _ := by ring

end

section

open scoped BigOperators

/-- Weight of a zero in the difference of the explicit formula at `x` and
`(1+δ)x`, after the common factor `x^ρ` has been removed. -/
noncomputable def zeroIncrementWeight (δ : ℝ) (ρ : ℂ) : ℂ :=
  ((((1+δ : ℝ) : ℂ)^ρ) - 1) / ρ

theorem zeroIncrementWeight_norm_le_delta {δ : ℝ} (hδ : 0 ≤ δ) {ρ : ℂ} (hρ : ρ.re = 1/2) :
    ‖zeroIncrementWeight δ ρ‖ ≤ δ := by
  have h := integral_cpow (a := 1) (b := 1+δ) (r := ρ-1) (Or.inl (by
    rw [Complex.sub_re, Complex.one_re, hρ]
    norm_num))
  have hw : zeroIncrementWeight δ ρ = ∫ y : ℝ in (1:ℝ)..1+δ, (y:ℂ)^(ρ-1) := by
    rw [h, sub_add_cancel]
    simp only [zeroIncrementWeight, Complex.ofReal_one, Complex.one_cpow]
  rw [hw]
  calc
    _ ≤ 1 * |(1+δ)-1| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      rw [Set.uIoc_of_le (by linarith : 1 ≤ 1+δ)] at hy
      have hy1 : 1 ≤ y := hy.1.le
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < y), Complex.sub_re, Complex.one_re, hρ]
      exact Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
    _ = δ := by rw [add_sub_cancel_left, abs_of_nonneg hδ, one_mul]

theorem zeroIncrementWeight_norm_le_height {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ (10:ℝ)^(-13:ℤ)) {ρ : ℂ} (hρ : ρ.re = 1/2) (him : ρ.im ≠ 0) :
    ‖zeroIncrementWeight δ ρ‖ ≤ 2.0001 / |ρ.im| := by
  have hsq : Real.sqrt (1+δ) ≤ 1.0001 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · norm_num at hsmall ⊢
      linarith
  have hbase : 0 < 1+δ := by linarith
  have hnum : ‖(((1+δ : ℝ) : ℂ)^ρ) - 1‖ ≤ 2.0001 := by
    have hb := norm_sub_le (((1+δ : ℝ) : ℂ)^ρ) (1:ℂ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase, hρ, ← Real.sqrt_eq_rpow, norm_one] at hb
    linarith
  rw [zeroIncrementWeight, norm_div]
  exact div_le_div₀ (by norm_num) hnum (abs_pos.mpr him) (Complex.abs_im_le_norm ρ)

/-- The norm bound at every height, including ordinate zero. -/
noncomputable def zeroIncrementMajorant (δ t : ℝ) : ℝ :=
  if t = 0 then δ else min δ (2.0001 / |t|)

theorem zeroIncrementWeight_norm_le {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ (10:ℝ)^(-13:ℤ)) {ρ : ℂ} (hρ : ρ.re = 1/2) :
    ‖zeroIncrementWeight δ ρ‖ ≤ zeroIncrementMajorant δ ρ.im := by
  by_cases h : ρ.im = 0
  · simpa only [zeroIncrementMajorant, ite_eq_left h] using zeroIncrementWeight_norm_le_delta hδ hρ
  · simpa only [zeroIncrementMajorant, ite_eq_right h, le_min_iff] using
      And.intro (zeroIncrementWeight_norm_le_delta hδ hρ) (zeroIncrementWeight_norm_le_height hδ hsmall hρ h)

/-- A finite quadratic form with the actual zero weights is bounded by the
corresponding double sum of the entrywise absolute majorants. The index
type allows repeated ordinates and repeated zeros. -/
theorem zero_weight_quadratic_form_le {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (K : ι → ι → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ (10:ℝ)^(-13:ℤ)) (hr : ∀ i ∈ S, (ρ i).re = 1/2) :
    ‖∑ i ∈ S, ∑ j ∈ S, zeroIncrementWeight δ (ρ i) * star (zeroIncrementWeight δ (ρ j)) * K i j‖ ≤
      ∑ i ∈ S, ∑ j ∈ S, zeroIncrementMajorant δ (ρ i).im * zeroIncrementMajorant δ (ρ j).im * ‖K i j‖ := by
  apply norm_sum_le_of_le
  intro i hi
  apply norm_sum_le_of_le
  intro j hj
  simp only [norm_mul, norm_star]
  have hwi := zeroIncrementWeight_norm_le hδ hsmall (hr i hi)
  have hwj := zeroIncrementWeight_norm_le hδ hsmall (hr j hj)
  exact mul_le_mul_of_nonneg_right (mul_le_mul hwi hwj (norm_nonneg _) ((norm_nonneg _).trans hwi)) (norm_nonneg _)

/-- For a symmetric matrix of kernel norms only squared individual weights
and row sums are required. -/
theorem zero_weight_quadratic_form_le_rows {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    (K : ι → ι → ℂ) (hsym : ∀ i ∈ S, ∀ j ∈ S, ‖K i j‖ = ‖K j i‖)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ (10:ℝ)^(-13:ℤ)) (hr : ∀ i ∈ S, (ρ i).re = 1/2) :
    ‖∑ i ∈ S, ∑ j ∈ S, zeroIncrementWeight δ (ρ i) * star (zeroIncrementWeight δ (ρ j)) * K i j‖ ≤
      ∑ i ∈ S, (zeroIncrementMajorant δ (ρ i).im)^2 * ∑ j ∈ S, ‖K i j‖ := by
  let b (i : ι) := zeroIncrementMajorant δ (ρ i).im
  apply (zero_weight_quadratic_form_le S ρ K hδ hsmall hr).trans
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (b i^2 * ‖K i j‖ + b j^2 * ‖K j i‖)/2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      change b i*b j*‖K i j‖ ≤ _
      rw [← hsym i hi j hj]
      have hb : 2 * (b i * b j) ≤ b i^2 + b j^2 := by nlinarith [sq_nonneg (b i - b j)]
      linarith only [mul_le_mul_of_nonneg_right hb (norm_nonneg (K i j))]
    _ = _ := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
      rw [show (∑ i ∈ S, ∑ j ∈ S, b j^2 * ‖K j i‖) = ∑ i ∈ S, ∑ j ∈ S, b i^2 * ‖K i j‖
        from Finset.sum_comm]
      simp only [← Finset.mul_sum, b, add_self_div_two]

end

section

open Complex MeasureTheory Set Finset
open scoped ComplexConjugate

/-- The Fourier transform of the absolute exponential at an angular frequency. -/
theorem exp_abs_fourier (t : ℝ) :
    let f := fun u : ℝ => (Real.exp (-2*|u|) : ℂ) * Complex.exp (I * (t : ℂ) * u)
    Integrable f ∧ ∫ u : ℝ, f u = ((4/(4+t^2) : ℝ) : ℂ) := by
  intro f
  let a : ℂ := 2+I*t
  let b : ℂ := -2+I*t
  have ha : 0 < a.re := by norm_num [a]
  have hb : b.re < 0 := by norm_num [b]
  have hl : EqOn f (fun u : ℝ => Complex.exp (a*u)) (Iic 0) := by
    intro u hu
    dsimp only [f,a]
    rw [abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  have hr : EqOn f (fun u : ℝ => Complex.exp (b*u)) (Ioi 0) := by
    intro u hu
    dsimp only [f,b]
    rw [abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  have hi₁ := (integrableOn_exp_mul_complex_Iic ha 0).congr_fun hl.symm measurableSet_Iic
  have hi₂ := (integrableOn_exp_mul_complex_Ioi hb 0).congr_fun hr.symm measurableSet_Ioi
  constructor
  · simpa using hi₁.union hi₂
  · rw [← intervalIntegral.integral_Iic_add_Ioi hi₁ hi₂, setIntegral_congr_fun measurableSet_Iic hl,
      setIntegral_congr_fun measurableSet_Ioi hr, integral_exp_mul_complex_Iic ha,
      integral_exp_mul_complex_Ioi hb]
    have ha' : a ≠ 0 := by intro he; simp [he] at ha
    have hb' : b ≠ 0 := by intro he; simp [he] at hb
    have hden : (4+(t : ℂ)^2) ≠ 0 := by exact_mod_cast (show 4+t^2 ≠ 0 by positivity)
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.ofReal_div,
      Complex.ofReal_ofNat,Complex.ofReal_add,Complex.ofReal_pow]
    field_simp [ha',hb',hden]
    dsimp only [a,b]
    ring_nf
    simp [I_sq,sub_eq_add_neg]

private theorem exp_mode_mul_conj (t r u : ℝ) :
    Complex.exp (I * (t : ℂ) * u) * conj (Complex.exp (I * (r : ℂ) * u)) =
      Complex.exp (I * ((t-r : ℝ) : ℂ) * u) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_I, conj_ofReal, ofReal_sub]
  ring

/-- The exact finite-frequency expansion of the weighted energy. The index
set may contain distinct indices carrying the same frequency. -/
theorem exp_abs_energy_eq {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    ((∫ u : ℝ, Real.exp (-2*|u|) * ‖∑ j ∈ s, a j * Complex.exp (I * (γ j : ℂ) * u)‖^2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, a j * conj (a k) * ((4/(4+(γ j-γ k)^2) : ℝ) : ℂ) := by
  classical
  let w (t u : ℝ) := (Real.exp (-2*|u|) : ℂ) * Complex.exp (I * (t : ℂ) * u)
  let f (j k : ι) (u : ℝ) := (a j * conj (a k)) * w (γ j-γ k) u
  have hpoint (u : ℝ) :
      ((Real.exp (-2*|u|) * ‖∑ j ∈ s, a j * Complex.exp (I * (γ j : ℂ) * u)‖^2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, f j k u := by
    rw [Finset.sum_comm (f := fun j k => f j k u),Complex.ofReal_mul,Complex.sq_norm,← Complex.mul_conj]
    simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [f,w]
    rw [← exp_mode_mul_conj]
    ring
  have hi (j k : ι) : Integrable (f j k) := (exp_abs_fourier (γ j-γ k)).1.const_mul _
  have he (j k : ι) : ∫ u : ℝ, f j k u =
      (a j * conj (a k)) * ((4/(4+(γ j-γ k)^2) : ℝ) : ℂ) := by
    rw [show f j k = _ from rfl, integral_const_mul, (exp_abs_fourier (γ j-γ k)).2]
  rw [← integral_complex_ofReal]
  simp_rw [hpoint]
  rw [integral_finsetSum s (fun j _ => integrable_finsetSum s (fun k _ => hi j k))]
  simp_rw [integral_finsetSum s (fun k _ => hi _ k), he]

/-- Symmetry and 2ab ≤ a²+b² bound a nonnegative quadratic form by the
diagonal square weights multiplied by the row sums. -/
theorem symmetric_row_sum_bound {ι : Type*} (s : Finset ι) (v : ι → ℝ) (K : ι → ι → ℝ)
    (hK : ∀ j k, 0 ≤ K j k) (hsym : ∀ j k, K j k = K k j) :
    (∑ j ∈ s, ∑ k ∈ s, v j*v k*K j k) ≤ ∑ j ∈ s, (v j)^2 * ∑ k ∈ s, K j k := by
  let b (j k : ι) := (v j)^2 * K j k
  have h (j k : ι) : v j*v k*K j k ≤ (b j k + b k j)/2 := by
    dsimp only [b]
    rw [← hsym j k]
    nlinarith only [mul_nonneg (sq_nonneg (v j-v k)) (hK j k)]
  calc
    _ ≤ ∑ j ∈ s, ∑ k ∈ s, (b j k + b k j)/2 :=
      sum_le_sum fun j _ => sum_le_sum fun k _ => h j k
    _ = ((∑ j ∈ s, ∑ k ∈ s, b j k) + ∑ j ∈ s, ∑ k ∈ s, b k j)/2 := by
      simp only [add_div,Finset.sum_add_distrib,Finset.sum_div]
    _ = ∑ j ∈ s, ∑ k ∈ s, b j k := by
      rw [Finset.sum_comm (f := fun j k => b k j)]
      ring
    _ = _ := by simp only [b,Finset.mul_sum]

theorem exp_abs_energy_integrable {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    Integrable (fun u : ℝ => Real.exp (-2*|u|) *
      ‖∑ j ∈ s, a j * Complex.exp (I * (γ j : ℂ) * u)‖^2) := by
  have hw : Integrable (fun u : ℝ => Real.exp (-2*|u|)) := by
    simpa [Complex.norm_exp] using (exp_abs_fourier 0).1.norm
  apply (hw.mul_const ((∑ j ∈ s, ‖a j‖)^2)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply (norm_sum_le ..).trans
  simp [Complex.norm_exp]

theorem exp_abs_energy_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) :
    (∫ u : ℝ, Real.exp (-2*|u|) * ‖∑ j ∈ s, a j * Complex.exp (I * (γ j : ℂ) * u)‖^2) ≤
      ∑ j ∈ s, ‖a j‖^2 * ∑ k ∈ s, 4/(4+(γ j-γ k)^2) := by
  let K (j k : ι) : ℝ := 4/(4+(γ j-γ k)^2)
  have hK (j k : ι) : 0 ≤ K j k := by dsimp [K]; positivity
  have hs (j k : ι) : K j k = K k j := by dsimp only [K]; rw [sub_sq_comm]
  have hn := congrArg norm (exp_abs_energy_eq s a γ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun u =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))] at hn
  rw [hn]
  apply le_trans _ (symmetric_row_sum_bound s (fun j => ‖a j‖) K hK hs)
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro j _
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro k _
  change ‖a j * conj (a k) * (K j k : ℂ)‖ ≤ _
  simp only [norm_mul, norm_conj, Complex.norm_of_nonneg (hK j k), le_refl]

end

section

open Complex MeasureTheory Set Finset
open scoped Interval

/-- The change of variables y = x exp(u) transfers the critical-line
power sum on [1,x] to the absolute exponential weight on the logarithmic axis. -/
theorem critical_line_physical_energy_le {ι : Type*} (s : Finset ι) (a ρ : ι → ℂ)
    (hρ : ∀ j ∈ s, (ρ j).re = 1/2) {x : ℝ} (hx : 1 ≤ x) :
    (∫ y : ℝ in 1..x, ‖∑ j ∈ s, a j * (y : ℂ) ^ (ρ j)‖^2) ≤
      x^2 * ∑ j ∈ s, ‖a j‖^2 * ∑ k ∈ s, 4/(4+((ρ j).im-(ρ k).im)^2) := by
  let T := -Real.log x
  let φ (u : ℝ) := x * Real.exp u
  let c (u : ℝ) := Real.exp (Real.log (φ u)/2)
  let γ (j : ι) := (ρ j).im
  let phase (j : ι) := Complex.exp (I * (γ j : ℂ) * (Real.log x : ℝ))
  let b (j : ι) := a j * phase j
  let P (y : ℝ) := ‖∑ j ∈ s, a j * (y : ℂ) ^ (ρ j)‖^2
  let A (u : ℝ) := ‖∑ j ∈ s, b j * Complex.exp (I * (γ j : ℂ) * u)‖^2
  let W (u : ℝ) := Real.exp (-2*|u|) * A u
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hT : T ≤ 0 := neg_nonpos.mpr (Real.log_nonneg hx)
  have hp (u : ℝ) : 0 < φ u := mul_pos hx' (Real.exp_pos _)
  have hc (u : ℝ) : c u ^ 2 = φ u := by
    dsimp only [c]
    rw [pow_two,← Real.exp_add,add_halves,Real.exp_log (hp u)]
  have hb (j : ι) : ‖b j‖ = ‖a j‖ := by simp [b,phase,Complex.norm_exp]
  have hP : Continuous P := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (Complex.continuous_ofReal_cpow_const (by rw [hρ j hj]; norm_num))
  have hφ (u : ℝ) : HasDerivAt φ (φ u) u := (Real.hasDerivAt_exp u).const_mul x
  have hchange := intervalIntegral.integral_comp_mul_deriv (a := T) (b := 0)
    (fun u _ => hφ u) (show ContinuousOn φ (uIcc T 0) from
      (continuous_const.mul Real.continuous_exp).continuousOn) hP
  have h1 : φ T = 1 := by dsimp [φ,T]; rw [Real.exp_neg,Real.exp_log hx',mul_inv_cancel₀ hx'.ne']
  rw [h1,show φ 0 = x by simp [φ] ] at hchange
  have hmode (u : ℝ) (j : ι) (hj : j ∈ s) :
      (φ u : ℂ) ^ (ρ j) = (c u : ℂ) * phase j * Complex.exp (I * (γ j : ℂ) * u) := by
    have hdecomp : ρ j = 1/2 + I * (γ j : ℂ) := by
      apply Complex.ext <;> simp [γ,hρ j hj]
    have hlog : Real.log (φ u) = Real.log x + u := by
      rw [show φ u = _ from rfl, Real.log_mul hx'.ne' (Real.exp_pos _).ne',Real.log_exp]
    dsimp only [c,phase]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (hp u).ne'),← Complex.ofReal_log (hp u).le,
      Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add,hdecomp,hlog]
    congr 1
    push_cast
    ring
  have hpoint (u : ℝ) (hu : u ∈ uIcc T 0) : (P ∘ φ) u * φ u = x^2 * W u := by
    have hu0 : u ≤ 0 := (uIcc_of_le hT ▸ hu).2
    have hsum : ∑ j ∈ s, a j * (φ u : ℂ) ^ (ρ j) =
        (c u : ℂ) * ∑ j ∈ s, b j * Complex.exp (I * (γ j : ℂ) * u) := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun j hj => by rw [hmode u j hj]; dsimp only [b]; ring
    change ‖∑ j ∈ s, a j * (φ u : ℂ) ^ (ρ j)‖^2 * φ u = x^2*(Real.exp (-2*|u|)*A u)
    rw [hsum,norm_mul,mul_pow,Complex.norm_of_nonneg (Real.exp_pos _).le,hc,abs_of_nonpos hu0]
    change φ u * A u * φ u = _
    rw [show -2 * -u = u+u by ring,Real.exp_add]
    dsimp only [φ]
    ring
  have hwi : Integrable W := exp_abs_energy_integrable s b γ
  change (∫ y : ℝ in 1..x, P y) ≤ _
  calc
    _ = ∫ u in T..0, (P ∘ φ) u * φ u := hchange.symm
    _ = ∫ u in T..0, x^2*W u := intervalIntegral.integral_congr hpoint
    _ = x^2 * (∫ u in T..0, W u) := intervalIntegral.integral_const_mul _ _
    _ ≤ x^2 * (∫ u : ℝ, W u) := by
      rw [intervalIntegral.integral_of_le hT]
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hwi (Filter.Eventually.of_forall
        (fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))) (sq_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
      simpa only [hb,γ,W,A] using exp_abs_energy_le s b γ

/-- With the difference-of-powers weights for the explicit formula, the
physical energy is controlled by the explicit majorant for each zero. -/
theorem zero_increment_physical_energy_le {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (hρ : ∀ j ∈ s, (ρ j).re = 1/2) {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ (10:ℝ)^(-13:ℤ)) :
    (∫ y : ℝ in 1..x, ‖∑ j ∈ s, zeroIncrementWeight δ (ρ j) * (y : ℂ) ^ (ρ j)‖^2) ≤
      x^2 * ∑ j ∈ s, (zeroIncrementMajorant δ (ρ j).im)^2 *
        ∑ k ∈ s, 4/(4+((ρ j).im-(ρ k).im)^2) := by
  apply (critical_line_physical_energy_le s (fun j => zeroIncrementWeight δ (ρ j)) ρ hρ hx).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
    (zeroIncrementWeight_norm_le hδ hsmall (hρ j hj)) 2) (sum_nonneg fun k _ => by positivity)

end

section

open scoped BigOperators

private theorem quarter_tail (j : ℕ) (w : ℝ) :
    (3/4 : ℝ) * (∑' k : ℕ, (1/4 : ℝ)^k * (if j ≤ k then w else 0)) =
      (1/4 : ℝ)^j * w := by
  let f (k : ℕ) := (1/4 : ℝ)^k * (if j ≤ k then w else 0)
  have hd : Summable (fun k : ℕ => (1/4 : ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hshift (k : ℕ) : f (k+j) = (1/4 : ℝ)^k * ((1/4 : ℝ)^j * w) := by
    simp [f, pow_add, mul_left_comm, mul_assoc]
  have hfs : Summable f := (summable_nat_add_iff (f := f) j).mp <|
    (hd.mul_right ((1/4 : ℝ)^j * w)).congr (fun k => (hshift k).symm)
  have hlow : (∑ k ∈ Finset.range j, f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f, Nat.not_le.mpr (Finset.mem_range.mp hk)]
  have hsplit := hfs.sum_add_tsum_nat_add j
  rw [hlow, zero_add] at hsplit
  change (3/4 : ℝ) * (∑' k : ℕ, f k) = _
  rw [← hsplit]
  simp_rw [hshift]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

/-- Bound the finite weighted spectrum by cumulative masses on dyadic windows.
The coefficient `3/4` comes from summing the geometric tail starting at the
first window which contains each ordinate. -/
theorem spectral_square_le_cumulative {ι : Type*} (S : Finset ι) (γ w : ι → ℝ)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (hw : ∀ i ∈ S, 0 ≤ w i) (P : ℕ → ℝ)
    (hP : ∀ k : ℕ, (∑ i ∈ S.filter (fun i => |γ i| ≤ (2:ℝ)^(k+1)*T), w i) ≤ P k)
    (hs : Summable (fun k : ℕ => (1/4 : ℝ)^k * P k)) :
    (∑ i ∈ S, w i * (if γ i = 0 then δ^2 else min (δ^2) ((δ*T / |γ i|)^2))) ≤
      (3/4:ℝ) * δ^2 * ∑' k : ℕ, (1/4:ℝ)^k * P k := by
  classical
  let U (k : ℕ) := (2:ℝ)^(k+1) * T
  let mass (i : ι) (k : ℕ) := (1/4:ℝ)^k * (if |γ i| ≤ U k then w i else 0)
  have hgeo : Summable (fun k : ℕ => (1/4 : ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmass (i : ι) (hi : i ∈ S) : Summable (mass i) := by
    apply (hgeo.mul_right (w i)).of_nonneg_of_le
    · intro k
      dsimp only [mass]
      split <;> positivity [hw i hi]
    · intro k
      dsimp only [mass]
      split
      · rfl
      · rw [mul_zero]
        positivity [hw i hi]
  have hpoint (i : ι) (hi : i ∈ S) :
      w i * (if γ i = 0 then δ^2 else min (δ^2) ((δ*T / |γ i|)^2)) ≤
        (3/4:ℝ) * δ^2 * ∑' k : ℕ, mass i k := by
    have hex : ∃ k : ℕ, |γ i| ≤ U k := by
      obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (|γ i| / T) (by norm_num : (1:ℝ)<2)
      refine ⟨k, ((div_lt_iff₀ hT).mp hk).le.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) (Nat.le_succ k)) hT.le
    let j := Nat.find hex
    have hiff (k : ℕ) : |γ i| ≤ U k ↔ j ≤ k := by
      refine ⟨fun hk => Nat.find_min' hex hk, fun hk => (Nat.find_spec hex).trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ hT.le
      exact pow_right_mono₀ (by norm_num) (Nat.succ_le_succ hk)
    have hsum : (3/4:ℝ) * (∑' k : ℕ, mass i k) = (1/4:ℝ)^j*w i := by
      simpa only [mass, hiff] using quarter_tail j (w i)
    have hvalue : (if γ i = 0 then δ^2 else min (δ^2) ((δ*T / |γ i|)^2)) ≤
        δ^2 * (1/4:ℝ)^j := by
      cases hj : j with
      | zero =>
        simp only [pow_zero, mul_one]
        split
        · exact le_rfl
        · exact min_le_left _ _
      | succ a =>
        have hmin : ¬ |γ i| ≤ U a := (hiff a).not.mpr (by omega)
        have hlo : (2:ℝ)^(a+1) * T < |γ i| := lt_of_not_ge hmin
        have ha : 0 < |γ i| := (mul_pos (pow_pos (by norm_num) _) hT).trans hlo
        rw [ite_eq_right (abs_pos.mp ha)]
        apply (min_le_right _ _).trans
        have hp : 0 < (2:ℝ)^(a+1) := by positivity
        have hq : δ*T / |γ i| ≤ δ / (2:ℝ)^(a+1) := by
          apply (div_le_div_iff₀ ha hp).mpr
          calc
            _ = δ * ((2:ℝ)^(a+1)*T) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hlo.le hδ.le
        calc
          _ ≤ (δ / (2:ℝ)^(a+1))^2 := pow_le_pow_left₀ (by positivity) hq 2
          _ = δ^2 * (1/4:ℝ)^(a+1) := by
            rw [div_pow, ← pow_mul, Nat.mul_comm (a+1) 2, pow_mul]
            norm_num
            rw [div_eq_mul_inv, ← inv_pow]
            norm_num
    calc
      _ ≤ w i * (δ^2 * (1/4:ℝ)^j) := mul_le_mul_of_nonneg_left hvalue (hw i hi)
      _ = δ^2 * ((1/4:ℝ)^j*w i) := by ring
      _ = _ := by rw [← hsum]; ring
  have hbound (k : ℕ) : (∑ i ∈ S, mass i k) ≤ (1/4:ℝ)^k * P k := by
    simpa only [mass, ← Finset.mul_sum, Finset.sum_filter] using
      mul_le_mul_of_nonneg_left (hP k) (show 0 ≤ (1/4:ℝ)^k by positivity)
  calc
    _ ≤ ∑ i ∈ S, ((3/4:ℝ) * δ^2 * ∑' k : ℕ, mass i k) := Finset.sum_le_sum hpoint
    _ = (3/4:ℝ)*δ^2*(∑' k : ℕ, ∑ i ∈ S, mass i k) := by
      rw [← Finset.mul_sum, Summable.tsum_finsetSum hmass]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.tsum_le_tsum hbound (summable_sum hmass) hs) (by positivity)

/-- The dyadic estimate in the normalization of the short-interval zero
increment, with the squared majorant preceding the row mass. -/
theorem spectral_increment_majorant_le_cumulative {ι : Type*} (S : Finset ι)
    (γ w : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (hscale : δ*T = 2.0001)
    (hw : ∀ i ∈ S, 0 ≤ w i) (P : ℕ → ℝ)
    (hP : ∀ k : ℕ, (∑ i ∈ S.filter (fun i => |γ i| ≤ (2:ℝ)^(k+1)*T), w i) ≤ P k)
    (hs : Summable (fun k : ℕ => (1/4 : ℝ)^k * P k)) :
    (∑ i ∈ S, (if γ i = 0 then δ else min δ (2.0001 / |γ i|))^2 * w i) ≤
      (3/4:ℝ) * δ^2 * ∑' k : ℕ, (1/4:ℝ)^k * P k := by
  apply le_trans _ (spectral_square_le_cumulative S γ w hδ hT hw P hP hs)
  apply Finset.sum_le_sum
  intro i hi
  rw [hscale, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  by_cases h : γ i = 0
  · simp [h]
  simp only [ite_eq_right h, le_min_iff]
  have hn : 0 ≤ min δ (2.0001 / |γ i|) := le_min hδ.le (by positivity)
  exact ⟨pow_le_pow_left₀ hn (min_le_left _ _) 2, pow_le_pow_left₀ hn (min_le_right _ _) 2⟩

end

section

/-- On the range of the moment estimate the first frequency cutoff is already
large enough to absorb the logarithms of all subsequent dyadic cutoffs. -/
theorem spectral_log_lower {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/10000000000000) :
    30 ≤ Real.log (2.0001/δ) := by
  have hpow : (Real.exp 1)^30 ≤ (2.72 : ℝ)^30 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  apply (Real.le_log_iff_exp_le (by positivity)).2
  calc
    Real.exp 30 ≤ 20000000000000 := by linarith
    _ ≤ 2.0001/δ := (le_div_iff₀ hd).2 (by linarith)

noncomputable def layerMajorant (T : ℝ) (k : ℕ) :=
  (1/4 : ℝ)^k * ((2:ℝ)^(k+1)*T/3) * (Real.log ((2:ℝ)^(k+1)*T))^2

private theorem layerMajorant_bound {T : ℝ} (hT : 0 < T) (hL : 30 ≤ Real.log T) (k : ℕ) :
    layerMajorant T k ≤ (2*T/3*(Real.log T)^2*(41/40)^2) *
      (((41/40 : ℝ)^2/2)^k) := by
  let L := Real.log T
  let n := k+1
  have hlog : Real.log ((2:ℝ)^n*T) = n*Real.log 2 + L := by
    rw [Real.log_mul (by positivity) hT.ne',Real.log_pow]
  have h2 : Real.log 2 ≤ (3/4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ L := by dsimp [L]; linarith
  have hg : 1+(n:ℝ)/40 ≤ (41/40:ℝ)^n := by
    convert one_add_mul_le_pow (show (-2:ℝ) ≤ 1/40 by norm_num) n using 1 <;> ring
  have hlog' : Real.log ((2:ℝ)^n*T) ≤ L*(41/40:ℝ)^n := by
    rw [hlog]
    calc
      _ ≤ L*(1+(n:ℝ)/40) := by
        have hc : Real.log 2 ≤ L/40 := by dsimp [L]; linarith
        nlinarith only [mul_le_mul_of_nonneg_left hc hn0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hl0
  have hpos : 0 ≤ Real.log ((2:ℝ)^n*T) := by
    rw [hlog]
    exact add_nonneg (mul_nonneg hn0 (Real.log_nonneg (by norm_num))) hl0
  have hsq := pow_le_pow_left₀ hpos hlog' 2
  unfold layerMajorant
  change (1/4:ℝ)^k * ((2:ℝ)^n*T/3) * _ ≤ _
  calc
    _ ≤ ((1/4:ℝ)^k * ((2:ℝ)^n*T/3)) * (L*(41/40:ℝ)^n)^2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
      simp only [n,pow_succ,one_div,inv_pow,div_pow,mul_pow,L]
      ring_nf
      field_simp
      rw [← mul_pow]
      norm_num

theorem layerMajorant_summable {T : ℝ} (hT : 0 < T) (hL : 30 ≤ Real.log T) :
    Summable (layerMajorant T) := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ (41/40)^2/2)
    (by norm_num)).mul_left (2*T/3*(Real.log T)^2*(41/40)^2)
  exact h.of_nonneg_of_le (fun k => by unfold layerMajorant; positivity) (layerMajorant_bound hT hL)

/-- A dyadic Cauchy-kernel mass bound with coefficient one third implies a
total spectral contribution below 2.22 times the natural scale. -/
theorem spectral_layer_total {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/10000000000000) :
    let T := 2.0001/δ
    (3/4)*δ^2 * (∑' k : ℕ, layerMajorant T k) ≤ 2.22 * δ * (Real.log T)^2 := by
  let T := 2.0001/δ
  let L := Real.log T
  have hT : 0 < T := by dsimp [T]; positivity
  have hL : 30 ≤ L := spectral_log_lower hd hu
  have hgeom := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ (41/40)^2/2) (by norm_num)
  have h := (layerMajorant_summable hT hL).tsum_le_tsum (layerMajorant_bound hT hL)
    (hgeom.mul_left (2*T/3*L^2*(41/40)^2))
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  change (3/4)*δ^2 * _ ≤ 2.22*δ*L^2
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (3/4)*δ^2)).trans
  have hcancel : δ*T = 2.0001 := by dsimp [T]; field_simp
  calc
    _ = (2.0001 * (1681/1519)) * (δ*L^2) := by
      rw [← hcancel]
      ring
    _ ≤ _ := by
      rw [mul_assoc (2.22:ℝ)]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end

section

open Finset MeasureTheory

/-- The Poisson kernel at scale two, with value one at its center. -/
noncomputable def zeroPoissonKernel (t : ℝ) : ℝ := 4 / (4 + t^2)

theorem zeroPoissonKernel_nonneg (t : ℝ) : 0 ≤ zeroPoissonKernel t := by
  unfold zeroPoissonKernel
  positivity

private theorem continuous_zeroPoissonKernel : Continuous zeroPoissonKernel := by
  unfold zeroPoissonKernel
  fun_prop (disch := intro t; positivity)

/-- A translated row entry has mass strictly larger than 6.2 in its own
interval of radius 1000. -/
theorem integral_zeroPoissonKernel_window (g : ℝ) :
    6.2 < ∫ t : ℝ in (g-1000)..(g+1000), zeroPoissonKernel (t-g) := by
  rw [intervalIntegral.integral_comp_sub_right, show g-1000-g = -1000 by ring,
    show g+1000-g = 1000 by ring]
  have han (t : ℝ) :
      HasDerivAt (fun u : ℝ => 2 * Real.arctan (u/2)) (zeroPoissonKernel t) t := by
    convert (((hasDerivAt_id t).div_const 2).arctan.const_mul 2) using 1
    · rfl
    unfold zeroPoissonKernel
    dsimp
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => han t)
    (continuous_zeroPoissonKernel.intervalIntegrable _ _)]
  norm_num only [show (-1000:ℝ)/2 = -500 by norm_num, show (1000:ℝ)/2 = 500 by norm_num,
    Real.arctan_neg]
  have h := Real.arctan_inv_of_pos (by norm_num : (0:ℝ)<500)
  have hi := Real.arctan_le_self (by norm_num : (0:ℝ) ≤ (500:ℝ)⁻¹)
  linarith [Real.pi_gt_d2]

/-- Integrating the row envelope over a larger interval gives a counting
estimate for the indices, including multiplicities represented by the indexing type. -/
theorem poisson_count_from_rows {ι : Type*} (S : Finset ι) (γ : ι → ℝ)
    (hrow : ∀ U : ℝ, 10^13 ≤ U → ∀ t : ℝ, |t| ≤ U →
      ∑ i ∈ S, zeroPoissonKernel (t-γ i) ≤ Real.log U)
    (T : ℝ) (hT : 2 * 10^13 ≤ T) :
    (((S.filter (fun i => |γ i| ≤ T)).card : ℝ)) ≤
      2 * (T+1000) / 6.2 * Real.log (T+1000) := by
  classical
  let F := S.filter (fun i => |γ i| ≤ T)
  let U := T+1000
  let k (i : ι) (t : ℝ) := zeroPoissonKernel (t - γ i)
  have hU : 10^13 ≤ U := by dsimp only [U]; linarith
  have hc (i : ι) : Continuous (k i) :=
    continuous_zeroPoissonKernel.comp (continuous_id.sub continuous_const)
  have hmass (i : ι) (hi : i ∈ F) : 6.2 ≤ ∫ t : ℝ in (-U)..U, k i t := by
    have hγ := abs_le.mp (Finset.mem_filter.mp hi).2
    apply (integral_zeroPoissonKernel_window (γ i)).le.trans
    exact intervalIntegral.integral_mono_interval (by dsimp only [U]; linarith [hγ.1])
      (by linarith) (by dsimp only [U]; linarith [hγ.2])
      (Filter.Eventually.of_forall fun t => zeroPoissonKernel_nonneg (t-γ i))
      ((hc i).intervalIntegrable _ _)
  have hh : (F.card : ℝ) * 6.2 ≤ 2 * U * Real.log U := by
    calc
      _ = ∑ _i ∈ F, (6.2:ℝ) := by simp
      _ ≤ ∑ i ∈ F, ∫ t : ℝ in (-U)..U, k i t := sum_le_sum hmass
      _ = ∫ t : ℝ in (-U)..U, ∑ i ∈ F, k i t :=
        (intervalIntegral.integral_finsetSum (fun i _ => (hc i).intervalIntegrable _ _)).symm
      _ ≤ ∫ t : ℝ in (-U)..U, Real.log U := by
        apply intervalIntegral.integral_mono_on (by linarith)
          ((continuous_finsetSum F (fun i _ => hc i)).intervalIntegrable _ _) intervalIntegrable_const
        intro t ht
        exact (sum_le_sum_of_subset_of_nonneg (filter_subset ..)
          (fun i _ _ => zeroPoissonKernel_nonneg (t-γ i))).trans (hrow U hU t (abs_le.mpr ht))
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  change (F.card : ℝ) ≤ 2 * U / 6.2 * Real.log U
  rw [show (6.2:ℝ) = 31/5 by norm_num] at hh ⊢
  linarith

/-- The integral counting bound and a second use of the same row estimate
at the individual ordinates give a sharp enough cumulative weight. -/
theorem poisson_weighted_count_from_rows {ι : Type*} (S : Finset ι) (γ : ι → ℝ)
    (hrow : ∀ U : ℝ, 10^13 ≤ U → ∀ t : ℝ, |t| ≤ U →
      ∑ i ∈ S, zeroPoissonKernel (t-γ i) ≤ Real.log U)
    (T : ℝ) (hT : 2 * 10^13 ≤ T) :
    ∑ i ∈ S.filter (fun i => |γ i| ≤ T), ∑ j ∈ S, zeroPoissonKernel (γ i - γ j)
      ≤ (T/3) * (Real.log T)^2 := by
  let F := S.filter (fun i => |γ i| ≤ T)
  have hT0 : 0 < T := by linarith
  have hlog : 1 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hT0).mpr (by linarith [Real.exp_one_lt_three])
  have hU : T+1000 ≤ (101/100 : ℝ)*T := by linarith
  have hLU : Real.log (T+1000) ≤ (101/100 : ℝ)*Real.log T := by
    calc
      _ ≤ Real.log ((101/100 : ℝ)*T) := Real.log_le_log (by positivity) hU
      _ = Real.log (101/100 : ℝ) + Real.log T := Real.log_mul (by norm_num) hT0.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 101/100)]
  have hcard : (F.card : ℝ) ≤ T/3 * Real.log T := by
    apply (poisson_count_from_rows S γ hrow T hT).trans
    have hLU0 : 0 ≤ Real.log (T+1000) := Real.log_nonneg (by linarith)
    calc
      _ ≤ 2*((101/100)*T)/6.2 * ((101/100)*Real.log T) := by gcongr
      _ ≤ _ := by
        rw [show (6.2:ℝ) = 31/5 by norm_num]
        nlinarith [mul_nonneg hT0.le (by linarith : 0 ≤ Real.log T)]
  calc
    _ ≤ ∑ _i ∈ F, Real.log T := by
      apply sum_le_sum
      intro i hi
      exact hrow T (by linarith) (γ i) (mem_filter.mp hi).2
    _ = (F.card : ℝ) * Real.log T := by simp
    _ ≤ (T/3 * Real.log T) * Real.log T := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring

end

section

open MeasureTheory Set Filter Chebyshev
open scoped Topology Interval

/-- Fatou's lemma in the form needed for a uniform bound on a sequence
that converges almost everywhere to a majorant of the target function. -/
private theorem integral_le_of_ae_limit_majorant {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f l : α → ℝ) (g : ℕ → α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : Integrable f μ) (hf₀ : ∀ᵐ y ∂μ, 0 ≤ f y)
    (hg : ∀ n, Integrable (g n) μ) (hg₀ : ∀ n, ∀ᵐ y ∂μ, 0 ≤ g n y)
    (hbound : ∀ n, ∫ y, g n y ∂μ ≤ B)
    (hlim : ∀ᵐ y ∂μ, Tendsto (fun n => g n y) atTop (𝓝 (l y)) ∧ f y ≤ l y) :
    ∫ y, f y ∂μ ≤ B := by
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [ofReal_integral_eq_lintegral_ofReal hf hf₀]
  calc
    _ ≤ ∫⁻ y, liminf (fun n => ENNReal.ofReal (g n y)) atTop ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hlim] with y hy
      rw [(ENNReal.tendsto_ofReal hy.1).liminf_eq]
      exact ENNReal.ofReal_le_ofReal hy.2
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (g n y) ∂μ) atTop :=
      lintegral_liminf_le' fun n => ENNReal.continuous_ofReal.aemeasurable.comp_aemeasurable
        (hg n).aemeasurable
    _ ≤ _ := by
      apply liminf_le_of_frequently_le'
      apply Frequently.of_forall
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hg n) (hg₀ n)]
      exact ENNReal.ofReal_le_ofReal (hbound n)

/-- Transfer uniform bounds on finite zero polynomials to the actual ψ
increment. The limits and the explicit-formula remainder are required only
on the local interval [x/100,x]. -/
theorem local_psi_moment_of_ae_zero_polynomials {x : ℝ} (hx : 1100000000000000000 ≤ x)
    (P : ℕ → ℝ → ℂ) (L : ℝ → ℂ) (hcont : ∀ n, Continuous (P n))
    (hpoly : ∀ n, (∫ y : ℝ in 1..x, ‖P n y‖^2) ≤
      2.22 * relativeWidth x * (Real.log x)^2 * x^2)
    (hlocal : ∀ᵐ y ∂volume.restrict (Icc (x/100) x),
      Tendsto (fun n => P n y) atTop (𝓝 (L y)) ∧
      ‖((psi ((1+relativeWidth x)*y)-psi y-relativeWidth x*y : ℝ) : ℂ) + L y‖ ≤ relativeWidth x) :
    (∫ y : ℝ in x/100..x, (psi ((1+relativeWidth x)*y)-psi y-relativeWidth x*y)^2) ≤
      2.54 * relativeWidth x * x^2 * (Real.log x)^2 := by
  let d := relativeWidth x
  let t := x/100
  let m := volume.restrict (Ioc t x)
  let E (y : ℝ) := psi ((1+d)*y)-psi y-d*y
  let G (n : ℕ) (y : ℝ) := 1.05*‖P n y‖^2+21*d^2
  let major (y : ℝ) := 1.05*‖L y‖^2+21*d^2
  let A := d*(Real.log x)^2*x^2
  have hx₀ : 0 ≤ x := by linarith
  have ht₁ : 1 ≤ t := by dsimp [t]; linarith
  have htx : t ≤ x := by dsimp [t]; linarith
  obtain ⟨hlog,hd,hdsmall,_,_,_⟩ := relativeWidth_bounds hx
  change 0 < d at hd
  change d ≤ _ at hdsmall
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hI (n : ℕ) : Continuous (G n) := by dsimp [G]; fun_prop (disch := exact hcont _)
  have hdom (n : ℕ) : (∫ y : ℝ in t..x, ‖P n y‖^2) ≤ 2.22*A := by
    apply (intervalIntegral.integral_mono_interval ht₁ htx le_rfl
      (Eventually.of_forall fun _ => sq_nonneg _) ((hcont n).norm.pow 2 |>.intervalIntegrable 1 x)).trans
    simpa only [A,d,mul_assoc] using hpoly n
  have hpen : 21*d^2*x ≤ 0.2*A := by
    have hd1 : d ≤ 1 := by linarith
    have hl2 : 1 ≤ (Real.log x)^2 := one_le_pow₀ hlog
    have he : 21*d ≤ 0.2*(Real.log x)^2*x := calc
      _ ≤ 21 := by linarith
      _ ≤ 0.2*1*x := by linarith
      _ ≤ _ := by gcongr
    dsimp only [A]
    nlinarith only [mul_le_mul_of_nonneg_right he (mul_nonneg hd.le hx₀)]
  have hbound (n : ℕ) : ∫ y, G n y ∂m ≤ 2.54*A := by
    change (∫ y in Ioc t x, G n y) ≤ _
    rw [← intervalIntegral.integral_of_le htx]
    have hi : IntervalIntegrable (fun y : ℝ => 1.05*‖P n y‖^2) volume t x :=
      (((hcont n).norm.pow 2).const_mul (1.05:ℝ)).intervalIntegrable t x
    have hc : IntervalIntegrable (fun _ : ℝ => 21*d^2) volume t x := intervalIntegrable_const
    dsimp only [G]
    rw [intervalIntegral.integral_add hi hc,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have ht₀ : 0 ≤ t := by linarith
    nlinarith only [hdom n,hpen,mul_nonneg (sq_nonneg d) ht₀,hA]
  have hlim : ∀ᵐ y ∂m, Tendsto (fun n => G n y) atTop (𝓝 (major y)) ∧ E y ^ 2 ≤ major y := by
    rw [← restrict_Ioc_eq_restrict_Icc] at hlocal
    filter_upwards [hlocal] with y hy
    refine ⟨((hy.1.norm.pow 2).const_mul (1.05:ℝ)).add_const _,?_⟩
    have htri : |E y| ≤ ‖L y‖+d := calc
      |E y| = ‖((E y : ℝ) : ℂ)‖ := by simp
      _ = ‖(((E y : ℝ) : ℂ) + L y) - L y‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖((E y : ℝ) : ℂ) + L y‖+‖L y‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [show ‖((E y : ℝ) : ℂ)+L y‖ ≤ d from hy.2]
    have hs := pow_le_pow_left₀ (abs_nonneg _) htri 2
    rw [sq_abs] at hs
    dsimp only [major]
    nlinarith only [hs,sq_nonneg (‖L y‖-20*d)]
  have hFatou := integral_le_of_ae_limit_majorant (fun y => E y^2) major G
    (B := 2.54*A) (by positivity) (psi_increment_sq_intervalIntegrable d t x).1
    (Eventually.of_forall fun _ => sq_nonneg _) (fun n => ((hI n).intervalIntegrable t x).1)
    (fun _ => Eventually.of_forall fun _ => by dsimp [G]; positivity) hbound hlim
  change (∫ y in t..x, E y^2) ≤ _
  rw [intervalIntegral.integral_of_le htx]
  apply hFatou.trans_eq
  dsimp only [A,d]
  ring

end

section

open scoped BigOperators Topology
open Filter Metric

/-- Divide out the prescribed multiplicities of the zeros in the inner
closed disk. The corrected quotient extends analytically across every
removed zero, remains analytic on the outer disk, and has no inner zeros. -/
theorem remove_prescribed_disk_zeros (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ w, f w = (∏ z ∈ Z, (w - z) ^ analyticOrderNatAt f z) * g w := by
  classical
  have hR := hr.trans hrR
  have hcenter : c ∈ closedBall c R := by simpa using hR
  have hfinite := (hf.exists_analyticOrderAt_ne_top_iff_forall (isConnected_closedBall hR)).mp
    ⟨⟨c, hcenter⟩, by rw [(hf c hcenter).analyticOrderAt_eq_zero.mpr hc]; simp⟩
  let m (z : ℂ) := analyticOrderNatAt f z
  let P (w : ℂ) := ∏ z ∈ Z, (w - z) ^ m z
  let Q (z w : ℂ) := ∏ a ∈ Z.erase z, (w - a) ^ m a
  have hsplit {z : ℂ} (hz : z ∈ Z) (w : ℂ) : P w = (w - z) ^ m z * Q z w :=
    (Z.mul_prod_erase (fun a => (w - a) ^ m a) hz).symm
  have hprod {F : Finset ℂ} {w : ℂ} (hw : w ∉ F) :
      (∏ a ∈ F, (w - a) ^ m a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hw (he ▸ ha)))
  have hprodAn (F : Finset ℂ) (w : ℂ) : AnalyticAt ℂ (fun b => ∏ a ∈ F, (b - a) ^ m a) w := by
    fun_prop
  have hlocal (z : ℂ) (hz : z ∈ Z) :
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, f w = (w - z) ^ m z * u w := by
    have hzR := closedBall_subset_closedBall hrR ((hZ z).mp hz).1
    exact (hf z hzR).analyticOrderAt_ne_top.mp (hfinite ⟨z, hzR⟩)
  choose u hu hune hfac using hlocal
  let g (w : ℂ) := if hw : w ∈ Z then u w hw w / Q w w else f w / P w
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hzR
    by_cases hz : z ∈ Z
    · have hQ : Q z z ≠ 0 := hprod (Finset.notMem_erase _ _)
      apply ((hu z hz).div (hprodAn (Z.erase z) z) hQ).congr
      have havoid : ∀ᶠ w in 𝓝 z, w ∉ Z.erase z :=
        (Z.erase z).isClosed.isOpen_compl.mem_nhds (Finset.notMem_erase _ _)
      filter_upwards [havoid, hfac z hz] with w hw hfw
      change u z hz w / Q z w = g w
      by_cases hwz : w = z
      · subst w
        simp [g, hz]
      · have hwZ : w ∉ Z := fun h => hw (Finset.mem_erase.mpr ⟨hwz, h⟩)
        have hpow := pow_ne_zero (m z) (sub_ne_zero.mpr hwz)
        simp only [g, dite_eq_right hwZ, hfw, hsplit hz w]
        field_simp
    · apply ((hf z hzR).div (hprodAn Z z) (hprod hz)).congr
      filter_upwards [Z.isClosed.isOpen_compl.mem_nhds (show z ∉ Z from hz)] with w hw
      change w ∉ Z at hw
      simp [g, hw, P]
  · intro z hzr
    by_cases hz : z ∈ Z
    · simp only [g, dite_eq_left hz]
      exact div_ne_zero (hune z hz) (hprod (Finset.notMem_erase _ _))
    · simp only [g, dite_eq_right hz]
      exact div_ne_zero (fun he => hz ((hZ z).mpr ⟨hzr, he⟩)) (hprod hz)
  · intro w
    change f w = P w * g w
    by_cases hw : w ∈ Z
    · have h := (hfac w hw).self_of_nhds
      rw [h, hsplit hw w]
      simp only [g, dite_eq_left hw]
      have hQ : Q w w ≠ 0 := hprod (Finset.notMem_erase _ _)
      field_simp
    · simp only [g, dite_eq_right hw]
      have hP : P w ≠ 0 := hprod hw
      field_simp

/-- A finite list of all inner zeros and its exact analytic factorization
exist on every nested pair of closed disks with a nonzero central value. -/
theorem remove_disk_zeros (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    ∃ (Z : Finset ℂ) (g : ℂ → ℂ), (∀ z : ℂ, z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0) ∧
      AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ w, f w = (∏ z ∈ Z, (w - z) ^ analyticOrderNatAt f z) * g w := by
  classical
  have hrAn : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR)
  have hd := hrAn.preimage_zero_mem_codiscreteWithin hc (mem_closedBall_self hr)
    (isConnected_closedBall hr)
  have hfinite : {z ∈ closedBall c r | f z = 0}.Finite :=
    ((isCompact_closedBall c r).finite_sdiff_of_mem_codiscreteWithin hd).subset
      (fun z hz => ⟨hz.1, by simp [hz.2]⟩)
  let Z := hfinite.toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0 := hfinite.mem_toFinset
  obtain ⟨g, han, hnz, hfac⟩ := remove_prescribed_disk_zeros f c r R hr hrR hf hc Z hZ
  exact ⟨Z, g, hZ, han, hnz, hfac⟩

open Complex Set

/-- A logarithmic-derivative oscillation estimate on a zero-free disk.
Subtracting the central value yields a second inverse power of the radius. -/
theorem logDeriv_oscillation_on_disk {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ g (ball 0 R)) (hn : ∀ w ∈ ball (0:ℂ) R, g w ≠ 0)
    (hb : ∀ w ∈ ball (0:ℂ) R, ‖g w‖ ≤ ‖g 0‖ * Real.exp M) {z : ℂ} (hz : ‖z‖ < R/2) :
    ‖logDeriv g z - logDeriv g 0‖ ≤ 96 * ‖z‖ * (M / R^2) := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  have hh : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := (hd.deriv isOpen_ball).div hd hn
  obtain ⟨u,hu0,hu⟩ := hh.isExactOn_ball.with_val_at (0:ℂ) 0
  have hud : DifferentiableOn ℂ u (ball 0 R) := fun w hw =>
    (hu w hw).differentiableAt.differentiableWithinAt
  have heud : DifferentiableOn ℂ (fun w => Complex.exp (u w)) (ball 0 R) := fun w hw =>
    (hu w hw).cexp.differentiableAt.differentiableWithinAt
  obtain ⟨k,_,heq⟩ := (logDeriv_eqOn_iff hd heud isOpen_ball (convex_ball _ _).isPreconnected
    (fun w _ => Complex.exp_ne_zero _) hn).mp (by
      intro w hw
      rw [logDeriv_apply (fun w => Complex.exp (u w)), (hu w hw).cexp.deriv]
      field_simp)
  have hk : g 0 = k := by simpa [hu0] using heq h0
  have hre (w : ℂ) (hw : w ∈ ball 0 R) : (u w).re ≤ M := by
    apply Real.exp_le_exp.mp
    have h := hb w hw
    rw [show g w = g 0 * Complex.exp (u w) by simpa [hk] using heq hw,
      norm_mul,Complex.norm_exp] at h
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (hn 0 h0))).mp h
  have hder (w : ℂ) (hw : w ∈ ball (0:ℂ) (R/2)) : ‖logDeriv g w‖ ≤ 24*M/R := by
    have hw' := mem_ball_zero_iff.mp hw
    have geo (v : ℂ) (hv : v ∈ closedBall w (R/4)) : ‖v‖ ≤ 3*R/4 := by
      have hh : ‖v-w‖ ≤ R/4 := by simpa only [mem_closedBall,dist_eq_norm] using hv
      linarith [norm_le_norm_sub_add v w]
    have inc : closedBall w (R/4) ⊆ ball (0:ℂ) R :=
      fun v hv => mem_ball_zero_iff.mpr (by linarith [geo v hv])
    have hC (v : ℂ) (hv : v ∈ sphere w (R/4)) : ‖u v‖ ≤ 6*M := by
      have hv' := sphere_subset_closedBall hv
      have hvr := geo v hv'
      apply (borelCaratheodory_zero hM hud (fun v hv => hre v hv) hR (inc hv') hu0).trans
      apply (div_le_iff₀ (by linarith)).2
      nlinarith only [mul_le_mul_of_nonneg_left hvr hM.le]
    rw [← (hu w (mem_ball_zero_iff.mpr (by linarith))).deriv]
    apply (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0<R/4)
      (hud.diffContOnCl_ball inc) hC).trans_eq
    ring
  have hmap : MapsTo (logDeriv g) (ball 0 (R/2)) (closedBall (logDeriv g 0) (48*M/R)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    calc
      _ ≤ ‖logDeriv g w‖ + ‖logDeriv g 0‖ := norm_sub_le .. 
      _ ≤ 24*M/R + 24*M/R := add_le_add (hder w hw) (hder 0 (mem_ball_self (by positivity)))
      _ = _ := by ring
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (hh.mono (ball_subset_ball (by linarith : R/2≤R))) hmap (mem_ball_zero_iff.mpr hz)
  rw [dist_eq_norm,dist_zero_right] at hs
  exact hs.trans_eq (by ring)

/-- Removing all interior zeros costs no additional boundary factor when the
outer circle has twice the radius of the zero disk. -/
private theorem quotient_relative_growth {f g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (Z : Finset ℂ) (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, ‖ρ‖ ≤ R)
    (hfac : ∀ w, f w = (∏ ρ ∈ Z, (w-ρ)^(m ρ)) * g w)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 (2*R)))
    (hb : ∀ w ∈ sphere (0:ℂ) (2*R), ‖f w‖ ≤ ‖f 0‖*Real.exp M) :
    ∀ w ∈ ball (0:ℂ) R, ‖g w‖ ≤ ‖g 0‖*Real.exp M := by
  let P (w : ℂ) := ∏ ρ ∈ Z, (w-ρ)^(m ρ)
  have hboundary (w : ℂ) (hw : w ∈ sphere 0 (2*R)) : ‖g w‖ ≤ ‖g 0‖*Real.exp M := by
    have hnw : ‖w‖ = 2*R := by simpa only [mem_sphere,dist_zero_right] using hw
    have hcmp : ‖P 0‖ ≤ ‖P w‖ := by
      simp only [P,norm_prod,norm_pow,zero_sub,norm_neg]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro ρ hr
      apply pow_le_pow_left₀ (norm_nonneg _)
      linarith [norm_le_norm_sub_add w ρ,hZ ρ hr]
    have hpos : 0 < ‖P w‖ := norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr (fun he => by have hh := hZ ρ hρ; rw [← he] at hh; linarith)))
    have h := hb w hw
    rw [hfac w,hfac 0,norm_mul,norm_mul] at h
    change ‖P w‖ * ‖g w‖ ≤ ‖P 0‖*‖g 0‖*Real.exp M at h
    apply (mul_le_mul_iff_right₀ hpos).mp
    exact h.trans (by rw [← mul_assoc]; gcongr)
  intro w hw
  have hd : DiffContOnCl ℂ g (ball 0 (2*R)) :=
    hg.differentiableOn.diffContOnCl_ball Set.Subset.rfl
  apply norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (fun v hv => hboundary v (by rwa [frontier_ball (0:ℂ) (by positivity : 2*R ≠ 0)] at hv))
  exact subset_closure (ball_subset_ball (by linarith : R ≤ 2*R) hw)

private theorem logDeriv_finite_factorization {f g : ℂ → ℂ} (Z : Finset ℂ) (m : ℂ → ℕ)
    (hfac : ∀ w, f w = (∏ ρ ∈ Z, (w-ρ)^(m ρ)) * g w)
    {w : ℂ} (hw : w ∉ Z) (hgd : DifferentiableAt ℂ g w) (hgn : g w ≠ 0) :
    logDeriv f w = (∑ ρ ∈ Z, (m ρ : ℂ)/(w-ρ)) + logDeriv g w := by
  let P (w : ℂ) := ∏ ρ ∈ Z, (w-ρ)^(m ρ)
  have hn (ρ : ℂ) (hr : ρ ∈ Z) : w-ρ ≠ 0 := sub_ne_zero.mpr (fun he => hw (he ▸ hr))
  have hz : P w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hn ρ hρ)
  have hd : DifferentiableAt ℂ P w := by dsimp [P]; fun_prop
  have heq : f = fun w => P w * g w := funext hfac
  rw [heq,logDeriv_fun_mul w hz hgn hd hgd]
  congr 1
  rw [show logDeriv P w = _ from logDeriv_fun_prod (f := fun ρ (v:ℂ) => (v-ρ)^(m ρ))
    (fun ρ hρ => pow_ne_zero _ (hn ρ hρ)) (fun _ _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [logDeriv_fun_pow (f := fun v : ℂ => v-ρ) (by fun_prop)]
  simp [logDeriv_apply,div_eq_mul_inv]

/-- On an open right half-plane, every zero on the imaginary axis contributes
a nonnegative real logarithmic derivative. The remaining error is explicit. -/
theorem imaginary_axis_zeros_logDeriv_disk {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h₀ : f 0 ≠ 0) (heven : ∀ w, f (-w) = f w) (haxis : ∀ w, f w = 0 → w.re = 0)
    {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hb : ∀ w ∈ sphere (0:ℂ) (2*R), ‖f w‖ ≤ ‖f 0‖*Real.exp M)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ‖ρ‖ ≤ R ∧ f ρ = 0)
    {z : ℂ} (hz : 0 < z.re) (hzR : ‖z‖ < R/2) :
    (∑ ρ ∈ S, ((analyticOrderNatAt f ρ : ℂ)/(z-ρ)).re) ≤
      (logDeriv f z).re + 96*‖z‖*(M/R^2) := by
  obtain ⟨Z,g,hZ,hg,hgn,hfac⟩ := remove_disk_zeros f 0 R (2*R) hR.le (by linarith)
    (fun w _ => hf.analyticAt w) h₀
  let m := analyticOrderNatAt f
  have hroot (ρ : ℂ) (hρ : ρ ∈ Z) := (hZ ρ).1 hρ
  have hax (ρ : ℂ) (hρ : ρ ∈ Z) := haxis ρ (hroot ρ hρ).2
  have hle (ρ : ℂ) (hρ : ρ ∈ Z) := mem_closedBall_zero_iff.mp (hroot ρ hρ).1
  have hzr : z ∈ ball 0 R := mem_ball_zero_iff.mpr (by linarith)
  have hzr' := ball_subset_closedBall hzr
  have hinc : closedBall (0:ℂ) R ⊆ closedBall 0 (2*R) := closedBall_subset_closedBall (by linarith)
  have hzZ : z ∉ Z := fun h => hz.ne' (hax z h)
  have h0Z : (0:ℂ) ∉ Z := fun h => h₀ (hroot 0 h).2
  have hsum := logDeriv_finite_factorization Z m hfac hzZ
    (hg z (hinc hzr')).differentiableAt (hgn z hzr')
  have hsum₀ := logDeriv_finite_factorization Z m hfac h0Z
    (hg 0 (mem_closedBall_self (by linarith))).differentiableAt (hgn 0 (mem_closedBall_self hR.le))
  have hld : logDeriv f 0 = 0 := by
    have hf' := deriv_comp_neg f (0 : ℂ)
    rw [show (fun w => f (-w)) = f from funext heven,neg_zero] at hf'
    simp only [logDeriv_apply]
    have h : deriv f 0 = 0 := by linear_combination (norm := ring_nf) (1/2 : ℂ)*hf'
    rw [h,zero_div]
  have hc : (logDeriv g 0).re = 0 := by
    have H := congrArg Complex.re hsum₀
    rw [hld,zero_re,add_re,Complex.re_sum] at H
    have hh : (∑ ρ ∈ Z, ((m ρ : ℂ)/(0-ρ)).re) = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      simp [Complex.div_re,hax ρ hρ]
    linarith
  have hosc := logDeriv_oscillation_on_disk hR hM
    (hg.differentiableOn.mono (Set.Subset.trans ball_subset_closedBall hinc))
    (fun w hw => hgn w (ball_subset_closedBall hw))
    (quotient_relative_growth hR Z m hle hfac hg hb) hzR
  have hreal := (Complex.abs_re_le_norm (logDeriv g z - logDeriv g 0)).trans hosc
  rw [sub_re,hc,sub_zero] at hreal
  have hsub : S ⊆ Z := fun ρ hρ => (hZ ρ).2 ⟨mem_closedBall_zero_iff.mpr (hS ρ hρ).1,(hS ρ hρ).2⟩
  have hnonnegative (ρ : ℂ) (hρ : ρ ∈ Z) : 0 ≤ ((m ρ : ℂ)/(z-ρ)).re := by
    simp only [Complex.div_re,Complex.natCast_re,Complex.natCast_im,zero_mul,zero_div,add_zero,
      sub_re,hax ρ hρ,sub_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hz.le) (Complex.normSq_nonneg _)
  have hcmp := Finset.sum_le_sum_of_subset_of_nonneg (f := fun ρ => ((m ρ : ℂ)/(z-ρ)).re)
    hsub (fun ρ hρ _ => hnonnegative ρ hρ)
  have hrealSum := congrArg Complex.re hsum
  rw [add_re,Complex.re_sum] at hrealSum
  change (∑ ρ ∈ S, ((m ρ : ℂ)/(z-ρ)).re) ≤ _
  linarith only [hcmp,(abs_le.mp hreal).1,hrealSum]

/-- An even entire function of subquadratic logarithmic growth whose zeros
lie on the imaginary axis satisfies the positive half-plane logarithmic
derivative inequality for every finite subset of its actual zeros. -/
theorem even_entire_zero_sum_le_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf₀ : f 0 ≠ 0) (heven : ∀ w, f (-w) = f w) (haxis : ∀ w, f w = 0 → w.re = 0)
    (L : ℝ → ℝ) (hbound : ∀ R : ℝ, 1 ≤ R → ∀ w : ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ Real.exp (L R))
    (hsmall : Tendsto (fun R : ℝ => L R / R^2) atTop (𝓝 0))
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, f ρ = 0) {z : ℂ} (hz : 0 < z.re) :
    (∑ ρ ∈ S, ((analyticOrderNatAt f ρ : ℂ)/(z-ρ)).re) ≤ (logDeriv f z).re := by
  let c := Real.log ‖f 0‖
  let M (R : ℝ) := L R-c+1
  have hpos := norm_pos_iff.mpr hf₀
  have ec : Real.exp c = ‖f 0‖ := Real.exp_log hpos
  have hSbound : ∀ᶠ R : ℝ in atTop, ∀ ρ ∈ S, 2*‖ρ‖ ≤ R :=
    S.eventually_all.mpr (fun ρ _ => eventually_ge_atTop _)
  have hrem : Tendsto (fun R : ℝ => 96*‖z‖*(M R/(R/2)^2)) atTop (𝓝 0) := by
    have hdec : Tendsto (fun R : ℝ => (1-c)*(R⁻¹)^2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.pow 2).const_mul (1-c)
    have H := (hsmall.add hdec).const_mul (384*‖z‖)
    apply Tendsto.congr' _ (by simpa only [zero_add,mul_zero] using H)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    dsimp only [M]
    field_simp [hR.ne']
    ring
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (by simpa only [add_zero] using hrem.const_add (logDeriv f z).re)
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_gt_atTop (4*‖z‖),hSbound] with R hR hzR hSR
  have hRp : 0 < R := by linarith
  have hc : c ≤ L R := by
    apply Real.exp_le_exp.mp
    rw [ec]
    exact hbound R hR 0 (by simpa using hRp.le)
  apply imaginary_axis_zeros_logDeriv_disk hf hf₀ heven haxis (R := R/2) (M := M R)
    (by linarith) (by dsimp [M]; linarith) _ S (fun ρ hρ => ⟨by linarith [hSR ρ hρ],hS ρ hρ⟩) hz
    (by linarith)
  intro w hw
  have hn : ‖w‖ = R := by simpa [mem_sphere,show 2*(R/2) = R by ring] using hw
  apply (hbound R hR w hn.le).trans
  rw [← ec,← Real.exp_add,Real.exp_le_exp]
  dsimp only [M]
  linarith

/-- The Poisson row for any finite selection of imaginary-axis zeros, with
their analytic multiplicities, is bounded by the actual logarithmic derivative. -/
theorem even_entire_poisson_row {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf₀ : f 0 ≠ 0) (heven : ∀ w, f (-w) = f w) (haxis : ∀ w, f w = 0 → w.re = 0)
    (L : ℝ → ℝ) (hbound : ∀ R : ℝ, 1 ≤ R → ∀ w : ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ Real.exp (L R))
    (hsmall : Tendsto (fun R : ℝ => L R / R^2) atTop (𝓝 0))
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, f ρ = 0) (t : ℝ) :
    (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ) * (4/(4+(t-ρ.im)^2))) ≤
      2*(logDeriv f ⟨2,t⟩).re := by
  let z : ℂ := ⟨2,t⟩
  have hh := even_entire_zero_sum_le_logDeriv hf hf₀ heven haxis L hbound hsmall S hS
    (z := z) (by norm_num [z])
  apply le_trans _ (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2))
  rw [Finset.mul_sum]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [z,Complex.div_re,Complex.natCast_re,Complex.natCast_im,sub_re,
    sub_im,haxis ρ (hS ρ hρ),sub_zero,zero_mul,zero_div,add_zero,Complex.normSq_apply]
  ring

end

section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private noncomputable def fracPart (t : ℝ) : ℂ := ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)

private theorem measurable_fracPart : Measurable fracPart := by
  unfold fracPart
  fun_prop

private theorem frac_norm {t : ℝ} (ht : 0 ≤ t) : ‖fracPart t‖ ≤ 1 := by
  rw [fracPart, Complex.norm_of_nonneg (Nat.zero_le_self_sub_floor ht)]
  exact (Nat.self_sub_floor_lt_one t).le

private noncomputable def fracMellinFun := (Set.Ioi (1 : ℝ)).indicator fracPart

private theorem mellin_frac_eq (s : ℂ) :
    mellin fracMellinFun (-s) = ∫ t in Set.Ioi (1 : ℝ), fracPart t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • fracMellinFun t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;>
      simp [fracMellinFun, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

private theorem frac_kernel_bound (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖fracPart t * (t : ℂ) ^ (-(s+1))‖ ≤ t ^ (-(s.re+1)) := by
  have ht' := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht'.le _) (frac_norm ht'.le)

private theorem frac_kernel_integrable (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) (Set.Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (show -(s.re+1) < -1 by linarith) zero_lt_one).mono'
  · exact (measurable_fracPart.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact frac_kernel_bound s ht

private theorem zeta_mellin_right (s : ℂ) (hs : 1 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * mellin fracMellinFun (-s) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have h0 : 0 < s.re := zero_lt_one.trans hs
  have hZ : riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s+1)) := by
    rw [← LSeries_one_eq_riemannZeta hs, LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one
      hs (LSeriesSummable_one_iff.mpr hs)]
    · simp [Nat.card_Icc]
    · apply Asymptotics.IsBigO.of_bound 1
      exact Eventually.of_forall (fun n => by simp [Nat.card_Icc])
  have he : (-s).re < -1 := by simpa using hs
  have hI := integral_Ioi_cpow_of_lt he zero_lt_one
  have hc : (s - 1) * (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s)) = 1 := by
    rw [hI, ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
    field_simp [sub_ne_zero.mpr hs1]
  have hsplit : (∫ t in Set.Ioi (1:ℝ), (⌊t⌋₊ : ℂ) * (t:ℂ)^(-(s+1))) =
      (∫ t : ℝ in Set.Ioi 1, (t:ℂ)^(-s)) - mellin fracMellinFun (-s) := by
    rw [mellin_frac_eq, ← integral_sub (integrableOn_Ioi_cpow_of_lt he zero_lt_one)
      (frac_kernel_integrable s h0)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hz : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hp : (t:ℂ) ^ (-s) = (t:ℂ) * (t:ℂ) ^ (-(s+1)) := by
      conv_lhs => rw [show -s = 1 + (-(s+1)) by ring, cpow_add _ _ hz, cpow_one]
    dsimp only
    rw [hp, fracPart, ofReal_sub, ofReal_natCast]
    ring
  have hreg : riemannZeta₁ s = (s-1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  rw [hreg, hZ, hsplit]
  linear_combination s * hc

/-- Euler's integral representation of the zeta function after removal of its
simple pole. The entire function on the left takes the value one at one. -/
theorem zeta_pole_removed_eq_floor_integral (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * ∫ t in Set.Ioi (1 : ℝ),
      (((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have hbound (t : ℝ) : ‖fracMellinFun t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa only [fracMellinFun, Set.indicator_of_mem ht] using frac_norm (zero_lt_one.trans ht).le
    · simp [fracMellinFun, Set.indicator_of_notMem ht]
  have hloc : LocallyIntegrableOn fracMellinFun (Set.Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_fracPart.indicator measurableSet_Ioi).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : fracMellinFun =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : fracMellinFun =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [fracMellinFun, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z - (z - 1) * z * mellin fracMellinFun (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.sub (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
      (hm.comp z differentiableAt_id.neg))).differentiableWithinAt
  have hZ := differentiable_riemannZeta₁.differentiableOn.analyticOnNhd ho
  have hagree : riemannZeta₁ =ᶠ[𝓝 (2:ℂ)] fun z => z - (z-1)*z*mellin fracMellinFun (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    exact zeta_mellin_right z hz
  have hh := hZ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [mellin_frac_eq, fracPart] using hh

/-- Uniform polynomial growth of the entire pole-removed zeta function on
the half-plane containing the nonprincipal character strip. -/
theorem zeta_pole_removed_norm_le_on_strip (s : ℂ) (hs : 1 / 8 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 9 * (1 + ‖s‖)^2 := by
  have hs' : 0 < s.re := by linarith
  have he : -(s.re+1) < -1 := by linarith
  have hI : ‖∫ t in Set.Ioi (1:ℝ), fracPart t * (t:ℂ)^(-(s+1))‖ ≤ 8 := by
    calc
      _ ≤ ∫ t in Set.Ioi (1:ℝ), t ^ (-(s.re+1)) := by
        apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        exact frac_kernel_bound s ht
      _ ≤ 8 := by
        rw [integral_Ioi_rpow_of_lt he zero_lt_one, Real.one_rpow,
          show -(s.re+1)+1 = -s.re by ring, neg_div_neg_eq, div_le_iff₀ hs']
        linarith
  rw [zeta_pole_removed_eq_floor_integral s hs']
  apply (norm_sub_le ..).trans
  rw [norm_mul, norm_mul]
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1:ℂ)
  calc
    _ ≤ ‖s‖ + (‖s‖ + 1) * ‖s‖ * 8 := by
      gcongr
      exact hI
    _ ≤ _ := by nlinarith [sq_nonneg ‖s‖, norm_nonneg s]

/-- The entire continuation of the completed xi function at both poles. -/
noncomputable def completedXi (s : ℂ) : ℂ :=
  (1 + s*(s-1)*completedRiemannZeta₀ s)/2

noncomputable def centeredXi (z : ℂ) : ℂ := completedXi (z+1/2)

theorem differentiable_completedXi : Differentiable ℂ completedXi := by
  unfold completedXi
  have hd := differentiable_completedZeta₀
  fun_prop

theorem differentiable_centeredXi : Differentiable ℂ centeredXi :=
  differentiable_completedXi.comp (differentiable_id.add_const _)

theorem completedXi_one_sub (s : ℂ) : completedXi (1-s) = completedXi s := by
  simp only [completedXi, completedRiemannZeta₀_one_sub]
  ring

theorem centeredXi_neg (z : ℂ) : centeredXi (-z) = centeredXi z := by
  simpa only [centeredXi, show -z+1/2 = 1-(z+1/2) by ring] using completedXi_one_sub (z+1/2)

theorem completedXi_eq_zeta₁_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    completedXi s = s * riemannZeta₁ s * Gammaℝ s / 2 := by
  by_cases h₁ : s = 1
  · simp [completedXi, h₁, riemannZeta₁_one, Gammaℝ_one]
  have h₀ : s ≠ 0 := by intro h; simp [h] at hs
  have hr : riemannZeta₁ s = (s-1)*riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul h₁, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h₁), one_mul]
  rw [completedXi, hr, riemannZeta_def_of_ne_zero h₀, completedRiemannZeta_eq]
  field_simp [h₀, sub_ne_zero.mpr (Ne.symm h₁), Gammaℝ_ne_zero_of_re_pos hs]
  ring

theorem centeredXi_zero_ne : centeredXi 0 ≠ 0 := by
  let a : ℂ := 1/2
  let f (t : ℝ) : ℝ := (t-(⌊t⌋₊:ℝ)) * t^(-(3/2):ℝ)
  have hId : (∫ t in Ioi (1:ℝ), ((t - (⌊t⌋₊:ℝ) : ℝ) : ℂ) * (t:ℂ)^(-(a+1))) =
      ((∫ t in Ioi (1:ℝ), f t : ℝ):ℂ) := by
    rw [← integral_complex_ofReal (f:=f) (μ:=volume.restrict (Ioi 1))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have he : -(a+1) = ((-(3/2):ℝ):ℂ) := by norm_num [a]
    have ht0 : 0 ≤ t := by linarith [show 1<t from ht]
    simp only [he, f, Complex.ofReal_mul, Complex.ofReal_cpow ht0]
  have hpos : 0 ≤ ∫ t in Ioi (1:ℝ), f t := setIntegral_nonneg measurableSet_Ioi
    (fun t ht => mul_nonneg (Nat.zero_le_self_sub_floor (by linarith [show 1 < t from ht]))
      (Real.rpow_nonneg (by linarith [show 1 < t from ht]) _))
  have ha : 0 < a.re := by norm_num [a]
  have hζ : riemannZeta₁ a ≠ 0 := by
    rw [zeta_pole_removed_eq_floor_integral a ha, hId]
    intro h
    have hh := congrArg Complex.re h
    norm_num [a,Complex.sub_re, Complex.mul_re] at hh
    linarith
  change completedXi (0+1/2) ≠ 0
  rw [zero_add]
  change completedXi a ≠ 0
  rw [completedXi_eq_zeta₁_Gammaℝ ha]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num [a]) hζ) (Gammaℝ_ne_zero_of_re_pos ha))
    (by norm_num)

theorem gamma_upper_by_factorial {s : ℂ} {n : ℕ} (h₀ : 1/4 ≤ s.re) (h₁ : s.re ≤ n+1) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (1/4) + (n.factorial:ℝ) := by
  let g (b t : ℝ) := Real.exp (-t) * t^(b-1)
  have hsmall : IntegrableOn (g (1/4)) (Ioi 0) := Real.GammaIntegral_convergent (by norm_num)
  have hlarge : IntegrableOn (g (n+1)) (Ioi 0) := Real.GammaIntegral_convergent (by positivity)
  rw [Complex.Gamma_eq_integral (by linarith), Complex.GammaIntegral]
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), g (1/4) t + g (n+1) t := by
      apply norm_integral_le_of_norm_le (hsmall.add hlarge)
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
      dsimp only [g, Pi.add_apply]
      have hl := Real.rpow_nonneg ht.le ((1:ℝ)/4 - 1)
      have hr := Real.rpow_nonneg ht.le ((n:ℝ)+1-1)
      rcases le_total t 1 with h | h
      · have hL := Real.rpow_le_rpow_of_exponent_ge ht h (sub_le_sub_right h₀ 1)
        exact (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le).trans
          (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le hr))
      · have hR := Real.rpow_le_rpow_of_exponent_le h (sub_le_sub_right h₁ 1)
        exact (mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le).trans
          (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hl))
    _ = _ := by
      rw [integral_add hsmall hlarge, ← Real.Gamma_nat_eq_factorial,
        Real.Gamma_eq_integral (by norm_num : 0 < (1:ℝ)/4), Real.Gamma_eq_integral (by positivity : 0 < (n:ℝ)+1)]

private theorem centeredXi_norm_right {R : ℝ} (hR : 1 ≤ R) {z : ℂ}
    (hz : ‖z‖ ≤ R) (hzr : 0 ≤ z.re) :
    ‖centeredXi z‖ ≤ (9 * (Real.Gamma (1/4)+1)) * (3*R)^(6*R : ℝ) := by
  let s := z+1/2
  let n := ⌈R⌉₊ + 1
  let V := 3*R
  have hV : 1 ≤ V := by dsimp only [V]; linarith
  have hRpos : 0 < R := by linarith
  have hsn : ‖s‖ ≤ R+1/2 := by
    calc ‖s‖ ≤ ‖z‖+‖(1/2:ℂ)‖ := norm_add_le .. 
         _ ≤ _ := by norm_num; linarith
  have hsR : 1/2 ≤ s.re := by simp [s]; linarith
  have hsh : (1:ℝ)/4 ≤ (s/2).re := by rw [Complex.div_ofNat_re]; linarith
  have hbig : (s/2).re ≤ (n:ℝ)+1 := by
    rw [Complex.div_ofNat_re]
    dsimp only [n]; push_cast
    linarith [Complex.re_le_norm s, Nat.le_ceil R]
  have hnV : (n:ℝ) ≤ V := by
    dsimp [n,V]; push_cast
    linarith [Nat.ceil_lt_add_one hRpos.le]
  have hfactor : (n.factorial:ℝ) ≤ V^V := calc
    _ ≤ (n:ℝ)^n := by exact_mod_cast n.factorial_le_pow
    _ ≤ V^n := pow_le_pow_left₀ (Nat.cast_nonneg _) hnV n
    _ = V^(n:ℝ) := (Real.rpow_natCast ..).symm
    _ ≤ V^V := Real.rpow_le_rpow_of_exponent_le hV hnV
  have hVpow : 1 ≤ V^V := Real.one_le_rpow hV (by linarith)
  have hΓq := (Real.Gamma_pos_of_pos (by norm_num : 0<(1:ℝ)/4)).le
  have hg : ‖Gammaℝ s‖ ≤ (Real.Gamma (1/4)+1)*V^V := by
    have hπ : ‖(Real.pi:ℂ)^(-s/2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      rw [Complex.div_ofNat_re, Complex.neg_re]
      linarith
    rw [Gammaℝ, norm_mul]
    calc
      _ ≤ ‖Complex.Gamma (s/2)‖ := mul_le_of_le_one_left (norm_nonneg _) hπ
      _ ≤ Real.Gamma (1/4) + (n.factorial:ℝ) := gamma_upper_by_factorial hsh hbig
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hVpow hΓq]
  have hζ := zeta_pole_removed_norm_le_on_strip s (by linarith)
  have hS : ‖s‖ ≤ V := by dsimp [V]; linarith
  have hS' : 1+‖s‖ ≤ V := by dsimp [V]; linarith
  change ‖completedXi s‖ ≤ _
  rw [completedXi_eq_zeta₁_Gammaℝ (by linarith), norm_div, norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ ‖s‖ * ‖riemannZeta₁ s‖ * ‖Gammaℝ s‖ :=
      div_le_self (by positivity) (by norm_num)
    _ ≤ V * (9*V^2) * ((Real.Gamma (1/4)+1)*V^V) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by positivity [hV])
      exact mul_le_mul hS (hζ.trans (by gcongr)) (norm_nonneg _) (by linarith)
    _ = (9 * (Real.Gamma (1/4)+1)) * V^((3:ℝ)+V) := by
      rw [Real.rpow_add (by linarith : 0<V), show V^(3:ℝ) = V^(3:ℕ) by norm_cast]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [hΓq])
      exact Real.rpow_le_rpow_of_exponent_le hV (by dsimp [V]; linarith)

/-- An explicit subquadratic logarithmic growth envelope on every centered
disk. The estimate on its left half follows from the xi functional equation. -/
theorem centeredXi_subquadratic_growth :
    ∃ L : ℝ → ℝ, (∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R → ‖centeredXi z‖ ≤ Real.exp (L R)) ∧
      Tendsto (fun R : ℝ => L R / R^2) atTop (𝓝 0) := by
  let C := 9*(Real.Gamma (1/4)+1)
  have hC : 0 < C := by
    dsimp [C]
    positivity [Real.Gamma_pos_of_pos (by norm_num : 0 < (1:ℝ)/4)]
  refine ⟨fun R => Real.log C + 6*R*Real.log (3*R), ?_, ?_⟩
  · intro R hR z hz
    have H : ‖centeredXi z‖ ≤ C * (3*R)^(6*R : ℝ) := by
      rcases le_total 0 z.re with h | h
      · exact centeredXi_norm_right hR hz h
      · rw [← centeredXi_neg z]
        exact centeredXi_norm_right hR (by simpa using hz) (by simpa using h)
    rw [Real.exp_add, Real.exp_log hC, mul_comm (6*R), ← Real.rpow_def_of_pos (by linarith : 0 < 3*R)]
    exact H
  · have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hl : Tendsto (fun R : ℝ => Real.log R/R) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hh := ((hi.pow 2).const_mul (Real.log C)).add
      (((hi.const_mul (Real.log 3)).add hl).const_mul 6)
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    rw [Real.log_mul (by norm_num) hR.ne']
    field_simp

theorem completedXi_zero_iff_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedXi s = 0 ↔ riemannZeta s = 0 := by
  by_cases h₁ : s = 1
  · simp [h₁, completedXi, riemannZeta_one_ne_zero]
  have h₀ : s ≠ 0 := by intro h; simp [h] at hs
  have hr : riemannZeta₁ s = (s-1)*riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul h₁, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h₁), one_mul]
  simp [completedXi_eq_zeta₁_Gammaℝ hs, hr, sub_ne_zero.mpr h₁, h₀, Gammaℝ_ne_zero_of_re_pos hs]

/-- Every zero of centered xi lies on the imaginary axis under RH. -/
theorem centeredXi_zero_re (hRH : RiemannHypothesis) {z : ℂ} (hz : centeredXi z = 0) :
    z.re = 0 := by
  have right (w : ℂ) (hw : 0 ≤ w.re) (h0 : centeredXi w = 0) : w.re = 0 := by
    let s := w + 1/2
    have hσ : s.re = w.re+1/2 := by simp [s]
    have hpos : 0 < s.re := by linarith
    have hζ := (completedXi_zero_iff_of_re_pos hpos).mp h0
    have hnot : ¬∃ n : ℕ, s = -2 * (n+1) := by
      rintro ⟨n,he⟩
      have hh := congrArg Complex.re he
      norm_num [Complex.mul_re] at hh
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hs1 : s ≠ 1 := by intro h; exact riemannZeta_one_ne_zero (h ▸ hζ)
    linarith [hRH s hζ hnot hs1]
  rcases le_total 0 z.re with h | h
  · exact right z h hz
  · simpa using right (-z) (by simpa using h) (by simpa [centeredXi_neg] using hz)

/-- The shift to centered xi preserves the analytic multiplicity at every
nontrivial zeta zero. -/
theorem centeredXi_order_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    analyticOrderNatAt centeredXi (s-1/2) = analyticOrderNatAt riemannZeta s := by
  let A (w : ℂ) := w*(w-1)*Gammaℝ w / 2
  have hgamma : AnalyticAt ℂ Gammaℝ s := by
    have h := (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
    change AnalyticAt ℂ (fun w => (Gammaℝ w)⁻¹⁻¹) s at h
    simpa only [inv_inv] using h
  have ha : AnalyticAt ℂ A s := by dsimp only [A]; fun_prop
  have h₀ : s ≠ 0 := by intro h; simp [h] at hs
  have hAn : A s ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero h₀ (sub_ne_zero.mpr hs₁))
    (Gammaℝ_ne_zero_of_re_pos hs)) (by norm_num)
  have heq : completedXi =ᶠ[𝓝 s] fun w => A w * riemannZeta w := by
    filter_upwards [(continuous_re.isOpen_preimage (Ioi (0:ℝ)) isOpen_Ioi).mem_nhds hs,
      compl_singleton_mem_nhds hs₁] with w hw hw'
    have hn : w ≠ 1 := hw'
    have hreg : riemannZeta₁ w = (w-1)*riemannZeta w := by
      rw [riemannZeta_eq_inv_sub_mul hn, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
    rw [completedXi_eq_zeta₁_Gammaℝ hw, hreg]
    dsimp only [A]
    ring
  let g (w : ℂ) := w+1/2
  have hg : AnalyticAt ℂ g (s-1/2) := by dsimp only [g]; fun_prop
  have hgd : deriv g (s-1/2) ≠ 0 := by simp [g]
  unfold analyticOrderNatAt
  change (analyticOrderAt (completedXi ∘ g) (s-1/2)).toNat = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg hgd, show g (s-1/2)=s by simp [g],
    analyticOrderAt_congr heq, analyticOrderAt_fun_mul ha (analyticOn_riemannZeta s hs₁),
    ha.analyticOrderAt_eq_zero.mpr hAn, zero_add]

end

section

open Complex ArithmeticFunction

private theorem log_le_sqrt_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  have he := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (div_pos hs he)
  rw [Real.log_div hs.ne' he.ne', Real.log_sqrt hx.le, Real.log_exp] at h
  have hh : Real.sqrt x / Real.exp 1 ≤ Real.sqrt x / 2 :=
    div_le_div_of_nonneg_left hs.le (by norm_num) Real.exp_one_gt_two.le
  linarith

/-- On the whole vertical line of real part 5/2 the Dirichlet series of
the negative logarithmic derivative is absolutely bounded by the Basel tail. -/
theorem zeta_logDeriv_norm_le_five_halves {s : ℂ} (hs : s.re = 5/2) :
    ‖logDeriv riemannZeta s‖ ≤ 3/4 := by
  have hs' : 1 < s.re := by rw [hs]; norm_num
  let f := LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) s
  have hf : Summable f := LSeriesSummable_vonMangoldt hs'
  have hzero : ‖logDeriv riemannZeta s‖ = ‖∑' n, f n‖ := by
    have hz := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'
    change (∑' n, f n) = _ at hz
    rw [hz, neg_div, norm_neg]
    rfl
  have hg := hasSum_zeta_two.sub (hasSum_ite_eq (1:ℕ) (1:ℝ))
  have hterm (n : ℕ) : ‖f n‖ ≤ 1/(n:ℝ)^2 - (if n=1 then 1 else 0) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    rcases eq_or_ne n 1 with rfl | hn₁
    · simp [f]
    have hnpos : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [f, LSeries.norm_term_eq, ite_eq_right hn, hs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, ite_eq_right hn₁, sub_zero]
    calc
      _ ≤ Real.sqrt n / (n:ℝ)^(5/2:ℝ) :=
        div_le_div_of_nonneg_right (vonMangoldt_le_log.trans (log_le_sqrt_pos hnpos)) (by positivity)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, show (5:ℝ)/2 = 1/2+2 by norm_num,
          Real.rpow_add hnpos, Real.rpow_two]
        field_simp
  rw [hzero]
  apply (norm_tsum_le_tsum_norm hf.norm).trans
  apply (hasSum_le hterm hf.norm.hasSum hg).trans
  nlinarith [Real.pi_lt_d2, sq_nonneg (Real.pi - 3.15),
    mul_self_le_mul_self Real.pi_nonneg Real.pi_lt_d2.le]

end

end GoldbachShortInterval

namespace GoldbachShortInterval

open Set Complex MeasureTheory

noncomputable def perronWeight (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => 1 - (x : ℂ)) t

theorem perronWeight_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin perronWeight s (1 / (s * (s + 1))) := by
  have h₁ := hasMellin_one_Ioc hs
  have h₂ := hasMellin_cpow_Ioc 1 (s := s) (by simp; linarith)
  have h := hasMellin_sub h₁.1 h₂.1
  rw [h₁.2, h₂.2] at h
  have hfun : (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
      (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) = perronWeight := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [perronWeight, ht]
  rw [hfun] at h
  convert h using 1
  have hz : s ≠ 0 := by intro h; simp [h] at hs
  have ho : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  field_simp
  ring

/-- The inverse Mellin transform on the line of real part two gives the usual
linear smoothing of a sharp cutoff. -/
theorem perronWeight_inversion {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / (s * (s + 1))) x = perronWeight x := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  have hline (t : ℝ) : (s t).re = 2 := by simp [s]
  have htransform (t : ℝ) : mellin perronWeight (s t) = 1 / (s t * (s t + 1)) :=
    (perronWeight_hasMellin (by rw [hline]; norm_num)).2
  have hb (t : ℝ) : 1 + t ^ 2 ≤ ‖s t‖ * ‖s t + 1‖ := by
    have h1 := Complex.sq_norm (s t)
    have h2 := Complex.sq_norm (s t + 1)
    simp [s, Complex.normSq_apply] at h1 h2
    have hn : ‖s t‖ ≤ ‖s t + 1‖ := by nlinarith [norm_nonneg (s t + 1)]
    nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (s t))]
  have hv : VerticalIntegrable (mellin perronWeight) 2 := by
    change Integrable fun y : ℝ => mellin perronWeight (s y)
    simp_rw [htransform]
    apply integrable_inv_one_add_sq.mono'
    · exact (by fun_prop : Measurable (fun y : ℝ => 1 / (s y * (s y + 1)))).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      rw [norm_div, norm_one, norm_mul, one_div]
      exact inv_anti₀ (by positivity) (hb t)
  have hcont : ContinuousAt perronWeight x := by
    have heq : perronWeight =ᶠ[nhds x] fun u : ℝ => ((max (1-u) 0 : ℝ) : ℂ) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      by_cases h : y ≤ 1
      · simp [perronWeight, hy, h]
      · simp [perronWeight, h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    exact (by fun_prop : ContinuousAt (fun u : ℝ => ((max (1-u) 0 : ℝ) : ℂ)) x).congr_of_eventuallyEq heq
  have hi := mellinInv_mellin_eq 2 perronWeight hx (perronWeight_hasMellin (by norm_num)).1 hv hcont
  unfold mellinInv at hi ⊢
  simpa only [show ∀ t : ℝ, mellin perronWeight ((2 : ℝ) + (t : ℂ) * I) =
      1 / (((2 : ℝ) + (t : ℂ) * I) * (((2 : ℝ) + (t : ℂ) * I) + 1)) from htransform] using hi

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex MeasureTheory Filter ArithmeticFunction DirichletCharacter Finset

private noncomputable def perronLine (t : ℝ) : ℂ := 2 + (t : ℂ) * I

private theorem perronLine_re (t : ℝ) : (perronLine t).re = 2 := by simp [perronLine]

private noncomputable def perronKernelAt (s : ℂ) := 1 / (s * (s + 1))

private theorem perronKernel_integrable : Integrable (fun t : ℝ => perronKernelAt (perronLine t)) := by
  apply integrable_inv_one_add_sq.mono'
  · exact (by unfold perronKernelAt perronLine; fun_prop : Measurable _).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have h1 : ‖perronLine t‖ ^ 2 = 2 * 2 + t * t := by
    simpa [perronLine, Complex.normSq_apply] using Complex.sq_norm (perronLine t)
  have h2 : ‖perronLine t + 1‖ ^ 2 = (2+1) * (2+1) + t * t := by
    simpa [perronLine, Complex.normSq_apply] using Complex.sq_norm (perronLine t + 1)
  have hn : ‖perronLine t‖ ≤ ‖perronLine t + 1‖ := by nlinarith [norm_nonneg (perronLine t + 1)]
  rw [perronKernelAt, norm_div, norm_one, norm_mul, one_div]
  apply inv_anti₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (perronLine t))]

theorem smoothed_lseries_perron (a : ℕ → ℂ) (ha₀ : a 0 = 0) (ha : LSeriesSummable a 2)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => LSeries a s * (1 / (s * (s + 1)))) x =
      ∑' n : ℕ, a n * perronWeight (n * x) := by
  let F (n : ℕ) (t : ℝ) := ((x : ℂ) ^ (-perronLine t) * perronKernelAt (perronLine t)) *
      LSeries.term a (perronLine t) n
  let b (n : ℕ) := x ^ (-2 : ℝ) * ‖LSeries.term a 2 n‖
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = b n * ‖perronKernelAt (perronLine t)‖ := by
    simp only [F, b, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, perronLine_re,
      LSeries.norm_term_eq, re_ofNat]
    ring
  have hmeas (n : ℕ) : Measurable (F n) := by
    simp only [F, perronKernelAt, perronLine, LSeries.term_def₀ ha₀]
    fun_prop
  have hi (n : ℕ) : Integrable (F n) := by
    apply (perronKernel_integrable.norm.const_mul (b n)).mono' (hmeas n).aestronglyMeasurable
    exact Eventually.of_forall fun t => (hnorm n t).le
  have hs : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact (ha.norm.mul_left (x ^ (-2 : ℝ))).mul_right _
  have hsum (t : ℝ) : (∑' n, F n t) =
      (x : ℂ) ^ (-perronLine t) * (LSeries a (perronLine t) * perronKernelAt (perronLine t)) := by
    rw [show (∑' n, F n t) = _ from tsum_mul_left]
    change _ * LSeries a (perronLine t) = _
    ring
  have hsingle (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, F n t) =
      a n * perronWeight (n * x) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha₀]
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hfun (t : ℝ) : F n t = a n * ((((n : ℝ) * x : ℝ) : ℂ) ^ (-perronLine t) *
          perronKernelAt (perronLine t)) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn'.le hx.le]
      simp only [F, LSeries.term_def₀ ha₀, Complex.ofReal_natCast]
      ring
    rw [← perronWeight_inversion (mul_pos hn' hx)]
    unfold mellinInv
    simp_rw [hfun]
    rw [integral_const_mul]
    change _ • (a n * _) = a n * (_ • _)
    rw [mul_smul_comm]
    rfl
  have hsm := (hasSum_integral_of_summable_integral_norm hi hs).const_smul
    (1 / (2 * Real.pi) : ℝ)
  simp_rw [hsingle, hsum] at hsm
  exact hsm.tsum_eq.symm

theorem twisted_smoothed_perron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) :
    mellinInv 2 (fun s : ℂ => (-deriv (LFunction χ) s / LFunction χ s) *
      (1 / (s * (s + 1)))) (1 / X) =
    ∑ n ∈ Icc 1 ⌊X⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ) * (1 - (n : ℂ) / (X : ℂ)) := by
  let a (n : ℕ) := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have ha₀ : a 0 = 0 := by simp [a]
  have ha : LSeriesSummable a 2 := LSeriesSummable_twist_vonMangoldt χ (by norm_num)
  calc
    _ = mellinInv 2 (fun s => LSeries a s * (1 / (s * (s + 1)))) (1 / X) := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      have hs : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by norm_num
      dsimp only
      rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
        ← LSeries_twist_vonMangoldt_eq χ hs]
      rfl
    _ = ∑' n : ℕ, a n * perronWeight ((n : ℝ) * (1 / X)) :=
      smoothed_lseries_perron a ha₀ ha (one_div_pos.mpr hX)
    _ = _ := by
      rw [tsum_eq_sum (s := Icc 1 ⌊X⌋₊) (fun n hn => ?_)]
      · apply sum_congr rfl
        intro n hn
        obtain ⟨hnp, hnf⟩ := mem_Icc.mp hn
        have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hnp
        have hnx : (n : ℝ) ≤ X := (Nat.le_floor_iff hX.le).mp hnf
        have hm : (n : ℝ) * (1 / X) ∈ Set.Ioc (0 : ℝ) 1 := by
          rw [mul_one_div]
          exact ⟨div_pos hnℝ hX, (div_le_one hX).mpr hnx⟩
        rw [perronWeight, Set.indicator_of_mem hm]
        simp only [mul_one_div, Complex.ofReal_div, Complex.ofReal_natCast, a]
      · by_cases hz : n = 0
        · simp [hz, ha₀]
        · have hn' : ⌊X⌋₊ < n := by
            by_contra! h
            exact hn (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz, h⟩)
          have hx : X < (n : ℝ) := (Nat.floor_lt hX.le).mp hn'
          have hm : (n : ℝ) * (1 / X) ∉ Set.Ioc (0 : ℝ) 1 := by
            intro h
            rw [mul_one_div] at h
            exact (not_le.mpr hx) ((div_le_one hX).mp h.2)
          rw [perronWeight, Set.indicator_of_notMem hm, mul_zero]

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex ArithmeticFunction DirichletCharacter MeasureTheory Filter
open scoped BigOperators Topology

noncomputable def negLogL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv χ.LFunction s / χ.LFunction s

noncomputable def rightLineBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) 2 n‖

theorem rightLineBound_nonneg : 0 ≤ rightLineBound := tsum_nonneg fun _ => norm_nonneg _

theorem negLogL_bound_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 2) : ‖negLogL χ s‖ ≤ rightLineBound := by
  have h : 1 < s.re := by linarith
  rw [negLogL, deriv_LFunction_eq_deriv_LSeries χ h, LFunction_eq_LSeries χ h,
    ← LSeries_twist_vonMangoldt_eq χ h]
  apply (norm_tsum_le_tsum_norm (LSeriesSummable_twist_vonMangoldt χ h).norm).trans
  apply Summable.tsum_le_tsum _ (LSeriesSummable_twist_vonMangoldt χ h).norm
    (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  intro n
  simp only [LSeries.norm_term_eq, hs, Complex.re_ofNat]
  split_ifs
  · rfl
  · apply div_le_div_of_nonneg_right _ (by positivity)
    change ‖χ (n : ZMod q) * (vonMangoldt n : ℂ)‖ ≤ ‖(vonMangoldt n : ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

noncomputable def verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

theorem continuous_verticalPoint (σ : ℝ) : Continuous (verticalPoint σ) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

set_option maxHeartbeats 1000000 in
theorem negLogL_continuous_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => negLogL χ (verticalPoint 2 t)) := by
  let U := ({1}ᶜ : Set ℂ)
  have ha : AnalyticOnNhd ℂ χ.LFunction U :=
    (show DifferentiableOn ℂ χ.LFunction U from fun w hw =>
      (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
      isOpen_compl_singleton
  apply continuous_iff_continuousAt.mpr
  intro t
  let s := verticalPoint 2 t
  have hre : s.re = 2 := by simp [s, verticalPoint]
  have hs : s ≠ 1 := by intro he; simp [he] at hre
  have hn := LFunction_ne_zero_of_one_le_re χ (s := s) (Or.inr hs) (by linarith)
  have h : AnalyticAt ℂ χ.LFunction s := ha s hs
  have hC : ContinuousAt (fun w => -deriv χ.LFunction w / χ.LFunction w) s :=
    h.deriv.continuousAt.neg.div h.continuousAt hn
  exact ContinuousAt.comp (x := t) hC (continuous_verticalPoint 2).continuousAt

theorem right_denominator (t : ℝ) :
    1 + t ^ 2 ≤ ‖verticalPoint 2 t‖ * ‖verticalPoint 2 t + 1‖ := by
  let s := verticalPoint 2 t
  have ha : ‖s‖^2 = 2*2 + t*t := by
    simpa [s, verticalPoint, Complex.normSq_apply] using Complex.sq_norm s
  have hb : ‖s+1‖^2 = (2+1)*(2+1) + t*t := by
    simpa [s, verticalPoint, Complex.normSq_apply] using Complex.sq_norm (s+1)
  have h : ‖s‖ ≤ ‖s+1‖ := by nlinarith [norm_nonneg (s+1)]
  change _ ≤ ‖s‖ * ‖s+1‖
  nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg s)]

private noncomputable def perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) : ℂ :=
  let s := verticalPoint 2 t
  negLogL χ s * (x : ℂ) ^ (s + 1) / (s * (s+1))

private theorem perronTerm_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖perronTerm χ x t‖ ≤ (rightLineBound * x^3) * (1 + t^2)⁻¹ := by
  let s := verticalPoint 2 t
  have hs : s.re = 2 := by simp [s, verticalPoint]
  have hn := negLogL_bound_right χ hs
  have hd := right_denominator t
  change 1 + t^2 ≤ ‖s‖ * ‖s+1‖ at hd
  simp only [perronTerm, ← show s = verticalPoint 2 t from rfl, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re, hs]
  norm_num
  rw [← div_eq_mul_inv]
  apply div_le_div₀ (by positivity [rightLineBound_nonneg]) _ (by positivity) hd
  exact mul_le_mul_of_nonneg_right hn (by positivity)

private theorem perronTerm_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) : Integrable (perronTerm χ x) := by
  apply (integrable_inv_one_add_sq.const_mul (rightLineBound * x^3)).mono'
  · unfold perronTerm
    have h := (negLogL_continuous_right χ).measurable
    have v := (continuous_verticalPoint 2).measurable
    have hw : Measurable (fun t : ℝ => (x : ℂ) ^ (verticalPoint 2 t + 1)) := by
      unfold verticalPoint
      fun_prop
    exact ((h.mul hw).div
      (v.mul (v.add measurable_const))).aestronglyMeasurable
  exact Eventually.of_forall (perronTerm_bound χ hx)

noncomputable def shortTriangle (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, vonMangoldt n * (y-n)

noncomputable def smoothPsi (η y : ℝ) : ℝ :=
  (shortTriangle ((1+η)*y) - shortTriangle y) / (η*y)

noncomputable def perronSmoothingFactor (η : ℝ) (s : ℂ) : ℂ :=
  (((1+η : ℝ) : ℂ)^(s+1)-1) / ((η:ℂ)*(s+1))

noncomputable def smoothedIncrementKernel (η δ y : ℝ) (s : ℂ) : ℂ :=
  (y:ℂ)^s * ((((1+δ : ℝ) : ℂ)^s-1)/s) * perronSmoothingFactor η s

private theorem shortTriangle_line {y : ℝ} (hy : 0 < y) :
    (shortTriangle y : ℂ) = (1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
      perronTerm (1 : DirichletCharacter ℂ 1) y t := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hM := twisted_smoothed_perron χ hy
  have hI : Finset.Icc 1 ⌊y⌋₊ = Finset.Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have he : (shortTriangle y : ℂ) = (y:ℂ) * mellinInv 2 (fun s : ℂ =>
      (-deriv (LFunction χ) s / LFunction χ s) * (1/(s*(s+1)))) (1/y) := by
    rw [hM,hI,Finset.mul_sum]
    unfold shortTriangle
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [DirichletCharacter.modOne_eq_one',one_mul]
    have hyn : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp
  rw [he,mellinInv,mul_smul_comm,← integral_const_mul]
  apply congrArg (fun z : ℂ => (1/(2*Real.pi):ℝ) • z)
  apply integral_congr_ae
  filter_upwards with t
  let s := verticalPoint 2 t
  change (y : ℂ) * (((1/y : ℝ) : ℂ)^(-s) * (negLogL χ s * (1/(s*(s+1))))) = _
  have hyn : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [one_div,Complex.ofReal_inv,Complex.cpow_neg,Complex.inv_cpow_ofReal_nonneg hy.le]
  change _ = negLogL χ s * (y:ℂ)^(s+1) / _
  rw [Complex.cpow_add _ _ hyn,Complex.cpow_one]
  simp only [inv_inv]
  ring

/-- Both one-sided smoothing errors are nonnegative. An interval of length
at most one contributes at most one additional von Mangoldt term. -/
theorem smoothPsi_error_bounds {η y : ℝ} (hη : 0 < η) (hy : 0 < y) (hshort : η*y ≤ 1) :
    0 ≤ smoothPsi η y - Chebyshev.psi y ∧
      smoothPsi η y - Chebyshev.psi y ≤ Real.log (y+1) := by
  let b := (1+η)*y
  let N := ⌊y⌋₊
  have hby : y ≤ b := by dsimp [b]; nlinarith only [(mul_pos hη hy).le]
  have hby' : b ≤ y+1 := by dsimp [b]; linarith only [hshort]
  have hN : N ≤ ⌊b⌋₊ := Nat.floor_mono hby
  have hN' : ⌊b⌋₊ ≤ N+1 := by
    simpa only [N,Nat.floor_add_one hy.le] using Nat.floor_mono hby'
  have hsum : (∑ n ∈ Finset.Ioc 0 N, vonMangoldt n * (b-n)) -
      (∑ n ∈ Finset.Ioc 0 N, vonMangoldt n * (y-n)) = η*y * Chebyshev.psi y := by
    rw [Chebyshev.psi,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [b]
    ring
  have hd := mul_pos hη hy
  change 0 ≤ (shortTriangle b-shortTriangle y)/(η*y)-_ ∧
    (shortTriangle b-shortTriangle y)/(η*y)-_ ≤ _
  unfold shortTriangle
  change 0 ≤ ((∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, _) - ∑ n ∈ Finset.Ioc 0 N, _)/(η*y)-_ ∧ _ ≤ _
  have hlog : 0 ≤ Real.log (y+1) := Real.log_nonneg (by linarith)
  rcases show ⌊b⌋₊ = N ∨ ⌊b⌋₊ = N+1 by omega with h|h
  · rw [h,hsum,mul_div_cancel_left₀ _ hd.ne',sub_self]
    exact ⟨le_rfl,hlog⟩
  · rw [h,Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    have hz : (N:ℝ)+1 ≤ b := by
      have hh : ((N+1:ℕ):ℝ) ≤ b := (Nat.le_floor_iff (hy.le.trans hby)).mp h.ge
      exact_mod_cast hh
    have hn' : y < (N:ℝ)+1 := Nat.lt_floor_add_one y
    let err := vonMangoldt (N+1)*(b-((N:ℝ)+1))/(η*y)
    have herr : 0 ≤ err := div_nonneg (mul_nonneg (vonMangoldt_nonneg) (sub_nonneg.mpr hz)) hd.le
    have herr' : err ≤ vonMangoldt (N+1) := by
      apply (div_le_iff₀ hd).2
      apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
      dsimp only [b]
      linarith only [hn'.le]
    have hlog' : vonMangoldt (N+1) ≤ Real.log (y+1) := by
      apply vonMangoldt_le_log.trans
      apply Real.log_le_log (by positivity)
      push_cast
      linarith [show (N:ℝ) ≤ y from Nat.floor_le hy.le]
    have he : ((∑ n ∈ Finset.Ioc 0 N, vonMangoldt n*(b-n)) +
        vonMangoldt (N+1)*(b-((N+1:ℕ):ℝ)) -
        (∑ n ∈ Finset.Ioc 0 N, vonMangoldt n*(y-n)))/(η*y)-Chebyshev.psi y = err := by
      dsimp only [err]
      push_cast
      field_simp
      linarith only [hsum]
    rw [he]
    exact ⟨herr,herr'.trans hlog'⟩

private noncomputable def slopeIntegrand (η y : ℝ) (t : ℝ) : ℂ :=
  (perronTerm (1 : DirichletCharacter ℂ 1) ((1+η)*y) t -
    perronTerm (1 : DirichletCharacter ℂ 1) y t)/((η:ℂ)*(y:ℂ))

private theorem slopeIntegrand_integrable {η y : ℝ} (hη : 0 < η) (hy : 0 < y) :
    Integrable (slopeIntegrand η y) := by
  exact ((perronTerm_integrable (1 : DirichletCharacter ℂ 1)
    (mul_pos (by linarith : 0 < 1+η) hy)).sub (perronTerm_integrable _ hy)).div_const _

private theorem smoothPsi_line {η y : ℝ} (hη : 0 < η) (hy : 0 < y) :
    (smoothPsi η y : ℂ) = (1/(2*Real.pi) : ℝ) • ∫ t : ℝ, slopeIntegrand η y t := by
  have hb : 0 < (1+η)*y := mul_pos (by linarith) hy
  unfold smoothPsi slopeIntegrand
  rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul, shortTriangle_line hb,
    shortTriangle_line hy, integral_div, integral_sub (perronTerm_integrable _ hb)
      (perronTerm_integrable _ hy), ← smul_sub, smul_div_assoc]

private theorem slopeIntegrand_eq {η y : ℝ} (hy : 0 < y) (hη : 0 < η) (t : ℝ) :
    let s := verticalPoint 2 t
    slopeIntegrand η y t = (-deriv riemannZeta s / riemannZeta s) *
      (y:ℂ)^s / s * perronSmoothingFactor η s := by
  let s := verticalPoint 2 t
  have hy' : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hx : 0 ≤ 1+η := by linarith
  unfold slopeIntegrand perronTerm negLogL perronSmoothingFactor
  simp only [DirichletCharacter.LFunction_modOne_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx hy.le, Complex.cpow_add _ _ hy', Complex.cpow_one]
  field_simp
  ring

noncomputable def smoothedPerronIntegrand (η δ y : ℝ) (t : ℝ) : ℂ :=
  let s := verticalPoint 2 t
  (-deriv riemannZeta s / riemannZeta s) * smoothedIncrementKernel η δ y s

private theorem smoothedPerronIntegrand_eq {η δ y : ℝ} (hη : 0 < η)
    (hδ : 0 ≤ δ) (hy : 0 < y) :
    smoothedPerronIntegrand η δ y = fun t =>
      slopeIntegrand η ((1+δ)*y) t - slopeIntegrand η y t := by
  ext1 t
  have h1 : 0 < 1+δ := by linarith
  rw [slopeIntegrand_eq (mul_pos h1 hy) hη,slopeIntegrand_eq hy hη]
  unfold smoothedPerronIntegrand smoothedIncrementKernel
  simp only [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h1.le hy.le]
  ring

theorem smoothedPerronIntegrand_integrable {η δ y : ℝ} (hη : 0 < η)
    (hδ : 0 ≤ δ) (hy : 0 < y) : Integrable (smoothedPerronIntegrand η δ y) := by
  rw [smoothedPerronIntegrand_eq hη hδ hy]
  exact (slopeIntegrand_integrable hη (mul_pos (by linarith) hy)).sub
    (slopeIntegrand_integrable hη hy)

/-- The right vertical line integral represents the real smoothed ψ increment. -/
theorem smoothPsi_increment_perron {η δ y : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (hy : 0 < y) :
    ((smoothPsi η ((1+δ)*y)-smoothPsi η y : ℝ) : ℂ) =
      (1/(2*Real.pi) : ℝ) • ∫ t : ℝ, smoothedPerronIntegrand η δ y t := by
  have hz := mul_pos (by linarith : 0 < 1+δ) hy
  rw [Complex.ofReal_sub,smoothPsi_line hη hz,smoothPsi_line hη hy,
    smoothedPerronIntegrand_eq hη hδ hy,integral_sub
    (slopeIntegrand_integrable hη hz) (slopeIntegrand_integrable hη hy),smul_sub]

/-- Both truncations may tend to infinity at independently selected safe heights. -/
theorem smoothPsi_increment_perron_truncated {η δ y : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ)
    (hy : 0 < y) {u v : ℕ → ℝ} (hu : Tendsto u atTop atBot) (hv : Tendsto v atTop atTop) :
    Tendsto (fun n => (1/(2*Real.pi):ℝ) •
      ∫ t : ℝ in u n..v n, smoothedPerronIntegrand η δ y t) atTop
      (𝓝 ((smoothPsi η ((1+δ)*y)-smoothPsi η y : ℝ) : ℂ)) := by
  rw [smoothPsi_increment_perron hη hδ hy]
  exact (intervalIntegral_tendsto_integral (smoothedPerronIntegrand_integrable hη hδ hy)
    hu hv).const_smul _

/-- At the common regularization scale, subtracting the two one-sided errors
costs at most the larger single logarithm. -/
theorem smoothPsi_increment_error {x y δ : ℝ} (hx : 0 < x) (hy : 0 < y) (hδ : 0 ≤ δ)
    (hyx : (1+δ)*y ≤ 2*x) :
    let η := 1/(4*x)
    |(smoothPsi η ((1+δ)*y)-smoothPsi η y) - (Chebyshev.psi ((1+δ)*y)-Chebyshev.psi y)| ≤
      Real.log (2*x+1) := by
  let z := (1+δ)*y
  let η := 1/(4*x)
  have hη : 0 < η := by dsimp [η]; positivity
  have hyz : y ≤ z := by dsimp [z]; nlinarith only [mul_nonneg hδ hy.le]
  have hz : 0 < z := hy.trans_le hyz
  have hηz : η*z ≤ 1 := by
    dsimp only [η]
    rw [one_div_mul_eq_div]
    apply (div_le_one (by positivity)).mpr
    linarith only [hyx, hx.le]
  obtain ⟨h1,h2⟩ := smoothPsi_error_bounds hη hy ((mul_le_mul_of_nonneg_left hyz hη.le).trans hηz)
  obtain ⟨h3,h4⟩ := smoothPsi_error_bounds hη hz hηz
  have hboth : Real.log (z+1) ≤ Real.log (2*x+1) := Real.log_le_log (by positivity)
    (by linarith only [hyx, show z = (1+δ)*y from rfl])
  have hlog : Real.log (y+1) ≤ Real.log (2*x+1) :=
    (Real.log_le_log (by positivity) (show y+1 ≤ z+1 by linarith only [hyz])).trans hboth
  change |_ - _ - (_ - _)| ≤ _
  apply abs_le.mpr
  change -_ ≤ smoothPsi η z - smoothPsi η y - (Chebyshev.psi z - Chebyshev.psi y) ∧
    smoothPsi η z - smoothPsi η y - (Chebyshev.psi z - Chebyshev.psi y) ≤ _
  exact ⟨by linarith only [h2,hlog,h3], by linarith only [h4,hboth,h1]⟩

/-- The two divided differences extended through their centers. -/
noncomputable def entireSmoothedIncrementKernel (η δ y : ℝ) (s : ℂ) : ℂ :=
  (y:ℂ)^s * dslope (fun z : ℂ => ((1+δ : ℝ):ℂ)^z) 0 s *
    dslope (fun z : ℂ => ((1+η : ℝ):ℂ)^z) 0 (s+1) / (η:ℂ)

theorem entireSmoothedIncrementKernel_analyticAt {η δ y : ℝ} (hη : 0 < η)
    (hδ : 0 ≤ δ) (hy : 0 < y) (s : ℂ) :
    AnalyticAt ℂ (entireSmoothedIncrementKernel η δ y) s := by
  have hp (x : ℝ) (hx : 0 < x) (z : ℂ) :
      AnalyticAt ℂ (fun t : ℂ => (x:ℂ)^t) z := by
    have : NeZero (x:ℂ) := ⟨by exact_mod_cast hx.ne'⟩
    exact (differentiable_const_cpow_of_neZero (x:ℂ)).analyticAt z
  have ha := (hp (1+δ) (by linarith) s).dslope 0
  have hb := (hp (1+η) (by linarith) (s+1)).dslope 0
  have hc : AnalyticAt ℂ (fun z : ℂ => z+1) s := by fun_prop
  exact (((hp y hy s).mul ha).mul (hb.comp (f := fun z : ℂ => z+1) hc)).div analyticAt_const
    (by exact_mod_cast hη.ne')

theorem entireSmoothedIncrementKernel_eq (η δ y : ℝ) {s : ℂ} (hs : s ≠ 0) (hs' : s+1 ≠ 0) :
    entireSmoothedIncrementKernel η δ y s = smoothedIncrementKernel η δ y s := by
  unfold entireSmoothedIncrementKernel smoothedIncrementKernel perronSmoothingFactor
  rw [dslope_of_ne _ hs, dslope_of_ne _ hs']
  simp only [slope_def_field, sub_zero, Complex.cpow_zero, div_eq_mul_inv, mul_inv_rev]
  ring

theorem smoothedIncrementKernel_one {η δ y : ℝ} (hη : 0 < η) :
    smoothedIncrementKernel η δ y 1 = ((δ*y*(1+η/2):ℝ):ℂ) := by
  have hη' : (η:ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  unfold smoothedIncrementKernel perronSmoothingFactor
  norm_num only [Complex.cpow_one,one_add_one_eq_two,Complex.cpow_ofNat,div_one]
  push_cast
  field_simp
  ring

theorem entireSmoothedIncrementKernel_one {η δ y : ℝ} (hη : 0 < η) :
    entireSmoothedIncrementKernel η δ y 1 = ((δ*y*(1+η/2):ℝ):ℂ) := by
  rw [entireSmoothedIncrementKernel_eq _ _ _ one_ne_zero (by norm_num)]
  exact smoothedIncrementKernel_one hη

section

open MeasureTheory Set Filter Finset Complex
open scoped Topology

private noncomputable def digammaBarrier (u b : ℝ) :=
  Real.log (u^2+b^2)/2 + 1/(u+|b|-1/2)

private theorem digammaBarrier_step {u : ℝ} (hu : 1 ≤ u) (b : ℝ) :
    digammaBarrier (u+1) b - digammaBarrier u b ≤ u/(u^2+b^2) := by
  let D := u^2+b^2
  let D' := (u+1)^2+b^2
  let c := u+|b|
  have hD : 0 < D := by dsimp [D]; positivity [show 0 < u by linarith]
  have hD' : 0 < D' := by dsimp [D']; positivity [show 0 < u by linarith]
  have hc : 1 ≤ c := by dsimp [c]; linarith [abs_nonneg b]
  have hminus : 0 < c-1/2 := by linarith
  have hplus : 0 < c+1/2 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hD' hD)
  rw [Real.log_div hD'.ne' hD.ne'] at hlog
  have hdelta : D'/D-1 = (2*u+1)/D := by
    field_simp
    dsimp [D,D']
    ring
  rw [hdelta] at hlog
  have hrec : 1/(2*D) ≤ 1/(c-1/2)-1/(c+1/2) := by
    rw [div_sub_div 1 1 hminus.ne' hplus.ne',
      show 1*(c+1/2) - (c-1/2)*1 = 1 by ring]
    apply one_div_le_one_div_of_le (mul_pos hminus hplus)
    dsimp only [D,c]
    nlinarith only [sq_nonneg (u-|b|),sq_abs b]
  have hsplit : (2*u+1)/D/2 = u/D+1/(2*D) := by field_simp
  change Real.log D'/2 + 1/(u+1+|b|-1/2) - (Real.log D/2 + 1/(c-1/2)) ≤ u/D
  rw [show u+1+|b|-1/2 = c+1/2 by dsimp [c]; ring]
  linarith

private theorem euler_sum_barrier (a b : ℝ) (ha : 1 ≤ a) (n : ℕ) (hn : n ≠ 0) :
    Real.log n - ∑ k ∈ range (n+1), (a+k)/((a+k)^2+b^2) ≤ digammaBarrier a b := by
  have ht (m : ℕ) : digammaBarrier (a+m) b - digammaBarrier a b ≤
      ∑ k ∈ range m, (a+k)/((a+k)^2+b^2) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h := digammaBarrier_step (u:=a+m) (by linarith [show 0 ≤ (m:ℝ) from Nat.cast_nonneg _]) b
      rw [sum_range_succ,Nat.cast_succ,← add_assoc]
      linarith
  have hnp : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnp' : (n:ℝ)^2 ≤ (a+(n+1:ℕ))^2+b^2 := by
    push_cast
    nlinarith [sq_nonneg b,mul_nonneg hnp.le (show 0 ≤ a by linarith),sq_nonneg a]
  have hlog := Real.log_le_log (sq_pos_of_pos hnp) hnp'
  rw [Real.log_pow] at hlog
  have hnon : 0 ≤ 1/(a+(n+1:ℕ)+|b|-1/2) := by
    apply one_div_nonneg.mpr
    push_cast
    linarith [abs_nonneg b]
  have h := ht (n+1)
  unfold digammaBarrier at *
  push_cast at *
  linarith

private theorem digammaBarrier_large {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 2) (hb : 50 ≤ |b|) :
    digammaBarrier a b ≤ Real.log |b| + 0.1 := by
  have hbpos : 0 < |b| := by linarith
  have hsq : a^2+b^2 ≤ (1.04*|b|)^2 := by
    have h1 : a ≤ 0.04*|b| := by linarith
    have h2 := pow_le_pow_left₀ (show 0 ≤ a by linarith) h1 2
    nlinarith [sq_abs b,sq_nonneg b]
  have hl := Real.log_le_log (show 0 < a^2+b^2 by positivity [show 0 < a by linarith]) hsq
  rw [Real.log_pow,Real.log_mul (by norm_num) hbpos.ne'] at hl
  have hc : 1/(a+|b|-1/2) ≤ 1/50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  unfold digammaBarrier
  push_cast at hl
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1.04)]

private theorem digammaBarrier_small {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 2) (hb : |b| ≤ 50) :
    digammaBarrier a b ≤ Real.log 100 + 3 := by
  have h1 := pow_le_pow_left₀ (abs_nonneg b) hb 2
  rw [sq_abs] at h1
  have hsq : a^2+b^2 ≤ (100:ℝ)^2 := by nlinarith [pow_le_pow_left₀ (show 0 ≤ a by linarith) ha' 2]
  have hl := Real.log_le_log (show 0 < a^2+b^2 by positivity [show 0 < a by linarith]) hsq
  rw [Real.log_pow] at hl
  have hc : 1/(a+|b|-1/2) ≤ 1/(1/2) := one_div_le_one_div_of_le (by norm_num) (by linarith [abs_nonneg b])
  unfold digammaBarrier
  push_cast at hl
  linarith

private noncomputable def eulerLogModel (n : ℕ) (b a : ℝ) : ℝ :=
  a*Real.log n + Real.log n.factorial - ∑ k ∈ range (n+1), Real.log ((a+k)^2+b^2)/2

private theorem eulerLogModel_tendsto {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun n => eulerLogModel n b a) atTop (𝓝 (Real.log ‖Gamma ⟨a,b⟩‖)) := by
  let z : ℂ := ⟨a,b⟩
  have H := ((Real.continuousAt_log (norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos (s:=z) ha))).tendsto).comp
    (GammaSeq_tendsto_Gamma z).norm
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hp (k : ℕ) : z+k ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re,natCast_re,zero_re,z] at h'
    linarith [show 0 ≤ (k:ℝ) from Nat.cast_nonneg _]
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hfact : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  change Real.log ‖GammaSeq z n‖ = _
  rw [GammaSeq,norm_div,norm_mul,norm_prod,Complex.norm_natCast_cpow_of_pos hn,Complex.norm_natCast,
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hnp _).ne' hfact.ne')
      (prod_ne_zero_iff.mpr (fun k _ => norm_ne_zero_iff.mpr (hp k))),
    Real.log_mul (Real.rpow_pos_of_pos hnp _).ne' hfact.ne',Real.log_rpow hnp,
    Real.log_prod (fun k _ => norm_ne_zero_iff.mpr (hp k))]
  change _ = a*Real.log n + Real.log n.factorial - ∑ k ∈ range (n+1), _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have he : ‖z+k‖^2 = (a+k)^2+b^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [z,pow_two]
  rw [← he,Real.log_pow]
  ring

private theorem eulerLogModel_hasDerivAt (n : ℕ) (b : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (eulerLogModel n b)
      (Real.log n - ∑ k ∈ range (n+1), (a+k)/((a+k)^2+b^2)) a := by
  have hs (k : ℕ) : HasDerivAt (fun w : ℝ => Real.log ((w+k)^2+b^2)/2)
      ((a+k)/((a+k)^2+b^2)) a := by
    have hp : 0 < (a+k)^2+b^2 := by positivity
    convert (((((hasDerivAt_id' a).add_const (k:ℝ)).pow 2).add_const (b^2)).log hp.ne').div_const 2 using 1
    simp only [Pi.pow_apply]
    ring
  have h := (((hasDerivAt_id' a).mul_const (Real.log n)).add_const (Real.log n.factorial)).sub
    (HasDerivAt.fun_sum (u:=range (n+1)) fun k _ => hs k)
  unfold eulerLogModel
  simpa only [Pi.sub_def,one_mul] using h

private theorem logGamma_norm_hasDerivAt {a b : ℝ} (ha : 0 < a) :
    HasDerivAt (fun w : ℝ => Real.log ‖Gamma ⟨w,b⟩‖) (digamma ⟨a,b⟩).re a := by
  let z : ℂ := ⟨a,b⟩
  have hn : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hd := (differentiableAt_Gamma z (fun n h => by
    have he := congrArg Complex.re h
    simp only [z, neg_re, natCast_re] at he
    linarith [show 0 ≤ (n:ℝ) from Nat.cast_nonneg _])).hasDerivAt
  have hz : (a:ℂ)+I*b = z := by rw [mul_comm I]; exact (mk_eq_add_mul_I a b).symm
  have hcomp : HasDerivAt (fun w : ℂ => Gamma (w+I*b)) (deriv Gamma z) (a:ℂ) := by
    have hd' : HasDerivAt Gamma (deriv Gamma z) ((a:ℂ)+I*b) := by rw [hz]; exact hd
    simpa only [Function.comp_def,mul_one] using hd'.comp
      (x := (a:ℂ)) (show HasDerivAt (fun w : ℂ => w+I*b) 1 (a:ℂ) from (hasDerivAt_id' _).add_const _)
  have hreal : HasDerivAt (fun w : ℝ => Gamma ⟨w,b⟩) (deriv Gamma z) a := by
    convert hcomp.comp_ofReal using 1
    funext w
    congr 1
    rw [mk_eq_add_mul_I,mul_comm I]
  have hs := ((hreal.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).div_const 2)
  convert hs using 1
  · funext w
    simp [Real.log_pow]
  · rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply,Complex.sq_norm]
    change (deriv Gamma z / Gamma z).re = 2 * (deriv Gamma z * (starRingEnd ℂ) (Gamma z)).re / normSq (Gamma z) / 2
    simp only [div_re,mul_re,conj_re,conj_im]
    ring

private theorem digamma_le_of_barrier (b C : ℝ)
    (hC : ∀ u ∈ Icc (1:ℝ) 2, digammaBarrier u b ≤ C) :
    (digamma ⟨5/4,b⟩).re ≤ C := by
  let a : ℝ := 5/4
  have ha : a ∈ Icc (1:ℝ) 2 := by norm_num [a]
  have hinc (v : ℝ) (hv : v ∈ Icc (1:ℝ) 2) (hav : a ≤ v) :
      Real.log ‖Gamma ⟨v,b⟩‖ - Real.log ‖Gamma ⟨a,b⟩‖ ≤ C*(v-a) := by
    have ht := (eulerLogModel_tendsto (a:=v) (by linarith [hv.1]) b).sub
      (eulerLogModel_tendsto (a:=a) (by norm_num [a]) b)
    apply le_of_tendsto ht
    filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
    have hd (u : ℝ) (hu : u ∈ Icc (1:ℝ) 2) := eulerLogModel_hasDerivAt n b
      (a:=u) (by linarith [hu.1])
    apply (convex_Icc (1:ℝ) 2).image_sub_le_mul_sub_of_deriv_le
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt) _ a ha v hv hav
    intro u hu
    obtain ⟨hu1,hu2⟩ := interior_subset hu
    rw [(hd u ⟨hu1,hu2⟩).deriv]
    exact (euler_sum_barrier u b hu1 n hn).trans (hC u ⟨hu1,hu2⟩)
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.1
    (logGamma_norm_hasDerivAt (a:=a) (b:=b) (by norm_num [a]))).2
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show a < 2 by norm_num [a])).filter_mono
    (nhdsWithin_le_nhds (s:=Ioi a))] with v hv hv2
  rw [slope_def_field]
  exact (div_le_iff₀ (sub_pos.mpr hv)).2 (hinc v ⟨ha.1.trans (le_of_lt hv),hv2.le⟩ (le_of_lt hv))

theorem digamma_five_fourths_large (t : ℝ) (ht : 100 ≤ |t|) :
    (Complex.digamma (⟨5/4,t/2⟩ : ℂ)).re ≤ Real.log |t/2| + 0.1 := by
  apply digamma_le_of_barrier
  intro u hu
  apply digammaBarrier_large hu.1 hu.2
  rw [abs_div]
  norm_num
  linarith

theorem digamma_five_fourths_small (t : ℝ) (ht : |t| ≤ 100) :
    (Complex.digamma (⟨5/4,t/2⟩ : ℂ)).re ≤ Real.log 100 + 3 := by
  apply digamma_le_of_barrier
  intro u hu
  apply digammaBarrier_small hu.1 hu.2
  rw [abs_div]
  norm_num
  linarith

private theorem euler_sum_lower (a b : ℝ) (ha : 1 ≤ a) (n : ℕ) (hn : n ≠ 0) :
    -2 ≤ Real.log n - ∑ k ∈ range (n+1), (a+k)/((a+k)^2+b^2) := by
  have h (k : ℕ) : (a+k)/((a+k)^2+b^2) ≤ ((k:ℝ)+1)⁻¹ := by
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
    have hak : 0 < a+k := by linarith
    rw [inv_eq_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hak.le (sub_nonneg.mpr ha),sq_nonneg b]
  have hs := sum_le_sum (s:=range (n+1)) (fun k _ => h k)
  have hH := harmonic_le_one_add_log (n+1)
  simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Nat.cast_add,Nat.cast_one,
    Rat.cast_add,Rat.cast_natCast,Rat.cast_one] at hH
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hl := Real.log_le_log (show 0 < (n:ℝ)+1 by positivity) (show (n:ℝ)+1 ≤ 2*n by linarith)
  rw [Real.log_mul (by norm_num) (show (n:ℝ) ≠ 0 by linarith)] at hl
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]

private theorem digammaBarrier_coarse {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 2) :
    digammaBarrier a b ≤ Real.log (2+|b|) + 2 := by
  have hsq : a^2+b^2 ≤ (2+|b|)^2 := by
    nlinarith [sq_abs b,abs_nonneg b,pow_le_pow_left₀ (show 0 ≤ a by linarith) ha' 2]
  have hl := Real.log_le_log (show 0 < a^2+b^2 by positivity [show 0 < a by linarith]) hsq
  rw [Real.log_pow] at hl
  have hc : 1/(a+|b|-1/2) ≤ 1/(1/2) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [abs_nonneg b])
  unfold digammaBarrier
  push_cast at hl
  linarith

theorem abs_re_digamma_of_one_le {a b : ℝ} (ha : 1 ≤ a) (ha' : a < 2) :
    |(digamma ⟨a,b⟩).re| ≤ Real.log (2+|b|) + 2 := by
  let C := Real.log (2+|b|) + 2
  have haS : a ∈ Set.Icc (1:ℝ) 2 := ⟨ha,ha'.le⟩
  have hinc (v : ℝ) (hv : v ∈ Set.Icc (1:ℝ) 2) :
      |Real.log ‖Gamma ⟨v,b⟩‖ - Real.log ‖Gamma ⟨a,b⟩‖| ≤ C*|v-a| := by
    have ht := ((eulerLogModel_tendsto (a:=v) (by linarith [hv.1]) b).sub
      (eulerLogModel_tendsto (a:=a) (by linarith) b)).abs
    apply le_of_tendsto ht
    filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
    have hd (u : ℝ) (hu : u ∈ Set.Icc (1:ℝ) 2) := eulerLogModel_hasDerivAt n b
      (a:=u) (by linarith [hu.1])
    apply (convex_Icc (1:ℝ) 2).norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (hd u hu).differentiableAt) _ haS hv
    intro u hu
    rw [(hd u hu).deriv,Real.norm_eq_abs,abs_le]
    refine ⟨?_,(euler_sum_barrier u b hu.1 n hn).trans (digammaBarrier_coarse hu.1 hu.2)⟩
    exact (show -C ≤ -2 by dsimp [C]; linarith [Real.log_nonneg (show 1 ≤ 2+|b| by linarith [abs_nonneg b])]).trans
      (euler_sum_lower u b hu.1 n hn)
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.1
    (logGamma_norm_hasDerivAt (a:=a) (b:=b) (by linarith))).2.abs
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ha').filter_mono
    (nhdsWithin_le_nhds (s:=Ioi a))] with v hv hv2
  rw [slope_def_field,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr (sub_pos.mpr hv).ne')).2
    (hinc v ⟨ha.trans (le_of_lt hv),hv2.le⟩)

theorem digamma_three_fourths_abs (t : ℝ) :
    |(digamma (⟨3/4,t/2⟩ : ℂ)).re| ≤ 100 * Real.log (2+|t|) := by
  let z : ℂ := ⟨3/4,t/2⟩
  have hz : z+1 = (⟨7/4,t/2⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [z]
  have hrec := congrArg Complex.re (digamma_apply_add_one z fun n h => by
    have h' := congrArg Complex.re h
    simp only [z,neg_re,natCast_re] at h'
    linarith [show 0 ≤ (n:ℝ) from Nat.cast_nonneg _])
  rw [hz,add_re] at hrec
  have hi : |(z⁻¹).re| ≤ 2 := by
    rw [inv_re,abs_of_nonneg (by exact div_nonneg (by norm_num [z]) (normSq_nonneg _))]
    apply (div_le_iff₀ (normSq_pos.mpr (fun h => by have hh := congrArg re h; norm_num [z] at hh))).2
    rw [Complex.normSq_apply]
    dsimp [z]
    nlinarith [sq_nonneg (t/2)]
  have hA := abs_re_digamma_of_one_le (a:=7/4) (b:=t/2) (by norm_num) (by norm_num)
  have hl : Real.log (2+|t/2|) ≤ Real.log (2+|t|) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div]
    norm_num
  have hL := Real.log_le_log (by norm_num : (0:ℝ)<2) (show 2 ≤ 2+|t| by linarith [abs_nonneg t])
  change |(digamma z).re| ≤ _
  rw [show (digamma z).re = (digamma (⟨7/4,t/2⟩ : ℂ)).re - (z⁻¹).re by linarith]
  calc
    _ ≤ |(digamma (⟨7/4,t/2⟩ : ℂ)).re| + |(z⁻¹).re| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (digamma (⟨7/4,t/2⟩ : ℂ)).re (-(z⁻¹).re)
    _ ≤ 100 * Real.log (2+|t|) := by linarith [Real.log_two_gt_d9]

end

section

open Complex Filter Set MeasureTheory
open scoped Topology

private noncomputable def leftMajorant (t : ℝ) : ℝ := (max 1 |t|)^(-9/8:ℝ)

private theorem leftMajorant_mass : (∫ t : ℝ, leftMajorant t) = 18 := by
  let f (t : ℝ) := (max 1 t)^(-9/8:ℝ)
  have hc : EqOn (fun _ : ℝ => (1:ℝ)) f (Ioc 0 1) := by
    intro t ht
    simp [f,max_eq_left ht.2]
  have ht : EqOn (fun t : ℝ => t^(-9/8:ℝ)) f (Ioi 1) := by
    intro t ht
    simp [f,max_eq_right (le_of_lt (Set.mem_Ioi.mp ht))]
  have hc' : IntegrableOn f (Ioc 0 1) := (integrableOn_const (by simp)).congr_fun hc measurableSet_Ioc
  have ht' : IntegrableOn f (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).congr_fun ht measurableSet_Ioi
  change (∫ t : ℝ, f |t|) = 18
  rw [integral_comp_abs, ← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1),
    setIntegral_union (Disjoint.mono_left Ioc_subset_Iic_self (Iic_disjoint_Ioi le_rfl))
      measurableSet_Ioi hc' ht',
    ← setIntegral_congr_fun measurableSet_Ioc hc, ← setIntegral_congr_fun measurableSet_Ioi ht,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  simp [Real.volume_real_Ioc]
  norm_num

private theorem leftMajorant_integrable : Integrable leftMajorant := by
  by_contra h
  have he := leftMajorant_mass
  rw [integral_undef h] at he
  norm_num at he

private theorem left_numeric_scale {x y : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) : (24*x)^(1/4:ℝ) / Real.sqrt y ≤ 1/1000 := by
  have hx₀ : 0 < x := by linarith
  have hy₀ : 0 < y := by linarith
  let r := x^(1/4:ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hx₀ _
  have hfour : r^4 = x := by
    simpa [r, one_div] using Real.rpow_inv_natCast_pow hx₀.le (by decide : (4:ℕ) ≠ 0)
  have hbig : 30000 ≤ r := by
    by_contra! hh
    have h := pow_le_pow_left₀ hr.le hh.le 4
    linarith only [h,hfour,hx]
  have hsqrt : r^2 ≤ 10*Real.sqrt y := by
    have hsq := Real.sq_sqrt hy₀.le
    nlinarith only [hfour,hsq,hy, sq_nonneg (r^2+10*Real.sqrt y),
      sq_nonneg r, Real.sqrt_nonneg y]
  have h24 : (24:ℝ)^(1/4:ℝ) ≤ 3 := by
    apply (Real.rpow_le_rpow (show (0:ℝ) ≤ 24 by norm_num) (show (24:ℝ) ≤ 3^4 by norm_num)
      (show (0:ℝ) ≤ 1/4 by norm_num)).trans_eq
    simpa [one_div] using Real.pow_rpow_inv_natCast (show (0:ℝ) ≤ 3 by norm_num)
      (by decide : (4:ℕ) ≠ 0)
  rw [Real.mul_rpow (by norm_num) hx₀.le]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hy₀)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right h24 hr.le,hsqrt,mul_le_mul_of_nonneg_right hbig hr.le]

private theorem left_log_growth {t : ℝ} :
    Real.log (2+|t|) ≤ 10*(max 1 |t|)^(1/8:ℝ) := by
  let d := max 1 |t|
  have hd : 1 ≤ d := le_max_left _ _
  have he : |t| ≤ d := le_max_right _ _
  have hlog := Real.log_le_log (show 0 < 2+|t| by positivity) (show 2+|t| ≤ 3*d by linarith)
  rw [Real.log_mul (by norm_num) (by linarith : d ≠ 0)] at hlog
  have hl := Real.log_le_rpow_div (zero_le_one.trans hd) (show (0:ℝ) < 1/8 by norm_num)
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have hp := Real.one_le_rpow hd (by norm_num : (0:ℝ) ≤ 1/8)
  change _ ≤ 10*d^_
  linarith

private theorem left_smoothing_bounds {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1) {s : ℂ}
    (hs : s.re = -1/2) :
    ‖perronSmoothingFactor η s‖ ≤ 1 ∧
    ‖perronSmoothingFactor η s‖ ≤ 6 / (η * max 1 |s.im|) := by
  have h1 : 0 < 1+η := by linarith
  have hrep : perronSmoothingFactor η s =
      (∫ u : ℝ in 1..1+η, (u:ℂ)^s)/(η:ℂ) := by
    rw [integral_cpow (Or.inl (by linarith : -1 < s.re))]
    unfold perronSmoothingFactor
    simp only [Complex.ofReal_one,Complex.one_cpow,div_eq_mul_inv,mul_inv_rev]
    ring
  constructor
  · rw [hrep,norm_div,Complex.norm_real, Real.norm_eq_abs,abs_of_pos hη,div_le_one hη]
    calc
      _ ≤ 1 * |(1+η)-1| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro u hu
        rw [uIoc_of_le (by linarith : 1 ≤ 1+η)] at hu
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1] : 0 < u),hs]
        exact Real.rpow_le_one_of_one_le_of_nonpos hu.1.le (by norm_num)
      _ = _ := by simp [abs_of_pos hη]
  · have hRe := Complex.abs_re_le_norm (s+1)
    have hi := Complex.abs_im_le_norm (s+1)
    simp only [Complex.add_re, Complex.one_re, hs,Complex.add_im,Complex.one_im,add_zero] at hRe hi
    norm_num at hRe
    have hd : max 1 |s.im| ≤ 2*‖s+1‖ := max_le (by linarith) (by linarith [norm_nonneg (s+1)])
    have hden : 0 < ‖s+1‖ := by linarith
    have hsqrt : Real.sqrt (1+η) ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
    have hn := norm_sub_le (((1+η:ℝ):ℂ)^(s+1)) (1:ℂ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.add_re,Complex.one_re,hs,
      show (-1/2:ℝ)+1 = 1/2 by norm_num, ← Real.sqrt_eq_rpow,norm_one] at hn
    rw [perronSmoothingFactor,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη]
    have hm : 0 < max 1 |s.im| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    apply (div_le_div_iff₀ (mul_pos hη hden) (mul_pos hη hm)).2
    have h3 := mul_le_mul_of_nonneg_right (hn.trans (by linarith : Real.sqrt (1+η)+1 ≤ 3)) hm.le
    nlinarith only [mul_le_mul_of_nonneg_left h3 hη.le,mul_le_mul_of_nonneg_left hd hη.le]

private theorem left_increment_bound {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : s.re = -1/2) :
    ‖((((1+δ:ℝ):ℂ)^s)-1)/s‖ ≤ 4 / max 1 |s.im| := by
  have hN := norm_sub_le (((1+δ:ℝ):ℂ)^s) (1:ℂ)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1+δ),hs,norm_one] at hN
  have hP : (1+δ)^(-(1:ℝ)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hRe := Complex.abs_re_le_norm s
  rw [hs] at hRe
  norm_num at hRe
  have hS : 0 < ‖s‖ := by linarith
  have hd : 0 < max 1 |s.im| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD : max 1 |s.im| ≤ 2*‖s‖ := max_le (by linarith)
    (by linarith [Complex.abs_im_le_norm s])
  rw [norm_div]
  apply (div_le_div_iff₀ hS hd).2
  linarith only [mul_le_mul_of_nonneg_right (hN.trans (by linarith : (1+δ)^(-1/2:ℝ)+1 ≤ 2)) hd.le,hD]

noncomputable def smoothedLeftIntegrand (η δ y t : ℝ) : ℂ :=
  let s : ℂ := ⟨-1/2,t⟩
  (-deriv riemannZeta s / riemannZeta s) * smoothedIncrementKernel η δ y s

/-- A power majorant independent of x and y on the working range. -/
theorem smoothedLeftIntegrand_bound {x y δ : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) (hδ : 0 ≤ δ) (t : ℝ)
    (hZ : ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|)) :
    ‖smoothedLeftIntegrand (1/(4*x)) δ y t‖ ≤ 40 * (max 1 |t|)^(-9/8:ℝ) := by
  let s : ℂ := ⟨-1/2,t⟩
  let d := max 1 |t|
  let η := 1/(4*x)
  have hx₀ : 0 < x := by linarith
  have hy₀ : 0 < y := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hη' : η ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hδw := left_increment_bound hδ (s := s) rfl
  change _ ≤ 4/d at hδw
  obtain ⟨hB1,hB2⟩ := left_smoothing_bounds hη hη' (s := s) rfl
  have hscale : 6 / (η * max 1 |s.im|) = 24*x/d := by
    dsimp only [η,s,d]
    field_simp
    ring
  rw [hscale] at hB2
  have hp : 0 < 24*x/d := by positivity
  have hB : ‖perronSmoothingFactor η s‖ ≤ (24*x/d)^(1/4:ℝ) := by
    by_cases h : 1 ≤ 24*x/d
    · exact hB1.trans (Real.one_le_rpow h (by norm_num))
    · exact hB2.trans (Real.self_le_rpow_of_le_one hp.le (le_of_not_ge h) (by norm_num))
  have hZ' : ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 1000*(10*d^(1/8:ℝ)) := by
    rw [neg_div, norm_neg]
    exact hZ.trans (mul_le_mul_of_nonneg_left left_log_growth (by norm_num))
  have hys : ‖(y:ℂ)^s‖ = (Real.sqrt y)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy₀]
    change y^(-1/2:ℝ) = _
    rw [show (-1/2:ℝ) = -(1/2) by ring,Real.rpow_neg hy₀.le,← Real.sqrt_eq_rpow]
  change ‖(-deriv riemannZeta s / riemannZeta s) * ((y:ℂ)^s *
      (((((1+δ:ℝ):ℂ)^s)-1)/s) * perronSmoothingFactor η s)‖ ≤ _
  simp only [norm_mul,hys]
  calc
    _ ≤ (1000*(10*d^(1/8:ℝ))) * ((Real.sqrt y)⁻¹ * (4/d) * ((24*x/d)^(1/4:ℝ))) := by
      gcongr
    _ = 40000 * ((24*x)^(1/4:ℝ) / Real.sqrt y) * (d^(-9/8:ℝ)) := by
      rw [Real.div_rpow (by positivity) hd.le]
      have hm : d^(-9/8:ℝ) = d^(1/8:ℝ) / (d*d^(1/4:ℝ)) := by
        rw [show (-9/8:ℝ) = 1/8-(1+1/4) by norm_num,Real.rpow_sub hd,Real.rpow_add hd,
          Real.rpow_one]
      rw [hm]
      ring
    _ ≤ _ := by
      have hc := left_numeric_scale hx hy
      change _ ≤ 40*d^(-9/8:ℝ)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
      linarith only [hc]

theorem smoothedLeftIntegrand_integrable {x y δ : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) (hδ : 0 ≤ δ)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|)) :
    Integrable (smoothedLeftIntegrand (1/(4*x)) δ y) := by
  apply (leftMajorant_integrable.const_mul 40).mono' _
    (Eventually.of_forall (fun t => smoothedLeftIntegrand_bound hx hy hδ t (hZ t)))
  let v (t : ℝ) : ℂ := ⟨-1/2,t⟩
  have hv : Continuous v := by
    have he : v = fun t : ℝ => ((-1/2:ℝ):ℂ) + (t:ℂ)*I := by
      funext t
      apply Complex.ext <;> simp [v]
    rw [he]
    fun_prop
  have hz (t : ℝ) : AnalyticAt ℂ riemannZeta (v t) := by
    apply analyticOn_riemannZeta
    intro h
    have he : (v t).re = (1:ℂ).re := congrArg Complex.re (show v t = 1 from h)
    norm_num [v] at he
  have hd : Continuous (fun t => deriv riemannZeta (v t)) := continuous_iff_continuousAt.mpr
    (fun t => (hz t).deriv.continuousAt.comp (x := t) hv.continuousAt)
  have hf : Continuous (fun t => riemannZeta (v t)) := continuous_iff_continuousAt.mpr
    (fun t => (hz t).continuousAt.comp (x := t) hv.continuousAt)
  have hk : Measurable (fun t => smoothedIncrementKernel (1/(4*x)) δ y (v t)) := by
    unfold smoothedIncrementKernel perronSmoothingFactor
    fun_prop
  exact ((hd.measurable.neg.div hf.measurable).mul hk).aestronglyMeasurable

theorem smoothedLeftIntegral_truncated {x y δ : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) (hδ : 0 ≤ δ)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|))
    {u v : ℕ → ℝ} (hu : Tendsto u atTop atBot) (hv : Tendsto v atTop atTop) :
    Tendsto (fun n => (1/(2*Real.pi):ℝ) •
      ∫ t : ℝ in u n..v n, smoothedLeftIntegrand (1/(4*x)) δ y t) atTop
      (𝓝 ((1/(2*Real.pi):ℝ) • ∫ t : ℝ, smoothedLeftIntegrand (1/(4*x)) δ y t)) := by
  exact (intervalIntegral_tendsto_integral (smoothedLeftIntegrand_integrable hx hy hδ hZ)
    hu hv).const_smul _

/-- The normalized contour contribution costs at most 120. -/
theorem smoothedLeftIntegral_le {x y δ : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) (hδ : 0 ≤ δ)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|)) :
    ‖(1/(2*Real.pi):ℝ) • ∫ t : ℝ, smoothedLeftIntegrand (1/(4*x)) δ y t‖ ≤ 120 := by
  have h := MeasureTheory.norm_integral_le_of_norm_le (leftMajorant_integrable.const_mul 40)
    (Eventually.of_forall (fun t => smoothedLeftIntegrand_bound hx hy hδ t (hZ t)))
  rw [integral_const_mul,leftMajorant_mass] at h
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),one_div,inv_mul_eq_div]
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h,Real.pi_gt_three])

theorem smoothedLeftIntegral_le_log_sq {x y δ : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) (hδ : 0 ≤ δ)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|)) :
    ‖(1/(2*Real.pi):ℝ) • ∫ t : ℝ, smoothedLeftIntegrand (1/(4*x)) δ y t‖ ≤
      0.3*(Real.log x)^2 := by
  apply (smoothedLeftIntegral_le hx hy hδ hZ).trans
  have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9] :
    Real.exp 1 ≤ 3) 20
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have hlog : 20 ≤ Real.log x :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith only [hpow,hx])
  nlinarith only [hlog,sq_nonneg (Real.log x-20)]

end

section

open Complex MeasureTheory

noncomputable def smoothedContourF (η δ y : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv riemannZeta s) * entireSmoothedIncrementKernel η δ y s

noncomputable def smoothedHorizontal (η δ y t : ℝ) : ℂ :=
  ∫ σ : ℝ in (-1/2:ℝ)..2, smoothedContourF η δ y ((σ:ℂ) + (t:ℂ)*I)

end

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Filter Set
open scoped Topology

/-- The exact decomposition of xi's logarithmic derivative in the right half-plane. -/
theorem logDeriv_completedXi_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedXi s = 1/s + 1/(s-1) + logDeriv riemannZeta s +
      (Complex.digamma (s/2) - Complex.log (Real.pi:ℂ))/2 := by
  let a (w : ℂ) := w*(w-1)
  let b (w : ℂ) := (Real.pi:ℂ)^(-w/2)
  let c (w : ℂ) := Complex.Gamma (w/2)
  have h₀ : s ≠ 0 := by intro h; norm_num [h] at hs
  have h₁ : s ≠ 1 := by intro h; simp [h] at hs
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : completedXi =ᶠ[𝓝 s] (fun w => ((a*riemannZeta)*(b*c)) w * (1/2)) := by
    filter_upwards [(continuous_re.isOpen_preimage (Ioi (1:ℝ)) isOpen_Ioi).mem_nhds hs] with w hw
    have hw' : 1 < w.re := hw
    have hn : w ≠ 1 := by intro h; simp [h] at hw'
    have hreg : riemannZeta₁ w = (w-1)*riemannZeta w := by
      rw [riemannZeta_eq_inv_sub_mul hn, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
    rw [completedXi_eq_zeta₁_Gammaℝ (by linarith), hreg]
    dsimp only [Pi.mul_apply, a, b, c, Gammaℝ]
    ring
  have ha : a s ≠ 0 := mul_ne_zero h₀ (sub_ne_zero.mpr h₁)
  have hb : b s ≠ 0 := cpow_ne_zero_iff.mpr (.inl hp)
  have hhalf : 0 < (s/2).re := by rw [Complex.div_ofNat_re]; linarith
  have hc : c s ≠ 0 := Gamma_ne_zero_of_re_pos hhalf
  have hζ := riemannZeta_ne_zero_of_one_le_re hs.le
  have hζd := (analyticOn_riemannZeta s h₁).differentiableAt
  have had : DifferentiableAt ℂ a s := by dsimp only [a]; fun_prop
  have hd : HasDerivAt (fun w : ℂ => w/2) (1/2) s := (hasDerivAt_id' s).div_const 2
  have hdn : HasDerivAt (fun w : ℂ => -w/2) (-1/2) s := (hasDerivAt_id' s).neg.div_const 2
  have hbd : DifferentiableAt ℂ b s := (hdn.const_cpow (.inl hp)).differentiableAt
  have hpoles : ∀ m : ℕ, s/2 ≠ -(m:ℂ) := by
    intro m he
    rw [he, Complex.neg_re, Complex.natCast_re] at hhalf
    linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hcd : DifferentiableAt ℂ c s := (differentiableAt_Gamma _ hpoles).comp s hd.differentiableAt
  have hla : logDeriv a s = 1/s+1/(s-1) := by
    have d := ((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).deriv
    change deriv a s / (s*(s-1)) = _
    rw [show deriv a s = _ from d]
    field_simp [h₀, sub_ne_zero.mpr h₁]
  have hlb : logDeriv b s = -Complex.log (Real.pi:ℂ)/2 := by
    rw [logDeriv_apply, show deriv b s = _ from Complex.deriv_const_cpow hdn.differentiableAt (Real.pi:ℂ),
      hdn.deriv]
    change _ * _ * b s / b s = _
    rw [mul_div_cancel_right₀ _ hb]
    ring
  rw [(logDeriv_congr_nhds heq).eq_of_nhds, logDeriv_mul_const s _ (by norm_num),
    logDeriv_mul (f:=a*riemannZeta) (g:=b*c) s (mul_ne_zero ha hζ) (mul_ne_zero hb hc) (had.mul hζd) (hbd.mul hcd),
    logDeriv_mul (f:=a) (g:=riemannZeta) s ha hζ had hζd, logDeriv_mul (f:=b) (g:=c) s hb hc hbd hcd, hla, hlb,
    show logDeriv c s = _ from hd.logDeriv_Gamma hpoles]
  ring

/-- The shifted identity on the single vertical line used by the Poisson kernel. -/
theorem centeredXi_logDeriv_right_re (t : ℝ) :
    2*(logDeriv centeredXi ⟨2,t⟩).re =
      2*((1/(⟨5/2,t⟩:ℂ)).re + (1/((⟨5/2,t⟩:ℂ)-1)).re) +
      2*(logDeriv riemannZeta ⟨5/2,t⟩).re +
      (Complex.digamma ⟨5/4,t/2⟩).re - Real.log Real.pi := by
  let s : ℂ := ⟨5/2,t⟩
  have hs : 1 < s.re := by norm_num [s]
  have hs' : (⟨2,t⟩ : ℂ)+1/2 = s := by apply Complex.ext <;> norm_num [s]
  have hh : s/2 = ⟨5/4,t/2⟩ := by apply Complex.ext <;> norm_num [s]
  have h : logDeriv centeredXi ⟨2,t⟩ = logDeriv completedXi s := by
    change logDeriv (fun w : ℂ => completedXi (w+1/2)) _ = _
    simp only [logDeriv_apply, deriv_comp_add_const, hs']
  rw [h, logDeriv_completedXi_of_one_lt_re hs, hh]
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.log_ofReal_re]
  change 2 * (_ + _ + _ + (_ - _) / 2) = _
  change 2 * ((1/s).re + (1/(s-1)).re + (logDeriv riemannZeta s).re +
    ((digamma ⟨5/4,t/2⟩).re - Real.log Real.pi)/2) =
    2*((1/s).re + (1/(s-1)).re) + 2*(logDeriv riemannZeta s).re +
      (digamma ⟨5/4,t/2⟩).re - Real.log Real.pi
  ring

/-- Explicit archimedean and zeta estimates bound the true xi logarithmic derivative. -/
theorem centeredXi_logDeriv_row_bound
    {U t : ℝ} (hU : 10^13 ≤ U) (ht : |t| ≤ U) :
    2*(logDeriv centeredXi ⟨2,t⟩).re ≤ Real.log U := by
  rw [centeredXi_logDeriv_right_re]
  let s : ℂ := ⟨5/2,t⟩
  have hz : (logDeriv riemannZeta s).re ≤ 3/4 :=
    (Complex.re_le_norm _).trans (zeta_logDeriv_norm_le_five_halves rfl)
  have hi (w : ℂ) {a : ℝ} (ha : 0<a) (haw : a≤‖w‖) : (1/w).re ≤ 1/a := by
    apply (Complex.re_le_norm _).trans
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le ha haw
  have hπ : 1 ≤ Real.log Real.pi := (Real.le_log_iff_exp_le Real.pi_pos).mpr
    (Real.exp_one_lt_three.le.trans Real.pi_gt_three.le)
  change 2*((1/s).re + (1/(s-1)).re) + 2*(logDeriv riemannZeta s).re +
      (digamma ⟨5/4,t/2⟩).re - Real.log Real.pi ≤ Real.log U
  rcases le_total 100 |t| with h | h
  · have ha := hi s (by norm_num : 0 < (100:ℝ)) (h.trans (Complex.abs_im_le_norm s))
    have hb := hi (s-1) (by norm_num : 0 < (100:ℝ)) (h.trans (by simpa [s] using Complex.abs_im_le_norm (s-1)))
    have hp : 0 < |t| := by linarith
    have hd := digamma_five_fourths_large t h
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), Real.log_div hp.ne' (by norm_num)] at hd
    linarith [Real.log_le_log hp ht, Real.log_two_gt_d9]
  · have ha := hi s (by norm_num : 0 < (1:ℝ)) (le_trans (by norm_num [s] : (1:ℝ) ≤ s.re) (Complex.re_le_norm _))
    have hb := hi (s-1) (by norm_num : 0 < (1:ℝ))
      (le_trans (by norm_num [s] : (1:ℝ) ≤ (s-1).re) (Complex.re_le_norm _))
    have hl := Real.log_le_log (by norm_num : (0:ℝ) < 10^13) hU
    rw [Real.log_pow] at hl
    have h10 : 1 ≤ Real.log 10 := (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_three])
    have h100 : Real.log 100 = 2*Real.log 10 := by
      rw [show (100:ℝ) = 10^2 by norm_num, Real.log_pow]; norm_num
    have hd := digamma_five_fourths_small t h
    rw [h100] at hd
    simp only [div_one, Nat.cast_ofNat] at ha hb hl
    linarith

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex

/-- Under RH, true zeta zeros in the critical strip, with analytic multiplicities,
obey the finite Poisson row estimate uniformly up to height U. -/
theorem riemannZeta_finite_poisson_row
    (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0)
    {U t : ℝ} (hU : 10^13 ≤ U) (ht : |t| ≤ U) :
    (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) * (4/(4+(t-ρ.im)^2))) ≤ Real.log U := by
  let e : ℂ ↪ ℂ := ⟨fun ρ => ρ-1/2, fun _ _ h => sub_left_inj.mp h⟩
  have hmap : ∀ w ∈ S.map e, centeredXi w = 0 := by
    intro w hw
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_map.mp hw
    change completedXi (ρ-1/2+1/2) = 0
    rw [sub_add_cancel]
    exact (completedXi_zero_iff_of_re_pos (hS ρ hρ).1).mpr (hS ρ hρ).2.2
  obtain ⟨L,hbound,ho⟩ := centeredXi_subquadratic_growth
  have hrow := even_entire_poisson_row differentiable_centeredXi centeredXi_zero_ne centeredXi_neg
    (fun _ h => centeredXi_zero_re hRH h) L hbound ho (S.map e) hmap t
  rw [Finset.sum_map] at hrow
  apply le_trans _ (hrow.trans (centeredXi_logDeriv_row_bound hU ht))
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro ρ hρ
  have h₁ : ρ ≠ 1 := by
    intro he
    have := (hS ρ hρ).2.1
    simp [he] at this
  change _ = (analyticOrderNatAt centeredXi (ρ-1/2):ℝ)*(4/(4+(t-(ρ-1/2).im)^2))
  rw [centeredXi_order_eq_zeta (hS ρ hρ).1 h₁]
  simp

end GoldbachShortInterval

namespace GoldbachShortInterval

/-- Label each selected zero by the natural numbers below its analytic multiplicity. -/
noncomputable def zetaZeroCopies (S : Finset ℂ) : Finset ((_:ℂ) × ℕ) :=
  S.sigma (fun ρ => Finset.range (analyticOrderNatAt riemannZeta ρ))

/-- Passing to labeled copies works equally for complex zero sums and real Poisson rows. -/
theorem sum_zetaZeroCopies {A : Type*} [AddCommMonoid A] (S : Finset ℂ) (f : ℂ → A) :
    (∑ i ∈ zetaZeroCopies S, f i.1) =
      ∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ • f ρ := by
  simp [zetaZeroCopies, Finset.sum_sigma]

theorem riemannZeta_copies_poisson_row
    (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0)
    {U t : ℝ} (hU : 10^13 ≤ U) (ht : |t| ≤ U) :
    (∑ i ∈ zetaZeroCopies S, 4/(4+(t-i.1.im)^2)) ≤ Real.log U := by
  simpa only [sum_zetaZeroCopies (f:=fun ρ => 4/(4+(t-ρ.im)^2)), nsmul_eq_mul] using
    riemannZeta_finite_poisson_row hRH S hS hU ht

end GoldbachShortInterval

namespace GoldbachShortInterval

open MeasureTheory Set Filter Chebyshev
open scoped Topology Interval

/-- A residual of at most half the squared logarithm can be absorbed in the local moment budget. -/
theorem local_psi_moment_of_smoothed_zero_polynomials {x : ℝ} (hx : 1100000000000000000 ≤ x)
    (P : ℕ → ℝ → ℂ) (L : ℝ → ℂ) (hcont : ∀ n, Continuous (P n))
    (hpoly : ∀ n, (∫ y : ℝ in 1..x, ‖P n y‖^2) ≤
      2.23 * relativeWidth x * (Real.log x)^2 * x^2)
    (hlocal : ∀ᵐ y ∂volume.restrict (Icc (x/100) x),
      Tendsto (fun n => P n y) atTop (𝓝 (L y)) ∧
      ‖((psi ((1+relativeWidth x)*y)-psi y-relativeWidth x*y : ℝ) : ℂ) + L y‖ ≤ 0.5*(Real.log x)^2) :
    (∫ y : ℝ in x/100..x, (psi ((1+relativeWidth x)*y)-psi y-relativeWidth x*y)^2) ≤
      2.54 * relativeWidth x * x^2 * (Real.log x)^2 := by
  let d := relativeWidth x
  let e := 0.5*(Real.log x)^2
  let t := x/100
  let m := volume.restrict (Ioc t x)
  let E (y : ℝ) := psi ((1+d)*y)-psi y-d*y
  let G (n : ℕ) (y : ℝ) := 1.05*‖P n y‖^2+21*e^2
  let major (y : ℝ) := 1.05*‖L y‖^2+21*e^2
  let A := d*(Real.log x)^2*x^2
  have hx₀ : 0 ≤ x := by linarith
  have ht₁ : 1 ≤ t := by dsimp [t]; linarith
  have htx : t ≤ x := by dsimp [t]; linarith
  obtain ⟨hlog,hd,hdsmall,_,_,_⟩ := relativeWidth_bounds hx
  change 0 < d at hd
  change d ≤ _ at hdsmall
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hI (n : ℕ) : Continuous (G n) := by dsimp [G]; fun_prop (disch := exact hcont _)
  have hdom (n : ℕ) : (∫ y : ℝ in t..x, ‖P n y‖^2) ≤ 2.23*A := by
    apply (intervalIntegral.integral_mono_interval ht₁ htx le_rfl
      (Eventually.of_forall fun _ => sq_nonneg _) ((hcont n).norm.pow 2 |>.intervalIntegrable 1 x)).trans
    simpa only [A,d,mul_assoc] using hpoly n
  have hpen : 21*e^2*x ≤ 0.1*A := by
    have hdcalc : d*x = (123/2)*(Real.log x)^2 := by
      dsimp only [d,relativeWidth]
      exact div_mul_cancel₀ _ (by linarith)
    dsimp only [A,e]
    nlinarith only [congrArg (fun a : ℝ => a*((Real.log x)^2*x)) hdcalc,
      mul_nonneg (sq_nonneg ((Real.log x)^2)) hx₀]
  have hbound (n : ℕ) : ∫ y, G n y ∂m ≤ 2.54*A := by
    change (∫ y in Ioc t x, G n y) ≤ _
    rw [← intervalIntegral.integral_of_le htx]
    have hi : IntervalIntegrable (fun y : ℝ => 1.05*‖P n y‖^2) volume t x :=
      (((hcont n).norm.pow 2).const_mul (1.05:ℝ)).intervalIntegrable t x
    have hc : IntervalIntegrable (fun _ : ℝ => 21*e^2) volume t x := intervalIntegrable_const
    dsimp only [G]
    rw [intervalIntegral.integral_add hi hc,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have ht₀ : 0 ≤ t := by linarith
    nlinarith only [hdom n,hpen,mul_nonneg (sq_nonneg e) ht₀,hA]
  have hlim : ∀ᵐ y ∂m, Tendsto (fun n => G n y) atTop (𝓝 (major y)) ∧ E y ^ 2 ≤ major y := by
    rw [← restrict_Ioc_eq_restrict_Icc] at hlocal
    filter_upwards [hlocal] with y hy
    refine ⟨((hy.1.norm.pow 2).const_mul (1.05:ℝ)).add_const _,?_⟩
    have htri : |E y| ≤ ‖L y‖+e := calc
      |E y| = ‖((E y : ℝ) : ℂ)‖ := by simp
      _ = ‖(((E y : ℝ) : ℂ) + L y) - L y‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖((E y : ℝ) : ℂ) + L y‖+‖L y‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [show ‖((E y : ℝ) : ℂ)+L y‖ ≤ e from hy.2]
    have hs := pow_le_pow_left₀ (abs_nonneg _) htri 2
    rw [sq_abs] at hs
    dsimp only [major]
    nlinarith only [hs,sq_nonneg (‖L y‖-20*e)]
  have hFatou := integral_le_of_ae_limit_majorant (fun y => E y^2) major G
    (B := 2.54*A) (by positivity) (psi_increment_sq_intervalIntegrable d t x).1
    (Eventually.of_forall fun _ => sq_nonneg _) (fun n => ((hI n).intervalIntegrable t x).1)
    (fun _ => Eventually.of_forall fun _ => by dsimp [G]; positivity) hbound hlim
  change (∫ y in t..x, E y^2) ≤ _
  rw [intervalIntegral.integral_of_le htx]
  apply hFatou.trans_eq
  dsimp only [A,d]
  ring

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Metric Set MeromorphicOn

theorem logDeriv_bound_nonvanishing_disk (f : ℂ → ℂ) {M : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 (23 / 8)))
    (hn : ∀ z ∈ ball (0 : ℂ) (23 / 8), f z ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) (23 / 8), ‖f z‖ ≤ ‖f 0‖ * Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 11 / 4) :
    ‖logDeriv f z‖ ≤ 1440 * M := by
  have h0 : (0 : ℂ) ∈ ball 0 (23 / 8) := mem_ball_self (by norm_num)
  have hh : DifferentiableOn ℂ (logDeriv f) (ball 0 (23 / 8)) :=
    (hf.deriv isOpen_ball).div hf hn
  obtain ⟨g, hg₀, hg⟩ := hh.isExactOn_ball.with_val_at (0 : ℂ) 0
  have hgd : DifferentiableOn ℂ g (ball 0 (23 / 8)) :=
    fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
  have heg : DifferentiableOn ℂ (fun x => Complex.exp (g x)) (ball 0 (23 / 8)) :=
    fun x hx => (hg x hx).cexp.differentiableAt.differentiableWithinAt
  have hrel := (logDeriv_eqOn_iff hf heg isOpen_ball (convex_ball _ _).isPreconnected
    (fun x _ => Complex.exp_ne_zero (g x)) hn).mp
  obtain ⟨k, hk, hfac⟩ := hrel (by
    intro x hx
    rw [logDeriv_apply (fun x => Complex.exp (g x)), (hg x hx).cexp.deriv]
    field_simp)
  have hk₀ : f 0 = k := by simpa [hg₀] using hfac h0
  have hre (w : ℂ) (hw : w ∈ ball 0 (23 / 8)) : (g w).re ≤ M := by
    apply Real.exp_le_exp.mp
    have heq : f w = f 0 * Complex.exp (g w) := by simpa [hk₀] using hfac hw
    have h := hbound w hw
    rw [heq, norm_mul, Complex.norm_exp] at h
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (hn 0 h0))).mp h
  have hgeo (w : ℂ) (hw : w ∈ closedBall z (1 / 16)) : ‖w‖ ≤ 45 / 16 := by
    have hs : ‖w - z‖ ≤ 1 / 16 := by simpa [mem_closedBall, dist_eq_norm] using hw
    linarith [norm_le_norm_sub_add w z]
  have hsub : closedBall z (1 / 16) ⊆ ball (0 : ℂ) (23 / 8) := by
    intro w hw
    rw [mem_ball_zero_iff]
    linarith [hgeo w hw]
  have hC : ∀ w ∈ sphere z (1 / 16), ‖g w‖ ≤ 90 * M := by
    intro w hw
    have hb := sphere_subset_closedBall hw
    have hle := hgeo w hb
    have hd : 0 < 23 / 8 - ‖w‖ := by linarith
    apply (borelCaratheodory_zero hM hgd (fun w hw => hre w hw) (by norm_num) (hsub hb) hg₀).trans
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hle)]
  have hzb : z ∈ ball (0 : ℂ) (23 / 8) := mem_ball_zero_iff.mpr (by linarith)
  rw [← (hg z hzb).deriv]
  apply (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/16)
    (hgd.diffContOnCl_ball hsub) hC).trans
  linarith

theorem logDeriv_bound_after_removing_zeros (f g : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hroots : ∀ ρ ∈ Z, ‖ρ‖ ≤ 23 / 8)
    (hfac : ∀ w ∈ closedBall (0 : ℂ) (47 / 16),
      f w = (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w)
    (hg : DiffContOnCl ℂ g (ball 0 (47 / 16)))
    (hgn : ∀ w ∈ ball (0 : ℂ) (23 / 8), g w ≠ 0)
    {M : ℝ} (hM : 0 < M)
    (hfbound : ∀ w ∈ sphere (0 : ℂ) (47 / 16), ‖f w‖ ≤ ‖f 0‖ * Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 11 / 4) (hzZ : z ∉ Z) :
    ‖logDeriv f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤
      1440 * (M + (∑ ρ ∈ Z, m ρ : ℕ) * Real.log 48) := by
  classical
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ
  let N := ∑ ρ ∈ Z, m ρ
  have hcenter : ‖f 0‖ ≤ (3 : ℝ) ^ N * ‖g 0‖ := by
    rw [hfac 0 (mem_closedBall_self (by norm_num)), norm_mul, norm_prod,
      ← Finset.prod_pow_eq_pow_sum Z m (3 : ℝ)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro ρ hρ
    rw [norm_pow, zero_sub, norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [hroots ρ hρ]) _
  have hboundary (w : ℂ) (hw : w ∈ sphere 0 (47 / 16)) :
      ‖g w‖ ≤ ‖g 0‖ * Real.exp (M + (N : ℝ) * Real.log 48) := by
    have hnw : ‖w‖ = 47/16 := by simpa [mem_sphere, dist_zero_right] using hw
    have hP : (1/16 : ℝ) ^ N ≤ ‖P w‖ := by
      rw [show ‖P w‖ = _ from norm_prod .., ← Finset.prod_pow_eq_pow_sum Z m (1/16 : ℝ)]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro ρ hρ
      rw [norm_pow]
      apply pow_le_pow_left₀ (by norm_num)
      linarith [norm_le_norm_sub_add w ρ, hroots ρ hρ]
    have hU := hfbound w hw
    rw [hfac w (sphere_subset_closedBall hw), norm_mul] at hU
    have hval : (1/16 : ℝ) ^ N * ‖g w‖ ≤ (3 : ℝ) ^ N * ‖g 0‖ * Real.exp M :=
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
        (hU.trans (mul_le_mul_of_nonneg_right hcenter (Real.exp_pos M).le))
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 48)]
    apply (mul_le_mul_iff_right₀ (show 0 < (1 / 16 : ℝ) ^ N by positivity)).mp
    calc
      _ ≤ _ := hval
      _ = _ := by
        have hk : ((1/16 : ℝ) ^ N) * (48 : ℝ) ^ N = 3 ^ N := by rw [← mul_pow]; norm_num
        linear_combination -(‖g 0‖ * Real.exp M) * hk
  have hUpos : 0 < M + (N : ℝ) * Real.log 48 :=
    (add_pos_of_pos_of_nonneg hM (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by norm_num))))
  have hsubset : ball (0 : ℂ) (23 / 8) ⊆ ball 0 (47 / 16) := ball_subset_ball (by norm_num)
  have hregular := logDeriv_bound_nonvanishing_disk g hUpos (hg.1.mono hsubset) hgn
    (fun w hw => norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
      (fun v hv => hboundary v (by rwa [frontier_ball (0 : ℂ) (by norm_num : (47 / 16 : ℝ) ≠ 0)] at hv))
      (subset_closure (hsubset hw))) hz
  have hzin : z ∈ ball (0 : ℂ) (23/8) := mem_ball_zero_iff.mpr (by linarith)
  have heq : f =ᶠ[nhds z] fun w => P w * g w := by
    filter_upwards [isOpen_ball.mem_nhds (hsubset hzin)] with w hw
    exact hfac w (ball_subset_closedBall hw)
  have hpz (ρ : ℂ) (hρ : ρ ∈ Z) : z - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hzZ (e ▸ hρ))
  have hPdiff : DifferentiableAt ℂ P z := by dsimp [P]; fun_prop
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun ρ hρ => pow_ne_zero _ (hpz ρ hρ))
  have hPder : logDeriv P z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
    rw [show logDeriv P z = _ from logDeriv_fun_prod
      (f := fun ρ (w : ℂ) => (w - ρ) ^ m ρ) (fun ρ hρ => pow_ne_zero _ (hpz ρ hρ))
      (fun _ _ => by fun_prop)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul z hPz (hgn z hzin) hPdiff
      (hg.1.differentiableAt (isOpen_ball.mem_nhds (hsubset hzin))), hPder, add_sub_cancel_left]
  exact hregular

theorem inner_disk_multiplicity_bound {f : ℂ → ℂ} (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, ‖ρ‖ ≤ 23 / 8)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (47 / 16))) (hf₀ : f 0 ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) (hboundary : ∀ z ∈ sphere 0 (47 / 16), ‖f z‖ ≤ B) :
    ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℝ) ≤
      Real.log (B / ‖f 0‖) / Real.log (47 / 46) := by
  classical
  let K := closedBall (0 : ℂ) (23 / 8)
  let d := MeromorphicOn.divisor f K
  have ha : AnalyticOnNhd ℂ f K := hf.mono (closedBall_subset_closedBall (by norm_num))
  have hs := d.finiteSupport (isCompact_closedBall 0 (23 / 8))
  let U := Z ∪ hs.toFinset
  have hu : Function.support d ⊆ (U : Set ℂ) :=
    fun _ hi => Finset.mem_union_right _ (hs.mem_toFinset.mpr hi)
  have hcount : ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℤ) ≤ ∑ᶠ w, d w := by
    rw [finsum_eq_sum_of_support_subset _ hu, Nat.cast_sum]
    calc
      _ = ∑ w ∈ Z, d w := by
        apply Finset.sum_congr rfl
        intro w hw
        change _ = MeromorphicOn.divisor f K w
        rw [ha.divisor_apply (mem_closedBall_zero_iff.mpr (hZ w hw))]
        unfold analyticOrderNatAt
        cases h : analyticOrderAt f w using ENat.recTopCoe <;> simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun w _ _ => ha.divisor_nonneg w)
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := (23/8 : ℝ))
    (R := (47/16 : ℝ)) (M := B) (by norm_num) (by norm_num) hB
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 47 / 16)] using hf) hf₀
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 47 / 16)] using hboundary)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 23 / 8),
    show (47 / 16 : ℝ) / (23 / 8) = 47 / 46 by norm_num] at hJ
  exact le_trans (by exact_mod_cast hcount) hJ

theorem local_logDeriv_bound_of_distance (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (47/16))) (hf₀ : f 0 ≠ 0)
    {B D δ : ℝ} (hB : 1 ≤ B) (hD : 0 < D) (hδ : 0 < δ)
    (hboundary : ∀ w ∈ sphere 0 (47 / 16), ‖f w‖ ≤ B)
    (hlog : Real.log (B / ‖f 0‖) ≤ D)
    {z : ℂ} (hz : ‖z‖ ≤ 11/4)
    (hsep : ∀ ρ ∈ closedBall (0 : ℂ) (23/8), f ρ = 0 → δ ≤ ‖z-ρ‖) :
    ‖logDeriv f z‖ ≤ (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) * D := by
  classical
  obtain ⟨Z, g, hZ, hg, hgn, hfac⟩ :=
    remove_disk_zeros f 0 (23 / 8) (47 / 16) (by norm_num) (by norm_num) hf hf₀
  let N := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hr (ρ) (hρ : ρ ∈ Z) := (hZ ρ).mp hρ
  have hd (ρ) (hρ : ρ ∈ Z) : δ ≤ ‖z-ρ‖ := hsep ρ (hr ρ hρ).1 (hr ρ hρ).2
  have hroot (ρ) (hρ : ρ ∈ Z) : ‖ρ‖ ≤ 23 / 8 := mem_closedBall_zero_iff.mp (hr ρ hρ).1
  have hfrel (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖f w‖ ≤ ‖f 0‖ * Real.exp D := by
    apply (hboundary w hw).trans
    have hn := norm_pos_iff.mpr hf₀
    have h := (Real.log_le_iff_le_exp (div_pos (by linarith) hn)).mp hlog
    simpa only [mul_comm] using (div_le_iff₀ hn).mp h
  have hzZ : z ∉ Z := by
    intro hzZ
    have := hd z hzZ
    simp at this
    linarith
  have hlogder := logDeriv_bound_after_removing_zeros f g Z (analyticOrderNatAt f)
    hroot (fun w _ => hfac w)
    (hg.differentiableOn.diffContOnCl_ball Set.Subset.rfl)
    (fun w hw => hgn w (ball_subset_closedBall hw)) hD hfrel hz hzZ
  have hN : (N : ℝ) ≤ D / Real.log (47/46) :=
    (inner_disk_multiplicity_bound Z hroot hf hf₀ hB hboundary).trans
      (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num)))
  have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z-ρ)‖ ≤ (N : ℝ) * (1/δ) := by
    apply (norm_sum_le ..).trans
    rw [show (N : ℝ) = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) by simp [N], Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast, mul_one_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hd ρ hρ)
  have hK : 0 ≤ 1440 * Real.log 48 + 1/δ := by positivity
  calc
    _ ≤ _ := norm_le_norm_sub_add (logDeriv f z) (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z-ρ))
    _ ≤ 1440 * (D + (N : ℝ) * Real.log 48) + N * (1/δ) := add_le_add hlogder hsum
    _ = 1440 * D + (N : ℝ) * (1440 * Real.log 48 + 1 / δ) := by ring
    _ ≤ 1440 * D + (D / Real.log (47/46)) * (1440 * Real.log 48 + 1 / δ) := by gcongr
    _ = _ := by ring

end GoldbachShortInterval

namespace GoldbachShortInterval

/-- Choose a height within one unit of T, quantitatively separated from
every member of a given finite set of ordinates. -/
theorem exists_height_avoiding (B : Finset ℝ) (T : ℝ) :
    ∃ t ∈ Set.Icc T (T + 1), ∀ b ∈ B, 1 / (3 * (B.card + 1 : ℝ)) ≤ |t - b| := by
  classical
  let N : ℝ := B.card + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let grid (j : Fin (B.card + 1)) : ℝ := T + (j.val : ℝ) / N
  have hI (j) : grid j ∈ Set.Icc T (T + 1) := by
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (by positivity) hN.le)
    · change T + (j.val : ℝ) / N ≤ T + 1
      apply add_le_add_right
      apply (div_le_one hN).2
      dsimp [N]
      exact_mod_cast j.isLt.le
  by_contra! hall
  have hchoice (j) : ∃ b : B, |grid j - (b : ℝ)| < 1 / (3 * N) := by
    obtain ⟨b, hb, h⟩ := hall (grid j) (hI j)
    exact ⟨⟨b, hb⟩, h⟩
  choose f hf using hchoice
  have hinj : Function.Injective f := by
    intro i j hij
    have ha := (abs_lt.mp (hf i))
    have hb := (abs_lt.mp (hf j))
    rw [hij] at ha
    have hdiff : |grid i - grid j| < 1 / N := by
      have hthird : (3 : ℝ) * (1 / (3 * N)) = 1 / N := by field_simp
      rw [abs_lt]
      constructor <;> linarith [one_div_pos.mpr hN]
    have hid : grid i - grid j = ((i.val : ℝ) - j.val) / N := by simp [grid]; ring
    rw [hid, abs_div, abs_of_pos hN, div_lt_div_iff_of_pos_right hN, abs_lt] at hdiff
    have hi : i.val < j.val + 1 := by exact_mod_cast (show (i.val : ℝ) < j.val + 1 by linarith [hdiff.2])
    have hj : j.val < i.val + 1 := by exact_mod_cast (show (j.val : ℝ) < i.val + 1 by linarith [hdiff.1])
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

end GoldbachShortInterval

namespace GoldbachShortInterval

open scoped BigOperators

/-- On the line of real part three, the tail of the Dirichlet series has norm at
most one half. The lower bound is uniform in both the character and its modulus. -/
theorem half_le_norm_LFunction_of_re_eq_three {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 3) :
    (1 / 2 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have hhalf : 1 < s.re := by rw [hs]; norm_num
  let f := LSeries.term (fun n : ℕ => χ (n : ZMod q)) s
  let u (k : ℕ) : ℝ := 1 / (2 * ((k : ℝ) + 1))
  have hf : Summable f := χ.LSeriesSummable_of_one_lt_re hhalf
  have hterm (k : ℕ) : ‖f (k + 2)‖ ≤ u k - u (k + 1) := by
    have hk : k + 2 ≠ 0 := by omega
    have hnorm : ‖f (k + 2)‖ =
        ‖χ ((k + 2 : ℕ) : ZMod q)‖ / (((k : ℝ) + 2) ^ 3) := by
      simp only [f, LSeries.norm_term_eq, ite_eq_right hk, hs]
      norm_cast
    rw [hnorm]
    calc
      _ ≤ 1 / (((k : ℝ) + 2) ^ 3) :=
        div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ ≤ _ := by
        simp only [u, Nat.cast_add_one]
        have h1 : 0 < (k : ℝ) + 1 := by positivity
        have h2 : 0 < (k : ℝ) + 2 := by positivity
        rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
        field_simp
        nlinarith [sq_nonneg (k : ℝ)]
  have htail : ‖∑' k : ℕ, f (k + 2)‖ ≤ 1 / 2 := by
    have hshift := (summable_nat_add_iff (f := f) 2).mpr hf
    apply le_of_tendsto hshift.hasSum.tendsto_sum_nat.norm
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
        norm_sum_le_of_le _ (fun k _ => hterm k)
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ 1 / 2 := by
        have hn : 0 ≤ u n := by dsimp [u]; positivity
        simpa [u] using sub_le_self (u 0) hn
  have hfirst : (∑ k ∈ Finset.range 2, f k) = 1 := by
    simp [Finset.sum_range_succ, f]
  have hsplit : (1 : ℂ) + (∑' k : ℕ, f (k + 2)) = χ.LFunction s := by
    rw [χ.LFunction_eq_LSeries hhalf, ← hfirst]
    exact hf.sum_add_tsum_nat_add 2
  have htriangle := norm_sub_le (χ.LFunction s) (∑' k : ℕ, f (k + 2))
  rw [← hsplit, add_sub_cancel_right, norm_one, hsplit] at htriangle
  linarith

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Finset MeasureTheory Set
open scoped Interval

/-- The smoothing multiplier is a normalized average of powers on [1,1+η]. -/
theorem critical_smoothingFactor_norm {η : ℝ} (hη : 0<η) (hη' : η ≤ 1/1000) {s : ℂ}
    (hs : s.re = 1/2) : ‖perronSmoothingFactor η s‖ ≤ 1.001 := by
  have hrep : perronSmoothingFactor η s =
      (∫ u : ℝ in 1..1+η, (u:ℂ)^s)/(η:ℂ) := by
    rw [integral_cpow (Or.inl (by linarith : -1 < s.re))]
    unfold perronSmoothingFactor
    simp only [Complex.ofReal_one,Complex.one_cpow,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hrep, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, div_le_iff₀ hη]
  calc
    _ ≤ 1.001 * |(1+η)-1| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      rw [uIoc_of_le (by linarith : 1≤1+η)] at hu
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1] : 0<u),hs,← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith [hu.2]⟩
    _ = _ := by rw [add_sub_cancel_left,abs_of_pos hη]

noncomputable def smoothedZeroPolynomial (S : Finset ℂ) (δ η y : ℝ) : ℂ :=
  ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ:ℂ) *
    (zeroIncrementWeight δ ρ * perronSmoothingFactor η ρ * (y:ℂ)^ρ)

theorem smoothedZeroPolynomial_continuous (S : Finset ℂ) (δ η : ℝ)
    (hline : ∀ ρ ∈ S, ρ.re=1/2) : Continuous (smoothedZeroPolynomial S δ η) := by
  apply continuous_finsetSum
  intro ρ hρ
  exact continuous_const.mul (continuous_const.mul (Complex.continuous_ofReal_cpow_const
    (by rw [hline ρ hρ]; norm_num)))

private theorem increment_spectral_sum {ι : Type*} (S : Finset ι) (γ : ι → ℝ) {δ : ℝ}
    (hd : 0 < δ) (hu : δ ≤ 1/10000000000000)
    (hrow : ∀ U : ℝ, 10^13 ≤ U → ∀ t : ℝ, |t| ≤ U →
      ∑ i ∈ S, zeroPoissonKernel (t-γ i) ≤ Real.log U) :
    (∑ i ∈ S, (zeroIncrementMajorant δ (γ i))^2 * ∑ j ∈ S, zeroPoissonKernel (γ i-γ j)) ≤
      2.22*δ*(Real.log (2.0001/δ))^2 := by
  let T := 2.0001/δ
  let w := fun i => ∑ j ∈ S, zeroPoissonKernel (γ i - γ j)
  let P := fun k : ℕ => ((2:ℝ)^(k+1)*T/3) * (Real.log ((2:ℝ)^(k+1)*T))^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hT₂ : 2*10^13 ≤ T := (le_div_iff₀ hd).2 (by linarith)
  have hP (k : ℕ) : (∑ i ∈ S.filter (fun i => |γ i| ≤ (2:ℝ)^(k+1)*T), w i) ≤ P k := by
    apply poisson_weighted_count_from_rows S γ hrow
    exact hT₂.trans (le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num)))
  have hser : Summable (fun k : ℕ => (1/4 : ℝ)^k*P k) := by
    have eqn : (fun k : ℕ => (1/4 : ℝ)^k*P k) = layerMajorant T := by
      funext k
      simp only [P,layerMajorant,mul_assoc]
    rw [eqn]
    exact layerMajorant_summable hT (spectral_log_lower hd hu)
  apply (spectral_increment_majorant_le_cumulative S γ w hd hT
    (by dsimp [T]; field_simp) (fun i _ => sum_nonneg fun j _ => zeroPoissonKernel_nonneg _) P hP hser).trans
  simpa only [P,layerMajorant,mul_assoc,T] using spectral_layer_total hd hu

/-- A smoothed finite zero sum satisfies the required uniform local energy estimate. -/
theorem smoothedZeroPolynomial_energy (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0)
    {x η : ℝ} (hx : 1100000000000000000 ≤ x) (hη : 0<η) (hη' : η ≤ 1/1000) :
    (∫ y : ℝ in 1..x, ‖smoothedZeroPolynomial S (relativeWidth x) η y‖^2) ≤
      2.23 * relativeWidth x * (Real.log x)^2 * x^2 := by
  let δ := relativeWidth x
  let C := zetaZeroCopies S
  let a (i : (_:ℂ) × ℕ) := zeroIncrementWeight δ i.1 * perronSmoothingFactor η i.1
  let w (i : (_:ℂ) × ℕ) := ∑ j ∈ C, zeroPoissonKernel (i.1.im-j.1.im)
  let A (i : (_:ℂ) × ℕ) := zeroIncrementMajorant δ i.1.im
  have hr (ρ : ℂ) (hρ : ρ ∈ S) : ρ.re = 1/2 := by
    obtain ⟨hpos,h1,hz⟩ := hS ρ hρ
    apply hRH ρ hz
    · rintro ⟨n,hn⟩
      have he := congrArg Complex.re hn
      norm_num [Complex.mul_re] at he
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    · intro h; simp [h] at h1
  have hrC (i) (hi : i∈C) : i.1.re=1/2 := hr i.1 (Finset.mem_sigma.mp hi).1
  have heq (y : ℝ) : smoothedZeroPolynomial S δ η y = ∑ i ∈ C, a i * (y:ℂ)^i.1 := by
    change _ = ∑ i ∈ zetaZeroCopies S, (fun ρ => zeroIncrementWeight δ ρ * perronSmoothingFactor η ρ * (y:ℂ)^ρ) i.1
    rw [sum_zetaZeroCopies S (fun ρ => zeroIncrementWeight δ ρ * perronSmoothingFactor η ρ * (y:ℂ)^ρ)]
    simp only [nsmul_eq_mul,smoothedZeroPolynomial]
  obtain ⟨_,hd,hu,_,hl,hxlog⟩ := relativeWidth_bounds hx
  change 0 < δ at hd
  have hφ := critical_line_physical_energy_le C a (fun i => i.1) hrC (by linarith : 1≤x)
  simp_rw [← heq] at hφ
  have hW (i) : 0 ≤ w i := sum_nonneg fun j _ => zeroPoissonKernel_nonneg _
  have ha (i) (hi : i∈C) : ‖a i‖^2 ≤ 1.001^2 * A i^2 := by
    have h1 := zeroIncrementWeight_norm_le hd.le (by norm_num at hu ⊢; exact hu) (hrC i hi)
    have h2 := critical_smoothingFactor_norm hη hη' (hrC i hi)
    have hm := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    change ‖zeroIncrementWeight δ i.1 * perronSmoothingFactor η i.1‖^2 ≤ _
    rw [norm_mul, ← mul_pow, mul_comm (1.001:ℝ)]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hm 2
  have hs := increment_spectral_sum C (fun i => i.1.im) hd hu
    (fun _ hU _ ht => riemannZeta_copies_poisson_row hRH S hS hU ht)
  change (∑ i ∈ C, A i^2*w i) ≤ _ at hs
  have hb : (∑ i ∈ C, ‖a i‖^2*w i) ≤ 1.001^2*(2.22*δ*(Real.log x)^2) := calc
    _ ≤ ∑ i ∈ C, 1.001^2 * (A i^2*w i) := sum_le_sum fun i hi => by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (ha i hi) (hW i)
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hl hxlog 2) (by positivity))) (by positivity)
  change _ ≤ x^2*(∑ i ∈ C, ‖a i‖^2*w i) at hφ
  apply hφ.trans ((mul_le_mul_of_nonneg_left hb (sq_nonneg x)).trans ?_)
  nlinarith only [mul_nonneg (mul_nonneg hd.le (sq_nonneg (Real.log x))) (sq_nonneg x)]

/-- The polynomial in the energy estimate is the very same sum of residues
that appears in the contour shift. -/
theorem smoothedZeroPolynomial_eq_kernel (S : Finset ℂ) (η δ y : ℝ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re) :
    smoothedZeroPolynomial S δ η y = ∑ ρ ∈ S,
      (analyticOrderNatAt riemannZeta ρ:ℂ) * entireSmoothedIncrementKernel η δ y ρ := by
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hp := hS ρ hρ
  have h0 : ρ ≠ 0 := by intro he; simp [he] at hp
  have h1 : ρ+1 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he'
    linarith
  rw [entireSmoothedIncrementKernel_eq η δ y h0 h1]
  dsimp only [smoothedIncrementKernel,zeroIncrementWeight]
  ring

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex ArithmeticFunction MeasureTheory Set Filter
open scoped Topology ComplexConjugate

/-- Absolute bound on the reflected Dirichlet series. -/
theorem zeta_logDeriv_norm_three_halves {s : ℂ} (hs : s.re = 3/2) :
    ‖logDeriv riemannZeta s‖ ≤ 16 := by
  have hs' : 1 < s.re := by rw [hs]; norm_num
  let f := LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) s
  have hf : Summable f := LSeriesSummable_vonMangoldt hs'
  have hseries : ‖logDeriv riemannZeta s‖ = ‖∑' n, f n‖ := by
    have h := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'
    change (∑' n, f n) = _ at h
    rw [h,neg_div,norm_neg]
    rfl
  let g := fun t : ℝ => t ^ (-(5/4):ℝ)
  have hanti : AntitoneOn g (Ici 1) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.out]) hab (by norm_num)
  have hint : IntegrableOn g (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hnon : ∀ t ∈ Ioi 1, 0 ≤ g t := fun t ht => Real.rpow_nonneg (by linarith [ht.out]) _
  have hsum := AntitoneOn.tsum_comp_add_le_integral (f := g) 1 (by simpa using hanti)
    (by simpa using hint) (by simpa using hnon)
  have hG : Summable (fun n : ℕ => g (n+1+1 : ℕ)) := by
    have h := Real.summable_nat_rpow.mpr (show -(5/4:ℝ) < -1 by norm_num)
    exact (summable_nat_add_iff 2).2 h
  have hpoint (n : ℕ) : ‖f (n+2)‖ ≤ 4*g (n+1+1 : ℕ) := by
    let m := n+2
    have hpos : 0 < (m:ℝ) := by dsimp [m]; positivity
    have hp := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (1/4))
    rw [Real.log_rpow hpos] at hp
    have hl : vonMangoldt m ≤ 4*(m:ℝ)^(1/4:ℝ) := by linarith [vonMangoldt_le_log (n := m)]
    change ‖f m‖ ≤ 4*(m:ℝ)^(-(5/4):ℝ)
    simp only [f,LSeries.norm_term_eq,ite_eq_right (show m ≠ 0 by dsimp [m]; omega),
      hs,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
    apply (div_le_div_of_nonneg_right hl (by positivity)).trans_eq
    rw [mul_div_assoc, ← Real.rpow_sub hpos]
    norm_num
  rw [hseries]
  apply (norm_tsum_le_tsum_norm hf.norm).trans
  rw [← hf.norm.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  have hzero : ‖f 0‖ + ‖f 1‖ = 0 := by simp [f]
  rw [hzero,zero_add]
  apply ((summable_nat_add_iff 2 |>.2 hf.norm).tsum_le_tsum hpoint (hG.mul_left 4)).trans
  rw [tsum_mul_left]
  have hi : ∫ t in Ioi (1:ℝ), g t = 4 := by
    rw [show g = (fun t : ℝ => t^(-(5/4):ℝ)) from rfl,integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
  rw [Nat.cast_one,hi] at hsum
  linarith

theorem digamma_conjugate (z : ℂ) : digamma (conj z) = conj (digamma z) := by
  have hf : conj ∘ Gamma ∘ conj = Gamma := by ext w; simp [Gamma_conj]
  have hd := congrFun (deriv_conj_conj (f := Gamma)) (conj z)
  rw [hf] at hd
  simpa only [digamma_def,logDeriv_apply,Function.comp_apply,conj_conj,map_div₀,Gamma_conj] using
    (congrArg (fun v : ℂ => v / Gamma (conj z)) hd)

private theorem gammaFactor_deriv {s : ℂ} (hp : ∀ n : ℕ, s/2 ≠ -n) :
    HasDerivAt Gammaℝ
      (Gammaℝ s * ((-(Real.log Real.pi : ℝ) : ℂ) + digamma (s/2))/2) s := by
  have hπ : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h₁ := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi:ℂ)) (.inl hπ)
  have h₂ := (differentiableAt_Gamma _ hp).hasDerivAt.comp s ((hasDerivAt_id s).div_const 2)
  have hh := h₁.mul h₂
  convert hh using 1
  · rfl
  · rw [Gammaℝ_def,digamma_def,logDeriv_apply,Complex.ofReal_log Real.pi_pos.le]
    simp only [Pi.neg_apply,id_eq,Function.comp_apply]
    field_simp [Gamma_ne_zero hp]

/-- The symmetric completion gives a functional equation in which the two
digamma terms are conjugate up to a single recurrence on the left edge. -/
theorem zeta_logDeriv_negative_half {s : ℂ} (hs : s.re = -1/2) :
    logDeriv riemannZeta s = -logDeriv riemannZeta (1-s) + (Real.log Real.pi : ℂ)
      - ((digamma (s/2+1)).re : ℂ) + 1/s := by
  have hn : s ≠ 0 := by intro h; norm_num [h] at hs
  have ho : s ≠ 1 := by intro h; norm_num [h] at hs
  have hr : (1-s).re = 3/2 := by simp [hs]; norm_num
  have hro : 1-s ≠ 1 := fun h => hn (sub_eq_self.mp h)
  have hrn : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm ho)
  have hpos (n : ℕ) : (1-s)/2 ≠ -n := by
    intro h
    have := congrArg Complex.re h
    simp only [div_ofNat_re,hr,neg_re,natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hneg (n : ℕ) : s/2 ≠ -n := by
    intro h
    have := congrArg Complex.re h
    simp only [div_ofNat_re,hs,neg_re,natCast_re] at this
    rcases n with _|n
    · norm_num at this
    · push_cast at this
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hg {w : ℂ} (h : ∀ n : ℕ, w/2 ≠ -n) : Gammaℝ w ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))) (Gamma_ne_zero h)
  have hζ' := riemannZeta_ne_zero_of_one_lt_re (s := 1-s) (by rw [hr]; norm_num)
  have hC : completedRiemannZeta (1-s) ≠ 0 := by
    rw [riemannZeta_def_of_ne_zero hrn] at hζ'
    exact (div_ne_zero_iff.mp hζ').1
  have hζ : riemannZeta s ≠ 0 := by
    rw [riemannZeta_def_of_ne_zero hn,← completedRiemannZeta_one_sub s]
    exact div_ne_zero hC (hg hneg)
  have heq {w : ℂ} (hw : w ≠ 0) (hp : ∀ n : ℕ, w/2 ≠ -n) :
      (fun v => riemannZeta v * Gammaℝ v) =ᶠ[𝓝 w] completedRiemannZeta := by
    filter_upwards [eventually_ne_nhds hw,(gammaFactor_deriv hp).continuousAt.eventually_ne (hg hp)]
      with v hv hgv
    rw [riemannZeta_def_of_ne_zero hv,div_mul_cancel₀ _ hgv]
  have eq₁ := (logDeriv_congr_nhds (heq hn hneg)).eq_of_nhds
  have eq₂ := (logDeriv_congr_nhds (heq hrn hpos)).eq_of_nhds
  rw [logDeriv_fun_mul _ hζ (hg hneg) (differentiableAt_riemannZeta ho) (gammaFactor_deriv hneg).differentiableAt] at eq₁
  rw [logDeriv_fun_mul _ hζ' (hg hpos) (differentiableAt_riemannZeta hro) (gammaFactor_deriv hpos).differentiableAt] at eq₂
  have hsym : completedRiemannZeta ∘ (fun v : ℂ => 1-v) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  have eh := congrArg (fun f : ℂ → ℂ => logDeriv f s) hsym
  change logDeriv (completedRiemannZeta ∘ (fun v : ℂ => 1-v)) s = logDeriv completedRiemannZeta s at eh
  have hdref : deriv (fun v : ℂ => 1-v) s = -1 := ((hasDerivAt_id s).const_sub (1:ℂ)).deriv
  rw [logDeriv_comp (differentiableAt_completedZeta hrn hro) (by fun_prop),hdref] at eh
  have hfac {w : ℂ} (hp : ∀ n : ℕ, w/2 ≠ -n) : logDeriv Gammaℝ w =
      ((-(Real.log Real.pi : ℝ) : ℂ)+digamma (w/2))/2 := by
    rw [logDeriv_apply,(gammaFactor_deriv hp).deriv]
    field_simp [hg hp]
  rw [hfac hneg] at eq₁
  rw [hfac hpos] at eq₂
  have hpair : (1-s)/2 = conj (s/2+1) := by
    apply Complex.ext <;> simp only [div_ofNat_re,div_ofNat_im,sub_re,sub_im,one_re,one_im,
      conj_re,conj_im,add_re,add_im,hs] <;> ring
  rw [hpair,digamma_conjugate] at eq₂
  have he := Complex.add_conj (digamma (s/2+1))
  push_cast at he
  have hd := digamma_apply_add_one (s/2) hneg
  have hi : (s/2)⁻¹ = 2/s := by ring
  rw [hi] at hd
  linear_combination eq₁ + eq₂ - eh - he/2 + hd/2

/-- On the entire displaced vertical line the logarithmic derivative has
logarithmic growth with an absolute numerical constant. -/
theorem zeta_logDeriv_left_bound (t : ℝ) :
    ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|) := by
  let s : ℂ := ⟨-1/2,t⟩
  have hs : s.re = -1/2 := rfl
  have hr := zeta_logDeriv_norm_three_halves (s := 1-s) (by norm_num [s])
  have hπ : |Real.log Real.pi| ≤ 4 := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    linarith [Real.log_le_sub_one_of_pos Real.pi_pos,Real.pi_lt_four]
  have he : s/2+1 = (⟨3/4,t/2⟩ : ℂ) := by apply Complex.ext <;> norm_num [s]
  have hsN : 1/2 ≤ ‖s‖ := by
    have hh := Complex.abs_re_le_norm s
    norm_num [hs] at hh
    exact hh
  have hInv : ‖1/s‖ ≤ 2 := by
    rw [norm_div,norm_one]
    exact (div_le_iff₀ (by linarith)).2 (by linarith)
  have hlog : (1/2:ℝ) ≤ Real.log (2+|t|) :=
    le_trans (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  change ‖logDeriv riemannZeta s‖ ≤ _
  rw [zeta_logDeriv_negative_half hs,he]
  calc
    _ ≤ ‖-logDeriv riemannZeta (1-s)‖ + ‖(Real.log Real.pi : ℂ)‖ +
          ‖((digamma (⟨3/4,t/2⟩ : ℂ)).re : ℂ)‖ + ‖1/s‖ := by
      generalize -logDeriv riemannZeta (1-s) = a
      generalize ((Real.log Real.pi : ℝ) : ℂ) = b
      generalize (((⟨3/4,t/2⟩ : ℂ).digamma.re : ℝ) : ℂ) = c
      generalize (1/s) = d
      linarith only [norm_add_le a b,norm_sub_le (a+b) c,norm_add_le (a+b-c) d]
    _ ≤ _ := by
      simp only [norm_neg,Complex.norm_real,Real.norm_eq_abs]
      linarith [digamma_three_fourths_abs t]

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Metric Set Filter
open scoped Topology

private theorem norm_cos_le_exp_abs_im (v : ℂ) : ‖Complex.cos v‖ ≤ Real.exp |v.im| := by
  rw [Complex.cos,norm_div]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
  have h₁ : ‖Complex.exp (v*I)‖ ≤ Real.exp |v.im| := by
    rw [Complex.norm_exp,Real.exp_le_exp]
    simpa using neg_le_abs v.im
  have h₂ : ‖Complex.exp (-v*I)‖ ≤ Real.exp |v.im| := by
    rw [Complex.norm_exp,Real.exp_le_exp]
    simpa using le_abs_self v.im
  linarith [norm_add_le (Complex.exp (v*I)) (Complex.exp (-v*I))]

private theorem reg_zeta_mul {s : ℂ} (h : s ≠ 1) :
    riemannZeta₁ s = (s-1)*riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul h,← mul_assoc,mul_inv_cancel₀ (sub_ne_zero.mpr h),one_mul]

/-- Exponential growth on a fixed strip crossing the imaginary axis. -/
theorem zeta_regular_horizontal_growth :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, -1 ≤ s.re → 1 ≤ |s.im| →
      ‖riemannZeta₁ s‖ ≤ Real.exp (K*(1+‖s‖)) := by
  let G := Real.Gamma (1/4) + 1
  have hG : 1 ≤ G := by dsimp [G]; linarith [Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/4)]
  refine ⟨18*G+5,by linarith,?_⟩
  intro s hleft hheight
  let R := 1+‖s‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hE : 1+R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
  have hE' : R ≤ Real.exp R := by linarith
  have habsorb : 18*G * Real.exp (5*R) ≤ Real.exp ((18*G+5)*R) := by
    rw [add_mul,Real.exp_add]
    gcongr
    exact (show 18*G ≤ 18*G*R by nlinarith [mul_nonneg (show 0≤G by linarith) (sub_nonneg.mpr hR)]).trans
      (by linarith [Real.add_one_le_exp (18*G*R)])
  by_cases hs : 1/8 ≤ s.re
  · apply (zeta_pole_removed_norm_le_on_strip s hs).trans
    change 9*R^2 ≤ _
    apply le_trans _ habsorb
    have htwo : (Real.exp R)^2 = Real.exp (2*R) := by simpa using (Real.exp_nat_mul R 2).symm
    have he : R^2 ≤ Real.exp (5*R) := (pow_le_pow_left₀ (by linarith) hE' 2).trans
      (htwo.le.trans (Real.exp_le_exp.mpr (by linarith)))
    exact mul_le_mul (by linarith) he (sq_nonneg _) (by linarith)
  let w := 1-s
  have hwr : 1/4 ≤ w.re := by change 1/4 ≤ 1-s.re; linarith
  have hwr' : w.re ≤ 2 := by change 1-s.re ≤ 2; linarith
  have hwΓ := gamma_upper_by_factorial (s:=w) (n:=1) hwr (by norm_num; exact hwr')
  norm_num only [Nat.factorial_one,Nat.cast_one] at hwΓ
  have hsn : 1 ≤ ‖s‖ := hheight.trans (abs_im_le_norm s)
  have hs0 : s ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hsn)
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hheight
  have hw1 : w ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
  have hwp (n : ℕ) : w ≠ -n := by
    intro h
    have hb := congrArg re h
    simp only [neg_re,natCast_re] at hb
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hwN : ‖w‖ ≤ R := by simpa [w,R] using norm_sub_le (1:ℂ) s
  have hmN : ‖s-1‖ ≤ R := by simpa [R,add_comm] using norm_sub_le s (1:ℂ)
  have hζ : ‖riemannZeta w‖ ≤ 9*(1+R)^2 := by
    rw [riemannZeta_eq_inv_sub_mul hw1,norm_mul,norm_inv,show w-1 = -s by dsimp [w]; abel,norm_neg]
    calc
      _ ≤ 1 * (9*(1+‖w‖)^2) := mul_le_mul (inv_le_one_of_one_le₀ hsn)
        (zeta_pole_removed_norm_le_on_strip w (by linarith)) (norm_nonneg _) (by norm_num)
      _ ≤ _ := by rw [one_mul]; gcongr
  have hp : ‖((2:ℂ)*Real.pi)^(-w)‖ ≤ 1 := by
    rw [show (2:ℂ)*Real.pi = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity),neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hcos : ‖Complex.cos (Real.pi*w/2)‖ ≤ Real.exp (2*R) := by
    apply (norm_cos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    calc
      _ ≤ ‖(Real.pi:ℂ)*w/2‖ := abs_im_le_norm _
      _ = Real.pi * ‖w‖ / 2 := by rw [norm_div,norm_mul,Complex.norm_of_nonneg Real.pi_pos.le]; norm_num
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (norm_nonneg w)]
  have hfun := riemannZeta_one_sub hwp hw1
  rw [show 1-w=s by dsimp [w]; abel] at hfun
  rw [reg_zeta_mul hs1,hfun]
  simp only [norm_mul,Complex.norm_ofNat]
  apply le_trans _ habsorb
  calc
    _ ≤ Real.exp R * (2*1*G*Real.exp (2*R)*(9*(Real.exp R)^2)) := by
      apply mul_le_mul (hmN.trans hE') _ (by positivity) (Real.exp_pos _).le
      gcongr
      exact hζ.trans (by gcongr)
    _ = 18*G*Real.exp (5*R) := by
      rw [show Real.exp (5*R) = (Real.exp R)^5 by simpa using Real.exp_nat_mul R 5,
        show Real.exp (2*R) = (Real.exp R)^2 by simpa using Real.exp_nat_mul R 2]
      ring

private theorem horizontal_zeta_logDeriv_subtract_pole {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
  have hs' := sub_ne_zero.mpr hs
  have hreg : riemannZeta₁ s ≠ 0 := by
    intro h
    exact hz (by rw [riemannZeta_eq_inv_sub_mul hs,h,mul_zero])
  rw [logDeriv_apply,logDeriv_apply,deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs,
    riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring

/-- Uniform horizontal-edge estimate at a distance at least δ from the zeros. -/
theorem horizontal_zeta_logDeriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (δ : ℝ), -1/2 ≤ s.re → s.re ≤ 2 →
      10 ≤ |s.im| → 0 < δ → (∀ ρ : ℂ, riemannZeta ρ = 0 → δ ≤ ‖s-ρ‖) →
      ‖logDeriv riemannZeta s‖ ≤ C*(1+1/δ)*(1+|s.im|) := by
  obtain ⟨K,hK,hgrowth⟩ := zeta_regular_horizontal_growth
  let L := Real.log (47/46)
  let A := 1440 + (1440*Real.log 48 + 2)/L
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hl48 : 0 < Real.log 48 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨8*K*A+1,by positivity [show 0 < K by linarith],?_⟩
  intro s δ hs₀ hs₁ ht hδ hsep
  let c : ℂ := ⟨3,s.im⟩
  let f (w : ℂ) := riemannZeta₁ (c+(4/3)*w)
  let z : ℂ := (s-c)/(4/3)
  let D := K*(8+|s.im|)
  have hD : 0 < D := by dsimp only [D]; positivity [show 0<K by linarith]
  have hcenter : 1 ≤ ‖f 0‖ := by
    have hfac : 2 ≤ ‖c-1‖ := by
      have hh := Complex.abs_re_le_norm (c-1)
      norm_num [c] at hh
      exact hh
    have hz : (1/2:ℝ) ≤ ‖riemannZeta c‖ := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using
        (half_le_norm_LFunction_of_re_eq_three (1 : DirichletCharacter ℂ 1) (s:=c) rfl)
    have hne : c ≠ 1 := by intro h; have hh := congrArg re h; norm_num [c] at hh
    simp only [f,mul_zero,add_zero,reg_zeta_mul hne,norm_mul]
    calc (1:ℝ) = 2*(1/2) := by norm_num
         _ ≤ _ := mul_le_mul hfac hz (by norm_num) (norm_nonneg _)
  have hpos := zero_lt_one.trans_le hcenter
  have hc : ‖c‖ ≤ 3+|s.im| := by simpa [c] using norm_le_abs_re_add_abs_im c
  have hnscale : ‖(4/3:ℂ)‖ = 4/3 := by norm_num [norm_div]
  have hbound (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖f w‖ ≤ Real.exp D := by
    let u : ℂ := (4/3)*w
    have hw' : ‖w‖ = 47/16 := by simpa [mem_sphere] using hw
    have hu : ‖u‖ ≤ 4 := by rw [show ‖u‖ = _ from norm_mul _ _,hnscale,hw']; norm_num
    have hR : -1 ≤ (c+u).re := by
      change -1 ≤ 3+u.re
      linarith [(abs_le.mp ((abs_re_le_norm u).trans hu)).1]
    have hT : 1 ≤ |(c+u).im| := by
      have hh := abs_sub (s.im+u.im) u.im
      rw [add_sub_cancel_right] at hh
      change 1 ≤ |s.im+u.im|
      linarith [(abs_im_le_norm u).trans hu]
    apply (hgrowth (c+u) hR hT).trans
    apply Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ K))
    linarith [norm_add_le c u]
  have hlog : Real.log (Real.exp D / ‖f 0‖) ≤ D := by
    simpa using Real.log_le_log (div_pos (Real.exp_pos _) hpos) (div_le_self (Real.exp_pos D).le hcenter)
  have hz' : c+(4/3)*z = s := by dsimp only [z]; ring
  have hzN : ‖z‖ ≤ 11/4 := by
    have hh : s-c = ((s.re-3:ℝ):ℂ) := by apply Complex.ext <;> simp [c]
    rw [show ‖z‖ = _ from norm_div _ _,hnscale,hh,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (by linarith : s.re-3≤0)]
    linarith
  have hloc (w : ℂ) (_ : w ∈ closedBall (0:ℂ) (23/8)) (hfw : f w = 0) : δ/2 ≤ ‖z-w‖ := by
    let v := c+(4/3)*w
    have hne : v ≠ 1 := by
      intro h
      change riemannZeta₁ v = 0 at hfw
      simp [h,riemannZeta₁_one] at hfw
    have hzeta : riemannZeta v = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hne,show riemannZeta₁ v = 0 from hfw,mul_zero]
    have hh := hsep v hzeta
    rw [show s-v = (4/3)*(z-w) by dsimp only [v]; linear_combination -hz',norm_mul,hnscale] at hh
    linarith
  have han : AnalyticOnNhd ℂ f (closedBall 0 (47/16)) := by
    intro w _
    exact (differentiable_riemannZeta₁.analyticAt _).comp (by fun_prop)
  have hlocal := local_logDeriv_bound_of_distance f han (norm_pos_iff.mp hpos)
    (Real.one_le_exp hD.le) hD (half_pos hδ) hbound hlog hzN hloc
  have hd : HasDerivAt f (deriv riemannZeta₁ s * (4/3)) z := by
    have hd₁ := (differentiable_riemannZeta₁ (c+(4/3)*z)).hasDerivAt
    have hmap := (((hasDerivAt_id' z).const_mul (4/3)).const_add c)
    simpa only [hz',mul_one,Function.comp_def] using hd₁.comp z hmap
  have hre : logDeriv f z = logDeriv riemannZeta₁ s * (4/3) := by
    rw [logDeriv_apply,hd.deriv,logDeriv_apply,show f z=riemannZeta₁ s by simp [f,hz'] ]
    ring
  rw [hre,norm_mul,hnscale] at hlocal
  have hcoef : 1440+(1440*Real.log 48 + 1/(δ/2))/L ≤ A*(1+1/δ) := by
    dsimp only [A]
    rw [show 1/(δ/2)=2/δ by ring]
    apply (le_of_sub_nonneg ?_)
    have hid : (1440+(1440*Real.log 48+2)/L)*(1+1/δ) -
        (1440+(1440*Real.log 48+2/δ)/L) =
        2/L + 1440/δ + 1440*Real.log 48 / L / δ := by ring
    rw [hid]
    positivity
  have hD' : D ≤ 8*K*(1+|s.im|) := by dsimp only [D]; nlinarith [mul_nonneg (show 0≤K by linarith) (abs_nonneg s.im)]
  have hreg : ‖logDeriv riemannZeta₁ s‖ ≤ (8*K*A)*(1+1/δ)*(1+|s.im|) := by
    apply le_trans (by linarith [norm_nonneg (logDeriv riemannZeta₁ s)] :
      ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ s‖*(4/3)) (hlocal.trans ?_)
    exact (mul_le_mul hcoef hD' hD.le (mul_nonneg hA.le (by positivity))).trans_eq (by ring)
  have hsn : s ≠ 1 := by intro h; norm_num [h] at ht
  have hzeta : riemannZeta s ≠ 0 := by
    intro h
    have hh := hsep s h
    rw [sub_self,norm_zero] at hh
    linarith
  have him : 1 ≤ ‖s-1‖ := by
    have hh := abs_im_le_norm (s-1)
    simp only [sub_im,one_im,sub_zero] at hh
    linarith
  rw [horizontal_zeta_logDeriv_subtract_pole hsn hzeta]
  apply (norm_sub_le ..).trans
  rw [norm_inv]
  have hbig : 1 ≤ (1+1/δ)*(1+|s.im|) := one_le_mul_of_one_le_of_one_le
    (by linarith [one_div_pos.mpr hδ]) (by linarith [abs_nonneg s.im])
  nlinarith [inv_le_one_of_one_le₀ him]

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Filter Set Finset

private theorem positive_zeta_zero_order {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    0 < analyticOrderNatAt riemannZeta ρ := by
  have h₁ : ρ ≠ 1 := by intro h; exact riemannZeta_one_ne_zero (h ▸ hρ)
  have hc : IsConnected (({1} : Set ℂ)ᶜ) := isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h₂ : (2 : ℂ) ∈ (({1}:Set ℂ)ᶜ) := by simp
  have hne : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hfin := (analyticOn_riemannZeta.exists_analyticOrderAt_ne_top_iff_forall hc).mp
    ⟨⟨2,h₂⟩,by rw [(analyticOn_riemannZeta 2 h₂).analyticOrderAt_eq_zero.mpr hne]; simp⟩ ⟨ρ,h₁⟩
  exact ENat.toNat_pos ((analyticOn_riemannZeta ρ h₁).analyticOrderAt_ne_zero.mpr hρ) hfin

/-- Each high unit interval contains a height quantitatively separated from the
ordinates of all zeta zeros, including the trivial zeros. -/
theorem exists_good_zeta_height (hRH : RiemannHypothesis) (T : ℝ) (hT : 10^13+10 ≤ |T|) :
    ∃ t ∈ Icc T (T+1), ∀ ρ : ℂ, riemannZeta ρ=0 →
      1/(3*(4*Real.sqrt |t|+1)) ≤ |t-ρ.im| := by
  classical
  let c := T+1/2
  let U := 2*|T|
  let K := Icc (1/2:ℝ) (1/2) ×ℂ Icc (c-1) (c+1)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  let Z := hK.inter_riemannZetaZeros_finite.toFinset
  let B := Z.image Complex.im
  have hZ (ρ : ℂ) : ρ ∈ Z ↔ ρ.re=1/2 ∧ |ρ.im-c|≤1 ∧ riemannZeta ρ=0 := by
    simp only [Z,Set.Finite.mem_toFinset,Set.mem_inter_iff,mem_riemannZetaZeros]
    change ((1/2 ≤ ρ.re ∧ ρ.re ≤ 1/2) ∧ c-1 ≤ ρ.im ∧ ρ.im ≤ c+1) ∧ _ ↔ _
    rw [abs_le]
    constructor
    · rintro ⟨⟨⟨hl,hr⟩,h1,h2⟩,hz⟩
      exact ⟨le_antisymm hr hl,⟨by linarith,by linarith⟩,hz⟩
    · rintro ⟨he,⟨h1,h2⟩,hz⟩
      exact ⟨⟨⟨he.ge,he.le⟩,by linarith,by linarith⟩,hz⟩
  have hSZ (ρ : ℂ) (hρ : ρ∈Z) : 0<ρ.re ∧ ρ.re<1 ∧ riemannZeta ρ=0 := by
    have hz := (hZ ρ).1 hρ
    rw [hz.1]
    exact ⟨by norm_num,by norm_num,hz.2.2⟩
  have hU : 10^13 ≤ U := by dsimp [U]; linarith
  have hc : |c| ≤ U := calc
    _ ≤ |T|+|1/2| := abs_add_le .. 
    _ ≤ _ := by dsimp [U]; norm_num; linarith
  have hrow := riemannZeta_finite_poisson_row hRH Z hSZ hU hc
  have hcard : (Z.card:ℝ) ≤ 2*Real.log U := by
    have half (ρ : ℂ) (hρ : ρ∈Z) :
        (1/2:ℝ) ≤ (analyticOrderNatAt riemannZeta ρ:ℝ)*(4/(4+(c-ρ.im)^2)) := by
      obtain ⟨_,hd,hζ⟩ := (hZ ρ).1 hρ
      have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta ρ := by
        exact_mod_cast positive_zeta_zero_order hζ
      have hs : (c-ρ.im)^2 ≤ 1 := by
        rw [← abs_sub_comm] at hd
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hd 2
      have hk : 1/2 ≤ 4/(4+(c-ρ.im)^2) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      exact hk.trans (le_mul_of_one_le_left (by positivity) hm)
    have hh := (Finset.sum_le_sum half).trans hrow
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    linarith
  obtain ⟨t,ht,havoid⟩ := exists_height_avoiding B T
  have hTt : |T| ≤ |t|+1 := calc
    |T| = |(T-t)+t| := by rw [sub_add_cancel]
    _ ≤ |T-t|+|t| := abs_add_le .. 
    _ ≤ _ := by rw [abs_of_nonpos (by linarith [ht.1] : T-t≤0)]; linarith [ht.2]
  have htbig : 1≤|t| := by linarith
  have hlog : Real.log U ≤ Real.sqrt U := by
    have hp : 0 < U := by linarith
    have hr : 0 < Real.sqrt U := Real.sqrt_pos.mpr hp
    have hh := Real.log_le_sub_one_of_pos (div_pos hr (by norm_num : (0:ℝ)<2))
    rw [Real.log_div hr.ne' (by norm_num),Real.log_sqrt hp.le] at hh
    linarith [Real.log_two_lt_d9]
  have hsqrt : Real.sqrt U ≤ 2*Real.sqrt |t| := by
    apply (Real.sqrt_le_sqrt (show U ≤ 4*|t| by dsimp [U]; linarith)).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  have hB : (B.card:ℝ) ≤ 4*Real.sqrt |t| := by
    have hb : (B.card:ℝ) ≤ Z.card := by exact_mod_cast Finset.card_image_le (s:=Z) (f:=Complex.im)
    linarith
  have hden : 0 < 3*(4*Real.sqrt |t|+1) := by positivity
  have hsmall : 1/(3*(4*Real.sqrt |t|+1)) ≤ 1/2 := by
    apply (div_le_iff₀ hden).mpr
    linarith [Real.sqrt_nonneg |t|]
  refine ⟨t,ht,fun ρ hρ => ?_⟩
  by_cases him : |ρ.im-c|≤1
  · by_cases htr : ∃ n : ℕ, ρ = -2*(n+1)
    · rcases htr with ⟨n,rfl⟩
      have he : ((-2:ℂ)*(n+1)).im = 0 := by norm_num [Complex.mul_im]
      rw [he,sub_zero]
      exact hsmall.trans (by linarith)
    · have hline := hRH ρ hρ htr (by intro he; exact riemannZeta_one_ne_zero (he ▸ hρ))
      have hb : ρ.im∈B := Finset.mem_image_of_mem _ ((hZ ρ).2 ⟨hline,him,hρ⟩)
      apply (one_div_le_one_div_of_le (by positivity : 0<3*((B.card:ℝ)+1))
        (by linarith : 3*((B.card:ℝ)+1) ≤ 3*(4*Real.sqrt |t|+1))).trans (havoid _ hb)
  · have htc : |t-c| ≤ 1/2 := abs_le.mpr ⟨by dsimp [c]; linarith [ht.1],by dsimp [c]; linarith [ht.2]⟩
    have htriangle := abs_sub_le ρ.im t c
    rw [abs_sub_comm ρ.im t] at htriangle
    exact hsmall.trans (by linarith [lt_of_not_ge him])

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Set Filter MeasureTheory
open scoped BigOperators Topology Interval

/-- Counterclockwise integration over the four directed edges of a rectangle. -/
noncomputable def rectangleBoundary (a b u v : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f (x + u * I)) - (∫ x in a..b, f (x + v * I)) +
  I * (∫ y in u..v, f (b + y * I)) - I * (∫ y in u..v, f (a + y * I))

private theorem integral_linear_pole_edge (γ : ℝ → ℂ) (V ρ k : ℂ) (a b : ℝ)
    (hγ : ∀ x, HasDerivAt γ V x) (hk : k ≠ 0)
    (hcut : ∀ x ∈ Set.uIcc a b, k * (γ x - ρ) ∈ slitPlane) :
    V * (∫ x in a..b, (γ x - ρ)⁻¹) =
      Complex.log (k * (γ b - ρ)) - Complex.log (k * (γ a - ρ)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h := (((hγ x).sub_const ρ).const_mul k).clog_real (hcut x hx)
    simpa only [mul_div_mul_left _ _ hk, div_eq_mul_inv] using h
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    have hγc : ContinuousOn γ (Set.uIcc a b) := fun x _ => (hγ x).continuousAt.continuousWithinAt
    exact (hγc.sub continuousOn_const).inv₀
      (fun x hx => (mul_ne_zero_iff.mp (slitPlane_ne_zero (hcut x hx))).2)

private theorem log_neg_above {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - Real.pi * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz, ofReal_sub]
  ring

private theorem log_neg_below {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + Real.pi * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz, ofReal_add]
  ring

/-- The logarithmic kernel at any interior point has winding number one. -/
theorem rectangleBoundary_inv_sub (a b u v : ℝ) (ρ : ℂ)
    (ha : a < ρ.re) (hb : ρ.re < b) (hu : u < ρ.im) (hv : ρ.im < v) :
    rectangleBoundary a b u v (fun z => (z - ρ)⁻¹) = 2 * Real.pi * I := by
  let H (y x : ℝ) := (x:ℂ) + (y:ℂ) * I
  let V (x y : ℝ) := (x:ℂ) + (y:ℂ) * I
  have hHd (y x : ℝ) : HasDerivAt (H y) 1 x := by
    simpa [H] using ((hasDerivAt_id x).ofReal_comp.add_const ((y:ℂ) * I))
  have hVd (x y : ℝ) : HasDerivAt (V x) I y := by
    simpa [V] using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ))
  have below (x : ℝ) : (H u x - ρ).im < 0 := by simpa [H] using sub_neg.mpr hu
  have above (x : ℝ) : 0 < (H v x - ρ).im := by simpa [H] using sub_pos.mpr hv
  have hbottom := integral_linear_pole_edge (H u) 1 ρ 1 a b (hHd u) one_ne_zero
    (fun x _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inr (below x).ne))
  have htop := integral_linear_pole_edge (H v) 1 ρ 1 a b (hHd v) one_ne_zero
    (fun x _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inr (above x).ne'))
  have hright := integral_linear_pole_edge (V b) I ρ 1 u v (hVd b) one_ne_zero
    (fun y _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inl (by simpa [V] using sub_pos.mpr hb)))
  have hleft := integral_linear_pole_edge (V a) I ρ (-1) u v (hVd a) (by norm_num)
    (fun y _ => by
      rw [neg_one_mul]
      exact mem_slitPlane_iff.mpr (.inl (by simp [V]; linarith)))
  dsimp only [H,V] at *
  simp only [one_mul, neg_one_mul] at hbottom htop hleft hright
  rw [rectangleBoundary, hbottom, htop, hright, hleft,
    log_neg_above (above a), log_neg_below (below a)]
  ring

private theorem rect_principal_edge (a b : ℝ) (γ : ℝ → ℂ) (f G : ℂ → ℂ)
    (P : Finset ℂ) (r : ℂ → ℂ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun x => G (γ x)) (Set.uIcc a b))
    (havoid : ∀ x ∈ Set.uIcc a b, ∀ ρ ∈ P, γ x ≠ ρ)
    (hdecomp : ∀ x ∈ Set.uIcc a b, f (γ x) =
      G (γ x) + ∑ ρ ∈ P, r ρ * (γ x - ρ)⁻¹) :
    (∫ x in a..b, f (γ x)) = (∫ x in a..b, G (γ x)) +
      ∑ ρ ∈ P, r ρ * (∫ x in a..b, (γ x - ρ)⁻¹) := by
  have hi (ρ : ℂ) (hρ : ρ ∈ P) : IntervalIntegrable
      (fun x => r ρ * (γ x - ρ)⁻¹) volume a b :=
    (continuousOn_const.mul ((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun x hx => sub_ne_zero.mpr (havoid x hx ρ hρ)))).intervalIntegrable
  have his : IntervalIntegrable (fun x => ∑ ρ ∈ P, r ρ * (γ x - ρ)⁻¹) volume a b := by
    convert IntervalIntegrable.sum P hi using 1
    ext x
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_congr hdecomp,
    intervalIntegral.integral_add hG.intervalIntegrable his,
    intervalIntegral.integral_finsetSum hi]
  simp only [intervalIntegral.integral_const_mul]

/-- The rectangle residue formula, given an analytic regular part after
subtracting the finitely many interior simple principal parts. The pointwise
values assigned to the original function at its poles play no role. -/
theorem rectangle_residues_of_regular_part (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (f G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ ρ ∈ P, a < ρ.re ∧ ρ.re < b ∧ u < ρ.im ∧ ρ.im < v)
    (hG : DifferentiableOn ℂ G (Set.Icc a b ×ℂ Set.Icc u v))
    (hf : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc u v, z ∉ P →
      f z = G z + ∑ ρ ∈ P, r ρ * (z-ρ)⁻¹) :
    rectangleBoundary a b u v f = (2 * Real.pi * I) * ∑ ρ ∈ P, r ρ := by
  let H (y x : ℝ) := (x:ℂ) + (y:ℂ) * I
  let V (x y : ℝ) := (x:ℂ) + (y:ℂ) * I
  have edge (m n : ℝ) (γ : ℝ → ℂ) (hc : Continuous γ)
      (hγ : ∀ x ∈ Set.uIcc m n, γ x ∈ Set.Icc a b ×ℂ Set.Icc u v)
      (hn : ∀ x ∈ Set.uIcc m n, γ x ∉ P) :
      (∫ x in m..n, f (γ x)) = (∫ x in m..n, G (γ x)) +
        ∑ ρ ∈ P, r ρ * (∫ x in m..n, (γ x - ρ)⁻¹) :=
    rect_principal_edge m n γ f G P r hc (hG.continuousOn.comp hc.continuousOn hγ)
      (fun x hx ρ hρ he => hn x hx (he ▸ hρ)) (fun x hx => hf _ (hγ x hx) (hn x hx))
  have hor (y : ℝ) (hy : y ∈ Set.Icc u v) (hey : y = u ∨ y = v) := edge a b (H y)
    (by dsimp [H]; fun_prop)
    (by intro x hx; rw [Set.uIcc_of_le hab] at hx; simpa [H, Complex.mem_reProdIm] using
          And.intro hx hy)
    (by intro x _ hp; obtain ⟨_,_,hlo,hhi⟩ := hP _ hp
        simp [H] at hlo hhi
        rcases hey with rfl | rfl <;> linarith)
  have ver (x : ℝ) (hx : x ∈ Set.Icc a b) (hex : x = a ∨ x = b) := edge u v (V x)
    (by dsimp [V]; fun_prop)
    (by intro y hy; rw [Set.uIcc_of_le huv] at hy; simpa [V, Complex.mem_reProdIm] using
          And.intro hx hy)
    (by intro y _ hp; obtain ⟨hlo,hhi,_,_⟩ := hP _ hp
        simp [V] at hlo hhi
        rcases hex with rfl | rfl <;> linarith)
  have hreg : rectangleBoundary a b u v G = 0 := by
    simpa only [rectangleBoundary, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn G (⟨a,u⟩ : ℂ) (⟨b,v⟩ : ℂ)
        (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le huv] using hG)
  calc
    rectangleBoundary a b u v f = rectangleBoundary a b u v G +
        ∑ ρ ∈ P, r ρ * rectangleBoundary a b u v (fun z => (z-ρ)⁻¹) := by
      change (∫ x in a..b, f (H u x)) - (∫ x in a..b, f (H v x)) +
        I * (∫ y in u..v, f (V b y)) - I * (∫ y in u..v, f (V a y)) = _
      rw [hor u ⟨le_rfl,huv⟩ (.inl rfl), hor v ⟨huv,le_rfl⟩ (.inr rfl),
        ver b ⟨hab,le_rfl⟩ (.inr rfl), ver a ⟨le_rfl,hab⟩ (.inl rfl)]
      simp only [H,V,rectangleBoundary,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        Finset.mul_sum, mul_left_comm (r _) I]
      ring
    _ = _ := by
      rw [hreg, zero_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      obtain ⟨h1,h2,h3,h4⟩ := hP ρ hρ
      rw [rectangleBoundary_inv_sub a b u v ρ h1 h2 h3 h4, mul_comm]

/-- Residue theorem for finitely many simple poles in a rectangle. Each pole
has a local holomorphic remainder after removal of its simple principal part.
Only differentiability near the other points of the closed rectangle is needed. -/
theorem rectangle_residues_of_local_principal_parts (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (f : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ ρ ∈ P, a < ρ.re ∧ ρ.re < b ∧ u < ρ.im ∧ ρ.im < v)
    (hhol : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc u v, z ∉ P → DifferentiableAt ℂ f z)
    (hlocal : ∀ ρ ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      f =ᶠ[𝓝[≠] ρ] fun z => g z + r ρ * (z-ρ)⁻¹) :
    rectangleBoundary a b u v f = (2 * Real.pi * I) * ∑ ρ ∈ P, r ρ := by
  classical
  choose! g hg hprincipal using hlocal
  let term (p z : ℂ) := r p * (z-p)⁻¹
  let G (z : ℂ) := if z ∈ P then g z z - ∑ p ∈ P.erase z, term p z
                    else f z - ∑ p ∈ P, term p z
  have dsum (S : Finset ℂ) (z : ℂ) (hn : z ∉ S) :
      DifferentiableAt ℂ (fun w => ∑ p ∈ S, term p w) z := by
    apply DifferentiableAt.fun_sum
    intro p hp
    have hzp : z-p ≠ 0 := sub_ne_zero.mpr (fun h => hn (h ▸ hp))
    change DifferentiableAt ℂ (fun w : ℂ => r p * (w-p)⁻¹) z
    fun_prop (disch := assumption)
  apply rectangle_residues_of_regular_part a b u v hab huv f G P r hP
  · intro z hz
    by_cases hp : z ∈ P
    · let H (w : ℂ) := g z w - ∑ p ∈ P.erase z, term p w
      have hnear : G =ᶠ[𝓝 z] H := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE _ (by simp [G,H,hp])
        have havoid : ∀ᶠ w in 𝓝[≠] z, w ∉ P :=
          nhdsNE_le_cofinite z P.finite_toSet.compl_mem_cofinite
        filter_upwards [hprincipal z hp, havoid] with w hfw hw
        simp only [G, H, ite_eq_right hw]
        rw [← Finset.sum_erase_add _ _ hp, hfw]
        dsimp [term]
        ring
      exact (((hg z hp).differentiableAt.sub (dsum (P.erase z) z (by simp))).congr_of_eventuallyEq
        hnear).differentiableWithinAt
    · have hnear : G =ᶠ[𝓝 z] fun w => f w - ∑ p ∈ P, term p w := by
        filter_upwards [P.finite_toSet.isClosed.compl_mem_nhds hp] with w hw
        exact ite_eq_right hw
      exact (((hhol z hz hp).sub (dsum P z hp)).congr_of_eventuallyEq hnear).differentiableWithinAt
  · intro z _ hz
    simp [G, hz, term]

end GoldbachShortInterval

namespace GoldbachShortInterval

open Filter Set
open scoped Topology

/-- Subtracting the pole of the logarithmic derivative at a zero of finite
order leaves a holomorphic germ. -/
theorem logDeriv_principal_part {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hord : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      ∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (analyticOrderNatAt f ρ : ℂ) / (z - ρ) + g z := by
  let m := analyticOrderNatAt f ρ
  obtain ⟨u, hanu, hu, heq⟩ := hf.analyticOrderAt_ne_top.mp hord
  refine ⟨logDeriv u, hanu.deriv.div hanu hu, ?_⟩
  have hprod : f =ᶠ[𝓝 ρ] fun z => (z - ρ)^m * u z := heq
  filter_upwards [(logDeriv_congr_nhds hprod).filter_mono nhdsWithin_le_nhds,
    hanu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hanu.continuousAt.eventually_ne hu).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz haz hn hne
  have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hne
  rw [hz, logDeriv_fun_mul (f := fun v : ℂ => (v - ρ) ^ m) (g := u) z
    (pow_ne_zero _ hzρ) hn (by fun_prop) haz.differentiableAt,
    logDeriv_fun_pow (f := fun v : ℂ => v - ρ) (by fun_prop)]
  simp [logDeriv_apply, m, div_eq_mul_inv]

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Filter Set DirichletCharacter
open scoped Classical Topology

/-- Multiplication by an analytic weight multiplies the simple residue by
the value of the weight at the pole. -/
theorem analytic_weight_principal_part {f w : ℂ → ℂ} {ρ r : ℂ}
    (hw : AnalyticAt ℂ w ρ)
    (hf : ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      f =ᶠ[𝓝[≠] ρ] fun z => g z + r * (z-ρ)⁻¹) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧
      (fun z => f z * w z) =ᶠ[𝓝[≠] ρ] fun z => G z + (r * w ρ) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := hf
  refine ⟨fun z => g z * w z + r * dslope w ρ z, ?_, ?_⟩
  · fun_prop (disch := assumption)
  · filter_upwards [he, self_mem_nhdsWithin] with z hz hne
    have hn : z ≠ ρ := hne
    rw [hz, dslope_of_ne w hn, slope_def_field]
    ring

private theorem neg_logDeriv_zero_principal_part {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (ho : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ (fun z => -logDeriv f z) =ᶠ[𝓝[≠] ρ]
      fun z => g z + (-(analyticOrderNatAt f ρ : ℂ)) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := logDeriv_principal_part hf ho
  refine ⟨fun z => -g z, hg.neg, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, div_eq_mul_inv]
  ring

private theorem neg_logDeriv_principal_character_pole (q : ℕ) [NeZero q] :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      (fun z => -logDeriv (LFunction (1 : DirichletCharacter ℂ q)) z) =ᶠ[𝓝[≠] (1 : ℂ)]
        fun z => g z + 1 * (z-1)⁻¹ := by
  let F := LFunctionTrivChar₁ q
  have ha : AnalyticAt ℂ F 1 := (differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hn : F 1 ≠ 0 := LFunctionTrivChar₁_apply_one_ne_zero q
  refine ⟨fun z => -logDeriv F z, (ha.deriv.div ha hn).neg, ?_⟩
  filter_upwards [(ha.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hF hz
  have hz' : z ≠ 1 := hz
  have he : F z = (z-1) * LFunction (1 : DirichletCharacter ℂ q) z :=
    Function.update_of_ne hz' _ _
  have hL : LFunction (1 : DirichletCharacter ℂ q) z ≠ 0 := right_ne_zero_of_mul (he ▸ hF)
  simp only [logDeriv_apply, F, deriv_LFunctionTrivChar₁_apply_of_ne_one q hz', one_mul]
  rw [show LFunctionTrivChar₁ q z = _ from he]
  change _ = -(((z-1) * deriv (LFunction (1 : DirichletCharacter ℂ q)) z +
    LFunction (1 : DirichletCharacter ℂ q) z) / _) + _
  field_simp [sub_ne_zero.mpr hz', hL]
  ring

private theorem finite_compact_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {b : ℂ} (hb : f b ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | f z = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hd := ha.preimage_zero_mem_codiscreteWithin hb
    (show b ∈ (univ : Set ℂ) from mem_univ b) isConnected_univ
  exact (hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (subset_univ K) hd)).subset fun z hz => ⟨hz.1, by simp [hz.2]⟩

private theorem short_zeros_finite (u v : ℝ) :
    {z : ℂ | z.re = 1/2 ∧ u < z.im ∧ z.im < v ∧ riemannZeta z = 0}.Finite := by
  let K := Icc (0:ℝ) 1 ×ℂ Icc u v
  have hfin := finite_compact_zeros differentiable_riemannZeta₁
    (by simp [riemannZeta₁_one] : riemannZeta₁ 1 ≠ 0) (K := K) (isCompact_Icc.reProdIm isCompact_Icc)
  apply hfin.subset
  rintro z ⟨hr,hu,hv,hz⟩
  have hn : z ≠ 1 := by intro h; simp [h] at hr
  refine ⟨⟨⟨by linarith, by linarith⟩,hu.le,hv.le⟩,?_⟩
  rw [riemannZeta_eq_inv_sub_mul hn] at hz
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (sub_ne_zero.mpr hn))

noncomputable def smoothedZeroCut (u v : ℝ) : Finset ℂ := (short_zeros_finite u v).toFinset

theorem mem_smoothedZeroCut {u v : ℝ} {z : ℂ} :
    z ∈ smoothedZeroCut u v ↔ z.re=1/2 ∧ u<z.im ∧ z.im<v ∧ riemannZeta z=0 :=
  (short_zeros_finite u v).mem_toFinset

private theorem short_zeta_order_finite {z : ℂ} (hz : z ≠ 1) :
    analyticOrderAt riemannZeta z ≠ ⊤ := by
  have hc : IsConnected ({1}ᶜ : Set ℂ) := isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hn : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have h₂ : (2:ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  exact (analyticOn_riemannZeta.exists_analyticOrderAt_ne_top_iff_forall hc).mp
    ⟨⟨2,h₂⟩, by rw [(analyticOn_riemannZeta 2 h₂).analyticOrderAt_eq_zero.mpr hn]; simp⟩ ⟨z,hz⟩

/-- The finite rectangle crosses every enclosed critical zero and the pole
at one. It contains no trivial zeta zero. -/
theorem smoothedRectangle_residue (hRH : RiemannHypothesis) {u v η δ y : ℝ}
    (hu : u < 0) (hv : 0 < v) (hη : 0 < η) (hδ : 0 ≤ δ) (hy : 0 < y)
    (hsafe : ∀ z : ℂ, z.re=1/2 → riemannZeta z=0 → z.im≠u ∧ z.im≠v) :
    rectangleBoundary (-1/2) 2 u v (smoothedContourF η δ y) =
      (2*Real.pi*I) * (((δ*y*(1+η/2):ℝ):ℂ) - smoothedZeroPolynomial (smoothedZeroCut u v) δ η y) := by
  classical
  let Z := smoothedZeroCut u v
  let P := insert (1:ℂ) Z
  let W := entireSmoothedIncrementKernel η δ y
  let r (z : ℂ) := if z=1 then W 1 else -(analyticOrderNatAt riemannZeta z : ℂ)*W z
  have hw (z : ℂ) : AnalyticAt ℂ W z := entireSmoothedIncrementKernel_analyticAt hη hδ hy z
  have hP (z : ℂ) (hz : z∈P) : -1/2 < z.re ∧ z.re<2 ∧ u<z.im ∧ z.im<v := by
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact ⟨by norm_num,by norm_num,hu,hv⟩
    · obtain ⟨hr,h₁,h₂,_⟩ := mem_smoothedZeroCut.mp hz
      exact ⟨by linarith,by linarith,h₁,h₂⟩
  have he := rectangle_residues_of_local_principal_parts (-1/2) 2 u v
    (by norm_num) (hu.trans hv).le (smoothedContourF η δ y) P r hP (by
    intro z hz hp
    have hne : z ≠ 1 := fun h => hp (Finset.mem_insert.mpr (.inl h))
    have hn : riemannZeta z ≠ 0 := by
      intro hn
      have hnt : ¬ ∃ n : ℕ, z = -2*(n+1) := by
        rintro ⟨n,hn'⟩
        have hbound := hz.1.1
        rw [hn'] at hbound
        simp at hbound
        linarith [Nat.cast_nonneg (α:=ℝ) n]
      have hline := hRH z hn hnt hne
      obtain ⟨hlo,hhi⟩ := hsafe z hline hn
      exact hp (Finset.mem_insert.mpr (.inr (mem_smoothedZeroCut.mpr
        ⟨hline,lt_of_le_of_ne hz.2.1 hlo.symm,lt_of_le_of_ne hz.2.2 hhi,hn⟩)))
    have ha := analyticOn_riemannZeta z hne
    exact ((ha.deriv.div ha hn).neg.mul (hw z)).differentiableAt) (by
    intro z hz
    change ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      (fun w => (-logDeriv riemannZeta w)*W w) =ᶠ[𝓝[≠] z] fun w => g w + r z*(w-z)⁻¹
    rcases Finset.mem_insert.mp hz with rfl|hz
    · have h := analytic_weight_principal_part (hw 1) (neg_logDeriv_principal_character_pole 1)
      simpa [smoothedContourF,r,W,DirichletCharacter.LFunction_modOne_eq] using h
    · have hr := (mem_smoothedZeroCut.mp hz).1
      have hn : z ≠ 1 := by intro h; simp [h] at hr
      simpa [smoothedContourF,r,hn,W] using analytic_weight_principal_part (hw z)
        (neg_logDeriv_zero_principal_part (analyticOn_riemannZeta z hn) (short_zeta_order_finite hn)))
  rw [he]
  congr 1
  have h1 : (1:ℂ) ∉ Z := by intro h; have hr := (mem_smoothedZeroCut.mp h).1; norm_num at hr
  rw [show P = insert (1:ℂ) Z from rfl,Finset.sum_insert h1]
  rw [show r 1 = W 1 from ite_eq_left rfl]
  rw [show W 1 = _ from entireSmoothedIncrementKernel_one hη,sub_eq_add_neg,
    smoothedZeroPolynomial,← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  have hr := (mem_smoothedZeroCut.mp hz).1
  have hn : z ≠ 1 := by intro h; simp [h] at hr
  have h0 : z ≠ 0 := by intro h; simp [h] at hr
  have hplus : z+1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [hr] at hh
  simp only [r,ite_eq_right hn,W,entireSmoothedIncrementKernel_eq η δ y h0 hplus,
    smoothedIncrementKernel,zeroIncrementWeight]
  ring

open MeasureTheory

private theorem smoothedContourF_right (η δ y t : ℝ) :
    smoothedContourF η δ y ((2:ℂ)+(t:ℂ)*I) = smoothedPerronIntegrand η δ y t := by
  let s := (2:ℂ)+(t:ℂ)*I
  have hr : s.re = 2 := by simp [s]
  have hs : s≠0 := by intro h; simp [h] at hr
  have hs' : s+1≠0 := by intro h; have hh := congrArg Complex.re h; norm_num [hr] at hh
  change (-logDeriv riemannZeta s)*entireSmoothedIncrementKernel η δ y s = _
  rw [entireSmoothedIncrementKernel_eq _ _ _ hs hs', logDeriv_apply,← neg_div]
  rfl

private theorem smoothedContourF_left (η δ y t : ℝ) :
    smoothedContourF η δ y (((-1/2:ℝ):ℂ)+(t:ℂ)*I) = smoothedLeftIntegrand η δ y t := by
  let s : ℂ := ⟨-1/2,t⟩
  have he : (((-1/2:ℝ):ℂ)+(t:ℂ)*I) = s := by apply Complex.ext <;> simp [s]
  have hs : s≠0 := by intro h; have h' := congrArg Complex.re h; norm_num [s] at h'
  have hs' : s+1≠0 := by intro h; have h' := congrArg Complex.re h; norm_num [s] at h'
  rw [he,smoothedContourF,entireSmoothedIncrementKernel_eq _ _ _ hs hs',logDeriv_apply,← neg_div]
  rfl

private theorem finite_smoothed_formula (hRH : RiemannHypothesis) {u v η δ y : ℝ}
    (hu : u<0) (hv : 0<v) (hη : 0<η) (hδ : 0≤δ) (hy : 0<y)
    (hsafe : ∀ z : ℂ, z.re=1/2 → riemannZeta z=0 → z.im≠u ∧ z.im≠v) :
    smoothedZeroPolynomial (smoothedZeroCut u v) δ η y =
      ((δ*y*(1+η/2):ℝ):ℂ) -
      (1/(2*Real.pi):ℝ) • (∫ t : ℝ in u..v, smoothedPerronIntegrand η δ y t) +
      (1/(2*Real.pi):ℝ) • (∫ t : ℝ in u..v, smoothedLeftIntegrand η δ y t) -
      (smoothedHorizontal η δ y u-smoothedHorizontal η δ y v)/(2*Real.pi*I) := by
  have hr := smoothedRectangle_residue hRH hu hv hη hδ hy hsafe
  rw [rectangleBoundary] at hr
  simp only [Complex.ofReal_ofNat,smoothedContourF_right,smoothedContourF_left] at hr
  change smoothedHorizontal η δ y u - smoothedHorizontal η δ y v +
    I*(∫ t : ℝ in u..v, smoothedPerronIntegrand η δ y t) -
    I*(∫ t : ℝ in u..v, smoothedLeftIntegrand η δ y t) = _ at hr
  have hC : ((1/(2*Real.pi):ℝ):ℂ) = 1/(2*(Real.pi:ℂ)) := by push_cast; rfl
  rw [Complex.real_smul,Complex.real_smul,hC]
  have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  set m : ℂ := ((δ*y*(1+η/2):ℝ):ℂ)
  field_simp [hpi,I_ne_zero]
  linear_combination hr

noncomputable def smoothedZeroLimit (η δ y : ℝ) : ℂ :=
  (((δ*y*(1+η/2) - (smoothPsi η ((1+δ)*y)-smoothPsi η y)):ℝ):ℂ) +
    (1/(2*Real.pi):ℝ) • ∫ t : ℝ, smoothedLeftIntegrand η δ y t

/-- A single sequence of zero sets, independent of y, gives the required
pointwise convergence along any two sequences of admissible horizontal sides. -/
theorem smoothedZeroPolynomial_tendsto (hRH : RiemannHypothesis) {x y δ : ℝ}
    (hx : 1100000000000000000 ≤ x) (hy : x/100 ≤ y) (hδ : 0≤δ)
    {u v : ℕ → ℝ} (hul : Tendsto u atTop atBot) (hvl : Tendsto v atTop atTop)
    (hu : ∀ n, u n<0) (hv : ∀ n, 0<v n)
    (hsafe : ∀ n (z : ℂ), z.re=1/2 → riemannZeta z=0 → z.im≠u n ∧ z.im≠v n)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|))
    (hH₁ : Tendsto (fun n => smoothedHorizontal (1/(4*x)) δ y (u n)) atTop (𝓝 0))
    (hH₂ : Tendsto (fun n => smoothedHorizontal (1/(4*x)) δ y (v n)) atTop (𝓝 0)) :
    Tendsto (fun n => smoothedZeroPolynomial (smoothedZeroCut (u n) (v n)) δ (1/(4*x)) y)
      atTop (𝓝 (smoothedZeroLimit (1/(4*x)) δ y)) := by
  let η := 1/(4*x)
  have hy₀ : 0<y := by linarith
  have hη : 0<η := by dsimp [η]; positivity [show 0<x by linarith]
  have hright := smoothPsi_increment_perron_truncated hη hδ hy₀ hul hvl
  have hleft := smoothedLeftIntegral_truncated hx hy hδ hZ hul hvl
  have hhor := (hH₁.sub hH₂).div_const (2*Real.pi*I)
  have hlim := (((hright.const_sub ((δ*y*(1+η/2):ℝ):ℂ)).add hleft).sub hhor)
  simp only [sub_self,zero_div,sub_zero] at hlim
  refine Tendsto.congr' (Eventually.of_forall fun n =>
    (finite_smoothed_formula hRH (hu n) (hv n) hη hδ hy₀ (hsafe n)).symm) ?_
  simpa only [smoothedZeroLimit,Complex.ofReal_sub,η] using hlim

theorem smoothedZeroLimit_centered_error {x y δ : ℝ} (hx : 1100000000000000000 ≤ x)
    (hy : x/100 ≤ y) (hy' : y ≤ x) (hδ : 0≤δ) (hδ' : δ≤1)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|)) :
    ‖((Chebyshev.psi ((1+δ)*y)-Chebyshev.psi y-δ*y:ℝ):ℂ) + smoothedZeroLimit (1/(4*x)) δ y‖
      ≤ 0.5*(Real.log x)^2 := by
  let η := 1/(4*x)
  let E := (smoothPsi η ((1+δ)*y)-smoothPsi η y) - (Chebyshev.psi ((1+δ)*y)-Chebyshev.psi y)
  let J := (1/(2*Real.pi):ℝ) • ∫ t : ℝ, smoothedLeftIntegrand η δ y t
  have hx₀ : 0<x := by linarith
  have hy₀ : 0<y := by linarith
  have he : |E| ≤ Real.log (2*x+1) := smoothPsi_increment_error hx₀ hy₀ hδ (by
    nlinarith only [mul_le_mul_of_nonneg_right hδ' hy₀.le,hy'])
  have hJ : ‖J‖ ≤ 120 := smoothedLeftIntegral_le hx hy hδ hZ
  have hη : 0≤η := by dsimp [η]; positivity
  have hsize : δ*y*η/2 ≤ 1 := by
    dsimp only [η]
    rw [mul_one_div]
    have hh := mul_le_mul_of_nonneg_right hδ' hy₀.le
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hlog : Real.log (2*x+1) ≤ Real.log x+2 := by
    have h := Real.log_le_log (by positivity : 0<2*x+1) (show 2*x+1 ≤ x*3 by linarith)
    rw [Real.log_mul hx₀.ne' (by norm_num)] at h
    linarith only [h, Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))]
  have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9] : Real.exp 1≤3) 20
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow
  have hL : 20≤Real.log x := (Real.le_log_iff_exp_le hx₀).2 (by linarith only [hpow,hx])
  have hid : ((Chebyshev.psi ((1+δ)*y)-Chebyshev.psi y-δ*y:ℝ):ℂ) + smoothedZeroLimit η δ y =
      -(E:ℂ) + ((δ*y*η/2 : ℝ):ℂ) + J := by
    unfold smoothedZeroLimit
    dsimp only [E,J]
    push_cast
    ring
  change ‖_ + smoothedZeroLimit η δ y‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖-(E:ℂ)‖ + ‖((δ*y*η/2:ℝ):ℂ)‖ + ‖J‖ := (norm_add_le _ _).trans
      (add_le_add_left (norm_add_le _ _) _)
    _ ≤ _ := by
      rw [norm_neg,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0≤δ*y*η/2)]
      nlinarith only [he,hJ,hsize,hlog,hL,sq_nonneg (Real.log x-20)]

/-- The local almost-everywhere input for the second-moment limiting argument. -/
theorem smoothedZeroPolynomial_ae_input (hRH : RiemannHypothesis) {x δ : ℝ}
    (hx : 1100000000000000000 ≤ x) (hδ : 0≤δ) (hδ' : δ≤1)
    {u v : ℕ → ℝ} (hul : Tendsto u atTop atBot) (hvl : Tendsto v atTop atTop)
    (hu : ∀ n, u n<0) (hv : ∀ n, 0<v n)
    (hsafe : ∀ n (z : ℂ), z.re=1/2 → riemannZeta z=0 → z.im≠u n ∧ z.im≠v n)
    (hZ : ∀ t : ℝ, ‖logDeriv riemannZeta (⟨-1/2,t⟩ : ℂ)‖ ≤ 1000*Real.log (2+|t|))
    (hH₁ : ∀ y ∈ Icc (x/100) x, Tendsto (fun n => smoothedHorizontal (1/(4*x)) δ y (u n))
      atTop (𝓝 0))
    (hH₂ : ∀ y ∈ Icc (x/100) x, Tendsto (fun n => smoothedHorizontal (1/(4*x)) δ y (v n))
      atTop (𝓝 0)) :
    ∀ᵐ y ∂volume.restrict (Icc (x/100) x),
      Tendsto (fun n => smoothedZeroPolynomial (smoothedZeroCut (u n) (v n)) δ (1/(4*x)) y)
        atTop (𝓝 (smoothedZeroLimit (1/(4*x)) δ y)) ∧
      ‖((Chebyshev.psi ((1+δ)*y)-Chebyshev.psi y-δ*y:ℝ):ℂ) + smoothedZeroLimit (1/(4*x)) δ y‖
        ≤ 0.5*(Real.log x)^2 := by
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a:=x/100) (b:=x))] with y hy
  exact ⟨smoothedZeroPolynomial_tendsto hRH hx hy.1 hδ hul hvl hu hv hsafe hZ (hH₁ y hy) (hH₂ y hy),
    smoothedZeroLimit_centered_error hx hy.1 hy.2 hδ hδ' hZ⟩

end GoldbachShortInterval

namespace GoldbachShortInterval

open MeasureTheory Complex Filter Set
open scoped Topology Interval

private noncomputable def horizontalKernelBound (η δ y : ℝ) :=
  y^2 * ((1+δ)^2+1) * ((1+η)^3+1) / η

/-- Away from the real axis the smoothing contributes a second power of
decay uniformly over the entire horizontal edge. -/
theorem horizontal_kernel_decay {η δ y : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (hy : 1 ≤ y)
    (s : ℂ) (hr : s.re ≤ 2) (ht : 0 < |s.im|) :
    ‖entireSmoothedIncrementKernel η δ y s‖ ≤ horizontalKernelBound η δ y/|s.im|^2 := by
  have ht' : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have ht₀ := Complex.abs_im_le_norm s
  have h₁ : s ≠ 0 := norm_pos_iff.mp (ht.trans_le ht₀)
  have h₂ : s+1 ≠ 0 := norm_pos_iff.mp (ht.trans_le ht')
  have hpow {v : ℝ} (hv : 1 ≤ v) (z : ℂ) (n : ℕ) (hz : z.re ≤ n) :
      ‖(v:ℂ)^z‖ ≤ v^n := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact (Real.rpow_le_rpow_of_exponent_le hv hz).trans_eq (Real.rpow_natCast ..)
  have ha := hpow hy s 2 (by exact_mod_cast hr)
  have hb : ‖((1+δ:ℝ):ℂ)^s-1‖ ≤ (1+δ)^2+1 := by
    have h := norm_sub_le (((1+δ:ℝ):ℂ)^s) 1
    rw [norm_one] at h
    exact h.trans (add_le_add (hpow (v := 1+δ) (by linarith) s 2 (by exact_mod_cast hr)) le_rfl)
  have hc : ‖((1+η:ℝ):ℂ)^(s+1)-1‖ ≤ (1+η)^3+1 := by
    have hh := hpow (v := 1+η) (by linarith) (s+1) 3 (by simp; linarith)
    have h := norm_sub_le (((1+η:ℝ):ℂ)^(s+1)) 1
    rw [norm_one] at h
    exact h.trans (add_le_add hh le_rfl)
  rw [entireSmoothedIncrementKernel_eq _ _ _ h₁ h₂,smoothedIncrementKernel,perronSmoothingFactor]
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη]
  have hd₁ := div_le_div₀ ((norm_nonneg _).trans hb) hb ht ht₀
  have hd₂ := div_le_div₀ ((norm_nonneg _).trans hc) hc (mul_pos hη ht) (mul_le_mul_of_nonneg_left ht' hη.le)
  calc
    _ ≤ y^2 * (((1+δ)^2+1)/|s.im|) * (((1+η)^3+1)/(η*|s.im|)) :=
      mul_le_mul (mul_le_mul ha hd₁ (by positivity) (sq_nonneg _)) hd₂ (by positivity) (by positivity)
    _ = _ := by unfold horizontalKernelBound; ring

/-- The horizontal integrals vanish at every sequence of well-separated
heights with an unbounded absolute value. -/
theorem smoothedHorizontal_limit_of_bounds {C : ℝ} (hC : 0 < C) {v : ℕ → ℝ}
    (hv : Tendsto (fun n => |v n|) atTop atTop) (hv₁ : ∀ n, 1 ≤ |v n|)
    (hZ : ∀ n, ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → s.im = v n →
      ‖logDeriv riemannZeta s‖ ≤ C*(1+3*(4*Real.sqrt |v n|+1))*(1+|v n|))
    {η δ y : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (hy : 1 ≤ y) :
    Tendsto (fun n => smoothedHorizontal η δ y (v n)) atTop (𝓝 0) := by
  let D := horizontalKernelBound η δ y
  have hD : 0 ≤ D := by dsimp [D,horizontalKernelBound]; positivity
  have hbound (n : ℕ) : ‖smoothedHorizontal η δ y (v n)‖ ≤ 80*C*D/Real.sqrt |v n| := by
    let t := |v n|
    let r := Real.sqrt t
    have ht : 1 ≤ t := hv₁ n
    have ht' : 0 < t := zero_lt_one.trans_le ht
    have hr : 1 ≤ r := by simpa [r] using Real.sqrt_le_sqrt ht
    have hrp : 0 < r := zero_lt_one.trans_le hr
    have hsqr : r^2 = t := Real.sq_sqrt ht'.le
    have hI (σ : ℝ) (hσ : σ ∈ uIoc (-1/2:ℝ) 2) :
        ‖smoothedContourF η δ y ((σ:ℂ)+(v n:ℂ)*I)‖ ≤ 32*C*D/r := by
      rw [uIoc_of_le (by norm_num)] at hσ
      let s : ℂ := (σ:ℂ)+(v n:ℂ)*I
      have hre : s.re = σ := by simp [s]
      have him : s.im = v n := by simp [s]
      have hk := horizontal_kernel_decay hη hδ hy s (hre.le.trans hσ.2) (by rw [him]; exact ht')
      rw [him] at hk
      have hz := hZ n s (hre ▸ hσ.1.le) (hre ▸ hσ.2) him
      change ‖logDeriv riemannZeta s‖ ≤ C*(1+3*(4*r+1))*(1+t) at hz
      have h₁ : 1+3*(4*r+1) ≤ 16*r := by linarith
      have h₂ : 1+t ≤ 2*t := by linarith
      have hz' : ‖logDeriv riemannZeta s‖ ≤ C*(16*r)*(2*t) :=
        hz.trans (mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC.le) h₂ (by positivity) (by positivity))
      change ‖(-logDeriv riemannZeta s) * entireSmoothedIncrementKernel η δ y s‖ ≤ _
      rw [norm_mul,norm_neg]
      calc
        _ ≤ (C*(16*r)*(2*t))*(D/t^2) := mul_le_mul hz' hk (norm_nonneg _) (by positivity)
        _ = _ := by field_simp; rw [hsqr]; ring
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hI
    change ‖smoothedHorizontal η δ y (v n)‖ ≤ _ at hh
    apply hh.trans_eq
    norm_num
    ring
  have hlim : Tendsto (fun n => 80*C*D/Real.sqrt |v n|) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hv)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

end GoldbachShortInterval

namespace GoldbachShortInterval

open Complex Set Filter
open scoped Topology

/-- A single sequence of rectangles avoids all nontrivial zeta zeros and has
vanishing horizontal integrals for every choice of the smoothing parameters. -/
theorem exists_smoothed_contour_heights (hRH : RiemannHypothesis) :
    ∃ u v : ℕ → ℝ, Tendsto u atTop atBot ∧ Tendsto v atTop atTop ∧
      (∀ n, u n<0) ∧ (∀ n, 0<v n) ∧
      (∀ n (z : ℂ), z.re=1/2 → riemannZeta z=0 → z.im ≠ u n ∧ z.im ≠ v n) ∧
      ∀ {η δ y : ℝ}, 0<η → 0 ≤ δ → 1 ≤ y →
        Tendsto (fun n => smoothedHorizontal η δ y (u n)) atTop (𝓝 0) ∧
          Tendsto (fun n => smoothedHorizontal η δ y (v n)) atTop (𝓝 0) := by
  let H (n : ℕ) : ℝ := 10^13+12+n
  have hH (n : ℕ) : 10^13+10 ≤ H n := by dsimp [H]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hpos (n : ℕ) : 0 < H n := by linarith [hH n]
  choose v hv hV using fun n => exists_good_zeta_height hRH (H n) (by rw [abs_of_pos (hpos n)]; exact hH n)
  choose u hu hU using fun n => exists_good_zeta_height hRH (-H n)
    (by rw [abs_neg,abs_of_pos (hpos n)]; exact hH n)
  have hu' (n : ℕ) : u n ≤ -(n:ℝ)-10 := by have h := (hu n).2; dsimp [H] at h; linarith
  have hv' (n : ℕ) : (n:ℝ)+10 ≤ v n := by have h := (hv n).1; dsimp [H] at h; linarith
  have hu₀ (n) : u n<0 := by linarith [hu' n,Nat.cast_nonneg (α:=ℝ) n]
  have hv₀ (n) : 0<v n := by linarith [hv' n,Nat.cast_nonneg (α:=ℝ) n]
  have hut : Tendsto u atTop atBot := tendsto_atBot.2 fun b => by
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (-b)] with n hn
    linarith [hu' n]
  have hvt : Tendsto v atTop atTop := tendsto_atTop.2 fun b => by
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop b] with n hn
    linarith [hv' n]
  have htu (n) : 10 ≤ |u n| := by rw [abs_of_neg (hu₀ n)]; linarith [hu' n,Nat.cast_nonneg (α:=ℝ) n]
  have htv (n) : 10 ≤ |v n| := by rw [abs_of_pos (hv₀ n)]; linarith [hv' n,Nat.cast_nonneg (α:=ℝ) n]
  have hnon (t : ℝ) (ρ : ℂ) (hsep : 1/(3*(4*Real.sqrt |t|+1)) ≤ |t-ρ.im|) : ρ.im ≠ t := by
    intro h
    rw [h,sub_self,abs_zero] at hsep
    exact (not_le_of_gt (by positivity)) hsep
  refine ⟨u,v,hut,hvt,hu₀,hv₀,fun n z _ hz => ⟨hnon _ _ (hU n z hz),hnon _ _ (hV n z hz)⟩,?_⟩
  obtain ⟨C,hC,hZ⟩ := horizontal_zeta_logDeriv_bound
  have hz {t : ℝ} (ht : 10 ≤ |t|)
      (hsep : ∀ ρ : ℂ, riemannZeta ρ=0 → 1/(3*(4*Real.sqrt |t|+1)) ≤ |t-ρ.im|)
      (s : ℂ) (h₁ : -1/2 ≤ s.re) (h₂ : s.re ≤ 2) (him : s.im=t) :
      ‖logDeriv riemannZeta s‖ ≤ C*(1+3*(4*Real.sqrt |t|+1))*(1+|t|) := by
    let d := 3*(4*Real.sqrt |t|+1)
    have hd : 0<d := by dsimp [d]; positivity
    have hsep' (ρ : ℂ) (hρ : riemannZeta ρ=0) : 1/d ≤ ‖s-ρ‖ := by
      apply (hsep ρ hρ).trans
      simpa only [Complex.sub_im,him] using Complex.abs_im_le_norm (s-ρ)
    have h := hZ s (1/d) h₁ h₂ (him ▸ ht) (one_div_pos.mpr hd) hsep'
    simpa only [him,one_div_one_div] using h
  have huta : Tendsto (fun n => |u n|) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop b] with n hn
    rw [abs_of_neg (hu₀ n)]
    linarith [hu' n]
  have hvta : Tendsto (fun n => |v n|) atTop atTop := by
    simpa only [fun n => abs_of_pos (hv₀ n)] using hvt
  intro η δ y hη hδ hy
  exact ⟨smoothedHorizontal_limit_of_bounds hC huta (fun n => by linarith [htu n])
      (fun n => hz (htu n) (hU n)) hη hδ hy,
    smoothedHorizontal_limit_of_bounds hC hvta (fun n => by linarith [htv n])
      (fun n => hz (htv n) (hV n)) hη hδ hy⟩

end GoldbachShortInterval

open GoldbachShortInterval

/-- Under RH every interval with the specified starting point and logarithmic
length contains the sum of two odd primes. -/
theorem PEqualNP.Outside.L_goldbach_rh_short_interval_large :
    RiemannHypothesis → ∀ x : ℝ, 1100000000000000000 ≤ x →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧
        x < ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) ≤ x + 123 * (Real.log x) ^ 2 := by
  intro hRH x hx
  obtain ⟨u,v,hul,hvl,hu,hv,hsafe,hH⟩ := exists_smoothed_contour_heights hRH
  let S := fun n => smoothedZeroCut (u n) (v n)
  let η := 1/(4*x)
  let δ := relativeWidth x
  have hx₀ : 0 < x := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hη' : η ≤ 1/1000 := by
    dsimp [η]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  obtain ⟨_,hd,hδ',_,_,_⟩ := relativeWidth_bounds hx
  have hδ : 0 ≤ δ := hd.le
  have hlocal := smoothedZeroPolynomial_ae_input hRH hx hδ (by dsimp [δ]; linarith)
    hul hvl hu hv hsafe zeta_logDeriv_left_bound
    (fun y hy => (hH hη hδ (show 1 ≤ y by linarith [hy.1])).1)
    (fun y hy => (hH hη hδ (show 1 ≤ y by linarith [hy.1])).2)
  apply primeSum_of_local_psi_moment hx
  apply local_psi_moment_of_smoothed_zero_polynomials hx
    (fun n => smoothedZeroPolynomial (S n) δ η) (smoothedZeroLimit η δ)
  · exact fun n => smoothedZeroPolynomial_continuous (S n) δ η
      (fun _ hz => (mem_smoothedZeroCut.mp hz).1)
  · intro n
    apply smoothedZeroPolynomial_energy hRH (S n) _ hx hη hη'
    intro ρ hρ
    obtain ⟨hr,_,_,hz⟩ := mem_smoothedZeroCut.mp hρ
    exact ⟨by linarith,by linarith,hz⟩
  · exact hlocal
