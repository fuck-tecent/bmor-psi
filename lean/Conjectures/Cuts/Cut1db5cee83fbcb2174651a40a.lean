import Mathlib
import Conjectures.Goldbach.Type2FixedTargetReciprocalError

/- The prime-power replacement and row identities are the verified
GoldbachTransitionSquare results in Type2FixedTargetReciprocalError. The
first-corner full-circle distance split and the 61/64 divisor-count bound
are from the research checkpoint in PR 3790. -/
-- child 1 zh: 在第一格点的对数素数行上，距离至多 n^(5/8) 的素数对的全圆系数为 O(n^(61/64))。
-- child 1 en: For first-corner prime rows the full-circle contribution of pairs at distance at most n^(5/8) is O(n^(61/64)).
-- child 2 zh: 在充分大偶数上，远素数对的全圆系数与所有素数对的宽弧系数之差为 o(n)。
-- child 2 en: Along even targets the full-circle coefficient of distant prime pairs differs from the wide-arc coefficient of all pairs by o(n).

open Filter Finset MeasureTheory GoldbachTransitionSquare
open scoped Topology

theorem Conjectures.Cuts.Cut1db5cee83fbcb2174651a40a
    (hnear :
  let e := fun (k : ℤ) (t : ℝ) => Complex.exp (((k:ℂ)*(2*(Real.pi:ℂ)*Complex.I))*(t:ℂ))
  let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
  let B := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
  let P := fun n : ℕ => (Finset.range (n+1)).filter fun p => n.sqrt < p ∧ p.Prime
  let D := fun n : ℕ => ⌊(n:ℝ)^(5/8:ℝ)⌋₊
  let c := fun (n p a : ℕ) => if (p,a) ∈ ((P n).product (Finset.range (B n+1))).filter
    (fun i => U n < i.2 ∧ U n < i.1 ∧ i.2*i.1 ≤ n) then
    (((∑ d ∈ a.divisors.filter (fun d => U n < d), (ArithmeticFunction.moebius d : ℝ))*Real.log p:ℝ):ℂ) else 0
  let R := fun (n p : ℕ) (t : ℝ) => ∑ a ∈ Finset.range (B n+1), c n p a * e a ((p:ℝ)*t)
  let A := fun n : ℕ => (P n).product (P n)
  let C := fun n : ℕ => (A n).filter fun i => |(i.1:ℤ)-i.2| ≤ D n
  let F := fun (n : ℕ) (T : Finset (ℕ×ℕ)) (t : ℝ) => (∑ i ∈ T, R n i.1 t * R n i.2 t)*e (-(n:ℤ)) t
  ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 1≤n → ‖intervalIntegral (F n (C n)) (0:ℝ) 1 MeasureTheory.volume‖ ≤ K*(n:ℝ)^(61/64:ℝ))
    (hfar :
  let e := fun (k : ℤ) (t : ℝ) => Complex.exp (((k:ℂ)*(2*(Real.pi:ℂ)*Complex.I))*(t:ℂ))
  let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
  let B := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
  let P := fun n : ℕ => (Finset.range (n+1)).filter fun p => n.sqrt < p ∧ p.Prime
  let D := fun n : ℕ => ⌊(n:ℝ)^(5/8:ℝ)⌋₊
  let c := fun (n p a : ℕ) => if (p,a) ∈ ((P n).product (Finset.range (B n+1))).filter
    (fun i => U n < i.2 ∧ U n < i.1 ∧ i.2*i.1 ≤ n) then
    (((∑ d ∈ a.divisors.filter (fun d => U n < d), (ArithmeticFunction.moebius d : ℝ))*Real.log p:ℝ):ℂ) else 0
  let R := fun (n p : ℕ) (t : ℝ) => ∑ a ∈ Finset.range (B n+1), c n p a * e a ((p:ℝ)*t)
  let A := fun n : ℕ => (P n).product (P n)
  let C := fun n : ℕ => (A n).filter fun i => |(i.1:ℤ)-i.2| ≤ D n
  let F := fun (n : ℕ) (T : Finset (ℕ×ℕ)) (t : ℝ) => (∑ i ∈ T, R n i.1 t * R n i.2 t)*e (-(n:ℤ)) t
  let W := fun n : ℕ =>
    let Q : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    let H : ℕ := 256*Q*(Nat.log 2 (n+2))^2
    {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ a.Coprime q ∧ |t-(a:ℝ)/q|≤(H:ℝ)/((q:ℝ)*n)}
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
    ‖intervalIntegral (F n (A n \ C n)) (0:ℝ) 1 MeasureTheory.volume -
      ∫ t in Set.Icc (0:ℝ) 1 ∩ W n, F n (A n) t‖ ≤ ε*(n:ℝ)) :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₁ n)‖ ≤ e * (n : ℝ)) := by
  classical
  let P := bigPrimes
  let B := cutoffL
  let D := fun n : ℕ => ⌊(n:ℝ)^(5/8:ℝ)⌋₊
  let c := fun n => primeRowCoeff n (cutoffU n) (cutoffU n) (B n)
  let W := fun n => wide n (cutoffB n) (arcHeight n)
  let E := fun n => (P n) ×ˢ (P n)
  let region := fun (n : ℕ) (s : Set ℝ) (I : Finset (ℕ×ℕ)) => arcRows s I (B n+1) n (c n)
  let allCircle := fun (n : ℕ) (I : Finset (ℕ×ℕ)) => ∫ t in (0:ℝ)..1, pairRows I (B n+1) n (c n) t
  let close := fun n => allCircle n (closePairs (P n) (D n))
  let remn := fun n => allCircle n (farPairs (P n) (D n)) - region n (W n) (E n)
  let original := fun n => pairIntegral (W n)ᶜ n (full n (cutoffU n) (cutoffU n) (B n))
      (full n (cutoffU n) (cutoffU n) (B n))
  let prime := fun n => pairIntegral (W n)ᶜ n (core n (cutoffU n) (cutoffU n) (B n))
      (core n (cutoffU n) (cutoffU n) (B n))
  change ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 1≤n → ‖close n‖ ≤ K*(n:ℝ)^(61/64:ℝ) at hnear
  change smallEven remn at hfar
  change smallEven original
  have hu (n : ℕ) (I : Finset (ℕ×ℕ)) : region n Set.univ I = allCircle n I := by
    have h := arcRows_partition (Set.univ:Set ℝ) MeasurableSet.univ I (B n+1) n (c n)
    have hz : arcRows (∅:Set ℝ) I (B n+1) n (c n)=0 := by
      change (∫ t in Set.Icc (0:ℝ) 1 ∩ (∅:Set ℝ), pairRows I (B n+1) n (c n) t) = 0
      rw [Set.inter_empty,setIntegral_empty]
    rw [Set.compl_univ,hz,zero_add] at h
    exact h
  have hsplit (n : ℕ) : prime n = remn n + close n := by
    have hp : prime n = region n (W n)ᶜ (E n) :=
      core_square_rows (W n)ᶜ (wide_measurable ..).compl n (cutoffU n) (cutoffU n) (B n)
    have hw := arcRows_partition (W n) (wide_measurable ..) (E n) (B n+1) n (c n)
    change region n (W n)ᶜ (E n) + region n (W n) (E n) = allCircle n (E n) at hw
    have hd := arcRows_far_close (Set.univ:Set ℝ) (P n) (D n) (B n+1) n (c n)
    change region n Set.univ (E n)-region n Set.univ (farPairs (P n) (D n)) =
      region n Set.univ (closePairs (P n) (D n)) at hd
    simp only [hu] at hd
    change prime n = (allCircle n (farPairs (P n) (D n))-region n (W n) (E n)) + allCircle n (closePairs (P n) (D n))
    linear_combination hp+hw+hd
  have smallPower (f : ℕ → ℂ) (r K : ℝ) (hr : r<1)
      (hb : ∀ n : ℕ, 1≤n → ‖f n‖ ≤ K*(n:ℝ)^r) (ε : ℝ) (he : 0<ε) :
      ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ ε*(n:ℝ) := by
    have hlim : Tendsto (fun n : ℕ => K*(n:ℝ)^(-(1-r))) atTop (𝓝 0) := by
      have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
      simpa only [Function.comp_def,mul_zero] using (tendsto_const_nhds (x:=K)).mul ht
    filter_upwards [eventually_ge_atTop 1,hlim.eventually_lt_const he] with n hn hx
    have hpos : (0:ℝ)<n := by exact_mod_cast (show 0<n from hn)
    calc
      _ ≤ K*(n:ℝ)^r := hb n hn
      _ = (K*(n:ℝ)^(-(1-r)))*(n:ℝ) := by rw [mul_assoc,←Real.rpow_add_one hpos.ne',show -(1-r)+1=r by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_right hx.le hpos.le
  obtain ⟨K,_,hclose⟩ := hnear
  obtain ⟨C,_,hC⟩ := transition_power_saving
  have herror (n : ℕ) (hn : 1≤n) : ‖original n-prime n‖ ≤ C*(n:ℝ)^(31/32:ℝ) := by
    have h1 : (1:ℝ)≤n := by exact_mod_cast hn
    have hB : (B n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) :=
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1/4:ℝ))).trans
        (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
    exact (hC n (cutoffU n) (cutoffU n) (B n) hn hB (W n)ᶜ (wide_measurable ..).compl).trans_eq
      (by rw [show (124/128:ℝ)=31/32 by norm_num])
  intro ε he
  obtain ⟨N,hN⟩ := hfar (ε/3) (by positivity)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N,smallPower close (61/64) K (by norm_num) hclose (ε/3) (by positivity),
    smallPower (fun n => original n-prime n) (31/32) C (by norm_num) herror (ε/3) (by positivity)] with n hn hc hp
  intro hEven
  have hr := hN n hn hEven
  have h₁ := norm_add_le (remn n) (close n)
  rw [←hsplit] at h₁
  have h₂ := norm_add_le (original n-prime n) (prime n)
  rw [sub_add_cancel] at h₂
  linarith only [h₁,h₂,hr,hc,hp]
