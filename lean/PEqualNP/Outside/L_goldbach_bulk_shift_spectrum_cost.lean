import Mathlib

open scoped BigOperators

/-!
# Mean-square cost of shifting the prime cutoff

The difference of the two truncated prime exponential sums has coefficients
`c k = high (n+h) k - high n k`.  Parseval turns the mean square into
`sum c k ^ 2`.  The coefficients can only be nonzero for the `h` new
frequencies `n < k <= n+h`, or for the bases whose cube leaves the interval
`(n, n+h]`; cubing is injective, so the second group has at most `h`
elements as well.  Every coefficient is bounded by `log (n+h)`, giving
`2 h (log (n+h))^2`.
-/

private lemma phase_add (s t : ℝ) :
    Complex.exp (((2*Real.pi*(s+t):ℝ):ℂ)*Complex.I)
      = Complex.exp (((2*Real.pi*s:ℝ):ℂ)*Complex.I) * Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_norm (x : ℝ) :
    ‖Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (((2*Real.pi*x:ℝ):ℂ)*Complex.I).re = 0 := by simp
  rw [h, Real.exp_zero]

private lemma phase_star (x : ℝ) :
    star (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))
      = Complex.exp (((2*Real.pi*(-x):ℝ):ℂ)*Complex.I) := by
  have h1 : (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))⁻¹
      = star (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) := Complex.inv_eq_conj (phase_norm x)
  rw [← h1, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

private lemma orth (m : ℤ) :
    ∫ t in (0:ℝ)..1, Complex.exp (((2*Real.pi*((m:ℝ)*t):ℝ):ℂ)*Complex.I)
      = if m = 0 then (1:ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl]
    have hone : (fun t : ℝ => Complex.exp (((2*Real.pi*(((0:ℤ):ℝ)*t):ℝ):ℂ)*Complex.I))
        = fun _ => (1:ℂ) := by
      funext t
      simp
    rw [hone, intervalIntegral.integral_const]
    simp
  · rw [if_neg hm]
    set c : ℂ := ((2*Real.pi*(m:ℝ) : ℝ) : ℂ) * Complex.I with hc
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have h2pim : (2 * Real.pi * (m:ℝ) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hpi) hmR
    have hcne : c ≠ 0 := by
      rw [hc]
      refine mul_ne_zero ?_ Complex.I_ne_zero
      intro h0
      exact h2pim (Complex.ofReal_inj.mp h0)
    let F : ℝ → ℂ := fun t => Complex.exp (c * (t:ℂ)) / c
    have hderiv_exp : ∀ x : ℝ,
        HasDerivAt (fun t : ℝ => Complex.exp (c * (t:ℂ))) (Complex.exp (c * (x:ℂ)) * c) x := by
      intro x
      have hlin : HasDerivAt (fun t : ℝ => c * (t:ℂ)) c x := by
        have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
        simpa using h1.const_mul c
      simpa using hlin.cexp
    have hF : ∀ x : ℝ, HasDerivAt F (Complex.exp (((2*Real.pi*((m:ℝ)*x):ℝ):ℂ)*Complex.I)) x := by
      intro x
      have h2 := (hderiv_exp x).div_const c
      have hval : Complex.exp (c * (x:ℂ)) * c / c
          = Complex.exp (((2*Real.pi*((m:ℝ)*x):ℝ):ℂ)*Complex.I) := by
        rw [mul_div_assoc, div_self hcne, mul_one]
        congr 1
        rw [hc]
        push_cast
        ring
      rw [hval] at h2
      exact h2
    have hint : IntervalIntegrable (fun t : ℝ =>
        Complex.exp (((2*Real.pi*((m:ℝ)*t):ℝ):ℂ)*Complex.I)) MeasureTheory.volume (0:ℝ) 1 :=
      Continuous.intervalIntegrable (by fun_prop) 0 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint
    have hexp1 : Complex.exp c = 1 := by
      rw [hc]
      have harg : ((2*Real.pi*(m:ℝ) : ℝ) : ℂ) * Complex.I
          = (m:ℂ) * (2 * ((Real.pi:ℝ):ℂ) * Complex.I) := by
        push_cast
        ring
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    have hF1 : F 1 = 1 / c := by
      simp only [F]
      rw [show c * ((1:ℝ):ℂ) = c by norm_num, hexp1]
    have hF0 : F 0 = 1 / c := by
      simp [F]
    rw [hFTC, hF1, hF0, sub_self]

private lemma phase_sub (j k : ℕ) (t : ℝ) :
    Complex.exp (((2*Real.pi*((j:ℝ)*t):ℝ):ℂ)*Complex.I)
      * star (Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))
    = Complex.exp (((2*Real.pi*(((j:ℝ)-(k:ℝ))*t):ℝ):ℂ)*Complex.I) := by
  rw [phase_star, ← phase_add]
  congr 1
  push_cast
  ring

private lemma intervalIntegrable_finset_sum {α : Type*} (s : Finset α) (f : α → ℝ → ℂ)
    (hf : ∀ k ∈ s, Continuous (f k)) :
    IntervalIntegrable (fun t => Finset.sum s (fun k => f k t)) MeasureTheory.volume (0:ℝ) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun t : ℝ => Finset.sum (∅ : Finset α) (fun k => f k t)) = fun _ => (0:ℂ) := by
        funext t; simp
      rw [h]
      exact intervalIntegrable_const
  | insert a s ha ih =>
      have ha' : IntervalIntegrable (f a) MeasureTheory.volume (0:ℝ) 1 :=
        Continuous.intervalIntegrable (hf a (Finset.mem_insert_self a s)) 0 1
      have hs' : IntervalIntegrable (fun t => Finset.sum s (fun k => f k t))
          MeasureTheory.volume (0:ℝ) 1 :=
        ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      have hadd := ha'.add hs'
      refine hadd.congr ?_
      intro t _
      simp only [Finset.sum_insert ha]

private lemma integral_finset_sum {α : Type*} (s : Finset α) (f : α → ℝ → ℂ)
    (hf : ∀ k ∈ s, Continuous (f k)) :
    ∫ t in (0:ℝ)..1, Finset.sum s (fun k => f k t)
      = Finset.sum s (fun k => ∫ t in (0:ℝ)..1, f k t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have ha' : IntervalIntegrable (f a) MeasureTheory.volume (0:ℝ) 1 :=
        Continuous.intervalIntegrable (hf a (Finset.mem_insert_self a s)) 0 1
      have hs' : IntervalIntegrable (fun t => Finset.sum s (fun k => f k t))
          MeasureTheory.volume (0:ℝ) 1 :=
        intervalIntegrable_finset_sum s f (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      rw [intervalIntegral.integral_add ha' hs']
      rw [ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))]

private lemma pair_integral (j k : ℕ) :
    ∫ t in (0:ℝ)..1,
      (Complex.exp (((2*Real.pi*((j:ℝ)*t):ℝ):ℂ)*Complex.I)
        * star (Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))
      = if j = k then (1:ℂ) else 0 := by
  have hfun : (fun t : ℝ =>
      (Complex.exp (((2*Real.pi*((j:ℝ)*t):ℝ):ℂ)*Complex.I)
        * star (Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))))
      = (fun t : ℝ => Complex.exp (((2*Real.pi*((((j:ℤ)-(k:ℤ):ℤ):ℝ)*t):ℝ):ℂ)*Complex.I)) := by
    funext t
    rw [phase_sub]
    congr 1
    push_cast
    ring
  rw [hfun, orth ((j:ℤ)-(k:ℤ))]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos (sub_self (j:ℤ)), if_pos rfl]
  · have hne : ((j:ℤ)-(k:ℤ)) ≠ 0 := by omega
    rw [if_neg hne, if_neg hjk]

private noncomputable def T (w : ℕ → ℝ) (j k : ℕ) (t : ℝ) : ℂ :=
  ((w j)*(w k) : ℝ) * (Complex.exp (((2*Real.pi*((j:ℝ)*t):ℝ):ℂ)*Complex.I)
    * star (Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))

private lemma continuous_finset_sum' {α : Type*} (s : Finset α) (f : α → ℝ → ℂ)
    (hf : ∀ k ∈ s, Continuous (f k)) :
    Continuous (fun t => Finset.sum s (fun k => f k t)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

private lemma cont_term (w : ℕ → ℝ) (j k : ℕ) : Continuous (fun t => T w j k t) := by
  unfold T
  fun_prop

private lemma cont_inner (w : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) :
    Continuous (fun t => Finset.sum s (fun k => T w j k t)) := by
  apply continuous_finset_sum'
  intro k hk
  exact cont_term w j k

private lemma term_integral (w : ℕ → ℝ) (j k : ℕ) :
    (∫ t in (0:ℝ)..1, T w j k t)
      = ((w j)*(w k) : ℝ) * (if j = k then (1:ℂ) else 0) := by
  unfold T
  rw [intervalIntegral.integral_const_mul, pair_integral j k]

private lemma parseval_core (n : ℕ) (w : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, ‖Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2)
      = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  classical
  set s : Finset ℕ := Finset.range (n+1) with hs
  have hpt : ∀ t : ℝ,
      ((‖Finset.sum s (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2 : ℝ) : ℂ)
      = Finset.sum s (fun j => Finset.sum s (fun k => T w j k t)) := by
    intro t
    set z : ℂ := Finset.sum s (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)) with hz
    have hnorm : ((‖z‖^2:ℝ):ℂ) = z * star z := by
      rw [← Complex.normSq_eq_norm_sq]
      exact (Complex.mul_conj z).symm
    rw [hnorm, hz, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    unfold T
    rw [star_mul]
    have hstarw : star ((w k : ℝ) : ℂ) = ((w k : ℝ) : ℂ) := by simp
    rw [hstarw]
    push_cast
    ring
  have hcast :
      ((∫ t in (0:ℝ)..1, ‖Finset.sum s (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2 : ℝ) : ℂ)
      = ∫ t in (0:ℝ)..1, ((‖Finset.sum s (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2 : ℝ) : ℂ) :=
    (intervalIntegral.integral_ofReal).symm
  have hcongr :
      (∫ t in (0:ℝ)..1, ((‖Finset.sum s (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2 : ℝ) : ℂ))
      = ∫ t in (0:ℝ)..1, Finset.sum s (fun j => Finset.sum s (fun k => T w j k t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hpt t
  have hdouble :
      (∫ t in (0:ℝ)..1, Finset.sum s (fun j => Finset.sum s (fun k => T w j k t)))
      = Finset.sum s (fun j => Finset.sum s (fun k => ((w j)*(w k) : ℝ) * (if j = k then (1:ℂ) else 0))) := by
    rw [integral_finset_sum s (fun j t => Finset.sum s (fun k => T w j k t)) (fun j _ => cont_inner w s j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finset_sum s (fun k t => T w j k t) (fun k _ => cont_term w j k)]
    apply Finset.sum_congr rfl
    intro k hk
    exact term_integral w j k
  have hsum_eval :
      Finset.sum s (fun j => Finset.sum s (fun k => ((w j)*(w k) : ℝ) * (if j = k then (1:ℂ) else 0)))
      = ((Finset.sum s (fun k => (w k)^2) : ℝ) : ℂ) := by
    have hinner : ∀ j ∈ s, Finset.sum s (fun k => ((w j)*(w k) : ℝ) * (if j = k then (1:ℂ) else 0)) = (((w j)^2 : ℝ) : ℂ) := by
      intro j hj
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, mul_one]
        congr 1
        ring
      · intro k hk hkj
        rw [if_neg (fun h : j = k => hkj h.symm), mul_zero]
      · intro hjs
        exact absurd hj hjs
    calc Finset.sum s (fun j => Finset.sum s (fun k => ((w j)*(w k) : ℝ) * (if j = k then (1:ℂ) else 0)))
        = Finset.sum s (fun j => (((w j)^2 : ℝ) : ℂ)) := Finset.sum_congr rfl hinner
      _ = ((Finset.sum s (fun j => (w j)^2) : ℝ) : ℂ) := by
          push_cast
          rfl
  have hcomp :
      ((∫ t in (0:ℝ)..1, ‖Finset.sum s (fun k => (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2 : ℝ) : ℂ)
      = ((Finset.sum s (fun k => (w k)^2) : ℝ) : ℂ) := by
    rw [hcast, hcongr, hdouble, hsum_eval]
  have hfin := Complex.ofReal_inj.mp hcomp
  simpa [hs] using hfin

/-! ## The shifted spectrum -/

private noncomputable def W (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0

private noncomputable def low (n k : ℕ) : ℝ := if k^3 ≤ n then W k else 0

private noncomputable def high (n k : ℕ) : ℝ := W k - low n k

private noncomputable def Sf (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (a k : ℂ) *
    Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))

private noncomputable def dcoef (n h k : ℕ) : ℝ :=
  high (n+h) k - if k ≤ n then high n k else 0

private lemma W_nonneg (k : ℕ) : 0 ≤ W k := by
  unfold W
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_lt hp).le)
  · exact le_rfl

private lemma high_eq (n k : ℕ) : high n k = if n < k^3 then W k else 0 := by
  unfold high low
  by_cases h : k^3 ≤ n
  · rw [if_pos h, if_neg (by omega : ¬ n < k^3)]
    ring
  · rw [if_neg h, if_pos (by omega : n < k^3)]
    ring

private lemma abs_dcoef_le_W (n h k : ℕ) : |dcoef n h k| ≤ W k := by
  have hW := W_nonneg k
  unfold dcoef
  rw [high_eq (n+h) k, high_eq n k]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    by_cases hle : k^3 ≤ n+h
    · by_cases hn : n < k^3
      · rw [if_neg (by omega : ¬ n+h < k^3), if_pos hn]
        rw [zero_sub, abs_neg, abs_of_nonneg hW]
      · rw [if_neg (by omega : ¬ n+h < k^3), if_neg hn]
        rw [sub_self, abs_zero]
        exact hW
    · rw [if_pos (by omega : n+h < k^3), if_pos (by omega : n < k^3)]
      rw [sub_self, abs_zero]
      exact hW
  · rw [if_neg hkn, sub_zero]
    by_cases hle : n+h < k^3
    · rw [if_pos hle, abs_of_nonneg hW]
    · rw [if_neg hle]
      rw [abs_zero]
      exact hW

private lemma W_le_log {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    W k ≤ Real.log (N:ℝ) := by
  have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  unfold W
  split_ifs with hp
  · exact Real.log_le_log (by exact_mod_cast (Nat.Prime.pos hp)) (by exact_mod_cast hk)
  · exact hlogN

private lemma dcoef_abs_le_log (n h k : ℕ) (hn : 1 ≤ n) (hk : k < n+h+1) :
    |dcoef n h k| ≤ Real.log ((n+h:ℕ):ℝ) := by
  have hk' : k ≤ n+h := by omega
  have hN : 1 ≤ n+h := by omega
  exact le_trans (abs_dcoef_le_W n h k) (W_le_log hN hk')

private lemma dcoef_sq_le_log_sq (n h k : ℕ) (hn : 1 ≤ n) (hk : k < n+h+1) :
    (dcoef n h k)^2 ≤ (Real.log ((n+h:ℕ):ℝ))^2 := by
  have hN : 1 ≤ n+h := by omega
  have hL : 0 ≤ Real.log ((n+h:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hd := dcoef_abs_le_log n h k hn hk
  have hpow := pow_le_pow_left₀ (abs_nonneg (dcoef n h k)) hd 2
  simpa only [sq_abs] using hpow

private def suppA (n h : ℕ) : Finset ℕ :=
  (Finset.range (n+h+1)).filter (fun k => n < k^3 ∧ k^3 ≤ n+h)

private def suppB (n h : ℕ) : Finset ℕ :=
  (Finset.range (n+h+1)).filter (fun k => n < k ∧ n+h < k^3)

private noncomputable def supp (n h : ℕ) : Finset ℕ :=
  (Finset.range (n+h+1)).filter (fun k => dcoef n h k ≠ 0)

private lemma dcoef_eq_zero_of_not (n h k : ℕ)
    (hA : ¬ (n < k^3 ∧ k^3 ≤ n+h)) (hB : ¬ (n < k ∧ n+h < k^3)) :
    dcoef n h k = 0 := by
  unfold dcoef
  rw [high_eq (n+h) k, high_eq n k]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    by_cases hle : k^3 ≤ n+h
    · by_cases hn : n < k^3
      · exact absurd ⟨hn, hle⟩ hA
      · rw [if_neg (by omega : ¬ n+h < k^3), if_neg hn]
        ring
    · rw [if_pos (by omega : n+h < k^3), if_pos (by omega : n < k^3)]
      ring
  · rw [if_neg hkn, sub_zero]
    by_cases hle : n+h < k^3
    · exact absurd ⟨by omega, hle⟩ hB
    · rw [if_neg hle]

private lemma supp_subset (n h : ℕ) : supp n h ⊆ suppA n h ∪ suppB n h := by
  intro k hk
  simp only [supp, suppA, suppB, Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hk ⊢
  by_cases hA : n < k^3 ∧ k^3 ≤ n+h
  · exact Or.inl ⟨hk.1, hA⟩
  · by_cases hB : n < k ∧ n+h < k^3
    · exact Or.inr ⟨hk.1, hB⟩
    · exfalso
      exact hk.2 (dcoef_eq_zero_of_not n h k hA hB)

private lemma suppA_card_le (n h : ℕ) : (suppA n h).card ≤ h := by
  have hcard : (Finset.Ioc n (n+h)).card = h := by simp
  have hmaps : Set.MapsTo (fun k : ℕ => k^3) (↑(suppA n h) : Set ℕ)
      (↑(Finset.Ioc n (n+h)) : Set ℕ) := by
    intro k hk
    simp only [suppA, Finset.mem_filter, Finset.mem_range, Finset.mem_coe] at hk
    exact Finset.mem_Ioc.mpr ⟨hk.2.1, hk.2.2⟩
  have hinj : (↑(suppA n h) : Set ℕ).InjOn (fun k : ℕ => k^3) := by
    intro a ha b hb hab
    exact Nat.pow_left_injective (by norm_num) hab
  calc (suppA n h).card ≤ (Finset.Ioc n (n+h)).card :=
        Finset.card_le_card_of_injOn (s := suppA n h) (t := Finset.Ioc n (n+h))
          (f := fun k : ℕ => k^3) hmaps hinj
    _ = h := hcard

private lemma suppB_card_le (n h : ℕ) : (suppB n h).card ≤ h := by
  have hsub : suppB n h ⊆ Finset.Ioc n (n+h) := by
    intro k hk
    simp only [suppB, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_Ioc.mpr ⟨hk.2.1, by omega⟩
  calc (suppB n h).card ≤ (Finset.Ioc n (n+h)).card := Finset.card_le_card hsub
    _ = h := by simp

private lemma supp_card_le (n h : ℕ) : (supp n h).card ≤ 2*h := by
  calc (supp n h).card ≤ (suppA n h ∪ suppB n h).card := Finset.card_le_card (supp_subset n h)
    _ ≤ (suppA n h).card + (suppB n h).card := Finset.card_union_le _ _
    _ ≤ h + h := Nat.add_le_add (suppA_card_le n h) (suppB_card_le n h)
    _ = 2*h := by ring

private lemma diff_eq_sum (n h : ℕ) (t : ℝ) :
    Sf (n+h) (high (n+h)) t - Sf n (high n) t
      = ∑ k ∈ Finset.range (n+h+1), (dcoef n h k : ℂ) *
          Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I) := by
  unfold Sf
  have hsmall : (∑ k ∈ Finset.range (n+1), (high n k : ℂ) *
      Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))
      = ∑ k ∈ Finset.range (n+h+1), ((if k ≤ n then high n k else 0 : ℝ) : ℂ) *
          Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I) := by
    calc (∑ k ∈ Finset.range (n+1), (high n k : ℂ) *
          Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))
        = ∑ k ∈ Finset.range (n+1), ((if k ≤ n then high n k else 0 : ℝ) : ℂ) *
            Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k < n+1 := Finset.mem_range.mp hk
          rw [if_pos (by omega : k ≤ n)]
      _ = ∑ k ∈ Finset.range (n+h+1), ((if k ≤ n then high n k else 0 : ℝ) : ℂ) *
            Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I) := by
          apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega : n+1 ≤ n+h+1))
          intro k hkbig hksmall
          have hk : ¬ k < n+1 := by simpa using hksmall
          rw [if_neg (by omega : ¬ k ≤ n)]
          simp
  rw [hsmall]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold dcoef
  push_cast
  ring

private lemma sum_dcoef_sq_le (n h : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n+h+1), (dcoef n h k)^2
      ≤ 2*(h:ℝ)*(Real.log ((n+h:ℕ):ℝ))^2 := by
  set L : ℝ := Real.log ((n+h:ℕ):ℝ) with hLdef
  have hN : 1 ≤ n+h := by omega
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hN)
  have hstep1 : ∑ k ∈ Finset.range (n+h+1), (dcoef n h k)^2
      = ∑ k ∈ supp n h, (dcoef n h k)^2 := by
    unfold supp
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : dcoef n h k = 0
    · rw [if_neg (by intro hne; exact hne h), h]
      ring
    · rw [if_pos h]
  calc ∑ k ∈ Finset.range (n+h+1), (dcoef n h k)^2
      = ∑ k ∈ supp n h, (dcoef n h k)^2 := hstep1
    _ ≤ ∑ k ∈ supp n h, L^2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n+h+1 := by
          simp only [supp, Finset.mem_filter, Finset.mem_range] at hk
          exact hk.1
        exact dcoef_sq_le_log_sq n h k hn hk'
    _ = ((supp n h).card : ℝ) * L^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2*h : ℕ) : ℝ) * L^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
        exact_mod_cast supp_card_le n h
    _ = 2*(h:ℝ)*L^2 := by
        push_cast
        ring

private theorem main (n h : ℕ) (hn : 1 ≤ n) :
    (∫ t in (0:ℝ)..1, ‖Sf (n+h) (high (n+h)) t - Sf n (high n) t‖^2)
      ≤ 2*(h:ℝ)*(Real.log ((n+h:ℕ):ℝ))^2 := by
  have hparse : (∫ t in (0:ℝ)..1, ‖Sf (n+h) (high (n+h)) t - Sf n (high n) t‖^2)
      = ∑ k ∈ Finset.range (n+h+1), (dcoef n h k)^2 := by
    have hfun : (fun t : ℝ => ‖Sf (n+h) (high (n+h)) t - Sf n (high n) t‖^2)
        = (fun t : ℝ => ‖∑ k ∈ Finset.range (n+h+1), (dcoef n h k : ℂ) *
            Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)‖^2) := by
      funext t
      rw [diff_eq_sum]
    rw [hfun]
    exact parseval_core (n+h) (dcoef n h)
  rw [hparse]
  exact sum_dcoef_sq_le n h hn

theorem PEqualNP.Outside.L_goldbach_bulk_shift_spectrum_cost :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; ∀ n h : ℕ, 1≤n → (∫ t in (0:ℝ)..1, ‖S (n+h) (high (n+h)) t - S n (high n) t‖^2) ≤ 2*(h:ℝ)*Real.log ((n+h:ℕ):ℝ)^2 := by
  dsimp only
  exact main
