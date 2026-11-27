import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor
import Conjectures.Goldbach.RoughFifthMass

/-!
# A prime and a squarefree almost-prime in a prime-square window

The proof uses published formal work under the Apache License 2.0.
The two community dependencies are LogTruSoul's contribution in PR 3746
and Tchikrazi's contribution in PR 3771 to CGandGameEngineLearner/goldbach-proofs.
The analytic estimates adapt finite Dirichlet polynomial, mollifier,
interpolation, and zero detection arguments from Tomas Ortega's Sidon
repository at 735de6d7c67b81a28b1e07e3f2661dbc17bb89d6, with
David Sanftenberg's RiemannGaussian work as credited in its notices.
The sieve formulas adapt subfish-zhou/goldbach-lean at
9d4c3a4010d42aedd9e7231bf94386019cfffccc, including work by Nous Research.
The finite divisor regrouping comes from OpenAI's openai/math at
f5702854040e97fa7675c21ba37a9608f5f92dd3.
The mathematical route and the finite factor-counting argument are credited
to LonelyQuantum's CentralPrimeAlmostPrime and RichertFactorBudget notes at
36b0d52d9585d07feeb93da6ac3b8de09b36f018.
-/

-- RichertFactorBudget
section

namespace GoldbachRichert

noncomputable def penalty (a : ℕ) (y : ℝ) : ℝ :=
  a.factorization.sum fun q e => (e : ℝ) * max (1 - Real.log q / Real.log y) 0

theorem factor_budget (a : ℕ) (y : ℝ) :
    (ArithmeticFunction.cardFactors a : ℝ) - Real.log a / Real.log y ≤ penalty a y := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Real.log_nat_eq_sum_factorization]
  simp only [penalty, Finsupp.sum, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro q _
  calc
    _ = (a.factorization q : ℝ) * (1 - Real.log q / Real.log y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)

theorem weighted_count_le (A : Finset ℕ) (r : ℕ) (y b lam : ℝ) (hlam : 0 < lam)
    (hsize : ∀ a ∈ A, Real.log a / Real.log y ≤ b)
    (hbudget : b + lam ≤ (r : ℝ) + 1) :
    (∑ a ∈ A, (1 - penalty a y / lam)) ≤
      ((A.filter fun a => ArithmeticFunction.cardFactors a ≤ r).card : ℝ) := by
  calc
    _ ≤ ∑ a ∈ A, (if ArithmeticFunction.cardFactors a ≤ r then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases good : ArithmeticFunction.cardFactors a ≤ r
      · simp only [good, ↓reduceIte]
        have hn : 0 ≤ penalty a y := by
          unfold penalty Finsupp.sum
          apply Finset.sum_nonneg
          intro q _
          exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
        linarith [div_nonneg hn hlam.le]
      · simp only [good, ↓reduceIte]
        have hc : r + 1 ≤ ArithmeticFunction.cardFactors a := Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_ge good)
        have hcr : (r : ℝ) + 1 ≤ (ArithmeticFunction.cardFactors a : ℝ) := by exact_mod_cast hc
        have hp : lam ≤ penalty a y := by linarith [factor_budget a y, hsize a ha]
        linarith [(one_le_div hlam).mpr hp]
    _ = _ := by simp [Finset.sum_boole]

end GoldbachRichert

end


-- TH8000Weight
section

namespace GoldbachSevenWeight

open Finset Real

lemma parameter_slack :
    (39/250 : ℝ) < 4/25 ∧ (39/250 : ℝ)/(104/675) = 81/80 ∧
    (39/250 : ℝ)/(39/1000) = 4 ∧ (675/104 : ℝ)+3/2 < 8 := by norm_num

noncomputable def distinctPenalty (a : ℕ) (y : ℝ) : ℝ :=
  ∑ q ∈ a.primeFactors, max (1 - log q / log y) 0

lemma penalty_eq_of_squarefree {a : ℕ} (hs : Squarefree a) (y : ℝ) :
    GoldbachRichert.penalty a y = distinctPenalty a y := by
  unfold GoldbachRichert.penalty distinctPenalty Finsupp.sum
  change (∑ q ∈ a.primeFactors, _) = _
  apply sum_congr rfl
  intro q hq
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hq
  simp only [Nat.factorization_eq_one_of_squarefree hs hp hd, Nat.cast_one, one_mul]

noncomputable def upperCut (X : ℕ) : ℝ := (X:ℝ) ^ (104/675 : ℝ)

lemma partner_log_bound {X a : ℕ} (hX : 2 ≤ X) (ha : 0 < a) (hle : a ≤ X) :
    log (a:ℝ) / log (upperCut X) ≤ 675/104 := by
  have hx : (1:ℝ)<X := by exact_mod_cast (show 1<X by omega)
  have hpos := Real.log_pos hx
  have hle' : log (a:ℝ) ≤ log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hle)
  rw [upperCut, Real.log_rpow (by linarith : 0 < (X:ℝ)), div_le_iff₀ (by positivity)]
  linarith

noncomputable def weight (X a : ℕ) : ℝ := 1 - distinctPenalty a (upperCut X)/(3/2)

lemma weight_le_one (X a : ℕ) : weight X a ≤ 1 := by
  have h : 0 ≤ distinctPenalty a (upperCut X) := sum_nonneg (fun _ _ => le_max_right _ _)
  unfold weight
  linarith

lemma weight_nonpos_of_many_factors {X a : ℕ} (hX : 2 ≤ X) (hs : Squarefree a)
    (haX : a ≤ X) (hmany : 7 < a.primeFactorsList.length) : weight X a ≤ 0 := by
  have ha : 0 < a := Nat.pos_of_ne_zero hs.ne_zero
  have hb := GoldbachRichert.factor_budget a (upperCut X)
  rw [penalty_eq_of_squarefree hs, ArithmeticFunction.cardFactors_apply] at hb
  have hlen : (8:ℝ) ≤ a.primeFactorsList.length := by exact_mod_cast hmany
  have hu := partner_log_bound hX ha haX
  unfold weight
  linarith

def hits (p H d b : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (fun h => (p^2+h)%d=b ∧ (p^2+h).Prime ∧
    (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7)

theorem weight_transfer (p H d b : ℕ) (hp : 2 ≤ p) (A : Finset ℕ)
    (hA : ∀ h ∈ A, h ∈ Icc 1 H ∧ (p^2+h)%d=b ∧ (p^2+h).Prime) :
    (∑ h ∈ A, weight (p^2) (p^2-h)) -
      ((A.filter fun h => ¬Squarefree (p^2-h)).card : ℝ) ≤ (hits p H d b).card := by
  let G := A.filter (fun h => (p^2-h).primeFactorsList.Nodup ∧
    (p^2-h).primeFactorsList.length ≤ 7)
  have hsub : G ⊆ hits p H d b := by
    intro h hh
    obtain ⟨hA', hn, hcount⟩ := mem_filter.mp hh
    obtain ⟨hI,hres,hprime⟩ := hA h hA'
    exact mem_filter.mpr ⟨hI,hres,hprime,hn,hcount⟩
  have hpoint (h : ℕ) (_ : h ∈ A) : weight (p^2) (p^2-h) ≤
      (if (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7 then (1:ℝ) else 0)
        + (if ¬Squarefree (p^2-h) then 1 else 0) := by
    have h1 := weight_le_one (p^2) (p^2-h)
    by_cases hs : Squarefree (p^2-h)
    · simp only [hs, not_true_eq_false, ite_false, add_zero, hs.nodup_primeFactorsList, true_and]
      split_ifs with hle
      · exact h1
      · exact weight_nonpos_of_many_factors (by nlinarith) hs (Nat.sub_le ..) (by omega)
    · have hnn : 0 ≤ (if (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7
          then (1:ℝ) else 0) := by split <;> norm_num
      simp only [hs, not_false_eq_true, ite_true]
      linarith
  have hsum := Finset.sum_le_sum hpoint
  rw [sum_add_distrib] at hsum
  simp only [Finset.sum_boole] at hsum
  have hg : (G.card:ℝ) ≤ (hits p H d b).card := by exact_mod_cast Finset.card_le_card hsub
  dsimp [G] at hg
  linarith

end GoldbachSevenWeight

end


-- TH8000Square
section

open Finset Filter
open scoped Classical

namespace TH8000Square

noncomputable def squareHits (p H z : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (fun h => ∃ q : ℕ, q.Prime ∧ z ≤ q ∧ q^2 ∣ p^2-h)

noncomputable def repeatedRough (p H z : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (fun h => z ≤ (p^2-h).minFac ∧ ¬ (p^2-h).primeFactorsList.Nodup)

/- The telescoping reciprocal-square estimate is adapted from goldbach-proofs,
RoughFifthSquareError.lean, blob de3ff3af11c97483115a76fb38310b69649e3b05,
under Apache License 2.0. The residue-class count below retains the window width. -/
private lemma reciprocal_tail (z k : ℕ) (hz : 1 ≤ z) :
    (∑ i ∈ range k, (1:ℝ) / ((z+i+1:ℕ):ℝ)^2) ≤ 1/(z:ℝ) - 1/((z+k:ℕ):ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have hstep : (1:ℝ)/((z+k+1:ℕ):ℝ)^2 ≤ 1/((z+k:ℕ):ℝ) - 1/((z+k+1:ℕ):ℝ) := by
      let x : ℝ := z+k
      have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < z+k by omega)
      push_cast
      change 1/(x+1)^2 ≤ 1/x - 1/(x+1)
      field_simp
      nlinarith
    change _ ≤ 1/(z:ℝ) - 1/((z+k+1:ℕ):ℝ)
    linarith

private lemma fiber_count (N H D : ℕ) (hH : H ≤ N) :
    ((Icc 1 H).filter (fun h => D ∣ N-h)).card ≤ H/D+1 := by
  have hmem (h) (hh : h ∈ (Icc 1 H).filter (fun h => D ∣ N-h)) :
      h % D = N % D := by
    obtain ⟨hi,hd⟩ := mem_filter.mp hh
    exact (Nat.modEq_iff_dvd' ((mem_Icc.mp hi).2.trans hH)).mpr hd
  rw [← card_range (H/D+1)]
  apply card_le_card_of_injOn (fun h => h/D)
  · intro h hh
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ((mem_Icc.mp (mem_filter.mp hh).1).2)))
  · intro h hh k hk he
    change h/D=k/D at he
    have hr := (hmem h hh).trans (hmem k hk).symm
    calc h = h % D + D*(h/D) := (Nat.mod_add_div ..).symm
      _ = k % D + D*(k/D) := by rw [hr,he]
      _ = k := Nat.mod_add_div .. 

theorem square_count_le (p H z : ℕ) (hp : 1 ≤ p) (hH : H ≤ p^2) (hz : 2 ≤ z) :
    ((squareHits p H z).card:ℝ) ≤ (H:ℝ)/((z:ℝ)-1) + p := by
  let q := fun i : ℕ => z-1+i+1
  let S := fun i : ℕ => (Icc 1 H).filter (fun h => (q i)^2 ∣ p^2-h)
  have cover : squareHits p H z ⊆ insert (p^2) ((range (p-1)).biUnion S) := by
    intro h hh
    obtain ⟨hh, r, _hr, hzr, hd⟩ := mem_filter.mp hh
    rcases eq_or_ne h (p^2) with he | he
    · exact mem_insert.mpr (Or.inl he)
    have hlt : h < p^2 := lt_of_le_of_ne ((mem_Icc.mp hh).2.trans hH) he
    have hsquare := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hd
    have h1 := (mem_Icc.mp hh).1
    have hrp : r < p := by
      by_contra! hge
      have := Nat.pow_le_pow_left hge 2
      omega
    apply mem_insert.mpr
    right
    apply mem_biUnion.mpr
    refine ⟨r-z, mem_range.mpr (by omega), mem_filter.mpr ⟨hh, ?_⟩⟩
    simpa only [show q (r-z) = r by dsimp [q]; omega] using hd
  have hc : (squareHits p H z).card ≤ (∑ i ∈ range (p-1), (H/(q i)^2+1)) + 1 := by
    calc
      _ ≤ _ := (card_le_card cover).trans (card_insert_le ..)
      _ ≤ (∑ i ∈ range (p-1), (S i).card) + 1 := Nat.add_le_add_right card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (sum_le_sum fun i _ => fiber_count (p^2) H ((q i)^2) hH) _
  have hcast : ((squareHits p H z).card:ℝ) ≤
      (∑ i ∈ range (p-1), (((H/(q i)^2:ℕ):ℝ)+1)) + 1 := by exact_mod_cast hc
  have hterm (i : ℕ) : ((H/(q i)^2:ℕ):ℝ) ≤ H*(1/((q i:ℕ):ℝ)^2) := by
    rw [mul_one_div, ← Nat.cast_pow]
    exact Nat.cast_div_le
  have hs : (∑ i ∈ range (p-1), 1/((q i):ℝ)^2) ≤ 1/((z:ℝ)-1) := by
    have h := reciprocal_tail (z-1) (p-1) (by omega)
    have hn : (0:ℝ) ≤ 1/((((z-1)+(p-1):ℕ):ℝ)) := by positivity
    have h' := h.trans (sub_le_self _ hn)
    simpa only [q, Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one] using h'
  have hsum := (sum_le_sum (s := range (p-1)) (fun i _ => hterm i))
  rw [← mul_sum] at hsum
  have hresult := hsum.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [sum_add_distrib] at hcast
  simp only [sum_const, nsmul_eq_mul, mul_one, card_range,
    Nat.cast_sub hp, Nat.cast_one] at hcast
  linarith only [hcast, hresult, mul_one_div (H:ℝ) ((z:ℝ)-1)]

theorem repeatedRough_subset (p H z : ℕ) : repeatedRough p H z ⊆ squareHits p H z := by
  intro h hh
  obtain ⟨hI,hz,hn⟩ := mem_filter.mp hh
  have hm : p^2-h ≠ 0 := by
    intro hm
    simp [hm] at hn
  have hsf : ¬Squarefree (p^2-h) := fun hs => hn ((Nat.squarefree_iff_nodup_primeFactorsList hm).mp hs)
  rw [Nat.squarefree_iff_prime_squarefree] at hsf
  push Not at hsf
  obtain ⟨q,hq,hd⟩ := hsf
  have hdiv : q ∣ p^2-h := dvd_trans (dvd_mul_right q q) hd
  exact mem_filter.mpr ⟨hI,q,hq,hz.trans (Nat.minFac_le_of_dvd hq.two_le hdiv),by simpa [sq] using hd⟩

private lemma eventually_logSquare_le {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∀ᶠ p : ℕ in atTop, (Real.log ((p:ℝ)^2))^2 ≤ e*(p:ℝ)^a := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) ha).bound (show 0 < e/4 by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [hnat] with p hp
  have hp' : (Real.log (p:ℝ))^2 ≤ e/4*(p:ℝ)^a := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (p:ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) a)] using hp
  rw [Real.log_pow, Nat.cast_ofNat]
  nlinarith only [hp']

private lemma width_bounds (p H : ℕ) (hp : 2 ≤ p)
    (hlo : H^3 ≤ p^4) (hhi : p^4 < (H+1)^3) :
    H ≤ p^2 ∧ (p:ℝ)*(p:ℝ)^(1/3:ℝ) ≤ 2*(H:ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hp4 : p^4 ≤ (p^2)^3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp1 (by norm_num)
  have hHp : H ≤ p^2 := by
    by_contra! h
    have := Nat.pow_lt_pow_left h (by norm_num : 3 ≠ 0)
    omega
  have hH0 : 1 ≤ H := by
    by_contra! h
    have : H = 0 := by omega
    subst H
    simp at hhi
    omega
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH0
  have h4 : (p:ℝ)^4 ≤ ((H:ℝ)+1)^3 := by exact_mod_cast hhi.le
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  refine ⟨hHp, ?_⟩
  calc
    (p:ℝ)*(p:ℝ)^(1/3:ℝ) = (p:ℝ)^(1+(1/3):ℝ) := by rw [Real.rpow_add (by positivity)]; simp
    _ = ((p:ℝ)^4)^(1/3:ℝ) := by
      rw [← Real.rpow_natCast (p:ℝ) 4, ← Real.rpow_mul hp0]
      norm_num
    _ ≤ (((H:ℝ)+1)^3)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = (H:ℝ)+1 := by
      rw [← Real.rpow_natCast ((H:ℝ)+1) 3, ← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ _ := by linarith

theorem square_error_negligible {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ H z : ℕ,
      H^3 ≤ p^4 → p^4 < (H+1)^3 → (p:ℝ)^η ≤ z →
      ((squareHits p H z).card:ℝ) * (Real.log ((p:ℝ)^2))^2 ≤ ε*(H:ℝ) := by
  have hηlog := eventually_logSquare_le hη (show 0 < ε/4 by positivity)
  have hthird := eventually_logSquare_le (show (0:ℝ) < 1/3 by norm_num) (show 0 < ε/4 by positivity)
  have hpow : Tendsto (fun p : ℕ => (p:ℝ)^η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [hηlog, hthird, hpow.eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with p hA hB hpow hp H z hlo hhi hz
  have hz2r : (2:ℝ) ≤ z := hpow.trans hz
  have hz2 : 2 ≤ z := by exact_mod_cast hz2r
  obtain ⟨hHp,hwidth⟩ := width_bounds p H hp hlo hhi
  have hcard := square_count_le p H z (by omega) hHp hz2
  let L := (Real.log ((p:ℝ)^2))^2
  have hper : L/((z:ℝ)-1) ≤ ε/2 := by
    apply (div_le_iff₀ (by linarith : 0 < (z:ℝ)-1)).mpr
    have hh := hA.trans (mul_le_mul_of_nonneg_left hz (show 0 ≤ ε/4 by positivity))
    have he := mul_nonneg hε.le (show 0 ≤ (z:ℝ)-2 by linarith)
    dsimp only [L]
    nlinarith only [hh, he]
  have hfirst : (H:ℝ)/((z:ℝ)-1)*L ≤ (H:ℝ)*(ε/2) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg _)
  have hsecond : (p:ℝ)*L ≤ (ε/4)*(2*(H:ℝ)) := by
    calc
      _ ≤ (p:ℝ)*(ε/4*(p:ℝ)^(1/3:ℝ)) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = (ε/4)*((p:ℝ)*(p:ℝ)^(1/3:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwidth (by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hcard (show 0 ≤ L from sq_nonneg _)
  change ((squareHits p H z).card:ℝ)*L ≤ _
  rw [add_mul] at hfinal
  linarith only [hfirst,hsecond,hfinal]

theorem repeatedRough_error_negligible {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ H z : ℕ,
      H^3 ≤ p^4 → p^4 < (H+1)^3 → (p:ℝ)^η ≤ z →
      ((repeatedRough p H z).card:ℝ) * (Real.log ((p:ℝ)^2))^2 ≤ ε*(H:ℝ) := by
  obtain ⟨P,hP⟩ := square_error_negligible hη hε
  refine ⟨P, fun p hp H z hlo hhi hz => le_trans ?_ (hP p hp H z hlo hhi hz)⟩
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast card_le_card (repeatedRough_subset p H z)

end TH8000Square

end


-- TH8000Transfer
section

namespace GoldbachSevenWeight
open Finset

noncomputable def sieveCut (p : ℕ) := ⌈(p:ℝ) ^ (39/500:ℝ)⌉₊

noncomputable def roughOffsets (p H d b : ℕ) :=
  (Icc 1 H).filter fun h => (p^2+h)%d=b ∧ (p^2+h).Prime ∧ sieveCut p ≤ (p^2-h).minFac

lemma half_window (p H : ℕ) (hp : 4 ≤ p) (hH : H^3 ≤ p^4) : 2*H ≤ p^2 := by
  have h8 : 8 ≤ p^2 := by nlinarith
  have hlevel : (2*H)^3 ≤ (p^2)^3 := calc
    (2*H)^3 = 8*H^3 := by ring
    _ ≤ 8*p^4 := by omega
    _ ≤ p^2*p^4 := Nat.mul_le_mul_right _ h8
    _ = _ := by ring
  by_contra! hlt
  exact (not_lt_of_ge hlevel) (Nat.pow_lt_pow_left hlt (by decide))

lemma case_error (p H d b : ℕ) (hp : 4 ≤ p) (hH : H^3 ≤ p^4) :
    ((roughOffsets p H d b).filter fun h => ¬Squarefree (p^2-h)) ⊆
      TH8000Square.repeatedRough p H (sieveCut p) := by
  intro h hh
  obtain ⟨hc,hs⟩ := mem_filter.mp hh
  obtain ⟨hI,_,_,hrough⟩ := mem_filter.mp hc
  have hwindow := half_window p H hp hH
  have hH' := (mem_Icc.mp hI).2
  have hX : 4 ≤ p^2 := by nlinarith
  have hpos : p^2-h ≠ 0 := by omega
  exact mem_filter.mpr ⟨hI,hrough,fun hnodup =>
    hs ((Nat.squarefree_iff_nodup_primeFactorsList hpos).mpr hnodup)⟩

theorem seven_of_weighted_lower
    (hweighted : ∀ d : ℕ, 0 < d → ∃ c : ℝ, 0 < c ∧ ∃ P : ℕ, ∀ p H b : ℕ,
      P ≤ p → p.Prime → b < d → b.Coprime d → (2*p^2-b).Coprime d →
      H^3 ≤ p^4 → p^4 < (H+1)^3 →
      c*(H:ℝ) ≤ (∑ h ∈ roughOffsets p H d b, weight (p^2) (p^2-h)) *
        (Real.log ((p:ℝ)^2))^2) :
    ∀ d : ℕ, 0 < d → ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p H b : ℕ,
      p₀ ≤ p → p.Prime → b < d → b.Coprime d → (2*p^2-b).Coprime d →
      H^3 ≤ p^4 → p^4 < (H+1)^3 →
      c*(H:ℝ) ≤ ((hits p H d b).card : ℝ) * (Real.log ((p:ℝ)^2))^2 := by
  intro d hd
  obtain ⟨c,hc,P,hpos⟩ := hweighted d hd
  obtain ⟨P',hbad⟩ := TH8000Square.repeatedRough_error_negligible
    (show (0:ℝ)<39/500 by norm_num) (half_pos hc)
  refine ⟨c/2,half_pos hc,max 4 (max P P'),?_⟩
  intro p H b hp hprime hb hadm hadm' hlo hhi
  have hp4 : 4 ≤ p := by omega
  have hm := hpos p H b (by omega) hprime hb hadm hadm' hlo hhi
  have he := hbad p (by omega) H (sieveCut p) hlo hhi (Nat.le_ceil _)
  have htrans := weight_transfer p H d b (by omega) (roughOffsets p H d b)
    (by
      intro h hh
      obtain ⟨hI,hres,ht,_⟩ := mem_filter.mp hh
      exact ⟨hI,hres,ht⟩)
  have hcard := Finset.card_le_card (case_error p H d b hp4 hlo)
  have hle : (((roughOffsets p H d b).filter fun h => ¬Squarefree (p^2-h)).card : ℝ) ≤
      ((TH8000Square.repeatedRough p H (sieveCut p)).card : ℝ) := by exact_mod_cast hcard
  have hs := mul_le_mul_of_nonneg_right hle (sq_nonneg (Real.log ((p:ℝ)^2)))
  have hh := mul_le_mul_of_nonneg_right htrans (sq_nonneg (Real.log ((p:ℝ)^2)))
  linarith only [hm,he,hs,hh]

end GoldbachSevenWeight

end


-- TH8000Band
section

namespace GoldbachSevenWeight
open Finset Real

noncomputable def penaltyBand (X z : ℕ) : Finset ℕ :=
  (Icc z X).filter (fun q : ℕ => q.Prime ∧ (q:ℝ)<upperCut X)

theorem distinctPenalty_band {X a z : ℕ} (hX : 2 ≤ X) (ha : 1 < a)
    (haX : a ≤ X) (hz : z ≤ a.minFac) :
    distinctPenalty a (upperCut X) =
      ∑ q ∈ penaltyBand X z, if q ∣ a then 1 - log q / log (upperCut X) else 0 := by
  have hX' : (1:ℝ) < X := by exact_mod_cast (show 1<X by omega)
  have hy : 1 < upperCut X := Real.one_lt_rpow hX' (by norm_num)
  have hly := Real.log_pos hy
  have heq : a.primeFactors.filter (fun q : ℕ => (q:ℝ) < upperCut X) =
      (penaltyBand X z).filter (fun q => q ∣ a) := by
    ext q
    simp only [penaltyBand, mem_filter, mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp,hd,_⟩,hqy⟩
      exact ⟨⟨⟨hz.trans (Nat.minFac_le_of_dvd hp.two_le hd),
        (Nat.le_of_dvd (by omega) hd).trans haX⟩,hp,hqy⟩,hd⟩
    · rintro ⟨⟨_,hp,hq⟩,hd⟩
      exact ⟨⟨hp,hd,by omega⟩,hq⟩
  unfold distinctPenalty
  rw [← Finset.sum_filter, ← heq, Finset.sum_filter]
  apply sum_congr rfl
  intro q hq
  have hqpos : (0:ℝ)<q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
  split_ifs with h
  · apply max_eq_left
    exact sub_nonneg.mpr ((div_le_one hly).mpr (Real.log_le_log hqpos h.le))
  · apply max_eq_right
    exact sub_nonpos.mpr ((one_le_div hly).mpr (Real.log_le_log (by linarith) (le_of_not_gt h)))

def rowCount (S : Finset ℕ) (X q : ℕ) : ℕ := (S.filter fun h => q ∣ X-h).card

theorem rough_weight_eq_rows (p H d b : ℕ) (hp : 4 ≤ p) (hH : H^3 ≤ p^4) :
    let S := roughOffsets p H d b
    ∑ h ∈ S, weight (p^2) (p^2-h) =
      (S.card:ℝ) - (∑ q ∈ penaltyBand (p^2) (sieveCut p),
        (1 - log q / log (upperCut (p^2))) * (rowCount S (p^2) q:ℝ))/(3/2) := by
  classical
  intro S
  have hp2 : 4 ≤ p^2 := by nlinarith
  have hhalf := half_window p H hp hH
  unfold weight
  rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  calc
    _ = ∑ h ∈ S, ∑ q ∈ penaltyBand (p^2) (sieveCut p),
        if q ∣ p^2-h then 1 - log q / log (upperCut (p^2)) else 0 := by
      apply sum_congr rfl
      intro h hh
      obtain ⟨hI,_,_,hz⟩ := mem_filter.mp hh
      have := (mem_Icc.mp hI).2
      exact distinctPenalty_band (by omega) (by omega) (Nat.sub_le ..) hz
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      rw [← sum_filter, sum_const, nsmul_eq_mul, rowCount, mul_comm]

end GoldbachSevenWeight

end


-- TH8000Amplitude
section

/-!
Adapted to the project toolchain from subfish-zhou/goldbach-lean commit
9d4c3a4010d42aedd9e7231bf94386019cfffccc, Apache License 2.0, including
the contributions of Nous Research. The two source modules are
SuzukiUpperSourcePairingWindowTail and SuzukiUpperSourcePTail. The base
sieve development is reused from goldbach-proofs PR 3771.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

theorem suzukiUpperSourcePairingWindowTail_of_sourceTail
    (hP : SuzukiUpperSourcePTail) :
    SuzukiUpperSourcePairingWindowTail := by
  unfold SuzukiUpperSourcePTail at hP
  have hp : SuzukiStandardUpperAdjointScaledTail :=
    suzukiStandardUpperAdjoint_scaledTail
  unfold SuzukiStandardUpperAdjointScaledTail at hp
  unfold SuzukiUpperSourcePairingWindowTail
  rw [Metric.tendsto_atTop] at hP hp ⊢
  intro ε hε
  obtain ⟨NP, hNP⟩ := hP 1 zero_lt_one
  obtain ⟨Np, hNp⟩ := hp 1 zero_lt_one
  refine ⟨max (max (NP + 1) Np) (max 2 (7 / ε)), ?_⟩
  intro s hs
  have hsNP : NP + 1 ≤ s :=
    le_trans (le_max_left (NP + 1) Np) (le_trans (le_max_left _ _) hs)
  have hsNp : Np ≤ s :=
    le_trans (le_max_right (NP + 1) Np) (le_trans (le_max_left _ _) hs)
  have hs2 : 2 ≤ s :=
    le_trans (le_max_left 2 (7 / ε)) (le_trans (le_max_right _ _) hs)
  have hspos : 0 < s := by linarith
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  apply lt_of_le_of_lt
    (intervalIntegral.norm_integral_le_of_norm_le_const (C := 6 / s) ?_)
  · rw [show |s - (s - 1)| = 1 by
      rw [show s - (s - 1) = 1 by ring]
      norm_num, mul_one]
    have heps : 6 / s ≤ 6 / (7 / ε) := by
      gcongr
      exact le_trans (le_max_right 2 (7 / ε)) (le_trans (le_max_right _ _) hs)
    have hcalc : 6 / (7 / ε) < ε := by
      field_simp
      nlinarith
    exact heps.trans_lt hcalc
  · intro t ht
    rw [uIoc_of_le (by linarith : s - 1 ≤ s)] at ht
    have htS : s ≤ t + 1 := by linarith [ht.1]
    have htNP : NP ≤ t := by linarith [hsNP, ht.1]
    have htNp : Np ≤ t + 1 := hsNp.trans htS
    have hPb := hNP t htNP
    have hpb := hNp (t + 1) htNp
    rw [Real.dist_eq] at hPb hpb
    have hPnorm : ‖suzukiUpperSourceP t‖ ≤ 3 := by
      rw [Real.norm_eq_abs]
      have : |suzukiUpperSourceP t| < 3 := by
        rw [abs_sub_lt_iff] at hPb
        rw [abs_lt]
        constructor <;> linarith [hPb.1, hPb.2]
      exact this.le
    have hqnorm : ‖(t + 1) * suzukiStandardUpperAdjoint (t + 1)‖ ≤ 2 := by
      rw [Real.norm_eq_abs]
      have : |(t + 1) * suzukiStandardUpperAdjoint (t + 1)| < 2 := by
        rw [abs_sub_lt_iff] at hpb
        rw [abs_lt]
        constructor <;> linarith [hpb.1, hpb.2]
      exact this.le
    have htpos : 0 < t + 1 := hspos.trans_le htS
    rw [show suzukiStandardUpperAdjoint (t + 1) =
        ((t + 1) * suzukiStandardUpperAdjoint (t + 1)) / (t + 1) by
          field_simp]
    rw [norm_mul, norm_div]
    simp only [Real.norm_eq_abs, abs_of_pos htpos]
    calc
      ‖(t + 1) * suzukiStandardUpperAdjoint (t + 1)‖ /
            (t + 1) * ‖suzukiUpperSourceP t‖
          ≤ 2 / (t + 1) * 3 := by gcongr
      _ ≤ 2 / s * 3 := by gcongr
      _ = 6 / s := by ring

end
end MathlibNt.SieveTheory

namespace MathlibNt.SieveTheory

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Interval
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

theorem tendsto_suzukiProposition118SourceQ_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiProposition118SourceQ atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    suzukiProposition118SourceQ_eventually_le_mul_exp hH
  apply squeeze_zero' (hbound.mono fun _ hs => hs.1)
    (hbound.mono fun _ hs => hs.2)
  simpa [mul_assoc] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul D

theorem tendsto_suzukiProposition118Source_parity_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiProposition118SourceTPlus atTop (𝓝 0) ∧
      Tendsto suzukiProposition118SourceTMinus atTop (𝓝 0) := by
  have hnonneg : ∀ᶠ s : ℝ in atTop,
      0 ≤ suzukiProposition118SourceTPlus s ∧
        0 ≤ suzukiProposition118SourceTMinus s := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    exact ⟨tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith)),
      tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg hs k)⟩
  have hbound : ∀ᶠ s : ℝ in atTop,
      suzukiProposition118SourceTPlus s ≤ suzukiProposition118SourceQ s ∧
        suzukiProposition118SourceTMinus s ≤ suzukiProposition118SourceQ s := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hnonneg] with s hs hsign
    rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr hs)]
    exact ⟨le_add_of_nonneg_right hsign.2, le_add_of_nonneg_left hsign.1⟩
  have hQ := tendsto_suzukiProposition118SourceQ_zero hH
  exact ⟨squeeze_zero' (hnonneg.mono fun _ hs => hs.1)
      (hbound.mono fun _ hs => hs.1) hQ,
    squeeze_zero' (hnonneg.mono fun _ hs => hs.2)
      (hbound.mono fun _ hs => hs.2) hQ⟩

private theorem suzukiUpperSourceP_eq_series
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiUpperSourceP s =
      2 + suzukiProposition118SourceTPlus s -
        suzukiProposition118SourceTMinus s := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [suzukiUpperSourceP_of_le_two (by norm_num),
      suzukiProposition118SourceTMinus_at_two_eq_one hH]
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      (s := (2 : ℝ)) (by norm_num) (by norm_num)
    field_simp
    linarith
  · rw [suzukiUpperSourceP_of_two_lt hs, suzukiContinuousLowerTail]

private theorem suzukiUpperSourceParity_shift_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => suzukiProposition118SourceTPlus (t - 1)) volume x y ∧
      IntervalIntegrable (fun t => suzukiProposition118SourceTMinus (t - 1)) volume x y := by
  have hQ := suzukiProposition118SourceQ_shift_intervalIntegrable hH
    (by linarith : 2 ≤ x) hxy
  have hlayer : ∀ n : ℕ, AEStronglyMeasurable
      (fun t => suzukiLayer 1 2 n (t - 1)) (volume.restrict (Set.uIoc x y)) := by
    intro n
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    have hr := (KappaOneModel.regular (by norm_num : (1 : ℝ) < 2) n).continuous
    apply (hr.comp (continuousOn_id.sub continuousOn_const) ?_).congr
      (fun t _ => (KappaOneModel.layer_eq_suzukiLayer 2 n (t - 1)).symm)
    intro t ht
    unfold KappaOneModel.closedDomain KappaOneModel.eps
    simp only [Set.mem_Ici]
    rw [Set.mem_uIoc] at ht
    have heps : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 2)))
    dsimp
    rcases ht with ht | ht <;> linarith
  have hpmeas : AEStronglyMeasurable
      (fun t => suzukiProposition118SourceTPlus (t - 1))
      (volume.restrict (Set.uIoc x y)) :=
    AEStronglyMeasurable.tsum (fun k => hlayer (2 * k + 1))
  have hmmeas : AEStronglyMeasurable
      (fun t => suzukiProposition118SourceTMinus (t - 1))
      (volume.restrict (Set.uIoc x y)) :=
    AEStronglyMeasurable.tsum (fun k => hlayer (2 * (k + 1)))
  constructor
  · apply hQ.mono_fun hpmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.mem_uIoc] at ht
    have ht2 : 2 ≤ t - 1 := by rcases ht with ht | ht <;> linarith
    have hp0 : 0 ≤ suzukiProposition118SourceTPlus (t - 1) :=
      tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith))
    have hm0 : 0 ≤ suzukiProposition118SourceTMinus (t - 1) :=
      tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg ht2 k)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0,
      suzukiProposition118SourceQ, if_neg (not_lt.mpr ht2),
      abs_of_nonneg (add_nonneg hp0 hm0)]
    linarith
  · apply hQ.mono_fun hmmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.mem_uIoc] at ht
    have ht2 : 2 ≤ t - 1 := by rcases ht with ht | ht <;> linarith
    have hp0 : 0 ≤ suzukiProposition118SourceTPlus (t - 1) :=
      tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith))
    have hm0 : 0 ≤ suzukiProposition118SourceTMinus (t - 1) :=
      tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg ht2 k)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm0,
      suzukiProposition118SourceQ, if_neg (not_lt.mpr ht2),
      abs_of_nonneg (add_nonneg hp0 hm0)]
    linarith

private theorem suzukiUpperSourceP_shift_intervalIntegrable_of_le_three
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3) :
    IntervalIntegrable (fun t => suzukiUpperSourceP (t - 1)) volume x y := by
  have hc : ContinuousOn
      (fun t : ℝ => suzukiLowerSieveAmplitude / (t - 1)) (Set.uIcc x y) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact ne_of_gt (by linarith [hx, ht.1] : 0 < t - 1)
  apply hc.intervalIntegrable.congr
  intro t ht
  rw [uIoc_of_le hxy] at ht
  change suzukiLowerSieveAmplitude / (t - 1) = suzukiUpperSourceP (t - 1)
  rw [suzukiUpperSourceP_of_le_two (by linarith [ht.2, hy] : t - 1 ≤ 2)]

private theorem suzukiUpperSourceP_shift_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => suzukiUpperSourceP (t - 1)) volume x y := by
  by_cases hy : y ≤ 3
  · exact suzukiUpperSourceP_shift_intervalIntegrable_of_le_three hx hxy hy
  by_cases hx3 : 3 ≤ x
  · rcases suzukiUpperSourceParity_shift_intervalIntegrable hH hx3 hxy with ⟨hp, hm⟩
    have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume x y :=
      intervalIntegrable_const
    apply (hc.add hp).sub hm |>.congr
    intro t ht
    rw [uIoc_of_le hxy] at ht
    change 2 + suzukiProposition118SourceTPlus (t - 1) -
      suzukiProposition118SourceTMinus (t - 1) = suzukiUpperSourceP (t - 1)
    rw [suzukiUpperSourceP_eq_series hH (by linarith [hx3, ht.1] : 2 ≤ t - 1)]
  · have hx3' : x ≤ 3 := le_of_not_ge hx3
    have h3y : 3 ≤ y := le_of_not_ge hy
    exact (suzukiUpperSourceP_shift_intervalIntegrable_of_le_three hx hx3' le_rfl).trans
      (by
        rcases suzukiUpperSourceParity_shift_intervalIntegrable hH le_rfl h3y with ⟨hp, hm⟩
        apply (intervalIntegrable_const.add hp).sub hm |>.congr
        intro t ht
        rw [uIoc_of_le h3y] at ht
        change 2 + suzukiProposition118SourceTPlus (t - 1) -
          suzukiProposition118SourceTMinus (t - 1) = suzukiUpperSourceP (t - 1)
        rw [suzukiUpperSourceP_eq_series hH (by linarith [ht.1] : 2 ≤ t - 1)])

private theorem suzukiUpperSourceP_weighted_sub_of_le_three
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3) :
    y * suzukiUpperSourceP y - x * suzukiUpperSourceP x =
      ∫ t in x..y, suzukiUpperSourceP (t - 1) := by
  have hminus := suzukiProposition118SourceTMinus_weighted_sub hH hx hxy
  have hplusInt : IntervalIntegrable
      (fun t => suzukiProposition118SourceTPlus (t - 1)) volume x y := by
    have hc : ContinuousOn
        (fun t : ℝ => suzukiLowerSieveAmplitude / (t - 1) - 1) (Set.uIcc x y) := by
      apply (continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_).sub
        continuousOn_const
      intro t ht
      rw [uIcc_of_le hxy] at ht
      exact ne_of_gt (by linarith [hx, ht.1] : 0 < t - 1)
    apply hc.intervalIntegrable.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).2
    have hne2 : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (μ := volume) (2 : ℝ))
    filter_upwards [hne2] with t ht2
    intro ht
    rw [uIoc_of_le hxy] at ht
    have ht1 : 1 < t - 1 := lt_of_le_of_ne (by linarith [hx, ht.1] : 1 ≤ t - 1)
      (fun h => ht2 (by linarith))
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      ht1 (by linarith [ht.2, hy] : t - 1 ≤ 3)
    field_simp [ne_of_gt (by linarith : 0 < t - 1)] at hp ⊢
    linarith
  have hIntegral :
      (∫ t in x..y, suzukiUpperSourceP (t - 1)) =
        (y - x) + ∫ t in x..y, suzukiProposition118SourceTPlus (t - 1) := by
    have hone : (∫ _t in x..y, (1 : ℝ)) = y - x := by simp
    rw [← hone, ← intervalIntegral.integral_add intervalIntegrable_const hplusInt]
    apply intervalIntegral.integral_congr_ae
    have hne2 : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (μ := volume) (2 : ℝ))
    filter_upwards [hne2] with t ht2
    intro ht
    rw [uIoc_of_le hxy] at ht
    have ht1 : 1 < t - 1 := lt_of_le_of_ne (by linarith [hx, ht.1] : 1 ≤ t - 1)
      (fun h => ht2 (by linarith))
    rw [suzukiUpperSourceP_of_le_two (by linarith [ht.2, hy] : t - 1 ≤ 2)]
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      ht1 (by linarith [ht.2, hy] : t - 1 ≤ 3)
    field_simp [ne_of_gt (by linarith : 0 < t - 1)] at hp ⊢
    linarith
  have hweighted (s : ℝ) (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
      s * suzukiUpperSourceP s =
        suzukiLowerSieveAmplitude + s -
          s * suzukiProposition118SourceTMinus s := by
    rw [suzukiUpperSourceP_eq_series hH hs2]
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      (by linarith : 1 < s) hs3
    linarith
  rw [hweighted y (hx.trans hxy) hy, hweighted x hx (hxy.trans hy), hIntegral]
  linarith

private theorem suzukiUpperSourceP_weighted_sub_of_three_le
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    y * suzukiUpperSourceP y - x * suzukiUpperSourceP x =
      ∫ t in x..y, suzukiUpperSourceP (t - 1) := by
  have hp := suzukiProposition118SourceTPlus_weighted_sub hH hx hxy
  have hm := suzukiProposition118SourceTMinus_weighted_sub hH (by linarith : 2 ≤ x) hxy
  rcases suzukiUpperSourceParity_shift_intervalIntegrable hH hx hxy with ⟨hpint, hmint⟩
  have hIntegral :
      (∫ t in x..y, suzukiUpperSourceP (t - 1)) =
        2 * (y - x) +
          (∫ t in x..y, suzukiProposition118SourceTPlus (t - 1)) -
          ∫ t in x..y, suzukiProposition118SourceTMinus (t - 1) := by
    have htwo : (∫ _t in x..y, (2 : ℝ)) = 2 * (y - x) := by simp; ring
    calc
      (∫ t in x..y, suzukiUpperSourceP (t - 1)) =
          ∫ t in x..y, (2 + suzukiProposition118SourceTPlus (t - 1) -
            suzukiProposition118SourceTMinus (t - 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hxy] at ht
        change suzukiUpperSourceP (t - 1) =
          2 + suzukiProposition118SourceTPlus (t - 1) -
            suzukiProposition118SourceTMinus (t - 1)
        rw [suzukiUpperSourceP_eq_series hH
          (by linarith [hx, ht.1] : 2 ≤ t - 1)]
      _ = (∫ _t in x..y, (2 : ℝ)) +
            (∫ t in x..y, suzukiProposition118SourceTPlus (t - 1)) -
            ∫ t in x..y, suzukiProposition118SourceTMinus (t - 1) := by
        rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hpint) hmint,
          intervalIntegral.integral_add intervalIntegrable_const hpint]
      _ = _ := by rw [htwo]
  rw [suzukiUpperSourceP_eq_series hH (by linarith : 2 ≤ y),
    suzukiUpperSourceP_eq_series hH (by linarith : 2 ≤ x), hIntegral]
  linarith

theorem suzukiUpperSourceP_weighted_sub
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    y * suzukiUpperSourceP y - x * suzukiUpperSourceP x =
      ∫ t in x..y, suzukiUpperSourceP (t - 1) := by
  by_cases hy : y ≤ 3
  · exact suzukiUpperSourceP_weighted_sub_of_le_three hH hx hxy hy
  by_cases hx3 : 3 ≤ x
  · exact suzukiUpperSourceP_weighted_sub_of_three_le hH hx3 hxy
  · have hx3' : x ≤ 3 := le_of_not_ge hx3
    have h3y : 3 ≤ y := le_of_not_ge hy
    have hlo := suzukiUpperSourceP_weighted_sub_of_le_three hH hx hx3' le_rfl
    have hhi := suzukiUpperSourceP_weighted_sub_of_three_le hH le_rfl h3y
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (suzukiUpperSourceP_shift_intervalIntegrable_of_le_three hx hx3' le_rfl)
      (suzukiUpperSourceP_shift_intervalIntegrable hH (by norm_num) h3y)
    linarith

private theorem weighted_source_continuous {A : ℝ → ℝ} {M : ℝ} (hM : 2 ≤ M)
    (hf : IntervalIntegrable (fun t => A (t-1)) volume 2 M)
    (hD : ∀ s ∈ Icc 2 M, s*A s - 2*A 2 = ∫ t in (2:ℝ)..s, A (t-1)) :
    ContinuousOn (fun s => s*A s) (Icc 2 M) := by
  let f : ℝ → ℝ := fun t => A (t-1)
  have hprim : ContinuousOn (fun s : ℝ => ∫ t in Ioc 2 s, f t) (Icc 2 M) :=
    intervalIntegral.continuousOn_primitive ((intervalIntegrable_iff_integrableOn_Icc_of_le hM).1 hf)
  have hc : ContinuousOn (fun s : ℝ => 2*A 2 + ∫ t in Ioc 2 s, f t) (Icc 2 M) :=
    continuousOn_const.add hprim
  apply hc.congr
  intro s hs
  have hd := hD s hs
  rw [intervalIntegral.integral_of_le hs.1] at hd
  change s * A s = 2 * A 2 + ∫ t in Ioc 2 s, A (t-1)
  linarith only [hd]

private theorem continuousOn_weighted_suzukiUpperSourceP
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {M : ℝ} (hM : 2 ≤ M) :
    ContinuousOn (fun s => s * suzukiUpperSourceP s) (Icc 2 M) := by
  apply weighted_source_continuous (A := suzukiUpperSourceP) hM
  · exact suzukiUpperSourceP_shift_intervalIntegrable hH (x := 2) (y := M) le_rfl hM
  · intro s hs
    exact suzukiUpperSourceP_weighted_sub hH (x := 2) (y := s) le_rfl hs.1

private theorem continuousOn_suzukiUpperSourceP
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ContinuousOn suzukiUpperSourceP (Ici (1 : ℝ)) := by
  intro s hs
  change 1 ≤ s at hs
  rcases lt_trichotomy s 2 with hs2 | rfl | hs2
  · have hr : ContinuousAt (fun u : ℝ => suzukiLowerSieveAmplitude / u) s :=
      continuousAt_const.div continuousAt_id (ne_of_gt (by linarith : 0 < s))
    apply hr.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hs2)] with u hu
      rw [suzukiUpperSourceP_of_le_two hu.le]
    · rw [suzukiUpperSourceP_of_le_two hs2.le]
  · have hr : ContinuousAt (fun u : ℝ => suzukiLowerSieveAmplitude / u) 2 :=
      continuousAt_const.div continuousAt_id (by norm_num)
    have hlo : ContinuousWithinAt suzukiUpperSourceP (Iic (2 : ℝ)) 2 := by
      apply hr.continuousWithinAt.congr
      · intro u hu
        exact suzukiUpperSourceP_of_le_two hu
      · exact suzukiUpperSourceP_of_le_two le_rfl
    have hW := continuousOn_weighted_suzukiUpperSourceP hH
      (M := (3 : ℝ)) (by norm_num)
    have hWsmall : ContinuousWithinAt
        (fun u => u * suzukiUpperSourceP u) (Icc (2 : ℝ) 3) 2 :=
      hW.continuousWithinAt ⟨le_rfl, by norm_num⟩
    have hsets : Icc (2 : ℝ) 3 =ᶠ[𝓝 (2 : ℝ)] Ici 2 := by
      filter_upwards [Iio_mem_nhds (by norm_num : (2 : ℝ) < 3)] with u hu
      change (2 ≤ u ∧ u ≤ 3) ↔ 2 ≤ u
      exact ⟨fun h => h.1, fun h => ⟨h, hu.le⟩⟩
    have hWright : ContinuousWithinAt
        (fun u => u * suzukiUpperSourceP u) (Ici (2 : ℝ)) 2 :=
      hWsmall.congr_set hsets
    have hdiv := hWright.div continuousWithinAt_id (by norm_num : (2 : ℝ) ≠ 0)
    have hhi : ContinuousWithinAt suzukiUpperSourceP (Ici (2 : ℝ)) 2 := by
      apply hdiv.congr
      · intro u hu
        change 2 ≤ u at hu
        change suzukiUpperSourceP u = (u * suzukiUpperSourceP u) / u
        field_simp [ne_of_gt (by linarith : 0 < u)]
      · norm_num
    have hall := hlo.union hhi
    have hat : ContinuousAt suzukiUpperSourceP 2 := by
      simpa only [Iic_union_Ici, continuousWithinAt_univ] using hall
    exact hat.continuousWithinAt
  · have hW := continuousOn_weighted_suzukiUpperSourceP hH
      (M := s + 1) (by linarith)
    have hWat := hW.continuousAt (Icc_mem_nhds hs2 (by linarith : s < s + 1))
    have hdiv := hWat.div continuousAt_id (ne_of_gt (by linarith : 0 < s))
    apply hdiv.continuousWithinAt.congr
    · intro u hu
      change 1 ≤ u at hu
      change suzukiUpperSourceP u = (u * suzukiUpperSourceP u) / u
      field_simp [ne_of_gt (by linarith : 0 < u)]
    · change suzukiUpperSourceP s = (s * suzukiUpperSourceP s) / s
      field_simp [ne_of_gt (by linarith : 0 < s)]

theorem suzukiUpperSourceP_integralDDE_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SuzukiUpperSourcePIntegralDDE :=
  ⟨continuousOn_suzukiUpperSourceP hH,
    fun _ _ hx hxy => suzukiUpperSourceP_weighted_sub hH hx hxy⟩

theorem suzukiUpperSourceP_tail_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SuzukiUpperSourcePTail := by
  rcases tendsto_suzukiProposition118Source_parity_zero hH with ⟨hp, hm⟩
  unfold SuzukiUpperSourcePTail
  have htail : Tendsto (fun s : ℝ =>
      2 + suzukiProposition118SourceTPlus s -
        suzukiProposition118SourceTMinus s) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add hp |>.sub hm
  apply htail.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  rw [suzukiUpperSourceP_of_two_lt hs, suzukiContinuousLowerTail]

theorem suzukiUpperSourcePairingWindowTail_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SuzukiUpperSourcePairingWindowTail :=
  suzukiUpperSourcePairingWindowTail_of_sourceTail
    (suzukiUpperSourceP_tail_of_sourceContract hH)

theorem suzukiUpperSourcePairing_eq_two_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiUpperSourcePairing suzukiStandardUpperAdjoint s = 2 := by
  apply suzukiUpperSourcePairing_eq_two
    (suzukiUpperSourceP_integralDDE_of_sourceContract hH)
  · intro u hu
    exact suzukiStandardUpperAdjoint_hasDerivAt_dde (by linarith)
  · exact suzukiUpperSourceP_tail_of_sourceContract hH
  · exact suzukiStandardUpperAdjoint_scaledTail
  · exact suzukiUpperSourcePairingWindowTail_of_sourceContract hH
  · exact hs

theorem suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    suzukiLowerSieveAmplitude =
      2 * Real.exp Real.eulerMascheroniConstant := by
  have hp : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt suzukiStandardUpperAdjoint
        (-suzukiStandardUpperAdjoint (t + 1) / t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    exact suzukiStandardUpperAdjoint_hasDerivAt_dde (by linarith [ht.1])
  have hpOn : ContinuousOn suzukiStandardUpperAdjoint (Ici (2 : ℝ)) := by
    intro t ht
    change 2 ≤ t at ht
    exact (suzukiStandardUpperAdjoint_hasDerivAt_dde
      (by linarith : 0 < t)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun t => suzukiStandardUpperAdjoint (t + 1) / t) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact hpOn.comp (continuousOn_id.add continuousOn_const) (by
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        simp only [Set.mem_Ici]
        linarith [ht.1])
    · exact continuousOn_id
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact ne_of_gt (by linarith [ht.1] : 0 < t)
  exact suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_upperPairing
    hp hint (suzukiUpperSourcePairing_eq_two_of_sourceContract hH (by norm_num))
    suzukiStandardUpperAdjoint_one_eq_exp_neg_eulerMascheroni_unconditional

end MathlibNt.SieveTheory

namespace TH8000Amplitude
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
theorem at_four :
    suzukiContinuousLowerFactor 4 = Real.exp Real.eulerMascheroniConstant / 2 * Real.log 3 := by
  unfold suzukiContinuousLowerFactor suzukiContinuousLowerTail
  rw [one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract (by norm_num) (by norm_num),
    suzukiLowerSieveFactorFirstInterval_eq_log (by norm_num) (by norm_num),
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]
  norm_num
  ring

open Filter MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

theorem lower_at_four {K ε : ℝ} (hK : 2 ≤ K) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ S : BoundingSieve,
      HasDimensionOneLocalProductBound S K →
      2 ≤ ⌈(D : ℝ)^(1/4:ℝ)⌉₊ →
      let z := ⌈(D : ℝ)^(1/4:ℝ)⌉₊
      (Real.exp Real.eulerMascheroniConstant / 2 * Real.log 3 - ε) *
          suzukiVProduct S (z : ℝ) ≤
        LinearSieve.lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  have hsrc : SuzukiClaim145SourceParameters (16:ℝ) (1/2:ℝ) (7:ℝ) := by
    constructor <;> norm_num
  obtain ⟨C₁, _, h⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_, _, C, _, _, hC, h⟩ := h C₁ le_rfl
  obtain ⟨Dσ, _, hσ⟩ := exists_sourceSigma_fixed_lower_threshold (16:ℝ) 4 (by norm_num)
  obtain ⟨DE, hE⟩ := eventually_atTop.1 (eventually_all_depth_suzuki_error_half
    (H := jr1965Section13HatLayers) (C := C) (K := K) (s := 4)
    jr1965Section13HatSourceContract.toSection13HatContract (by linarith) (by norm_num) ε hε)
  refine ⟨max 2 (max ⌈Dσ⌉₊ ⌈DE⌉₊), ?_⟩
  intro D hD S hlocal hz
  have hD₂ : 2 ≤ D := (le_max_left _ _).trans hD
  have hDσ : Dσ ≤ (D : ℝ) :=
    Nat.ceil_le.mp ((le_max_left _ _).trans ((le_max_right _ _).trans hD))
  have hDE : DE ≤ (D : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans ((le_max_right _ _).trans hD))
  let z := ⌈(D:ℝ)^(1/4:ℝ)⌉₊
  let depth := 2 * ((suzukiSupportedBelow S z).card + 1)
  have herror := (hE (D : ℝ) hDE depth).2
  have hmain := h S K hK hlocal D hD₂ 4 (by norm_num) (hσ (D : ℝ) hDσ) hz
  change suzukiVProduct S (z : ℝ) * (suzukiContinuousLowerFactor 4 - _) ≤ _ at hmain
  rw [at_four] at hmain
  change (_ - ε) * suzukiVProduct S (z : ℝ) ≤ _
  rw [mul_comm (_ - ε)]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (suzukiVProduct_pos S (z : ℝ)).le) hmain
  exact sub_le_sub_left herror.le _

end TH8000Amplitude

end


-- TH8000UpperSource
section

/- Finite upper Rosser identities and the all-depth upper density comparison,
from subfish-zhou/goldbach-lean at 9d4c3a4010d42aedd9e7231bf94386019cfffccc,
Apache License 2.0. This extracts the first-interval case needed at parameter two. -/

section
open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

noncomputable def upperSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) : ℝ :=
  ∑ q ∈ suzukiSupportedBelow S z,
    S.nu q * sourceDiscreteEuler S q *
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
        ((suzukiSupportedBelow S z).filter (fun p => q < p)) k

private theorem upper_ceilDiv_ceilDiv_eq
    {D a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (D ⌈/⌉ a) ⌈/⌉ b = D ⌈/⌉ (a * b) := by
  exact MathlibNt.SieveTheory.ceilDiv_ceilDiv_eq ha hb

private theorem upperSuzukiUnnormalizedLayer_succ
    (S : BoundingSieve) (D z k : ℕ) :
    upperSuzukiUnnormalizedLayer S D z (k + 1) =
      ∑ p₀ ∈ (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D),
        S.nu p₀ * ∑ p₁ ∈ suzukiSupportedBelow S p₀,
          S.nu p₁ * upperSuzukiUnnormalizedLayer S
            (D ⌈/⌉ (p₀ * p₁)) p₁ k := by
  classical
  let Z := suzukiSupportedBelow S z
  unfold upperSuzukiUnnormalizedLayer
  change (∑ q ∈ Z,
      S.nu q * sourceDiscreteEuler S q *
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (Z.filter (fun p => q < p)) (k + 1)) = _
  have hexpand (q : ℕ) (hq : q ∈ Z) :
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (Z.filter (fun p => q < p)) (k + 1) =
        ∑ p₀ ∈ Z.filter (fun p => q < p),
          ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            S.nu p₀ * S.nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity S.nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k := by
    apply upperRosserBoundaryChainsFixedDepthDensity_succ S.nu
    · simp
    · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    · intro p hp
      exact Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.le
  have hrewrite :
      (∑ q ∈ Z,
        S.nu q * sourceDiscreteEuler S q *
          upperRosserBoundaryChainsFixedDepthDensity S.nu D q
            (Z.filter (fun p => q < p)) (k + 1)) =
      ∑ q ∈ Z,
        S.nu q * sourceDiscreteEuler S q *
          (∑ p₀ ∈ Z.filter (fun p => q < p),
            ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              S.nu p₀ * S.nu p₁ *
                upperRosserBoundaryChainsFixedDepthDensity S.nu
                  (D ⌈/⌉ (p₀ * p₁)) q
                  ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hexpand q hq]
  rw [hrewrite]
  change (∑ q ∈ Z,
      S.nu q * sourceDiscreteEuler S q *
        (∑ p₀ ∈ Z.filter (fun p => q < p),
          ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            S.nu p₀ * S.nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity S.nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k)) = _
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ p₀ ∈ Z,
          ∑ q ∈ Z.filter (fun q => q < p₀),
            ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              S.nu q * sourceDiscreteEuler S q *
                (S.nu p₀ * S.nu p₁ *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
          apply Finset.sum_comm'
          intro q p₀
          simp only [Finset.mem_filter]
          tauto
    _ = ∑ p₀ ∈ Z,
          ∑ p₁ ∈ Z.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            ∑ q ∈ Z.filter (fun q => q < p₁),
              S.nu q * sourceDiscreteEuler S q *
                (S.nu p₀ * S.nu p₁ *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          apply Finset.sum_comm'
          intro q p₁
          constructor
          · intro h
            rcases h with ⟨hq, hp₁⟩
            have hq' := Finset.mem_filter.mp hq
            have hp₁' := Finset.mem_filter.mp hp₁
            have hp₁base := Finset.mem_filter.mp hp₁'.1
            exact ⟨Finset.mem_filter.mpr ⟨hq'.1, hp₁base.2⟩,
              Finset.mem_filter.mpr ⟨hp₁base.1, hp₁'.2⟩⟩
          · intro h
            rcases h with ⟨hq, hp₁⟩
            have hq' := Finset.mem_filter.mp hq
            have hp₁' := Finset.mem_filter.mp hp₁
            exact ⟨Finset.mem_filter.mpr ⟨hq'.1, hq'.2.trans hp₁'.2.1⟩,
              Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨hp₁'.1, hq'.2⟩, hp₁'.2⟩⟩
    _ = ∑ p₀ ∈ Z.filter (fun p => p ^ 3 < D),
          S.nu p₀ * ∑ p₁ ∈ suzukiSupportedBelow S p₀,
            S.nu p₁ *
              (∑ q ∈ suzukiSupportedBelow S p₁,
                S.nu q * sourceDiscreteEuler S q *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((suzukiSupportedBelow S p₁).filter (fun p => q < p)) k) := by
          rw [Finset.sum_filter]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          have hp₀z : p₀ < z := (Finset.mem_filter.mp hp₀).2
          by_cases hcut : p₀ ^ 3 < D
          · rw [if_pos hcut]
            apply Finset.sum_congr
            · ext p₁
              simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
              constructor
              · rintro ⟨⟨hp₁S, hp₁z⟩, hp₁p₀, _⟩
                exact ⟨hp₁S, hp₁p₀⟩
              · rintro ⟨hp₁S, hp₁p₀⟩
                exact ⟨⟨hp₁S, hp₁p₀.trans hp₀z⟩,
                  hp₁p₀, hcut⟩
            · intro p₁ hp₁
              have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2
              have hp₁z : p₁ < z := hp₁p₀.trans hp₀z
              apply Finset.sum_congr
              · ext q
                simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
                constructor
                · rintro ⟨⟨hqS, hqz⟩, hqp₁⟩
                  exact ⟨hqS, hqp₁⟩
                · rintro ⟨hqS, hqp₁⟩
                  exact ⟨⟨hqS, hqp₁.trans hp₁z⟩,
                    hqp₁⟩
              · intro q hq
                have hcarrier :
                    (Z.filter (fun p => q < p)).filter (fun p => p < p₁) =
                      (suzukiSupportedBelow S p₁).filter (fun p => q < p) := by
                  ext p
                  simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
                  constructor
                  · rintro ⟨⟨⟨hpS, hpz⟩, hqp⟩, hpp₁⟩
                    exact ⟨⟨hpS, hpp₁⟩, hqp⟩
                  · rintro ⟨⟨hpS, hpp₁⟩, hqp⟩
                    exact ⟨⟨⟨hpS, hpp₁.trans hp₁z⟩, hqp⟩, hpp₁⟩
                rw [hcarrier]
                ring
          · rw [if_neg hcut]
            apply Finset.sum_eq_zero
            intro p₁ hp₁
            exact False.elim (hcut (Finset.mem_filter.mp hp₁).2.2)
    _ = _ := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          rfl

theorem suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) (hD : 1 < D) :
    suzukiSourceV S (2 * k + 1) D z =
      upperSuzukiUnnormalizedLayer S D z k := by
  induction k generalizing D z with
  | zero =>
      classical
      rw [show 2 * 0 + 1 = 1 by omega, suzukiSourceV_one]
      change (∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => D ≤ q ^ 3),
          S.nu q * sourceDiscreteEuler S q) =
        ∑ q ∈ suzukiSupportedBelow S z,
          S.nu q * sourceDiscreteEuler S q *
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              ((suzukiSupportedBelow S z).filter (fun p => q < p)) 0
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      have hqprime : q.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      rw [upperRosserBoundaryChainsFixedDepthDensity_zero S.nu hD
        (by simp) hqprime]
      · by_cases hcube : D ≤ q ^ 3 <;> simp [hcube]
      · intro p hp
        exact (Finset.mem_filter.mp hp).2.le
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
        suzukiSourceV_odd_succ_eq_upper_only S (by omega)
          (show Odd (2 * k + 3) from ⟨k + 1, by omega⟩)]
      rw [upperSuzukiUnnormalizedLayer_succ]
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      apply congrArg (fun x : ℝ => S.nu p₀ * x)
      rw [suzukiSourceV_succ_eq_unrestricted S (by omega)
        (by
          intro hodd
          exact (Nat.not_odd_iff_even.mpr
            (show Even (2 * k + 2) from ⟨k + 1, by omega⟩) hodd).elim)]
      apply Finset.sum_congr rfl
      intro p₁ hp₁
      have hp₀pos : 0 < p₀ := (Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).1).pos
      have hp₁prime : p₁.Prime := Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp hp₁).1
      have hDres : 1 < (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
        have hcut : p₀ ^ 3 < D := (Finset.mem_filter.mp hp₀).2
        have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2
        have hle : p₀ ≤ (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
          by_contra hn
          have hc : (D ⌈/⌉ p₀) ⌈/⌉ p₁ < p₀ := Nat.lt_of_not_ge hn
          have hmul₁ := (ceilDiv_le_iff_le_mul hp₁prime.pos).1 hc.le
          have hmul₀ := (ceilDiv_le_iff_le_mul hp₀pos).1 hmul₁
          have hp₁le : p₁ ≤ p₀ := hp₁p₀.le
          nlinarith [hp₁prime.two_le]
        exact hp₁prime.one_lt.trans_le (hp₁p₀.le.trans hle)
      rw [ih ((D ⌈/⌉ p₀) ⌈/⌉ p₁) p₁ hDres,
        upper_ceilDiv_ceilDiv_eq hp₀pos hp₁prime.pos]

theorem suzukiActualT_odd_eq_sum_upperSuzukiUnnormalizedLayers
    (S : BoundingSieve) (D z m : ℕ) (hD : 1 < D) :
    suzukiActualT S (2 * m + 1) D z =
      ∑ k ∈ Finset.range (m + 1), upperSuzukiUnnormalizedLayer S D z k := by
  induction m with
  | zero =>
      rw [show 2 * 0 + 1 = 1 by omega, suzukiActualT_one,
        suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer S D z 0 hD]
      simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        suzukiActualT_add_two]
      have hlayer : suzukiSourceV S (2 * m + 1 + 2) D z =
          upperSuzukiUnnormalizedLayer S D z (m + 1) := by
        simpa only [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega] using
          suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer S D z (m + 1) hD
      rw [hlayer, ih]
      simpa only [add_comm] using (Finset.sum_range_succ
        (fun k => upperSuzukiUnnormalizedLayer S D z k) (m + 1)).symm

end MathlibNt.SieveTheory
end

section
open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

def UpperRosserSuzukiExactBridge : Prop :=
  ∀ (S : BoundingSieve) (D z : ℕ),
    1 < D →
    (∀ p ∈ S.prodPrimes.primeFactors, p < D) →
    (∀ p ∈ S.prodPrimes.primeFactors, p < z) →
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        suzukiActualT S (2 * S.prodPrimes.primeFactors.card + 1) D z

private theorem upper_euler_factor_ne_zero
    (S : BoundingSieve) {p : ℕ} (hp : p ∈ S.prodPrimes.primeFactors) :
    1 - S.nu p ≠ 0 := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdiv : p ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
  exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv))

private theorem upper_euler_product_split_at
    (S : BoundingSieve) {q : ℕ} (hq : q ∈ S.prodPrimes.primeFactors) :
    (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)) =
      sourceDiscreteEuler S q * (1 - S.nu q) *
        ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
          (1 - S.nu p) := by
  classical
  let P := S.prodPrimes.primeFactors
  let L := P.filter (fun p => p < q)
  let U := P.filter (fun p => q < p)
  have hrest : P.filter (fun p => ¬p < q) = insert q U := by
    ext p
    simp only [P, U, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hpP, hpq⟩
      by_cases hpqeq : p = q
      · exact Or.inl hpqeq
      · exact Or.inr ⟨hpP,
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hpq) (fun h => hpqeq h.symm)⟩
    · rintro (rfl | ⟨hpP, hqp⟩)
      · exact ⟨hq, by omega⟩
      · exact ⟨hpP, by omega⟩
  have hqU : q ∉ U := by simp [U]
  calc
    (∏ p ∈ P, (1 - S.nu p)) =
        (∏ p ∈ L, (1 - S.nu p)) *
          ∏ p ∈ P.filter (fun p => ¬p < q), (1 - S.nu p) :=
      (Finset.prod_filter_mul_prod_filter_not P (fun p => p < q)
        (fun p => 1 - S.nu p)).symm
    _ = (∏ p ∈ L, (1 - S.nu p)) *
          ((1 - S.nu q) * ∏ p ∈ U, (1 - S.nu p)) := by
      rw [hrest, Finset.prod_insert hqU]
    _ = sourceDiscreteEuler S q * (1 - S.nu q) *
          ∏ p ∈ P.filter (fun p => q < p), (1 - S.nu p) := by
      unfold sourceDiscreteEuler suzukiSupportedBelow
      ring

private theorem upper_relative_depth_mul_fullEuler
    (S : BoundingSieve) {D q k : ℕ}
    (hq : q ∈ S.prodPrimes.primeFactors) :
    (S.nu q / (1 - S.nu q)) *
        upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k *
        (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)) =
      S.nu q * sourceDiscreteEuler S q *
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  have hqfactor : 1 - S.nu q ≠ 0 := upper_euler_factor_ne_zero S hq
  have htailfactor :
      (∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
        (1 - S.nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact upper_euler_factor_ne_zero S (Finset.mem_filter.mp hp).1
  unfold upperRosserBoundaryChainsFixedDepthRelativeDensity
  rw [upper_euler_product_split_at S hq]
  field_simp [hqfactor, htailfactor]

private theorem upper_boundary_depth_sum_extend_to_support
    (S : BoundingSieve) (D q : ℕ) :
    (∑ k ∈ Finset.range
        ((S.prodPrimes.primeFactors.filter (fun p => q < p)).card + 1),
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
        (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) =
      ∑ k ∈ Finset.range (S.prodPrimes.primeFactors.card + 1),
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  apply Finset.sum_subset
  · apply Finset.range_mono
    exact Nat.add_le_add_right
      (Finset.card_le_card (Finset.filter_subset (fun p => q < p)
        S.prodPrimes.primeFactors)) 1
  · intro k hkBig hkSmall
    apply upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_card_lt
    simp only [Finset.mem_range] at hkBig hkSmall
    omega

theorem mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    (S : BoundingSieve) (D z : ℕ) (hD : 1 < D)
    (hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D)
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        suzukiActualT S (2 * S.prodPrimes.primeFactors.card + 1) D z := by
  classical
  let P := S.prodPrimes.primeFactors
  let V := ∏ p ∈ P, (1 - S.nu p)
  have hprime : ∀ p ∈ P, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 :=
    fun _ hp => upper_euler_factor_ne_zero S hp
  have hV : V ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hratio :=
    LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths
      S.nu P hD hprime hlevel hfactor
  have hterm (q : ℕ) (hq : q ∈ P) :
      (S.nu q / (1 - S.nu q) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
              (P.filter (fun p => q < p)) k) * V =
        S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k := by
    calc
      (S.nu q / (1 - S.nu q) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
              (P.filter (fun p => q < p)) k) * V =
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            (S.nu q / (1 - S.nu q)) *
              upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
                (P.filter (fun p => q < p)) k * V := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            S.nu q * sourceDiscreteEuler S q *
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact upper_relative_depth_mul_fullEuler S hq
      _ = S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k := by
            rw [← Finset.mul_sum,
              upper_boundary_depth_sum_extend_to_support S D q]
  have hdensity :
      LinearSieve.upperRosserSetDensitySum S.nu D P =
        V + ∑ q ∈ P,
          S.nu q * sourceDiscreteEuler S q *
            ∑ k ∈ Finset.range (P.card + 1),
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
    calc
      LinearSieve.upperRosserSetDensitySum S.nu D P =
          (LinearSieve.upperRosserSetDensitySum S.nu D P / V) * V :=
        (div_mul_cancel₀ _ hV).symm
      _ = (1 + ∑ q ∈ P,
          (S.nu q / (1 - S.nu q)) *
            ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
              upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
                (P.filter (fun p => q < p)) k) * V := by rw [hratio]
      _ = V + ∑ q ∈ P,
          S.nu q * sourceDiscreteEuler S q *
            ∑ k ∈ Finset.range (P.card + 1),
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
        rw [add_mul, one_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        exact hterm q hq
  have hsupport : suzukiSupportedBelow S z = P := by
    ext p
    simp only [suzukiSupportedBelow, P, Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · exact fun hp => ⟨hp, hz p hp⟩
  have hboundary :
      (∑ q ∈ P,
        S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k) =
        ∑ k ∈ Finset.range (P.card + 1),
          upperSuzukiUnnormalizedLayer S D z k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    unfold upperSuzukiUnnormalizedLayer
    rw [hsupport]
  rw [LinearSieve.mainSum_upperRosserWeight_eq_setDensitySum]
  change LinearSieve.upperRosserSetDensitySum S.nu D P = _
  rw [hdensity, hboundary,
    ← suzukiActualT_odd_eq_sum_upperSuzukiUnnormalizedLayers
      S D z P.card hD]
  simp [P, V, AnalyticNumberTheory.Sieve.sieveProductPrimeFactors]

theorem upperRosserSuzukiExactBridge : UpperRosserSuzukiExactBridge := by
  intro S D z hD hlevel hz
  exact (mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    S D z hD hlevel hz).le

end MathlibNt.SieveTheory
end

section
open Set Filter Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable section

theorem errorEnvelope_odd_le_sixteen_on_upper_window
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {N : ℕ} (hN : Odd N) {D d s : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D) (hlog : 4 ^ d ≤ Real.log D)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    errorEnvelope H N D d s ≤ 16 := by
  have hs0 : 0 ≤ s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hsd : s ^ d ≤ (4 : ℝ) ^ d :=
    Real.rpow_le_rpow hs0 (by linarith) hd
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one hlogpos).2 (hsd.trans hlog)
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := by positivity
  have hperturb : (1 + s ^ d / Real.log D) ^ s ≤ 16 := by
    calc
      (1 + s ^ d / Real.log D) ^ s ≤ (2 : ℝ) ^ s :=
        Real.rpow_le_rpow hbase0 (by linarith) hs0
      _ ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hshi
      _ = 16 := by norm_num
  have hweighted_nonneg : 0 ≤ weightedHat H .plus s := by
    unfold weightedHat
    exact mul_nonneg (sq_nonneg s) (hH.positive .plus s (by linarith)).le
  have hweighted : weightedHat H .plus s ≤ 1 := by
    by_cases hs3 : s ≤ 3
    · rw [hH.initial_plus s (by linarith) (by norm_num; linarith)]
      norm_num
    · have h3s : 3 < s := lt_of_not_ge hs3
      have hanti : AntitoneOn (weightedHat H .plus) (Icc (3 : ℝ) s) :=
        weightedHat_antitoneOn_Icc_closed hH .plus (by norm_num [ErrorSign.epsilon])
      have hle := hanti ⟨le_rfl, h3s.le⟩ ⟨h3s.le, le_rfl⟩ h3s.le
      rw [hH.initial_plus 3 (by norm_num) (by norm_num)] at hle
      norm_num at hle ⊢
      exact hle
  have hT : 0 ≤ H.Tplus s := by
    exact (hH.positive .plus s (by linarith)).le
  have hsT : s * H.Tplus s ≤ 1 := by
    have hw : s ^ 2 * H.Tplus s ≤ 1 := by
      simpa [weightedHat, Section13HatLayers.T] using hweighted
    nlinarith
  rw [errorEnvelope_odd hN]
  calc
    (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s =
        (1 + s ^ d / Real.log D) ^ s * (s * H.Tplus s) := by ring
    _ ≤ 16 * 1 := mul_le_mul hperturb hsT (mul_nonneg hs0 hT) (by norm_num)
    _ = 16 := by norm_num

theorem eventually_all_odd_depth_suzuki_error_upper_window
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {C K d Δ ρ : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hΔ : 0 < Δ)
    (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ N : ℕ, Odd N → ∀ s : ℝ,
      3 / 2 ≤ s → s ≤ 4 →
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) ∧
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) < ρ := by
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-Δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hΔ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * 16
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-Δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-Δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).mul hdecay)
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, (4 : ℝ) ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((4 : ℝ) ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with D hsmallD hlogD hD
  intro N hN s hslo hshi
  have hE := errorEnvelope_odd_le_sixteen_on_upper_window H hH hN hd hD hlogD hslo hshi
  have hE0 : 0 ≤ errorEnvelope H N D d s :=
    errorEnvelope_nonneg H N hD (by linarith)
      (hH.positive (ErrorSign.ofDepth N) s (by linarith)).le
  have hlog0 : 0 ≤ Real.log D := (Real.log_pos hD).le
  have hdecay0 : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlog0 _
  constructor
  · positivity
  · calc
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) ≤ A * (Real.log D) ^ (-Δ) := by
            apply mul_le_mul_of_nonneg_right _ hdecay0
            dsimp [A]
            exact mul_le_mul_of_nonneg_left hE
              (mul_nonneg hC (Real.exp_pos _).le)
      _ < ρ := hsmallD

theorem finiteSourceLayer_two_mul_add_one_eq_sum_oddLayers
    (m : ℕ) (s : ℝ) :
    finiteSourceLayer 1 2 (2 * m + 1) s =
      ∑ k ∈ Finset.range (m + 1), suzukiLayer 1 2 (2 * k + 1) s := by
  classical
  have hcarrier :
      (Finset.Icc 1 (2 * m + 1)).filter (fun n => n % 2 = 1) =
        (Finset.range (m + 1)).image (fun k => 2 * k + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hn1, hnm⟩, hnOdd⟩
      refine ⟨n / 2, ?_, ?_⟩ <;> omega
    · rintro ⟨k, hk, rfl⟩
      constructor <;> omega
  unfold finiteSourceLayer
  rw [show (2 * m + 1) % 2 = 1 by omega]
  rw [← Finset.sum_filter, hcarrier, Finset.sum_image]
  intro a ha b hb hab
  change 2 * a + 1 = 2 * b + 1 at hab
  omega

theorem finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (m : ℕ) {s : ℝ} (hs : 1 < s) :
    finiteSourceLayer 1 2 (2 * m + 1) s ≤
      suzukiContinuousUpperFactor s - 1 := by
  rw [finiteSourceLayer_two_mul_add_one_eq_sum_oddLayers]
  unfold suzukiContinuousUpperFactor suzukiProposition118SourceTPlus
  have hsum := summable_suzukiProposition118SourceTPlus_of_sourceContract hH hs
  linarith [hsum.sum_le_tsum (Finset.range (m + 1))
    (fun k hk => suzukiLayer_one_two_odd_nonneg hs k)]

theorem upperRosserDensity_at_natCeil_of_allDepth
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve)
    {C K d Δ : ℝ} (hall : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2)
    (D : ℕ) (s : ℝ)
    (hD : 2 ≤ D) (hslo : 3 / 2 ≤ s) (_hshi : s ≤ 4)
    (hsSigma : s ≤ sourceSigma (D : ℝ) d)
    (hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let m : ℕ := S.prodPrimes.primeFactors.card
  let N : ℕ := 2 * m + 1
  have hNodd : Odd N := by dsimp [N]; exact ⟨m, by omega⟩
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hsdom : s ∈ KappaOneModel.parityDomain 2 N := by
    simp [KappaOneModel.parityDomain, Nat.odd_iff.mp hNodd]
    linarith
  have hSuzuki := hall N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hfinite := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    H hH m (by linarith : 1 < s)
  have hVeq : suzukiVProduct S (z : ℝ) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold suzukiVProduct
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, by simpa [z] using hcut p hp⟩
  have hzD : z ≤ D := by
    apply Nat.ceil_le.mpr
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one (by linarith : 0 < s)]
      linarith
    simpa [z] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact lt_of_lt_of_le (hcut p hp) hzD
  have hexact := upperRosserSuzukiExactBridge S D z (by omega) hlevel
    (by simpa [z] using hcut)
  dsimp only [N, m, z] at hSuzuki hexact ⊢
  rw [hVeq] at hSuzuki
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S (z : ℝ)).le
  calc
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          suzukiActualT S
            (2 * S.prodPrimes.primeFactors.card + 1) D z := by
              simpa [z] using hexact
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (finiteSourceLayer 1 2
              (2 * S.prodPrimes.primeFactors.card + 1) s +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H
                (2 * S.prodPrimes.primeFactors.card + 1)
                (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          gcongr
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          have hf := hfinite
          dsimp [m] at hf
          nlinarith

theorem exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ (S : BoundingSieve) (K : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D → ∀ s : ℝ,
              3 / 2 ≤ s → s ≤ 4 → s ≤ sourceSigma (D : ℝ) d →
              2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
              (∀ p ∈ S.prodPrimes.primeFactors,
                p < ⌈(D : ℝ) ^ (1 / s)⌉₊) →
              S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
                  (suzukiContinuousUpperFactor s +
                    C * Real.exp (Real.sqrt K) *
                      errorEnvelope H
                        (2 * S.prodPrimes.primeFactors.card + 1)
                        (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  obtain ⟨C1min, hC1min, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hdepth⟩ := hall C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro S K hK hlocal D hD s hslo hshi hsSigma hz2 hcut
  exact upperRosserDensity_at_natCeil_of_allDepth H hH S
    (hdepth S K hK hlocal) D s hD hslo hshi hsSigma hz2 hcut

end
end MathlibNt.SieveTheory
end

end


-- TH8000UpperTwo
section

namespace CentralUpperSieve
open Filter MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem at_two : suzukiContinuousUpperFactor 2 = Real.exp Real.eulerMascheroniConstant := by
  have hs := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub jr1965Section13HatSourceContract
    (by norm_num : (1:ℝ)<2) (by norm_num : (2:ℝ)≤3)
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract] at hs
  unfold suzukiContinuousUpperFactor
  linarith

theorem upper_at_two {K ε : ℝ} (hK : 2≤K) (hε : 0<ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ S : BoundingSieve,
      HasDimensionOneLocalProductBound S K →
      let z := ⌈(D:ℝ)^(1/2:ℝ)⌉₊
      2≤z → (∀ p ∈ S.prodPrimes.primeFactors, p<z) →
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        (Real.exp Real.eulerMascheroniConstant + ε)*suzukiVProduct S (z:ℝ) := by
  have hsrc : SuzukiClaim145SourceParameters (16:ℝ) (1/2:ℝ) (7:ℝ) := by
    constructor <;> norm_num
  obtain ⟨C₁,_,h⟩ := exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth
    jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_,_,C,_,_,hC,h⟩ := h C₁ le_rfl
  obtain ⟨Dσ,_,hσ⟩ := exists_sourceSigma_fixed_lower_threshold (16:ℝ) 2 (by norm_num)
  obtain ⟨DE,hE⟩ := eventually_atTop.1 (eventually_all_odd_depth_suzuki_error_upper_window
    jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
    (C:=C) (K:=K) (d:=16) (Δ:=1/2) (by linarith) (by norm_num) (by norm_num) hε)
  refine ⟨max 2 (max ⌈Dσ⌉₊ ⌈DE⌉₊),?_⟩
  intro D hD S hlocal z hz hcut
  have hD2 : 2≤D := by omega
  have hDσ : Dσ ≤ (D:ℝ) := Nat.ceil_le.mp (by omega)
  have hDE : DE ≤ (D:ℝ) := Nat.ceil_le.mp (by omega)
  have hmain := h S K hK hlocal D hD2 2 (by norm_num) (by norm_num)
    (hσ (D:ℝ) hDσ) hz hcut
  have he := (hE _ hDE _ (show Odd (2*S.prodPrimes.primeFactors.card+1)
    from ⟨_,rfl⟩) 2 (by norm_num) (by norm_num)).2
  rw [at_two] at hmain
  have hprod := suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt S
    (z:=(z:ℝ)) (fun p hp => by exact_mod_cast hcut p hp)
  rw [← hprod] at hmain
  exact hmain.trans (by
    rw [mul_comm (Real.exp _ + ε)]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he.le) (suzukiVProduct_pos _ _).le)

end CentralUpperSieve

end


-- TH8000AP
section

namespace GoldbachCentralSeven

open Finset

def crtClass (p d b k : ℕ) : ℕ :=
  if hc : d.Coprime k then Nat.chineseRemainder hc b (2*p^2) else 0

theorem crtClass_data {p d b k : ℕ} (hd : 0 < d) (hk : 0 < k) (hc : d.Coprime k) :
    crtClass p d b k < d*k ∧
    Nat.ModEq d (crtClass p d b k) b ∧ Nat.ModEq k (crtClass p d b k) (2*p^2) := by
  simp only [crtClass, dite_eq_left hc]
  exact ⟨Nat.chineseRemainder_lt_mul hc b (2*p^2) hd.ne' hk.ne',
    (Nat.chineseRemainder hc b (2*p^2)).property⟩

private theorem coprime_of_ap_class {a b d : ℕ} (hm : Nat.ModEq d a b) (hb : b.Coprime d) :
    a.Coprime d := by
  unfold Nat.ModEq at hm
  change a.gcd d = 1
  rw [Nat.gcd_comm a d, Nat.gcd_rec, hm, ← Nat.gcd_rec, Nat.gcd_comm d b]
  exact hb

theorem crtClass_reduced {p d b k : ℕ} (hp : p.Prime) (hd : 0 < d) (hk : 0 < k)
    (hkp : k < p) (hc : d.Coprime k) (hk2 : Nat.Coprime 2 k) (hb : b.Coprime d) :
    (crtClass p d b k).Coprime (d*k) := by
  obtain ⟨_, h1, h2⟩ := crtClass_data (p := p) (b := b) hd hk hc
  have hpk := Nat.coprime_of_lt_prime hk.ne' hkp hp
  exact Nat.coprime_mul_iff_right.mpr ⟨coprime_of_ap_class h1 hb,
    coprime_of_ap_class h2 (hk2.mul_left (hpk.pow_left 2))⟩

theorem crtClass_iff {p d b k t : ℕ} (hd : 0 < d) (hk : 0 < k) (hc : d.Coprime k) :
    Nat.ModEq (d*k) t (crtClass p d b k) ↔ Nat.ModEq d t b ∧ Nat.ModEq k t (2*p^2) := by
  obtain ⟨_, h1, h2⟩ := crtClass_data (p := p) (b := b) hd hk hc
  constructor
  · intro h
    obtain ⟨hd', hk'⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hc).mpr h
    exact ⟨hd'.trans h1, hk'.trans h2⟩
  · rintro ⟨h1',h2'⟩
    simpa only [crtClass, dite_eq_left hc] using Nat.chineseRemainder_modEq_unique hc h1' h2'

theorem reflected_dvd_iff {X h k : ℕ} (hh : h ≤ X) :
    k ∣ X-h ↔ Nat.ModEq k (X+h) (2*X) := by
  rw [Nat.modEq_iff_dvd' (by omega), show 2*X-(X+h)=X-h by omega]

theorem reflected_coprime_fixed {X h d b : ℕ} (hh : h ≤ X) (hb : b ≤ 2*X)
    (ht : Nat.ModEq d (X+h) b) (hadm : (2*X-b).Coprime d) : (X-h).Coprime d := by
  have heq : Nat.ModEq d ((X+h)+(X-h)) (b+(2*X-b)) := by
    rw [show X+h+(X-h)=2*X by omega, show b+(2*X-b)=2*X by omega]
  exact coprime_of_ap_class (Nat.ModEq.add_left_cancel' b ((ht.add_right (X-h)).symm.trans heq)) hadm

def sievedAPOffsets (p H d b k : ℕ) := (Icc 1 H).filter (fun h =>
  (p^2+h).Prime ∧ Nat.ModEq d (p^2+h) b ∧ k ∣ p^2-h)

def shortAPPrimes (X H q a : ℕ) := (Ioc X (X+H)).filter (fun t => t.Prime ∧ t % q = a)

theorem rho_count_eq_short_AP {p H d b k : ℕ} (hH : H ≤ p^2) (hd : 0 < d)
    (hk : 0 < k) (hc : d.Coprime k) :
    (sievedAPOffsets p H d b k).card =
      (shortAPPrimes (p^2) H (d*k) (crtClass p d b k)).card := by
  have hrep := (crtClass_data (p := p) (b := b) hd hk hc).1
  have hmem (h : ℕ) (hh : h ≤ p^2) :
      p^2+h ∈ shortAPPrimes (p^2) H (d*k) (crtClass p d b k) ↔
        h ∈ sievedAPOffsets p H d b k := by
    simp only [shortAPPrimes, sievedAPOffsets, mem_filter, mem_Ioc, mem_Icc]
    have hm : (p^2+h) % (d*k) = crtClass p d b k ↔
        Nat.ModEq d (p^2+h) b ∧ k ∣ p^2-h := by
      rw [reflected_dvd_iff hh, ← crtClass_iff hd hk hc]
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hrep]
    rw [hm]
    have hw : p^2 < p^2+h ∧ p^2+h ≤ p^2+H ↔ 1 ≤ h ∧ h ≤ H := by omega
    rw [hw]
  refine card_bij' (fun h _ => p^2+h) (fun t _ => t-p^2) ?_ ?_ ?_ ?_
  · intro h hh
    exact (hmem h ((mem_Icc.mp (mem_filter.mp hh).1).2.trans hH)).mpr hh
  · intro t ht
    have hi := mem_Ioc.mp (mem_filter.mp ht).1
    exact (hmem (t-p^2) (by omega)).mp (by simpa only [Nat.add_sub_of_le hi.1.le] using ht)
  · intro h _; omega
  · intro t ht
    have hi := mem_Ioc.mp (mem_filter.mp ht).1
    omega

theorem normalized_main_mul {d k : ℕ} (hc : d.Coprime k) (J : ℝ) :
    J/(d*k).totient = (J/(d.totient:ℝ))/(k.totient:ℝ) := by
  rw [Nat.totient_mul hc, Nat.cast_mul, div_mul_eq_div_div]

noncomputable def shortAPWorst (X H q : ℕ) (J : ℝ) : NNReal :=
  (range q).sup fun a => if a.Coprime q then
    (⟨|((shortAPPrimes X H q a).card : ℝ) - J/q.totient|, abs_nonneg _⟩ : NNReal)
    else 0

theorem shortAP_error_le {X H q a : ℕ} (ha : a < q) (hc : a.Coprime q) (J : ℝ) :
    |((shortAPPrimes X H q a).card : ℝ) - J/q.totient| ≤ (shortAPWorst X H q J : ℝ) := by
  let e := fun a : ℕ => if a.Coprime q then
    (⟨|((shortAPPrimes X H q a).card : ℝ) - J/q.totient|, abs_nonneg _⟩ : NNReal) else 0
  have h : e a ≤ (range q).sup e := le_sup (f := e) (mem_range.mpr ha)
  have he : (e a : ℝ) = |((shortAPPrimes X H q a).card : ℝ) - J/q.totient| := by
    unfold e
    rw [ite_eq_left hc]
  rw [← he]
  exact NNReal.coe_le_coe.mpr h

theorem sum_rho_errors_le {p H d b D : ℕ} (hp : p.Prime) (hd : 0 < d) (hb : b.Coprime d)
    (hH : H ≤ p^2) (S : Finset ℕ) (J : ℝ)
    (hS : ∀ k ∈ S, 0 < k ∧ k < p ∧ d.Coprime k ∧ Nat.Coprime 2 k ∧ d*k ≤ D) :
    (∑ k ∈ S, |((sievedAPOffsets p H d b k).card : ℝ) - J/d.totient/k.totient|) ≤
      ∑ q ∈ Icc 1 D, (shortAPWorst (p^2) H q J : ℝ) := by
  calc
    _ ≤ ∑ k ∈ S, (shortAPWorst (p^2) H (d*k) J : ℝ) := by
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hkpos, hkp, hc, hk2, _⟩ := hS k hk
      rw [rho_count_eq_short_AP hH hd hkpos hc, ← normalized_main_mul hc J]
      exact shortAP_error_le (crtClass_data hd hkpos hc).1
        (crtClass_reduced hp hd hkpos hkp hc hk2 hb) J
    _ = ∑ q ∈ S.image (fun k => d*k), (shortAPWorst (p^2) H q J : ℝ) := by
      rw [sum_image]
      intro a _ b _ hh
      exact Nat.eq_of_mul_eq_mul_left hd hh
    _ ≤ _ := by
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => (shortAPWorst (p^2) H q J).coe_nonneg)
      intro q hq
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
      obtain ⟨hkpos, _, _, _, hdk⟩ := hS k hk
      exact mem_Icc.mpr ⟨Nat.mul_pos hd hkpos, hdk⟩

theorem reflected_coprime_twice_fixed {X h d b : ℕ} (hh : h ≤ X) (hb : b ≤ 2*X)
    (ht : Nat.ModEq d (X+h) b) (hadm : (2*X-b).Coprime d)
    (hp : (X+h).Prime) (hgt : 2 < X+h) : (X-h).Coprime (2*d) := by
  refine Nat.coprime_mul_iff_right.mpr ⟨?_, reflected_coprime_fixed hh hb ht hadm⟩
  apply Nat.coprime_two_right.mpr
  have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  exact Nat.odd_iff.mpr (by omega)

theorem floor_window_le_center {p H : ℕ} (hp : 0 < p) (h : H^3 ≤ p^4) : H ≤ p^2 := by
  have hpp : p^4 ≤ (p^2)^3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (by norm_num)
  exact le_of_not_gt fun hgt => (Nat.pow_lt_pow_left hgt (by decide : 3 ≠ 0)).not_ge (h.trans hpp)

end GoldbachCentralSeven

end


-- TH8000Level
section

namespace GoldbachCentralSeven

open Filter Finset

noncomputable def fixedSieveLevel (X : ℕ) := ⌊(X:ℝ)^(5/32:ℝ)⌋₊
noncomputable def shortDistributionLevel (X : ℕ) (B : ℝ) :=
  ⌊(X:ℝ)^(1/6:ℝ)/(Real.log (X:ℝ))^B⌋₊

theorem eventually_fixed_modulus_level (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ k ≤ fixedSieveLevel X,
      d*k ≤ shortDistributionLevel X B := by
  have hdpos : 0 < (d:ℝ) := by exact_mod_cast hd
  have hf := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop B (show 0 < (1/96 : ℝ) by norm_num)).bound
      (show 0 < 1/(d:ℝ) by positivity))
  filter_upwards [hf, eventually_ge_atTop 2] with X hX htwo
  intro k hk
  have hgt : 1 < (X:ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hpos : 0 < (X:ℝ) := by linarith
  have hlog := Real.log_pos hgt
  have hlogB := Real.rpow_pos_of_pos hlog B
  change ‖Real.log (X:ℝ)^B‖ ≤ (1/(d:ℝ))*‖(X:ℝ)^(1/96:ℝ)‖ at hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogB,
    abs_of_pos (Real.rpow_pos_of_pos hpos _)] at hX
  have hcost : (d:ℝ)*(Real.log (X:ℝ))^B ≤ (X:ℝ)^(1/96:ℝ) := by
    calc
      _ ≤ (d:ℝ)*((1/(d:ℝ))*(X:ℝ)^(1/96:ℝ)) := by gcongr
      _ = _ := by field_simp
  have hkR : (k:ℝ) ≤ (X:ℝ)^(5/32:ℝ) := (by exact_mod_cast hk : (k:ℝ) ≤ fixedSieveLevel X).trans
    (Nat.floor_le (by positivity))
  apply (Nat.le_floor_iff (div_nonneg (Real.rpow_nonneg hpos.le _) hlogB.le)).mpr
  rw [Nat.cast_mul]
  apply (le_div_iff₀ hlogB).mpr
  calc
    _ = (k:ℝ)*((d:ℝ)*Real.log (X:ℝ)^B) := by ring
    _ ≤ (X:ℝ)^(5/32:ℝ)*(X:ℝ)^(1/96:ℝ) :=
      mul_le_mul hkR hcost (mul_nonneg hdpos.le hlogB.le) (by positivity)
    _ = _ := by rw [← Real.rpow_add hpos]; norm_num

theorem fixed_level_at_prime_squares (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ k ≤ fixedSieveLevel (p^2),
      k < p ∧ d*k ≤ shortDistributionLevel (p^2) B := by
  have hh := (tendsto_pow_atTop (α := ℕ) (by decide : 2 ≠ 0)).eventually
    (eventually_fixed_modulus_level d hd B)
  apply eventually_atTop.mp
  filter_upwards [hh, eventually_ge_atTop 2] with p hp htwo
  intro k hk
  refine ⟨?_, hp k hk⟩
  have hgt : 1 < ((p^2:ℕ):ℝ) := by
    exact_mod_cast (by nlinarith : 1 < p^2)
  have hlt : (((p^2:ℕ):ℝ))^(5/32:ℝ) < (((p^2:ℕ):ℝ))^(1/2:ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hgt (by norm_num)
  have hright : (((p^2:ℕ):ℝ))^(1/2:ℝ) = p := by
    rw [← Real.sqrt_eq_rpow, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg p)]
  rw [hright] at hlt
  have hk' : (k:ℝ) ≤ fixedSieveLevel (p^2) := by exact_mod_cast hk
  exact_mod_cast hk'.trans_lt ((Nat.floor_le (by positivity)).trans_lt hlt)

theorem eventually_reflected_remainder_at_level (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime → ∀ (H b : ℕ) (S : Finset ℕ) (J : ℝ),
      H^3 ≤ p^4 → b.Coprime d →
      (∀ k ∈ S, 0 < k ∧ k ≤ fixedSieveLevel (p^2) ∧ d.Coprime k ∧ Nat.Coprime 2 k) →
      (∑ k ∈ S, |((sievedAPOffsets p H d b k).card : ℝ) - J/d.totient/k.totient|) ≤
        ∑ q ∈ Icc 1 (shortDistributionLevel (p^2) B), (shortAPWorst (p^2) H q J : ℝ) := by
  obtain ⟨p₀, h₀⟩ := fixed_level_at_prime_squares d hd B
  refine ⟨p₀, ?_⟩
  intro p hp hprime H b S J hH hb hS
  apply sum_rho_errors_le hprime hd hb (floor_window_le_center hprime.pos hH)
  intro k hk
  obtain ⟨hpos, hlevel, hc, hk2⟩ := hS k hk
  obtain ⟨hlt, hdk⟩ := h₀ p hp k hlevel
  exact ⟨hpos, hlt, hc, hk2, hdk⟩

end GoldbachCentralSeven

end


-- TH8000UpperRows
section

namespace GoldbachCentralSeven
open Finset

theorem auxiliary_upper_row {p H d b q k : ℕ} (hc : q.Coprime k) :
    (sievedAPOffsets p H d b q).filter (fun h => k ∣ p^2-h) =
      sievedAPOffsets p H d b (q*k) := by
  ext h
  simp only [sievedAPOffsets, mem_filter]
  constructor
  · rintro ⟨⟨hh, hp, hb, hq⟩, hk⟩
    exact ⟨hh, hp, hb, hc.mul_dvd_of_dvd_of_dvd hq hk⟩
  · rintro ⟨hh, hp, hb, hv⟩
    exact ⟨⟨hh,hp,hb,(dvd_mul_right q k).trans hv⟩,(dvd_mul_left k q).trans hv⟩

noncomputable def rhoRemainder (p H d b : ℕ) (J : ℝ) (e : ℕ) : ℝ :=
  ((sievedAPOffsets p H d b e).card : ℝ) - J/d.totient/e.totient

theorem upper_row_remainder_eq {p H d b q k : ℕ} (hc : q.Coprime k) (J : ℝ) :
    ((((sievedAPOffsets p H d b q).filter (fun h => k ∣ p^2-h)).card):ℝ) -
        J/d.totient/q.totient/k.totient = rhoRemainder p H d b J (q*k) := by
  rw [auxiliary_upper_row hc, rhoRemainder, normalized_main_mul hc (J/d.totient)]

theorem outer_prime_coprime {q k z : ℕ} (hq : q.Prime) (hz : z ≤ q) (hk : 0 < k)
    (hsmall : ∀ l ∈ k.primeFactors, l < z) : q.Coprime k := by
  apply hq.coprime_iff_not_dvd.mpr
  exact fun h => (hsmall q (Nat.mem_primeFactors.mpr ⟨hq,h,hk.ne'⟩)).not_ge hz

def combinedUpperModuli (Q : Finset ℕ) (K : ℕ → Finset ℕ) : Finset ℕ :=
  Q.biUnion (fun q => (K q).image (fun k => q*k))

theorem upper_rows_charge_once (Q : Finset ℕ) (K : ℕ → Finset ℕ) (z : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ q)
    (hK : ∀ q ∈ Q, ∀ k ∈ K q, 0 < k ∧ ∀ l ∈ k.primeFactors, l < z)
    (g : ℕ → ℝ) :
    (∑ q ∈ Q, ∑ k ∈ K q, g (q*k)) = ∑ e ∈ combinedUpperModuli Q K, g e := by
  unfold combinedUpperModuli
  have hd : Set.PairwiseDisjoint (Q : Set ℕ) (fun q => (K q).image (fun k => q*k)) := by
    intro q hq q' hq' hne
    exact disjoint_left.mpr (by
      intro e he he'
      obtain ⟨k, hk, hx⟩ := mem_image.mp he
      obtain ⟨k', hk', hx'⟩ := mem_image.mp he'
      have hdiv : q ∣ q'*k' := (hx.trans hx'.symm) ▸ dvd_mul_right q k
      rcases (hQ q hq).1.dvd_mul.mp hdiv with h | h
      · exact hne ((Nat.prime_dvd_prime_iff_eq (hQ q hq).1 (hQ q' hq').1).mp h)
      · have hK' := hK q' hq' k' hk'
        exact (hK'.2 q (Nat.mem_primeFactors.mpr ⟨(hQ q hq).1,h,hK'.1.ne'⟩)).not_ge (hQ q hq).2)
  rw [sum_biUnion hd]
  refine sum_congr rfl fun q hq => ?_
  rw [sum_image]
  exact fun _ _ _ _ hh => Nat.eq_of_mul_eq_mul_left (hQ q hq).1.pos hh

theorem total_upper_remainder {p H d b D z : ℕ} (J : ℝ) (Q : Finset ℕ)
    (K : ℕ → Finset ℕ) (hp : p.Prime) (hd : 0 < d) (hb : b.Coprime d)
    (hH : H ≤ p^2) (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ q)
    (hK : ∀ q ∈ Q, ∀ k ∈ K q, 0 < k ∧ (∀ l ∈ k.primeFactors, l < z) ∧
        q*k < p ∧ d.Coprime (q*k) ∧ Nat.Coprime 2 (q*k) ∧ d*(q*k) ≤ D) :
    (∑ q ∈ Q, ∑ k ∈ K q,
      |((((sievedAPOffsets p H d b q).filter (fun h => k ∣ p^2-h)).card):ℝ) -
        J/d.totient/q.totient/k.totient|) ≤
      ∑ a ∈ Icc 1 D, (shortAPWorst (p^2) H a J : ℝ) := by
  calc
    _ = ∑ q ∈ Q, ∑ k ∈ K q, |rhoRemainder p H d b J (q*k)| := by
      apply sum_congr rfl
      intro q hq
      apply sum_congr rfl
      intro k hk
      obtain ⟨hqpr,hzq⟩ := hQ q hq
      obtain ⟨hkpos, hsmall, _⟩ := hK q hq k hk
      exact congrArg abs (upper_row_remainder_eq (p := p) (H := H) (d := d) (b := b)
        (outer_prime_coprime hqpr hzq hkpos hsmall) J)
    _ = ∑ e ∈ combinedUpperModuli Q K, |rhoRemainder p H d b J e| :=
      upper_rows_charge_once Q K z hQ (fun q hq k hk => ⟨(hK q hq k hk).1,(hK q hq k hk).2.1⟩)
        (fun e => |rhoRemainder p H d b J e|)
    _ ≤ _ := by
      apply sum_rho_errors_le hp hd hb hH (combinedUpperModuli Q K) J
      intro e he
      obtain ⟨q,hq,hh⟩ := mem_biUnion.mp he
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hh
      obtain ⟨hkpos,_,hkp,hc,h2,hD⟩ := hK q hq k hk
      exact ⟨Nat.mul_pos (hQ q hq).1.pos hkpos,hkp,hc,h2,hD⟩

end GoldbachCentralSeven

namespace GoldbachCentralSeven
open Finset

theorem weighted_upper_remainder_at_level (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime →
      ∀ (H b z : ℕ) (J : ℝ) (Q : Finset ℕ) (K : ℕ → Finset ℕ)
        (a : ℕ → ℝ) (coeffU : ℕ → ℕ → ℝ),
      H^3 ≤ p^4 → b.Coprime d → (∀ q ∈ Q, q.Prime ∧ z ≤ q ∧ |a q| ≤ 1) →
      (∀ q ∈ Q, ∀ k ∈ K q, 0 < k ∧ (∀ l ∈ k.primeFactors, l < z) ∧
        q*k ≤ fixedSieveLevel (p^2) ∧ d.Coprime (q*k) ∧ Nat.Coprime 2 (q*k) ∧ |coeffU q k| ≤ 1) →
      (∑ q ∈ Q, ∑ k ∈ K q, |a q * coeffU q k *
        (((((sievedAPOffsets p H d b q).filter (fun h => k ∣ p^2-h)).card):ℝ) -
          J/d.totient/q.totient/k.totient)|) ≤
        ∑ m ∈ Icc 1 (shortDistributionLevel (p^2) B), (shortAPWorst (p^2) H m J : ℝ) := by
  obtain ⟨p₀,hp₀⟩ := fixed_level_at_prime_squares d hd B
  refine ⟨p₀,?_⟩
  intro p hstart hp H b z J Q K a coeffU hH hb hQ hK
  apply le_trans _ (total_upper_remainder J Q K hp hd hb (floor_window_le_center hp.pos hH)
    (fun q hq => ⟨(hQ q hq).1,(hQ q hq).2.1⟩) (by
      intro q hq k hk
      obtain ⟨hk0,hsmall,hcut,hc,h2,_⟩ := hK q hq k hk
      obtain ⟨hbelow,hD⟩ := hp₀ p hstart (q*k) hcut
      exact ⟨hk0,hsmall,hbelow,hc,h2,hD⟩))
  apply sum_le_sum
  intro q hq
  apply sum_le_sum
  intro k hk
  rw [abs_mul,abs_mul]
  have hcoeff := (hK q hq k hk).2.2.2.2.2
  have hprod : |a q| * |coeffU q k| ≤ 1 := mul_le_one₀ (hQ q hq).2.2 (abs_nonneg _) hcoeff
  exact mul_le_of_le_one_left (abs_nonneg _) hprod

end GoldbachCentralSeven

end


-- TH8000UpperGeometry
section

namespace CentralUpperGeometry
open Filter Real

def radius (z q : ℕ) : ℕ := min z (Nat.sqrt (z^4/q))
noncomputable def penaltyEnd (z : ℕ) : ℝ := (z:ℝ)^(320/81:ℝ)
noncomputable def discount (z q : ℕ) : ℝ := 1 - log (q:ℝ)/log (penaltyEnd z)

theorem small_radius {z q : ℕ} (hq : 0<q) (hsmall : q≤z^2) : radius z q = z := by
  unfold radius
  apply min_eq_left
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le hq).mpr
  exact (Nat.mul_le_mul_left (z^2) hsmall).trans_eq (by ring)

theorem level_fits (z q : ℕ) : q*(radius z q)^2 ≤ z^4 := by
  unfold radius
  have hs := Nat.pow_le_pow_left (min_le_right z (Nat.sqrt (z^4/q))) 2
  exact (Nat.mul_le_mul_left q (hs.trans (Nat.sqrt_le' _))).trans (Nat.mul_div_le ..)

theorem radius_uniform (M : ℕ) : ∀ᶠ z : ℕ in atTop, ∀ q : ℕ, 0<q →
    (q:ℝ)≤penaltyEnd z → M ≤ radius z q := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<4/81)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually (eventually_ge_atTop ((M:ℝ)^2)), eventually_ge_atTop M,
    eventually_ge_atTop (1:ℕ)] with z hz hM hz1
  intro q hq hqy
  refine le_min hM (Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hq).mpr ?_))
  have hx : 0 < (z:ℝ) := by exact_mod_cast hz1
  have he : (z:ℝ)^(4/81:ℝ) * penaltyEnd z = (z:ℝ)^4 := by
    unfold penaltyEnd
    rw [← Real.rpow_add hx]; norm_num
  have hle := mul_le_mul (show (M:ℝ)^2 ≤ (z:ℝ)^(4/81:ℝ) from hz) hqy
    (Nat.cast_nonneg q) (Real.rpow_nonneg hx.le _)
  rw [he] at hle
  exact_mod_cast hle

theorem discount_nonneg {z q : ℕ} (hz : 2≤z) (hq : 0<q)
    (hqe : (q:ℝ) ≤ penaltyEnd z) : 0 ≤ discount z q := by
  have hx : (1:ℝ)<z := by exact_mod_cast (show 1<z by omega)
  have hy : 1<penaltyEnd z := Real.one_lt_rpow hx (by norm_num)
  exact sub_nonneg.mpr ((div_le_one (log_pos hy)).mpr
    (log_le_log (by exact_mod_cast hq) hqe))

theorem discount_linear {z q : ℕ} (hz : 2 ≤ z) (hq : 1≤q) :
    discount z q ≤ 1-log (q:ℝ)/(4*log (z:ℝ)) := by
  have hz1 : 1<(z:ℝ) := by exact_mod_cast (show 1<z by omega)
  have hl := log_pos hz1
  have hn := Real.log_natCast_nonneg q
  have hlog : log (penaltyEnd z) = (320/81:ℝ)*log (z:ℝ) :=
    Real.log_rpow (by linarith) _
  unfold discount
  rw [hlog]
  apply sub_le_sub_left
  exact div_le_div_of_nonneg_left hn (by positivity) (by linarith)

theorem upper_band_cost (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ z : ℕ in atTop, ∀ q : ℕ, z^2<q → (q:ℝ)≤penaltyEnd z →
      discount z q * (log (z:ℝ)/log (radius z q:ℝ)) ≤ (1+ε)/2 := by
  obtain ⟨M,hM⟩ := exists_nat_gt (exp (1/ε))
  filter_upwards [radius_uniform (max M 2), eventually_ge_atTop (2:ℕ)] with z hrad hz
  intro q hlarge hqy
  have hq : 0<q := by omega
  let m := radius z q
  have hm2 : 2 ≤ m := (le_max_right _ _).trans (hrad q hq hqy)
  have hmM : M ≤ m := (le_max_left _ _).trans (hrad q hq hqy)
  have hm := log_pos (by exact_mod_cast (show 1 < m by omega) : (1:ℝ)< m)
  have hzlog := log_pos (by exact_mod_cast (show 1<z by omega) : (1:ℝ)<z)
  have hmpos : (0:ℝ)< m := by exact_mod_cast (show 0 < m by omega)
  have hqpos : (0:ℝ)<q := by exact_mod_cast hq
  have hmEq : m = Nat.sqrt (z^4/q) := by
    apply min_eq_right
    by_contra! hgt
    have hs := Nat.le_sqrt'.mp (le_of_lt hgt)
    have hl := (Nat.le_div_iff_mul_le hq).mp hs
    nlinarith [Nat.mul_lt_mul_of_pos_left hlarge (by positivity : 0<z^2)]
  have hdiv : z^4/q < (m+1)^2 := by rw [hmEq]; exact Nat.lt_succ_sqrt' _
  have hraw := (Nat.div_lt_iff_lt_mul hq).mp hdiv
  have hreal : (z:ℝ)^4 < ((m:ℝ)+1)^2 * q := by exact_mod_cast hraw
  have hlog := log_lt_log (by positivity : 0<(z:ℝ)^4) hreal
  rw [log_mul (by positivity) hqpos.ne', Real.log_pow, Real.log_pow] at hlog
  have hminv : 1/ε ≤ log (m:ℝ) := by
    rw [← log_exp (1/ε)]
    exact log_le_log (exp_pos _) (hM.le.trans (by exact_mod_cast hmM))
  have heps : 1 ≤ ε*log (m:ℝ) := by
    have hh := (div_le_iff₀ hε).mp hminv
    linarith
  have hm1 : log ((m:ℝ)+1) ≤ (1+ε)*log (m:ℝ) := by
    have hr := log_le_sub_one_of_pos (by positivity : 0<((m:ℝ)+1)/m)
    rw [log_div (by positivity) hmpos.ne'] at hr
    have hc : ((m:ℝ)+1)/m ≤ 2 := (div_le_iff₀ hmpos).mpr (by exact_mod_cast (show m+1≤2*m by omega))
    linarith
  have hbudget := mul_le_mul_of_nonneg_right (discount_linear hz hq)
    (le_of_lt hzlog)
  have hid : (1-log (q:ℝ)/(4*log (z:ℝ)))*log (z:ℝ) =
      (4*log (z:ℝ)-log (q:ℝ))/4 := by field_simp
  rw [hid] at hbudget
  change discount z q * (log (z:ℝ)/log (m:ℝ)) ≤ _
  rw [← mul_div_assoc, div_le_iff₀ hm]
  norm_num at hlog
  linarith only [hbudget,hlog,hm1]

end CentralUpperGeometry

end


-- TH8000SieveModel
section

namespace GoldbachCentralSeven.Model
open Finset GoldbachRoughFifth MathlibNt.SieveTheory.SwitchingPrinciple

def primes (d z : ℕ) := (range z).filter (fun l => l.Prime ∧ ¬l ∣ 2*d)
def product (d z : ℕ) := ∏ l ∈ primes d z, l

lemma product_sqfree (d z : ℕ) : Squarefree (product d z) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (mem_filter.mp hp).2.1
      (mem_filter.mp hq).2.1).mpr hpq)
  · intro p hp
    exact (mem_filter.mp hp).2.1.squarefree

lemma primeFactors_product (d z : ℕ) : (product d z).primeFactors = primes d z := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp,hd,_⟩
    obtain ⟨p,hm,hq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    simpa [(Nat.prime_dvd_prime_iff_eq hp (mem_filter.mp hm).2.1).mp hq] using hm
  · intro hq
    exact ⟨(mem_filter.mp hq).2.1, dvd_prod_of_mem _ hq,(product_sqfree d z).ne_zero⟩

lemma supported_prime {d z q : ℕ} (hq : q ∈ primes d z) :
    q.Prime ∧ 2 < q ∧ q < z ∧ ¬q ∣ 2*d := by
  obtain ⟨hlo,hp,hnd⟩ := mem_filter.mp hq
  have hne : q ≠ 2 := fun e => hnd (e ▸ dvd_mul_right _ _)
  exact ⟨hp,by have := hp.two_le; omega,mem_range.mp hlo,hnd⟩

lemma coprime_product {d z a : ℕ} (ha : 1<a) (hc : a.Coprime (2*d)) :
    (product d z).Coprime a ↔ z ≤ a.minFac := by
  rw [product,Nat.coprime_prod_left_iff]
  constructor
  · intro h
    by_contra! hsmall
    let q := a.minFac
    have hp : q.Prime := Nat.minFac_prime (by omega)
    have hd : q ∣ a := Nat.minFac_dvd _
    have hnd : ¬q ∣ 2*d := (hp.coprime_iff_not_dvd).mp (hc.coprime_dvd_left hd)
    exact hp.coprime_iff_not_dvd.mp (h q (mem_filter.mpr ⟨mem_range.mpr hsmall,hp,hnd⟩)) hd
  · intro h q hq
    obtain ⟨hp,_,hz,_⟩ := supported_prime hq
    exact hp.coprime_iff_not_dvd.mpr fun hd => hz.not_ge (h.trans (Nat.minFac_le_of_dvd hp.two_le hd))

noncomputable def model (p H d b j z : ℕ) (J : ℝ) : BoundingSieve where
  support := (sievedAPOffsets p H d b j).image (fun h => p^2-h)
  prodPrimes := product d z
  prodPrimes_squarefree := product_sqfree d z
  weights _ := 1
  weights_nonneg _ := zero_le_one
  totalMass := J/d.totient/j.totient
  nu := progressionDensity
  nu_mult := progressionDensity_mult
  nu_pos_of_prime q hp _ := by
    rw [progressionDensity_prime hp]
    have : (1:ℝ)<q := by exact_mod_cast hp.one_lt
    positivity
  nu_lt_one_of_prime q hp hd := by
    have hm := Nat.mem_primeFactors.mpr ⟨hp,hd,(product_sqfree d z).ne_zero⟩
    rw [primeFactors_product] at hm
    have hq : (2:ℝ)<q := by exact_mod_cast (supported_prime hm).2.1
    rw [progressionDensity_prime hp]
    exact (div_lt_one (by linarith)).mpr (by linarith)

private theorem reflection_inj {p H d b j : ℕ} (hH : H≤p^2) :
    Set.InjOn (fun h => p^2-h) (sievedAPOffsets p H d b j) := by
  intro h hs k ht he
  have h1 := (mem_Icc.mp (mem_filter.mp hs).1).2
  have h2 := (mem_Icc.mp (mem_filter.mp ht).1).2
  change p^2-h=p^2-k at he; omega

theorem row_remainder {p H d b j z k : ℕ} (J : ℝ) (hH : H≤p^2) (hc : j.Coprime k) :
    (model p H d b j z J).rem k = rhoRemainder p H d b J (j*k) := by
  unfold BoundingSieve.rem BoundingSieve.multSum
  change (∑ a ∈ (sievedAPOffsets p H d b j).image (fun h => p^2-h), if k ∣ a then (1:ℝ) else 0) -
    ((k.totient:ℝ))⁻¹*(J/d.totient/j.totient) = _
  rw [sum_image (reflection_inj hH), Finset.sum_boole]
  simpa only [div_eq_mul_inv, mul_comm ((k.totient:ℝ))⁻¹] using
    (upper_row_remainder_eq (p:=p) (H:=H) (d:=d) (b:=b) hc J)

noncomputable def rough (p H d b z : ℕ) :=
  (sievedAPOffsets p H d b 1).filter fun h => z ≤ (p^2-h).minFac

theorem sifted_row {p H d b j z : ℕ} (J : ℝ) (hH : H≤p^2) (hb : b≤2*p^2)
    (hadm : (2*p^2-b).Coprime d) (h2 : 2<p^2) (hpos : 1<p^2-H) :
    (model p H d b j z J).siftedSum =
      (((sievedAPOffsets p H d b j).filter fun h => z ≤ (p^2-h).minFac).card:ℝ) := by
  unfold BoundingSieve.siftedSum
  change (∑ a ∈ (sievedAPOffsets p H d b j).image (fun h => p^2-h),
      if (product d z).Coprime a then (1:ℝ) else 0) = _
  rw [sum_image (reflection_inj hH),sum_boole]
  congr 2
  apply filter_congr
  intro h hh
  obtain ⟨hint,hp,hr,_⟩ := mem_filter.mp hh
  have hhi := (mem_Icc.mp hint).2
  have hcop := reflected_coprime_twice_fixed (hhi.trans hH) hb hr hadm hp (by omega)
  exact coprime_product (by omega) hcop

noncomputable def V (d z : ℕ) : ℝ := ∏ q ∈ primes d z, (1-1/((q:ℝ)-1))

theorem product_at_cut (p H d b j z : ℕ) (J : ℝ) :
    suzukiVProduct (model p H d b j z J) (z:ℝ) = V d z := by
  change (∏ q ∈ (product d z).primeFactors.filter (fun q : ℕ => (q:ℝ)<z),
      (1-progressionDensity q)) = _
  rw [primeFactors_product, filter_eq_self.mpr (fun q hq => by exact_mod_cast (supported_prime hq).2.2.1)]
  exact prod_congr rfl (fun q hq => by rw [progressionDensity_prime (supported_prime hq).1])

end GoldbachCentralSeven.Model

end


-- TH8000LocalProducts
section

namespace GoldbachCentralSeven.Model
open Finset MathlibNt.SieveTheory.SwitchingPrinciple

theorem V_pos (d z : ℕ) : 0 < V d z := by
  apply prod_pos
  intro l hl
  have h : (2:ℝ)<l := by exact_mod_cast (supported_prime hl).2.1
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

theorem local_product_control : ∃ K : ℝ, 2 ≤ K ∧
    (∀ p H d b j z : ℕ, ∀ J : ℝ, HasDimensionOneLocalProductBound (model p H d b j z J) K) ∧
    (∀ d w z : ℕ, 2 ≤ w → w ≤ z →
      V d w ≤ V d z * (Real.log z / Real.log w) * (1+K/Real.log w)) := by
  obtain ⟨k,hk,h⟩ := RoughFifthLocalProduct.exists_goldbach_inverse_interval_bound
  let K := max 2 k
  have hbase (P : Finset ℕ) (a b : ℝ) (ha : 2≤a) (hab : a≤b)
      (hP : ∀ l ∈ P, l.Prime ∧ 2<l)
      (hwin : ∀ l ∈ P, a≤(l:ℝ) ∧ (l:ℝ)<b) :
      (∏ l ∈ P, (1-1/((l:ℝ)-1))⁻¹) ≤ Real.log b / Real.log a * (1+K/Real.log a) := by
    apply (h P hP a b ha hab hwin).trans
    have halog := Real.log_pos (by linarith : 1<a)
    have hblog := Real.log_nonneg (by linarith : 1≤b)
    gcongr
    exact le_max_right _ _
  refine ⟨K,le_max_left ..,?_,?_⟩
  · intro p H d b j z J a u ha hau
    let F := (primes d z).filter (fun l : ℕ => a≤(l:ℝ) ∧ (l:ℝ)<u)
    have hp (l) (hl : l ∈ F) : l.Prime ∧ 2<l := by
      have hq := supported_prime (mem_filter.mp hl).1
      exact ⟨hq.1,hq.2.1⟩
    change (∏ l ∈ (product d z).primeFactors.filter (fun l : ℕ => a≤(l:ℝ) ∧ (l:ℝ)<u),
        (1-GoldbachRoughFifth.progressionDensity l)⁻¹) ≤ _
    rw [primeFactors_product]
    change (∏ l ∈ F, _) ≤ _
    calc
      _ = ∏ l ∈ F, (1-1/((l:ℝ)-1))⁻¹ := by
        apply prod_congr rfl
        intro l hl
        rw [GoldbachRoughFifth.progressionDensity_prime (hp l hl).1]
      _ ≤ _ := hbase _ _ _ ha hau hp (fun l hl => (mem_filter.mp hl).2)
  · intro d w z hw hwz
    have hs : primes d w ⊆ primes d z := fun l hl => mem_filter.mpr
      ⟨mem_range.mpr ((mem_range.mp (mem_filter.mp hl).1).trans_le hwz), (mem_filter.mp hl).2⟩
    let F := primes d z \ primes d w
    have hP (l) (hl : l∈F) : l.Prime ∧ 2<l := by
      have hq := supported_prime (mem_sdiff.mp hl).1
      exact ⟨hq.1,hq.2.1⟩
    have hwin (l) (hl : l∈F) : (w:ℝ)≤l ∧ (l:ℝ)<z := by
      obtain ⟨hlz,hlw⟩ := mem_sdiff.mp hl
      have hq := supported_prime hlz
      have hlower : w≤l := le_of_not_gt (fun hlo => hlw
        (mem_filter.mpr ⟨mem_range.mpr hlo,(mem_filter.mp hlz).2⟩))
      exact ⟨by exact_mod_cast hlower,by exact_mod_cast hq.2.2.1⟩
    have hbound := hbase F w z (by exact_mod_cast hw) (by exact_mod_cast hwz) hP hwin
    have hδ : 0 < ∏ l ∈ F, (1-1/((l:ℝ)-1)) := by
      apply prod_pos
      intro l hl
      have h2 : (2:ℝ)<l := by exact_mod_cast (hP l hl).2
      exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
    have hp : (∏ l ∈ F, (1-1/((l:ℝ)-1))) * V d w = V d z :=
      prod_sdiff hs
    rw [prod_inv_distrib] at hbound
    have heq : V d w = V d z * (∏ l ∈ F, (1-1/((l:ℝ)-1)))⁻¹ := by
      rw [← hp]
      field_simp
    calc
      _ = _ := heq
      _ ≤ V d z * (Real.log (z:ℝ) / Real.log (w:ℝ) * (1 + K/Real.log (w:ℝ))) :=
        mul_le_mul_of_nonneg_left hbound (V_pos ..).le
      _ = _ := by ring

lemma volume_floor {K : ℝ} (hK : 2≤K)
    (h : ∀ d w z : ℕ, 2≤w → w≤z → V d w ≤ V d z *
      (Real.log z/Real.log w)*(1+K/Real.log w)) :
    ∃ c : ℝ, 0<c ∧ ∀ d z : ℕ, 2≤z → c/Real.log z ≤ V d z := by
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hf : 0 < 1+K/Real.log 2 := by positivity
  refine ⟨Real.log 2/(1+K/Real.log 2),by positivity,?_⟩
  intro d z hz
  have hlogz := Real.log_pos (by exact_mod_cast (show 1<z by omega) : (1:ℝ)<z)
  have h2 : primes d 2 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨_,hgt,hlt,_⟩ := supported_prime hq
    omega
  have hh := h d 2 z (by omega) hz
  rw [show V d 2 = 1 by simp only [V,h2,prod_empty]] at hh
  push_cast at hh
  rw [div_div, div_le_iff₀ (mul_pos hf hlogz)]
  nlinarith only [mul_le_mul_of_nonneg_right hh hlog.le,
    show V d z * (Real.log z / Real.log 2) * (1+K/Real.log 2) * Real.log 2 =
      V d z*((1+K/Real.log 2)*Real.log z) by field_simp]

end GoldbachCentralSeven.Model

end


-- TH8000FiniteRosser
section

namespace GoldbachCentralSeven.Model
open Finset Filter Real MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple

def moduli (d z D : ℕ) := (product d z).divisors.filter (fun k => k<D)

lemma modulus_data {d z D k : ℕ} (hk : k∈ moduli d z D) :
    0<k ∧ k<D ∧ (2*d).Coprime k ∧ ∀ l ∈ k.primeFactors, l<z := by
  obtain ⟨hm,hlt⟩ := mem_filter.mp hk
  have hdiv := Nat.dvd_of_mem_divisors hm
  have hcop : (product d z).Coprime (2*d) := by
    rw [product,Nat.coprime_prod_left_iff]
    intro l hl
    obtain ⟨hp,_,_,hnd⟩ := supported_prime hl
    exact hp.coprime_iff_not_dvd.mpr hnd
  refine ⟨Nat.pos_of_mem_divisors hm,hlt,(hcop.coprime_dvd_left hdiv).symm,?_⟩
  intro l hl
  obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hl
  have hm' := Nat.mem_primeFactors.mpr ⟨hp,hd.trans hdiv,(product_sqfree d z).ne_zero⟩
  rw [primeFactors_product] at hm'
  exact (supported_prime hm').2.2.1

private lemma ceil_level_root (z v : ℕ) (hv : 0<v) :
    ⌈((z^v : ℕ):ℝ) ^ (1/(v:ℝ))⌉₊ = z := by
  have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg z), mul_one_div_cancel hvR,
    Real.rpow_one, Nat.ceil_natCast]

private lemma supported_lt {p H d b j z : ℕ} {J : ℝ}
    (l) (hl : l ∈ (model p H d b j z J).prodPrimes.primeFactors) : l<z := by
  change l ∈ (product d z).primeFactors at hl
  rw [primeFactors_product] at hl
  exact (supported_prime hl).2.2.1

private lemma errSum_le {p H d b j z D : ℕ} (J : ℝ) (hH : H≤p^2)
    (hc : ∀ k∈moduli d z D, j.Coprime k) (w : ℕ → ℝ)
    (hw : ∀ k ∈ moduli d z D, |w k| ≤ 1) :
    (∑ k ∈ moduli d z D, |w k| * |(model p H d b j z J).rem k|) ≤
      ∑ k ∈ moduli d z D, |rhoRemainder p H d b J (j*k)| := by
  apply sum_le_sum
  intro k hk
  rw [row_remainder J hH (hc k hk)]
  exact mul_le_of_le_one_left (abs_nonneg _) (hw k hk)

theorem lower_bound {K ε : ℝ} (hK : 2≤K) (hε : 0<ε) :
    ∃ Z : ℕ, ∀ z≥Z, ∀ p H d b : ℕ, ∀ J : ℝ, 0≤J → H≤p^2 → b≤2*p^2 →
      (2*p^2-b).Coprime d → 2<p^2 → 1<p^2-H →
      HasDimensionOneLocalProductBound (model p H d b 1 z J) K →
      (J/d.totient) * V d z * (Real.exp Real.eulerMascheroniConstant/2 * log 3-ε) -
        (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤
      ((rough p H d b z).card:ℝ) := by
  obtain ⟨D₀,hD₀⟩ := TH8000Amplitude.lower_at_four hK hε
  refine ⟨max 2 D₀,?_⟩
  intro z hz p H d b J hJ hH hb hadm h2 hpos hlocal
  have hz2 : 2≤z := by omega
  have hle : z≤z^4 := by simpa using Nat.pow_le_pow_right (by omega : 0<z) (show 1≤4 by decide)
  let S := model p H d b 1 z J
  let w := lowerRosserWeight (product d z) (z^4)
  have hc := ceil_level_root z 4 (by decide)
  norm_num only [Nat.cast_ofNat] at hc
  have hl := hD₀ (z^4) (by omega) S hlocal (by rw [hc]; exact hz2)
  dsimp only at hl
  rw [hc,product_at_cut] at hl
  have hmain := mainSum_lowerRosserWeight_eq_suzukiLowerDensity_of_all_lt S (z^4)
    (fun l hl => supported_lt l hl)
  rw [← hmain] at hl
  have hcert := lowerRosserWeight_certificate S.prodPrimes_squarefree S.prodPrimes_ne_zero
    (fun l hl => (supported_lt l hl).trans_le hle)
  have hfinite := mainSum_sub_lowerErrSum_le_siftedSum (S:=S) (z^4) w hcert
    (lowerRosserWeight_hasLowerLevelSupport _ _)
  have he := errSum_le (d:=d) (b:=b) (j:=1) (z:=z) (D:=z^4) J hH
    (fun _ _ => Nat.coprime_one_left _) w (fun _ _ => abs_lowerRosserWeight_le_one ..)
  simp only [one_mul] at he
  have hm : S.totalMass = J/d.totient := by simp [S,model]
  rw [hm] at hfinite
  rw [sifted_row J hH hb hadm h2 hpos] at hfinite
  apply le_trans _ hfinite
  apply sub_le_sub _ he
  change _ ≤ J/d.totient * S.mainSum (lowerRosserWeight S.prodPrimes (z^4))
  simpa only [mul_left_comm, mul_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hl (by positivity : 0≤J/d.totient)

theorem upper_bound {K ε : ℝ} (hK : 2≤K) (hε : 0<ε) :
    ∃ Z : ℕ, ∀ w≥Z, ∀ p H d b q : ℕ, ∀ J : ℝ,
      0≤J → H≤p^2 → b≤2*p^2 → (2*p^2-b).Coprime d → 2<p^2 → 1<p^2-H →
      q.Prime → w≤q → HasDimensionOneLocalProductBound (model p H d b q w J) K →
      (((sievedAPOffsets p H d b q).filter (fun h => w≤(p^2-h).minFac)).card:ℝ) ≤
        (J/d.totient/q.totient) * V d w * (Real.exp Real.eulerMascheroniConstant + ε) +
          ∑ k ∈ moduli d w (w^2), |rhoRemainder p H d b J (q*k)| := by
  obtain ⟨D₀,hD₀⟩ := CentralUpperSieve.upper_at_two hK hε
  refine ⟨max 2 D₀,?_⟩
  intro w hw p H d b q J hJ hH hb hadm h2 hpos hq hwq hlocal
  have hw2 : 2≤w := by omega
  have hwD : w≤w^2 := by simpa using Nat.pow_le_pow_right (by omega : 0<w) (show 1≤2 by decide)
  let S := model p H d b q w J
  have hc := ceil_level_root w 2 (by decide)
  norm_num only [Nat.cast_ofNat] at hc
  have hu := hD₀ (w^2) (by omega) S hlocal
  dsimp only at hu
  rw [hc] at hu
  have hmain := hu hw2 (fun l hl => supported_lt l hl)
  rw [product_at_cut] at hmain
  have hcert := upperRosserWeight_certificate S.prodPrimes_squarefree S.prodPrimes_ne_zero
    (by omega : 1<w^2) (fun l hl => (supported_lt l hl).trans_le hwD)
  have hv := siftedSum_le_mainSum_add_upperErrSum_upperRosser (S:=S) (w^2) hcert
  have he := errSum_le (d:=d) (b:=b) (j:=q) (z:=w) (D:=w^2) J hH
    (fun k hk => outer_prime_coprime hq hwq (modulus_data hk).1 (modulus_data hk).2.2.2)
    (upperRosserWeight S.prodPrimes (w^2)) (fun _ _ => abs_upperRosserWeight_le_one ..)
  rw [sifted_row J hH hb hadm h2 hpos] at hv
  apply hv.trans
  apply add_le_add _ he
  change J/d.totient/q.totient * _ ≤ _
  simpa only [mul_left_comm, mul_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hmain (by positivity : 0≤J/d.totient/q.totient)

end GoldbachCentralSeven.Model

end


-- TH8000SieveScale
section

namespace CentralUpperGeometry
open Filter Real GoldbachSevenWeight

lemma level_alignment {p : ℕ} (hp : 0 < p) :
    ((p^2:ℕ):ℝ)^(39/1000:ℝ) ≤ (sieveCut p:ℝ) ∧
      upperCut (p^2) ≤ penaltyEnd (sieveCut p) := by
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  have hz := Nat.le_ceil ((p:ℝ)^(39/500:ℝ))
  have hsmall : ((p^2:ℕ):ℝ)^(39/1000:ℝ) ≤ (sieveCut p:ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hpR.le]
    norm_num
    exact hz
  refine ⟨hsmall,?_⟩
  have hh := Real.rpow_le_rpow
    (by positivity : 0 ≤ ((p^2:ℕ):ℝ)^(39/1000:ℝ)) hsmall
    (by norm_num : (0:ℝ)≤320/81)
  rw [← Real.rpow_mul (Nat.cast_nonneg (p^2))] at hh
  norm_num at hh
  simpa only [upperCut, penaltyEnd, Nat.cast_pow] using hh

theorem aligned_level_eventually (d : ℕ) : ∀ᶠ p : ℕ in atTop,
    d*(sieveCut p)^4 ≤ ⌊((p^2:ℕ):ℝ)^(5/32:ℝ)⌋₊ ∧ (sieveCut p)^4 < p := by
  have hgap := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2000)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hroom := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<86/125)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hgap.eventually (eventually_ge_atTop (16*(d:ℝ))),
    hroom.eventually (eventually_gt_atTop (16:ℝ)),eventually_ge_atTop (2:ℕ)]
    with p hgap' hroom' hp
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast (show 1≤p by omega)
  have hp0 : (0:ℝ)<p := zero_lt_one.trans_le hpR
  have hang : (sieveCut p : ℝ) ≤ 2*(p:ℝ)^(39/500:ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hp0.le (39/500:ℝ))
    have h1 := Real.one_le_rpow hpR (by norm_num : (0:ℝ)≤39/500)
    change (⌈(p:ℝ)^(39/500:ℝ)⌉₊ : ℝ) ≤ _
    linarith
  have h4 := pow_le_pow_left₀ (Nat.cast_nonneg (sieveCut p)) hang 4
  rw [mul_pow, ← Real.rpow_mul_natCast hp0.le] at h4
  norm_num at h4
  constructor
  · apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
    push_cast
    rw [← Real.rpow_natCast_mul hp0.le]
    norm_num
    calc
      _ ≤ (16*(d:ℝ))*(p:ℝ)^(39/125:ℝ) := by nlinarith only [mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg d)]
      _ ≤ (p:ℝ)^(1/2000:ℝ)*(p:ℝ)^(39/125:ℝ) := mul_le_mul_of_nonneg_right hgap' (by positivity)
      _ = _ := by rw [← Real.rpow_add hp0]; norm_num
  · have hlt : ((sieveCut p:ℝ))^4 < p := calc
      _ ≤ 16*(p:ℝ)^(39/125:ℝ) := h4
      _ < (p:ℝ)^(86/125:ℝ)*(p:ℝ)^(39/125:ℝ) :=
        mul_lt_mul_of_pos_right hroom' (Real.rpow_pos_of_pos hp0 _)
      _ = _ := by rw [← Real.rpow_add hp0]; norm_num
    exact_mod_cast hlt

theorem tendsto_cut : Tendsto sieveCut atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<39/500)).comp
    tendsto_natCast_atTop_atTop)

end CentralUpperGeometry

end


-- TH8000Unweight
section

namespace GoldbachCentralSeven
open Finset

def classWindow (X H q a : ℕ) : Finset ℕ :=
  (Ioc X (X+H)).filter (fun t => t % q = a)

noncomputable def psiWindow (X H q a : ℕ) : ℝ :=
  ∑ t ∈ classWindow X H q a, ArithmeticFunction.vonMangoldt t

noncomputable def thetaWindow (X H q a : ℕ) : ℝ :=
  ∑ t ∈ shortAPPrimes X H q a, Real.log (t:ℝ)

theorem powers_in_class {X H q a : ℕ} (hH : H ≤ X) :
    0 ≤ psiWindow X H q a - thetaWindow X H q a ∧
      psiWindow X H q a - thetaWindow X H q a ≤
        Chebyshev.psi (2*X) - Chebyshev.theta (2*X) := by
  have hset : shortAPPrimes X H q a = (classWindow X H q a).filter Nat.Prime := by
    ext t
    simp only [shortAPPrimes, classWindow, mem_filter]
    tauto
  have hdiff : psiWindow X H q a - thetaWindow X H q a =
      ∑ t ∈ (classWindow X H q a).filter (fun t => ¬t.Prime), ArithmeticFunction.vonMangoldt t := by
    unfold psiWindow thetaWindow
    rw [hset, sum_filter, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro t _
    by_cases ht : t.Prime <;> simp [ht, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [hdiff]
  constructor
  · exact sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  · change _ ≤ Chebyshev.psi ((2:ℝ)*X) - Chebyshev.theta ((2:ℝ)*X)
    rw [show (2:ℝ)*X = ((2*X:ℕ):ℝ) by norm_cast, Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro t ht
      obtain ⟨ht,hnot⟩ := mem_filter.mp ht
      obtain ⟨hint,_⟩ := mem_filter.mp ht
      have h := mem_Ioc.mp hint
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hnot⟩
    · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem theta_count_gap {X H q a : ℕ} (hX : 2 ≤ X) :
    0 ≤ thetaWindow X H q a - (shortAPPrimes X H q a).card * Real.log X ∧
      thetaWindow X H q a - (shortAPPrimes X H q a).card * Real.log X ≤ (H:ℝ)^2/X := by
  let S := shortAPPrimes X H q a
  have hXr : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hgap (t) (ht : t ∈ S) : 0 ≤ Real.log (t:ℝ)-Real.log X ∧
      Real.log (t:ℝ)-Real.log X ≤ (H:ℝ)/X := by
    obtain ⟨hx,hhi⟩ := mem_Ioc.mp (mem_filter.mp ht).1
    have htr : (X:ℝ) < t := by exact_mod_cast hx
    have htr' : (t:ℝ) ≤ X+H := by exact_mod_cast hhi
    have htp := hXr.trans htr
    refine ⟨sub_nonneg.mpr (Real.log_le_log hXr htr.le),?_⟩
    have hl := Real.log_le_sub_one_of_pos (div_pos htp hXr)
    rw [Real.log_div htp.ne' hXr.ne'] at hl
    apply hl.trans
    rw [sub_le_iff_le_add, div_le_iff₀ hXr]
    field_simp
    linarith
  have hcount : S.card ≤ H := by
    have hh := card_le_card (filter_subset (fun t : ℕ => t.Prime ∧ t % q = a) (Ioc X (X+H)))
    simpa [S,shortAPPrimes] using hh
  have hid : thetaWindow X H q a - S.card * Real.log X =
      ∑ t ∈ S, (Real.log (t:ℝ)-Real.log X) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; rfl
  change 0 ≤ thetaWindow X H q a - S.card * Real.log X ∧ _
  rw [hid]
  refine ⟨sum_nonneg (fun t ht => (hgap t ht).1), ?_⟩
  calc
    _ ≤ ∑ _t ∈ S, (H:ℝ)/X := sum_le_sum fun t ht => (hgap t ht).2
    _ = (S.card:ℝ)*((H:ℝ)/X) := by simp
    _ ≤ (H:ℝ)*((H:ℝ)/X) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
    _ = _ := by ring

theorem short_count_error {X H q a : ℕ} (hX : 2 ≤ X) (hH : H ≤ X) (M : ℝ) :
    |((shortAPPrimes X H q a).card:ℝ) - (M/Real.log X)/q.totient| ≤
      (|psiWindow X H q a - M/q.totient| +
       (Chebyshev.psi (2*X) - Chebyshev.theta (2*X)) + (H:ℝ)^2/X) / Real.log X := by
  have hlog := Real.log_pos (by exact_mod_cast (show 1<X by omega) : (1:ℝ)<X)
  obtain ⟨hp0,hp⟩ := powers_in_class (q:=q) (a:=a) hH
  obtain ⟨ht0,ht⟩ := theta_count_gap (H:=H) (q:=q) (a:=a) hX
  rw [le_div_iff₀ hlog, ← abs_of_pos hlog, ← abs_mul, abs_of_pos hlog, sub_mul]
  rw [show (M/Real.log X)/q.totient * Real.log X = M/q.totient by
    rw [div_right_comm, div_mul_cancel₀ _ hlog.ne']]
  have h := abs_le.mp (le_refl |psiWindow X H q a - M/q.totient|)
  apply abs_le.mpr
  constructor <;> linarith

end GoldbachCentralSeven

end


-- TH8000SiftRemainders
section

namespace GoldbachCentralSeven
open Finset Filter
noncomputable section

def fullPsiMass (X H : ℕ) : ℝ := ∑ t ∈ Ioc X (X+H), ArithmeticFunction.vonMangoldt t
def psiWorst (X H q : ℕ) (M : ℝ) : NNReal :=
  (range q).sup fun a => if a.Coprime q then
    (⟨|psiWindow X H q a - M/q.totient|,abs_nonneg _⟩ : NNReal) else 0

theorem psi_error_le_worst {X H q a : ℕ} (M : ℝ) (ha : a < q) (hc : a.Coprime q) :
    |psiWindow X H q a - M/q.totient| ≤ (psiWorst X H q M:ℝ) := by
  let v := fun b : ℕ => if b.Coprime q then
    (⟨|psiWindow X H q b - M/q.totient|,abs_nonneg _⟩ : NNReal) else 0
  have hv : (v a : ℝ) = |psiWindow X H q a - M/q.totient| := by unfold v;rw [ite_eq_left hc]
  rw [←hv]
  exact NNReal.coe_le_coe.mpr (le_sup (f := v) (mem_range.mpr ha))

theorem class_unweight_total {X H D : ℕ} (M : ℝ) (hX : 2 ≤ X) (hH : H ≤ X) :
    (∑ q ∈ Icc 1 D, (shortAPWorst X H q (M/Real.log X):ℝ)) ≤
    ((∑ q ∈ Icc 1 D, (psiWorst X H q M:ℝ)) +
       D*(Chebyshev.psi (2*X)-Chebyshev.theta (2*X)+(H:ℝ)^2/X))/Real.log X := by
  let e := Chebyshev.psi (2*X)-Chebyshev.theta (2*X)+(H:ℝ)^2/X
  have he : 0 ≤ e := add_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (by positivity)
  have hL := Real.log_pos (show (1:ℝ)<X by exact_mod_cast (by omega : 1<X))
  have hrow (q : ℕ) : (shortAPWorst X H q (M/Real.log X):ℝ) ≤ ((psiWorst X H q M:ℝ)+e)/Real.log X := by
    let A : NNReal := ⟨((psiWorst X H q M:ℝ)+e)/Real.log X,by positivity⟩
    change (shortAPWorst X H q (M/Real.log X):ℝ) ≤ (A:ℝ)
    apply NNReal.coe_le_coe.mpr; unfold shortAPWorst; apply Finset.sup_le
    intro a ha
    change (if a.Coprime q then
      (⟨|((shortAPPrimes X H q a).card:ℝ)-(M/Real.log X)/q.totient|, abs_nonneg _⟩:NNReal) else 0) ≤ A
    by_cases h : a.Coprime q
    · rw [ite_eq_left h]; apply NNReal.coe_le_coe.mp
      change _ ≤ ((psiWorst X H q M:ℝ)+e)/Real.log X
      apply (short_count_error (q:=q) (a:=a) hX hH M).trans
      apply div_le_div_of_nonneg_right _ hL.le
      have hp := psi_error_le_worst (X:=X) (H:=H) M (mem_range.mp ha) h
      dsimp [e];linarith only [hp]
    · rw [ite_eq_right h];exact bot_le
  calc
    _ ≤ ∑ q ∈ Icc 1 D, ((psiWorst X H q M:ℝ)+e)/Real.log X := sum_le_sum fun q _ => hrow q
    _ = _ := by rw [←sum_div,sum_add_distrib]; simp [Nat.card_Icc,e,mul_add]

theorem floor_window_real_bounds {p H : ℕ} (hp : 2 ≤ p) (hH : H^3 ≤ p^4) (hh : p^4 < (H+1)^3) :
    let X : ℝ := (p^2:ℕ)
    (H:ℝ) ≤ X^(2/3:ℝ) ∧ X^(2/3:ℝ) ≤ 2*H := by
  dsimp only
  have hpow : ((((p^2:ℕ):ℝ))^(2/3:ℝ))^3 = (p:ℝ)^4 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0 ≤ ((p^2:ℕ):ℝ)),
      Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    norm_num
  have hlo : (H:ℝ)^3 ≤ ((((p^2:ℕ):ℝ))^(2/3:ℝ))^3 := by rw [hpow]; exact_mod_cast hH
  have hhi : ((((p^2:ℕ):ℝ))^(2/3:ℝ))^3 < ((H:ℝ)+1)^3 := by rw [hpow]; exact_mod_cast hh
  have hl : (H:ℝ) ≤ (((p^2:ℕ):ℝ))^(2/3:ℝ) :=
    le_of_not_gt (fun h => (pow_lt_pow_left₀ h (by positivity) (by decide : 3≠0)).not_ge hlo)
  have hu : (((p^2:ℕ):ℝ))^(2/3:ℝ) < (H:ℝ)+1 :=
    lt_of_not_ge (fun h => (pow_le_pow_left₀ (by positivity) h 3).not_gt hhi)
  have hn : 1 ≤ H := by
    by_contra! h
    have : H=0 := by omega
    subst H; norm_num at hh; nlinarith [Nat.pow_le_pow_left hp 4]
  exact ⟨hl,by linarith [show (1:ℝ)≤H by exact_mod_cast hn]⟩

theorem unweight_loss_at_level (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ D H : ℕ, (D:ℝ) ≤ (X:ℝ)^(5/32:ℝ) →
      (H:ℝ) ≤ (X:ℝ)^(2/3:ℝ) → (X:ℝ)^(2/3:ℝ) ≤ 2*H →
      D*(Chebyshev.psi (2*X)-Chebyshev.theta (2*X)+(H:ℝ)^2/X) ≤ H/(Real.log X)^A := by
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop ((A+1:ℕ):ℝ) (by norm_num : 0 < (1/96:ℝ))).bound
      (by norm_num : (0:ℝ) < 1/18))
  filter_upwards [h,eventually_ge_atTop 4] with X hsmall hX
  intro D H hD hH hH'
  have hx4 : (4:ℝ) ≤ X := by exact_mod_cast hX
  have hx1 : (1:ℝ) ≤ X := by linarith
  have hx : 0 < (X:ℝ) := by linarith
  let ℓ := Real.log X
  have hL : 1 ≤ ℓ := (Real.le_log_iff_exp_le hx).mpr (by linarith [Real.exp_one_lt_three])
  have hLpos : 0 < ℓ := by linarith
  have hhalf := Real.one_le_rpow hx1 (by norm_num : 0 ≤ (1/2:ℝ))
  have hlog2 : Real.log (2*(X:ℝ)) ≤ 2*ℓ := by
    rw [Real.log_mul (by norm_num) hx.ne']
    have h' := Real.log_le_log (by norm_num : (0:ℝ)<2) (show 2 ≤ (X:ℝ) by linarith)
    dsimp [ℓ];linarith
  have hroot : Real.sqrt (2*(X:ℝ)) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
    rw [Real.sqrt_mul (by norm_num),←Real.sqrt_eq_rpow]
    gcongr; norm_num
  have hpp := Chebyshev.psi_sub_theta_le (show 1 ≤ 2*(X:ℝ) by linarith)
  have hpow : (H:ℝ)^2/(X:ℝ) ≤ (X:ℝ)^(1/3:ℝ) := by
    apply (div_le_iff₀ hx).mpr
    calc
      _ ≤ ((X:ℝ)^(2/3:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hH 2
      _ = _ := by
        rw [←Real.rpow_two,←Real.rpow_mul hx.le,show (2/3:ℝ)*2=1/3+1 by norm_num,
          Real.rpow_add hx,Real.rpow_one]
  have hpow' := hpow.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1/3:ℝ) ≤ 1/2))
  have hmass : Chebyshev.psi (2*(X:ℝ))-Chebyshev.theta (2*(X:ℝ))+(H:ℝ)^2/X ≤
      9*(X:ℝ)^(1/2:ℝ)*ℓ := by
    have hp' := mul_le_mul (mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ)≤2)) hlog2
      (Real.log_nonneg (by linarith)) (by positivity)
    nlinarith only [hpp,hp',hpow',mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hx.le (1/2:ℝ))]
  change ‖Real.log (X:ℝ)^((A+1:ℕ):ℝ)‖ ≤ 1/18*‖(X:ℝ)^(1/96:ℝ)‖ at hsmall
  rw [Real.rpow_natCast,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hLpos.le _),
    abs_of_pos (Real.rpow_pos_of_pos hx _)] at hsmall
  apply (le_div_iff₀ (pow_pos hLpos A)).mpr
  have hh : (D:ℝ)*(Chebyshev.psi (2*(X:ℝ))-Chebyshev.theta (2*(X:ℝ))+(H:ℝ)^2/X) ≤
      9*(X:ℝ)^(21/32:ℝ)*ℓ := by
    apply (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)).trans
    have he := mul_le_mul_of_nonneg_right hD (by positivity : 0 ≤ 9*(X:ℝ)^(1/2:ℝ)*ℓ)
    rw [show (21/32:ℝ) = 5/32+1/2 by norm_num,Real.rpow_add hx]
    linarith only [he]
  have hcut : 18*ℓ^(A+1) ≤ (X:ℝ)^(1/96:ℝ) := by dsimp [ℓ];linarith only [hsmall]
  have hm := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hx.le (21/32:ℝ))
  rw [← Real.rpow_add hx,show (21/32:ℝ)+1/96=2/3 by norm_num,pow_succ] at hm
  nlinarith only [mul_le_mul_of_nonneg_right hh (pow_nonneg hLpos.le A),hm,hH']

theorem sieve_remainders_from_psi (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ (D H : ℕ) (M : ℝ), (D:ℝ) ≤ (X:ℝ)^(5/32:ℝ) →
      H ≤ X → (H:ℝ) ≤ (X:ℝ)^(2/3:ℝ) → (X:ℝ)^(2/3:ℝ) ≤ 2*H →
      (∑ q ∈ Icc 1 D, (psiWorst X H q M:ℝ)) ≤ H/(Real.log X)^A →
      (∑ q ∈ Icc 1 D, (shortAPWorst X H q (M/Real.log X):ℝ)) ≤ H/(Real.log X)^A := by
  filter_upwards [unweight_loss_at_level A,eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2]
    with X hcost hX hlog
  intro D H M hD hh hlow hhigh hpsi
  have hl : 2 ≤ Real.log (X:ℝ) := hlog
  have hL : 0 < Real.log (X:ℝ) := by linarith
  have hs := hcost D H hD hlow hhigh
  apply (class_unweight_total (D:=D) M hX hh).trans
  apply (div_le_iff₀ hL).mpr
  have hz : 0 ≤ (H:ℝ)/(Real.log X)^A := by positivity
  linarith only [hpsi,hs,mul_le_mul_of_nonneg_left hl hz]

theorem prime_square_remainders_from_psi (A : ℕ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ H D : ℕ, H^3 ≤ p^4 → p^4 < (H+1)^3 →
      (D:ℝ) ≤ ((p^2:ℕ):ℝ)^(5/32:ℝ) →
      (∑ q ∈ Icc 1 D, (psiWorst (p^2) H q (fullPsiMass (p^2) H):ℝ)) ≤
        H/(Real.log ((p^2:ℕ):ℝ))^A →
      (∑ q ∈ Icc 1 D, (shortAPWorst (p^2) H q
        (fullPsiMass (p^2) H/Real.log ((p^2:ℕ):ℝ)):ℝ)) ≤ H/(Real.log ((p^2:ℕ):ℝ))^A := by
  have hu := (tendsto_pow_atTop (α:=ℕ) (by decide : 2 ≠ 0)).eventually (sieve_remainders_from_psi A)
  apply eventually_atTop.mp
  filter_upwards [hu,eventually_ge_atTop 2] with p hp hp2
  intro H D hfloor hlo hD hM
  obtain ⟨hH,hscale⟩ := floor_window_real_bounds hp2 hfloor hlo
  exact hp D H _ hD (floor_window_le_center (by omega) hfloor) hH hscale hM

end
end GoldbachCentralSeven

end


-- TH8000RosserRemainders
section

namespace GoldbachCentralSeven.Model
open Finset Filter CentralUpperGeometry GoldbachSevenWeight

theorem upper_bad_prime_empty {p H d b q : ℕ} (hH : H ≤ p^2) (h2 : 2 < p^2)
    (hb : b ≤ 2*p^2) (hadm : (2*p^2-b).Coprime d) (hq : q.Prime) (hqbad : q ∣ 2*d) :
    sievedAPOffsets p H d b q = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨hslot,hpr,hmod,hqdiv⟩ := mem_filter.mp hh
  have hc := reflected_coprime_twice_fixed ((mem_Icc.mp hslot).2.trans hH) hb hmod hadm hpr (by omega)
  have hg := Nat.dvd_gcd hqdiv hqbad
  rw [(show Nat.gcd (p^2-h) (2*d)=1 from hc)] at hg
  exact hq.not_dvd_one hg

theorem lower_remainders_to_ap {p H d b z : ℕ} (J : ℝ) (hp : p.Prime) (hd : 0 < d)
    (hb : b.Coprime d) (hH : H ≤ p^2) (hz : z^4 < p) :
    (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤
      ∑ m ∈ Icc 1 (d*z^4), (shortAPWorst (p^2) H m J:ℝ) := by
  apply sum_rho_errors_le hp hd hb hH (moduli d z (z^4)) J
  intro k hk
  obtain ⟨hpos,hkz,hc,_⟩ := modulus_data hk
  obtain ⟨h2,hd'⟩ := Nat.coprime_mul_iff_left.mp hc
  exact ⟨hpos,hkz.trans hz,hd',h2,Nat.mul_le_mul_left d hkz.le⟩

theorem upper_remainders_to_ap {p H d b z : ℕ} (J : ℝ) (Q : Finset ℕ) (hp : p.Prime)
    (hd : 0 < d) (hb : b.Coprime d) (hH : H ≤ p^2) (hz : z^4 < p)
    (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ q ∧ ¬q ∣ 2*d) :
    (∑ q ∈ Q, ∑ k ∈ moduli d (radius z q) ((radius z q)^2), |rhoRemainder p H d b J (q*k)|) ≤
      ∑ m ∈ Icc 1 (d*z^4), (shortAPWorst (p^2) H m J:ℝ) := by
  let K := fun q => moduli d (radius z q) ((radius z q)^2)
  have hqr (q : ℕ) : radius z q ≤ z := min_le_left _ _
  have ht := upper_rows_charge_once Q K z (fun q hq => ⟨(hQ q hq).1,(hQ q hq).2.1⟩)
    (fun q _ k hk => ⟨(modulus_data hk).1, fun l hl => ((modulus_data hk).2.2.2 l hl).trans_le (hqr q)⟩)
    (fun e => |rhoRemainder p H d b J e|)
  rw [ht]
  apply sum_rho_errors_le hp hd hb hH (combinedUpperModuli Q K) J
  intro e he
  obtain ⟨q,hq,he⟩ := mem_biUnion.mp he
  obtain ⟨k,hk,rfl⟩ := mem_image.mp he
  obtain ⟨hpr,hqz,hbad⟩ := hQ q hq
  obtain ⟨hkp,hkle,hcop,_⟩ := modulus_data hk
  have hle : q*k ≤ z^4 := (Nat.mul_le_mul_left q hkle.le).trans (level_fits z q)
  have hc : (2*d).Coprime (q*k) := Nat.coprime_mul_iff_right.mpr
    ⟨(hpr.coprime_iff_not_dvd.mpr hbad).symm,hcop⟩
  obtain ⟨h2,hdf⟩ := Nat.coprime_mul_iff_left.mp hc
  exact ⟨Nat.mul_pos hpr.pos hkp,hle.trans_lt hz,hdf,h2,Nat.mul_le_mul_left d hle⟩

theorem rosser_remainder_pair (d A : ℕ) (hd : 0 < d) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime → ∀ (H b : ℕ) (Q : Finset ℕ),
      H^3 ≤ p^4 → p^4 < (H+1)^3 → b.Coprime d →
      let z := sieveCut p
      let X := p^2
      let M := fullPsiMass X H
      let J := M/Real.log X
      (∀ q ∈ Q, q.Prime ∧ z ≤ q ∧ ¬q ∣ 2*d) →
      (∑ q ∈ Icc 1 (d*z^4), (psiWorst X H q M:ℝ)) ≤ H/(Real.log X)^A →
      (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤ H/(Real.log X)^A ∧
      (∑ q ∈ Q, ∑ k ∈ moduli d (radius z q) ((radius z q)^2),
        |rhoRemainder p H d b J (q*k)|) ≤ H/(Real.log X)^A := by
  obtain ⟨K,hK⟩ := prime_square_remainders_from_psi A
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop K,aligned_level_eventually d] with p hp halign
  intro hpr H b Q hH hh hb
  dsimp only
  intro hQ hpsi
  have hrest := hK p hp H (d*(sieveCut p)^4) hH hh
    ((Nat.le_floor_iff (by positivity : 0 ≤ ((p^2:ℕ):ℝ)^(5/32:ℝ))).mp halign.1) hpsi
  have hle := floor_window_le_center hpr.pos hH
  exact ⟨(lower_remainders_to_ap _ hpr hd hb hle halign.2).trans hrest,
    (upper_remainders_to_ap _ Q hpr hd hb hle halign.2 hQ).trans hrest⟩

end GoldbachCentralSeven.Model

end


-- TH8000WeightedCombine
section

namespace GoldbachCentralSeven.Model
open Finset Filter Real GoldbachSevenWeight CentralUpperGeometry
noncomputable section

theorem offsets_eq_model_rough {p H d b : ℕ} (hb : b < d) :
    roughOffsets p H d b = rough p H d b (sieveCut p) := by
  apply Finset.ext; intro h
  simp only [roughOffsets,rough,sievedAPOffsets,mem_filter,one_dvd,and_true,Nat.ModEq,
    Nat.mod_eq_of_lt hb]
  tauto

private theorem row_le_relaxed {p H d b q : ℕ} (hb : b < d) :
    rowCount (roughOffsets p H d b) (p^2) q ≤
      (((sievedAPOffsets p H d b q).filter (fun h => radius (sieveCut p) q ≤ (p^2-h).minFac)).card) := by
  apply card_le_card
  intro h hh
  obtain ⟨hh,hdiv⟩ := mem_filter.mp hh
  obtain ⟨hI,hmod,hpr,hmin⟩ := mem_filter.mp hh
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hI,hpr,hmod.trans (Nat.mod_eq_of_lt hb).symm,hdiv⟩,
    (min_le_left _ _).trans hmin⟩

theorem penaltyBand_conditions {p d : ℕ} (hd : 0 < d) (hz : 2*d < sieveCut p) :
    ∀ q ∈ penaltyBand (p^2) (sieveCut p), q.Prime ∧ sieveCut p ≤ q ∧ ¬q ∣ 2*d := by
  intro q hq
  obtain ⟨hi,hpr,_⟩ := mem_filter.mp hq
  exact ⟨hpr,(mem_Icc.mp hi).1,fun h => (hz.trans_le (mem_Icc.mp hi).1).not_ge
    (Nat.le_of_dvd (by omega) h)⟩

private theorem penalty_bounds {p q : ℕ} (hp : 4 ≤ p)
    (hq : q ∈ penaltyBand (p^2) (sieveCut p)) :
    0 ≤ 1-log q/log (upperCut (p^2)) ∧
    1-log q/log (upperCut (p^2)) ≤ discount (sieveCut p) q ∧
    1-log q/log (upperCut (p^2)) ≤ 1 := by
  obtain ⟨_,hpr,hqy⟩ := mem_filter.mp hq
  have hp2 : 1 < (((p^2:ℕ)):ℝ) := by exact_mod_cast (by nlinarith : 1<p^2)
  have hY : 1 < upperCut (p^2) := Real.one_lt_rpow hp2 (by norm_num)
  have hLY := Real.log_pos hY
  have h0 := Real.log_natCast_nonneg q
  have hupper := (level_alignment (p:=p) (by omega)).2
  have hq0 : (0:ℝ)<q := by exact_mod_cast hpr.pos
  have hLE := Real.log_le_log (show 0 < upperCut (p^2) by linarith) hupper
  refine ⟨sub_nonneg.mpr ((div_le_one hLY).mpr (Real.log_le_log hq0 hqy.le)),?_,?_⟩
  · exact sub_le_sub_left (div_le_div_of_nonneg_left h0 hLY hLE) 1
  · linarith only [div_nonneg h0 hLY.le]

theorem weighted_combine_at_cut {p H d b : ℕ} (hp : 4 ≤ p) (hb : b < d) (hH : H^3 ≤ p^4)
    (J ε E : ℝ) (hJ : 0 ≤ J) (hε : 0 < ε) :
    let X := p^2
    let z := sieveCut p
    let Q := penaltyBand X z
    ((J/d.totient)*V d z*(Real.exp Real.eulerMascheroniConstant/2*Real.log 3-ε) -
      (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤ (rough p H d b z).card) →
    (∀ q ∈ Q, let w := radius z q
      (((sievedAPOffsets p H d b q).filter (fun h => w ≤ (p^2-h).minFac)).card:ℝ) ≤
      (J/d.totient/q.totient)*V d w*(Real.exp Real.eulerMascheroniConstant+ε) +
      ∑ k ∈ moduli d w (w^2), |rhoRemainder p H d b J (q*k)|) →
    (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤ E →
    (∑ q ∈ Q, ∑ k ∈ moduli d (radius z q) ((radius z q)^2), |rhoRemainder p H d b J (q*k)|) ≤ E →
    (J/d.totient)*V d z*(Real.exp Real.eulerMascheroniConstant/2*Real.log 3-ε) - E -
      ((J/d.totient)*(Real.exp Real.eulerMascheroniConstant+ε) *
        (∑ q ∈ Q, discount z q*V d (radius z q)/((q:ℝ)-1)) + E)/(3/2) ≤
      ∑ h ∈ roughOffsets p H d b, weight X (X-h) := by
  intro X z Q hlow hupper hEL hEU
  let S := roughOffsets p H d b
  let B := J/d.totient * (Real.exp Real.eulerMascheroniConstant+ε)
  let c := fun q : ℕ => 1-log q/log (upperCut X)
  let W := fun q : ℕ => discount z q*V d (radius z q)/((q:ℝ)-1)
  let R := fun q : ℕ => ∑ k ∈ moduli d (radius z q) ((radius z q)^2), |rhoRemainder p H d b J (q*k)|
  have hcost (q : ℕ) (hq : q ∈ Q) :
      c q*(rowCount S X q:ℝ) ≤ B*W q + R q := by
    obtain ⟨hc0,hcD,hc1⟩ := penalty_bounds hp hq
    obtain ⟨_,hpr,_⟩ := mem_filter.mp hq
    have he : (q.totient:ℝ) = (q:ℝ)-1 := by
      rw [Nat.totient_prime hpr,Nat.cast_sub hpr.one_le,Nat.cast_one]
    have hfirst := (show (rowCount S X q:ℝ) ≤ _ by exact_mod_cast row_le_relaxed (p:=p) (H:=H) (q:=q) hb).trans (hupper q hq)
    have hmain : 0 ≤ (J/d.totient/q.totient)*V d (radius z q)*(Real.exp Real.eulerMascheroniConstant+ε) := by
      have := V_pos d (radius z q)
      positivity
    have hR : 0 ≤ R q := sum_nonneg fun k _ => abs_nonneg _
    apply (mul_le_mul_of_nonneg_left hfirst hc0).trans
    rw [mul_add]
    apply add_le_add _ (mul_le_of_le_one_left hR hc1)
    apply (mul_le_mul_of_nonneg_right hcD hmain).trans_eq
    dsimp [B,W]
    rw [he];ring
  have hpen : (∑ q ∈ Q, c q*(rowCount S X q:ℝ)) ≤ B*(∑ q ∈ Q,W q)+E := by
    apply (sum_le_sum hcost).trans
    rw [sum_add_distrib,←mul_sum]
    exact add_le_add le_rfl hEU
  have hrough := offsets_eq_model_rough (p:=p) (H:=H) hb
  have hbase := (sub_le_sub le_rfl hEL).trans hlow
  rw [← hrough] at hbase
  rw [rough_weight_eq_rows p H d b hp hH]
  change _ ≤ (S.card:ℝ) - (∑ q ∈ Q, c q*(rowCount S X q:ℝ))/(3/2)
  exact sub_le_sub hbase (div_le_div_of_nonneg_right hpen (by norm_num))

end
end GoldbachCentralSeven.Model

end


-- TH8000DensityAlgebra
section

namespace GoldbachCentralSeven.Density

noncomputable def exponent (r t σ : ℝ) : ℝ :=
  -r + (3*(2*r+t)/(2-σ)-1)*(1-σ)

theorem exponent_identity (r t u : ℝ) (hu : 0 ≤ u) :
    exponent r t (1-u) * (1+u) = r*(5*u-1) + (3*t-1)*u - u^2 := by
  unfold exponent
  rw [show 2-(1-u)=1+u by ring]
  field_simp
  ring

theorem medium_strip_margin {r t σ : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 5/32) (ht : t ≤ 1/3+1/1024)
    (hσlo : 1/2 ≤ σ) (hσhi : σ ≤ 7/8) :
    exponent r t σ ≤ -(1/1024) := by
  let u := 1-σ
  have hu : (1:ℝ)/8 ≤ u := by dsimp [u]; linarith
  have hu' : u ≤ (1:ℝ)/2 := by dsimp [u]; linarith
  have h0 : 0 ≤ u := by linarith
  have hid := exponent_identity r t u h0
  rw [show 1-u = σ by dsimp [u]; ring] at hid
  apply le_of_mul_le_mul_right (a := 1+u) _ (by linarith)
  rw [hid]
  have ht' : 3*t-1 ≤ 3/1024 := by linarith
  have htprod := mul_le_mul_of_nonneg_right ht' h0
  by_cases hsign : 5*u-1 ≤ 0
  · have hrprod := mul_nonpos_of_nonneg_of_nonpos hr0 hsign
    nlinarith only [hrprod, htprod, hu, hu', mul_nonneg h0 (sub_nonneg.mpr hu)]
  · have hrprod := mul_le_mul_of_nonneg_right hr (le_of_not_ge hsign)
    nlinarith only [hrprod, htprod, hu', sq_nonneg (u-25/64)]

theorem middle_witness (r : ℝ) (hr : 0 ≤ r) :
    exponent r (1/3) (1-5*r/2) * (1+5*r/2) = r*(25*r/4-1) := by
  rw [exponent_identity _ _ _ (by positivity)]
  ring

theorem level_witness (t : ℝ) (ht : 1/3 ≤ t) :
    (1/2:ℝ) < 93/158 ∧ (93/158:ℝ) < 7/8 ∧
    (117/35234:ℝ) ≤ exponent (13/79) t (93/158) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold exponent
  norm_num
  linarith

theorem near_one_obstruction {δ : ℝ} (hδ : 0 < δ) :
    0 < exponent 0 (1/3+δ) (1-δ) := by
  have h := exponent_identity 0 (1/3+δ) δ hδ.le
  apply pos_of_mul_pos_left (b := 1+δ) _ (by linarith)
  rw [h]
  nlinarith only [sq_pos_of_pos hδ]

theorem near_one_conductor_margin {δ t r σ : ℝ} (ht : t ≤ 1/3+δ)
    (hr : 12*δ^2 ≤ r) (hσlo : 7/8 ≤ σ) (hσhi : σ ≤ 1) :
    exponent r t σ ≤ -r/6 := by
  let u := 1-σ
  have h0 : 0 ≤ u := by dsimp [u]; linarith
  have hu : u ≤ (1:ℝ)/8 := by dsimp [u]; linarith
  have hr0 : 0 ≤ r := by nlinarith only [hr, sq_nonneg δ]
  have hid := exponent_identity r t u h0
  rw [show 1-u=σ by dsimp [u]; ring] at hid
  apply le_of_mul_le_mul_right (a := 1+u) _ (by linarith)
  rw [hid]
  have hru := mul_le_mul_of_nonneg_left hu hr0
  have huT := mul_le_mul_of_nonneg_right (by linarith : 3*t-1 ≤ 3*δ) h0
  nlinarith only [hr, hru, huT, sq_nonneg (u-3*δ/2)]

theorem near_one_boundary {u : ℝ} (hu : 0 ≤ u) :
    exponent 0 (1/3) (1-u) = -u^2/(1+u) := by
  apply (eq_div_iff (by linarith : 1+u ≠ 0)).mpr
  rw [exponent_identity _ _ _ hu]
  ring

theorem quadratic_loss_at_two_thirds_scale :
    Filter.Tendsto (fun L : ℝ => (L ^ (-(2/3:ℝ)))^2 * L) Filter.atTop (nhds 0) := by
  have hlim := tendsto_rpow_neg_atTop (show 0 < (1/3:ℝ) by norm_num)
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with L hL
  rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
  conv_rhs => rhs; rw [← Real.rpow_one L]
  rw [← Real.rpow_add hL]
  norm_num

end GoldbachCentralSeven.Density

end


-- TH8000DensityBand
section

namespace GoldbachCentralSeven.Density

open Finset

theorem conductor_band_sum {ι : Type*} (F : Finset ι) (R : ι → Finset ℕ)
    (β : ι → ℕ → ℝ) (q : ι → ℕ) (Q : ℕ) {X r t T σ C : ℝ}
    (hX : 1 < X) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr' : r ≤ 5/32)
    (ht : t ≤ 1/3+1/1024) (hT : 2 ≤ T) (hT' : T ≤ X^t)
    (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 7/8)
    (hQpos : 1 ≤ Q) (hQu : (Q:ℝ) ≤ X^r) (hQl : X^r ≤ 2*(Q:ℝ))
    (hq : ∀ j ∈ F, Q ≤ 2*q j)
    (hcount : (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
      C*((Q:ℝ)^2*T)^(3*(1-σ)/(2-σ))*(Real.log ((Q:ℝ)*T))^13) :
    (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+1/2048),
      X^(β j i-1)/(q j:ℝ)) ≤ 4*C*X^(-(1/2048:ℝ))*(Real.log X)^13 := by
  have hXpos : 0 < X := by linarith
  let e := 3*(1-σ)/(2-σ)
  have he : 0 ≤ e := div_nonneg (by linarith) (by linarith)
  have hbase : 0 < X^r := Real.rpow_pos_of_pos hXpos _
  have hQ1 : 1 ≤ (Q:ℝ) := by exact_mod_cast hQpos
  have hL : 0 ≤ Real.log ((Q:ℝ)*T) := Real.log_nonneg (by nlinarith)
  have hQTr : (Q:ℝ)*T ≤ X^(r+t) := by
    rw [Real.rpow_add hXpos]
    exact mul_le_mul hQu hT' (by linarith) hbase.le
  have hQTx : (Q:ℝ)*T ≤ X := hQTr.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le (show r+t≤1 by linarith))
  have hLog := Real.log_le_log (by positivity : 0 < (Q:ℝ)*T) hQTx
  have hQTpow : ((Q:ℝ)^2*T)^e ≤ X^((2*r+t)*e) := by
    rw [Real.rpow_mul hXpos.le, Real.rpow_add hXpos, mul_comm (2:ℝ) r,
      Real.rpow_mul hXpos.le, Real.rpow_two]
    apply Real.rpow_le_rpow (by positivity) _ he
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hQu 2) hT' (by linarith) (sq_nonneg _)
  have hcnt :
      (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
      C*X^((2*r+t)*e)*(Real.log X)^13 := hcount.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hQTpow hC)
        (pow_le_pow_left₀ hL hLog 13) (pow_nonneg hL _) (by positivity))
  have hscale : σ+1/2048-1-r+(2*r+t)*e ≤ -(1/2048:ℝ) := by
    have h := medium_strip_margin hr hr' ht hσ hσ'
    have hid : σ+1/2048-1-r + (2*r+t)*e = exponent r t σ + 1/2048 := by
      dsimp [e, exponent]
      ring
    linarith
  let K := 4*X^(σ+1/2048-1-r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hk (j : ι) (hj : j ∈ F) (i : ℕ) (hi : β j i ≤ σ+1/2048) :
      X^(β j i-1)/(q j:ℝ) ≤ K := by
    have hq' : (Q:ℝ) ≤ 2*(q j:ℝ) := by exact_mod_cast hq j hj
    have hqpos : 0 < (q j:ℝ) := by linarith
    have hratio : X^r ≤ 4*(q j:ℝ) := by linarith
    have ha := Real.rpow_le_rpow_of_exponent_le hX.le (sub_le_sub_right hi 1)
    apply (div_le_iff₀ hqpos).mpr
    refine ha.trans ?_
    dsimp [K]
    rw [Real.rpow_sub hXpos (σ+1/2048-1) r, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hbase]
    nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hXpos.le (σ+1/2048-1))]
  calc
    _ ≤ ∑ j ∈ F, K*(((R j).filter (fun i => σ ≤ β j i)).card : ℝ) := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ _i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+1/2048), K := by
          exact sum_le_sum fun i hi => hk j hj i (mem_filter.mp hi).2.2
        _ ≤ _ := by
          simp only [sum_const, nsmul_eq_mul]
          rw [mul_comm K]
          apply mul_le_mul_of_nonneg_right _ hK
          have sub : (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+1/2048) ⊆
              (R j).filter (fun i => σ ≤ β j i) := by
            intro i hi
            exact mem_filter.mpr ⟨(mem_filter.mp hi).1, (mem_filter.mp hi).2.1⟩
          exact_mod_cast card_le_card sub
    _ ≤ K*(C*X^((2*r+t)*e)*(Real.log X)^13) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hcnt hK
    _ = 4*C*X^(σ+1/2048-1-r+(2*r+t)*e)*(Real.log X)^13 := by
      rw [Real.rpow_add hXpos]
      dsimp [K]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX.le hscale) (by positivity))
      (pow_nonneg (Real.log_nonneg hX.le) _)

end GoldbachCentralSeven.Density

namespace GoldbachCentralSeven.Density

open Finset

private noncomputable def bandStart (b : ℕ) : ℝ := 1/2 + b/2048

private theorem bandStart_bounds {b : ℕ} (hb : b ∈ range 769) :
    1/2 ≤ bandStart b ∧ bandStart b ≤ 7/8 := by
  have hbr := mem_range.mp hb
  have : (b:ℝ) ≤ 768 := by exact_mod_cast (show b ≤ 768 by omega)
  dsimp [bandStart]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b]

private theorem band_cover {v : ℝ} (hv : 1/2 ≤ v) (hv' : v ≤ 7/8) :
    ∃ b ∈ range 769, bandStart b ≤ v ∧ v ≤ bandStart b + 1/2048 := by
  let b : ℕ := ⌊(v-1/2)*2048⌋₊
  have hlo : (b:ℝ) ≤ (v-1/2)*2048 := Nat.floor_le (by linarith)
  have hhi : (v-1/2)*2048 < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hb : (b:ℝ) < 769 := by linarith
  refine ⟨b, mem_range.mpr (by exact_mod_cast hb), ?_, ?_⟩ <;> dsimp [bandStart] <;> linarith

theorem conductor_full_middle_sum {ι : Type*} (F : Finset ι) (R : ι → Finset ℕ)
    (β : ι → ℕ → ℝ) (q : ι → ℕ) (Q : ℕ) {X r t T C : ℝ}
    (hX : 1 < X) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr' : r ≤ 5/32)
    (ht : t ≤ 1/3+1/1024) (hT : 2 ≤ T) (hT' : T ≤ X^t)
    (hQpos : 1 ≤ Q) (hQu : (Q:ℝ) ≤ X^r) (hQl : X^r ≤ 2*(Q:ℝ))
    (hq : ∀ j ∈ F, Q ≤ 2*q j)
    (hcount : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 7/8 →
      (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
        C*((Q:ℝ)^2*T)^(3*(1-σ)/(2-σ))*(Real.log ((Q:ℝ)*T))^13) :
    (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => 1/2 ≤ β j i ∧ β j i ≤ 7/8),
      X^(β j i-1)/(q j:ℝ)) ≤ (769*4)*C*X^(-(1/2048:ℝ))*(Real.log X)^13 := by
  let wt (j : ι) (i : ℕ) := X^(β j i-1)/(q j:ℝ)
  let bins := range 769
  let W (b : ℕ) (j : ι) := (R j).filter (fun i => bandStart b ≤ β j i ∧ β j i ≤ bandStart b+1/2048)
  have hw (j : ι) (i : ℕ) : 0 ≤ wt j i := div_nonneg (Real.rpow_nonneg (by linarith) _) (Nat.cast_nonneg _)
  have hrow (j : ι) :
      (∑ i ∈ (R j).filter (fun i => 1/2 ≤ β j i ∧ β j i ≤ 7/8), wt j i) ≤
        ∑ b ∈ bins, ∑ i ∈ W b j, wt j i := by
    simp only [W, sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro i _
    by_cases hi : 1/2 ≤ β j i ∧ β j i ≤ 7/8
    · obtain ⟨b, hb, hin⟩ := band_cover hi.1 hi.2
      rw [ite_eq_left hi]
      refine (le_of_eq ?_).trans (single_le_sum (s := bins) (a := b)
        (f := fun a => if bandStart a ≤ β j i ∧ β j i ≤ bandStart a+1/2048 then wt j i else 0)
        (fun a _ => by split <;> simp [hw]) hb)
      rw [ite_eq_left hin]
    · rw [ite_eq_right hi]
      exact sum_nonneg fun _ _ => by split <;> simp [hw]
  calc
    _ ≤ ∑ j ∈ F, ∑ b ∈ bins, ∑ i ∈ W b j, wt j i := sum_le_sum fun j _ => hrow j
    _ = ∑ b ∈ bins, ∑ j ∈ F, ∑ i ∈ W b j, wt j i := sum_comm
    _ ≤ ∑ _b ∈ bins, 4*C*X^(-(1/2048:ℝ))*(Real.log X)^13 := by
      apply sum_le_sum
      intro b hb
      obtain ⟨hl, hu⟩ := bandStart_bounds hb
      exact conductor_band_sum F R β q Q hX hC hr hr' ht hT hT' hl hu hQpos hQu hQl hq
        (hcount _ hl hu)
    _ = _ := by simp [bins]; ring

end GoldbachCentralSeven.Density

end


-- TH8000ActualDensity
section

namespace GoldbachCentralSeven.Density

open Finset OAI.Ostmann

theorem actual_weighted_middle :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r t T : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      1 < X → 0 ≤ r → r ≤ 5/32 → t ≤ 1/3+1/1024 → 2 ≤ T → T ≤ X^t →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i =>
          1/2 ≤ ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ 7/8),
          X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
            C * X^(-(1/2048:ℝ)) * (Real.log X)^13 := by
  obtain ⟨K, hK, hbase⟩ := V1f0
  refine ⟨(769*4)*K, by positivity, ?_⟩
  intro X r t T Q F hX hr hr' ht hT hT' hQ hQu hQl hF
  apply conductor_full_middle_sum F (fun χ => (V1 χ).V14 T)
    (fun χ i => ((V1 χ).zeros i).re) PrimitiveComplexCharacter.modulus Q
    hX hK.le hr hr' ht hT hT' hQ hQu hQl (fun χ hχ => (hF χ hχ).2)
  intro σ hs hs'
  exact hbase Q hQ T σ hT hs (by linarith) F (fun χ hχ => (hF χ hχ).1)

theorem actual_weighted_middle_log {A ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ (r t T : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      0 ≤ r → r ≤ 5/32 → t ≤ 1/3+1/1024 → 2 ≤ T → T ≤ X^t →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i =>
          1/2 ≤ ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ 7/8),
          X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤ ε/(Real.log X)^A := by
  obtain ⟨C, hC, hc⟩ := actual_weighted_middle
  have hg := (isLittleO_log_rpow_rpow_atTop (13+A)
    (by norm_num : 0 < (1/2048:ℝ))).bound (show 0 < ε/C by positivity)
  filter_upwards [hg, Filter.eventually_gt_atTop (1:ℝ)] with X hX hx
  intro r t T Q F hr hr' ht hT hT' hQ hQu hQl hF
  refine (hc X r t T Q F hx hr hr' ht hT hT' hQ hQu hQl hF).trans ?_
  have hpos : 0 < X := by linarith
  have hlog := Real.log_pos hx
  change ‖Real.log X^(13+A)‖ ≤ ε/C*‖X^(1/2048:ℝ)‖ at hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog _),
    abs_of_pos (Real.rpow_pos_of_pos hpos _)] at hX
  have h13 : (Real.log X)^13 * (Real.log X)^A = (Real.log X)^(13+A) := by
    rw [Real.rpow_add hlog]
    norm_cast
  have hg' := mul_le_mul_of_nonneg_left hX hC.le
  rw [show C * (ε/C * X^(1/2048:ℝ)) = ε*X^(1/2048:ℝ) by field_simp] at hg'
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog _)).mpr
  rw [Real.rpow_neg hpos.le]
  calc
    _ = C*(Real.log X)^(13+A)/X^(1/2048:ℝ) := by rw [← h13]; ring
    _ ≤ ε := (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).mpr hg'

end GoldbachCentralSeven.Density

end


-- THHighZeros
section

namespace GoldbachCentralSeven.Density
open Finset Filter OAI.Ostmann

noncomputable def damping (X T : ℝ) := min 1 (X^(1/3:ℝ)/T)

lemma damping_nonneg {X T : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) : 0 ≤ damping X T :=
  le_min zero_le_one (div_nonneg (Real.rpow_nonneg hX _) hT)

lemma damped_power {X T A e : ℝ} (hX : 0 < X) (hT : 0 < T) (hA : 0 ≤ A)
    (he : 0 ≤ e) (he1 : e ≤ 1) :
    damping X T * (A*T)^e ≤ (A*X^(1/3:ℝ))^e := by
  let D := X^(1/3:ℝ)
  have hD : 0 < D := Real.rpow_pos_of_pos hX _
  by_cases h : T ≤ D
  · exact (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
      (min_le_left _ _)).trans (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left h hA) he)
  have hu : 1 ≤ T/D := (one_le_div hD).mpr (le_of_not_ge h)
  have hid : A*T = (A*D)*(T/D) := by field_simp
  have hp := Real.rpow_le_self_of_one_le hu he1
  calc
    _ ≤ (D/T)*(A*T)^e := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = (D/T)*((A*D)^e*(T/D)^e) := by rw [hid,Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (D/T)*((A*D)^e*(T/D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by change _ = (A*D)^e; field_simp

lemma weighted_bin {ι : Type*} (F : Finset ι) (R : ι → Finset ℕ)
    (β : ι → ℕ → ℝ) (q : ι → ℕ) (Q : ℕ) {X r T σ w C : ℝ}
    (hX : 1 < X) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr' : r ≤ 5/32)
    (hT : 2 ≤ T) (hT' : T ≤ X^2) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1)
    (hQpos : 1 ≤ Q) (hQu : (Q:ℝ) ≤ X^r) (hQl : X^r ≤ 2*(Q:ℝ))
    (hq : ∀ j ∈ F, Q ≤ 2*q j)
    (hcount : (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
      C*((Q:ℝ)^2*T)^(3*(1-σ)/(2-σ))*(Real.log ((Q:ℝ)*T))^13) :
    (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w),
      damping X T * X^(β j i-1)/(q j:ℝ)) ≤
      4*C*X^(exponent r (1/3) σ + w)*(3*Real.log X)^13 := by
  have hx : 0 < X := by linarith
  let e := 3*(1-σ)/(2-σ)
  have he : 0 ≤ e := div_nonneg (by linarith) (by linarith)
  have he1 : e ≤ 1 := (div_le_iff₀ (by linarith : 0 < 2-σ)).mpr (by linarith)
  have hbase : 0 < X^r := Real.rpow_pos_of_pos hx _
  have hQ1 : 1 ≤ (Q:ℝ) := by exact_mod_cast hQpos
  have hL : 0 ≤ Real.log ((Q:ℝ)*T) := Real.log_nonneg (by nlinarith)
  have hQX : (Q:ℝ) ≤ X := hQu.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le (by linarith : r ≤ 1))
  have hLog : Real.log ((Q:ℝ)*T) ≤ 3*Real.log X := by
    calc
      _ ≤ Real.log (X^3) := Real.log_le_log (by positivity) (by
        calc
          (Q:ℝ)*T ≤ X*X^2 := mul_le_mul hQX hT' (by linarith) hx.le
          _ = X^3 := by ring)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hd := damping_nonneg hx.le (by linarith : 0 ≤ T)
  have hp : damping X T * ((Q:ℝ)^2*T)^e ≤ X^((2*r+1/3)*e) := by
    refine (damped_power hx (by linarith) (sq_nonneg _) he he1).trans ?_
    rw [Real.rpow_mul hx.le,Real.rpow_add hx,mul_comm (2:ℝ) r,Real.rpow_mul hx.le,Real.rpow_two]
    exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hQu 2) (by positivity)) he
  have hcnt : damping X T * (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
      C*X^((2*r+1/3)*e)*(3*Real.log X)^13 := by
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount hd
      _ = C * (damping X T * ((Q:ℝ)^2*T)^e) * (Real.log ((Q:ℝ)*T))^13 := by dsimp [e]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hp hC)
        (pow_le_pow_left₀ hL hLog 13) (pow_nonneg hL _) (by positivity)
  let K := 4*X^(σ+w-1-r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hk (j : ι) (hj : j ∈ F) (i : ℕ) (hi : β j i ≤ σ+w) : X^(β j i-1)/(q j:ℝ) ≤ K := by
    have hq' : (Q:ℝ) ≤ 2*(q j:ℝ) := by exact_mod_cast hq j hj
    have hqpos : 0 < (q j:ℝ) := by linarith
    have hratio : X^r ≤ 4*(q j:ℝ) := by linarith
    have ha := Real.rpow_le_rpow_of_exponent_le hX.le (sub_le_sub_right hi 1)
    apply (div_le_iff₀ hqpos).mpr
    refine ha.trans ?_
    dsimp [K]
    rw [Real.rpow_sub hx (σ+w-1) r, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hbase]
    nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hx.le (σ+w-1))]
  calc
    _ ≤ ∑ j ∈ F, (damping X T*K)*(((R j).filter (fun i => σ ≤ β j i)).card : ℝ) := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ _i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w), damping X T*K := by
          apply sum_le_sum
          intro i hi
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (hk j hj i (mem_filter.mp hi).2.2) hd
        _ ≤ _ := by
          simp only [sum_const,nsmul_eq_mul]
          rw [mul_comm (damping X T*K)]
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hd hK)
          exact_mod_cast card_le_card
            (show (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w) ⊆
                (R j).filter (fun i => σ ≤ β j i) from fun i hi =>
              mem_filter.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hi).2.1⟩)
    _ = K * (damping X T * (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ))) := by
      rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcnt hK
    _ = _ := by
      have hh : exponent r (1/3) σ+w = σ+w-1-r+(2*r+1/3)*e := by dsimp [exponent,e]; ring
      rw [hh,Real.rpow_add hx]
      dsimp [K]; ring

private noncomputable def meshStart (l w : ℝ) (b : ℕ) : ℝ := l+b*w

theorem sum_mesh {ι : Type*} (F : Finset ι) (R : ι → Finset ℕ)
    (β m : ι → ℕ → ℝ) {l u w W : ℝ} (hw : 0 < w) (hlu : l ≤ u)
    (hm : ∀ j i, 0 ≤ m j i) (hW : 0 ≤ W)
    (hstrip : ∀ σ : ℝ, l ≤ σ → σ ≤ u →
      (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w), m j i) ≤ W) :
    (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => l ≤ β j i ∧ β j i ≤ u), m j i) ≤
      (1+(u-l)/w)*W := by
  classical
  let B := ⌊(u-l)/w⌋₊
  let bins := range (B+1)
  have hB : (B:ℝ) ≤ (u-l)/w := Nat.floor_le (by positivity)
  let Wset (b : ℕ) (j : ι) := (R j).filter (fun i =>
    meshStart l w b ≤ β j i ∧ β j i ≤ meshStart l w b+w)
  have hst (b : ℕ) (hb : b ∈ bins) : l ≤ meshStart l w b ∧ meshStart l w b ≤ u := by
    have hb' : b ≤ B := Nat.lt_succ_iff.mp (mem_range.mp hb)
    have hbR : (b:ℝ) ≤ (u-l)/w := (by exact_mod_cast hb' : (b:ℝ) ≤ B).trans hB
    have hh := (le_div_iff₀ hw).mp hbR
    dsimp [meshStart]
    constructor <;> linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) b) hw.le]
  have cover {v : ℝ} (hl : l ≤ v) (hu : v ≤ u) :
      ∃ b ∈ bins, meshStart l w b ≤ v ∧ v ≤ meshStart l w b+w := by
    let b := ⌊(v-l)/w⌋₊
    have hb0 : (b:ℝ) ≤ (v-l)/w := Nat.floor_le (by positivity)
    have hb1 : (v-l)/w < (b:ℝ)+1 := Nat.lt_floor_add_one _
    have hb : b ≤ B := Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hu l) hw.le)
    refine ⟨b,mem_range.mpr (Nat.lt_succ_of_le hb),?_,?_⟩ <;> dsimp [meshStart]
    · linarith [(le_div_iff₀ hw).mp hb0]
    · linarith [(div_lt_iff₀ hw).mp hb1]
  have hrow (j : ι) :
      (∑ i ∈ (R j).filter (fun i => l ≤ β j i ∧ β j i ≤ u), m j i) ≤
        ∑ b ∈ bins, ∑ i ∈ Wset b j, m j i := by
    simp only [Wset,sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro i _
    by_cases hi : l ≤ β j i ∧ β j i ≤ u
    · obtain ⟨b,hb,hbi⟩ := cover hi.1 hi.2
      rw [ite_eq_left hi]
      refine (le_of_eq ?_).trans (single_le_sum (s:=bins) (a:=b)
        (f:=fun a => if meshStart l w a ≤ β j i ∧ β j i ≤ meshStart l w a+w then m j i else 0)
        (fun a _ => by split <;> simp [hm]) hb)
      rw [ite_eq_left hbi]
    · rw [ite_eq_right hi]
      exact sum_nonneg fun _ _ => by split <;> simp [hm]
  calc
    _ ≤ ∑ j ∈ F, ∑ b ∈ bins, ∑ i ∈ Wset b j, m j i := sum_le_sum fun j _ => hrow j
    _ = ∑ b ∈ bins, ∑ j ∈ F, ∑ i ∈ Wset b j, m j i := sum_comm
    _ ≤ ∑ _b ∈ bins, W := sum_le_sum fun b hb => hstrip _ (hst b hb).1 (hst b hb).2
    _ ≤ _ := by
      simp only [bins, sum_const, card_range, nsmul_eq_mul, Nat.cast_add_one]
      apply mul_le_mul_of_nonneg_right _ hW
      linarith

theorem actual_high_large :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r T : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      1 < X → 0 ≤ r → r ≤ 5/32 → 2 ≤ T → T ≤ X^2 →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i =>
          7/8 ≤ ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ 1),
          damping X T * X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          C*(1+Real.log X)*X^(-r/6)*(3*Real.log X)^13 := by
  obtain ⟨K,hK,hden⟩ := V1f0
  refine ⟨4*K*Real.exp 1,by positivity,?_⟩
  intro X r T Q F hX hr hr' hT hT' hQ hQu hQl hF
  have hx := lt_trans zero_lt_one hX
  have hl := Real.log_pos hX
  let w := 1/Real.log X
  have hw : 0 < w := by dsimp [w]; positivity
  have hwX : X^w = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    dsimp [w]
    field_simp
  let W := 4*K*X^(-r/6)*Real.exp 1*(3*Real.log X)^13
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hbin (σ : ℝ) (hσ : 7/8 ≤ σ) (hσ1 : σ ≤ 1) := weighted_bin F
    (fun χ => (V1 χ).V14 T) (fun χ i => ((V1 χ).zeros i).re) PrimitiveComplexCharacter.modulus Q
    (w:=w) hX hK.le hr hr' hT hT' (by linarith : 1/2 ≤ σ) hσ1
    hQ hQu hQl (fun χ hχ => (hF χ hχ).2) (hden Q hQ T σ hT
      (by linarith) hσ1 F (fun χ hχ => (hF χ hχ).1))
  have hc := sum_mesh F (fun χ => (V1 χ).V14 T) (fun χ i => ((V1 χ).zeros i).re)
    (fun χ i => damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ))
    (l:=7/8) (u:=1) hw (by norm_num)
    (fun χ i => div_nonneg (mul_nonneg (damping_nonneg hx.le (by linarith)) (by positivity))
      (Nat.cast_nonneg _)) hW (fun σ hσ hs => by
      refine (hbin σ hσ hs).trans ?_
      have h := near_one_conductor_margin (δ:=0) (t:=(1/3:ℝ)) (r:=r) (σ:=σ)
        (by norm_num) (by simpa using hr) hσ hs
      dsimp [W]
      rw [Real.rpow_add hx,hwX]
      rw [← mul_assoc (4*K) (X^exponent r (1/3) σ) (Real.exp 1)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX.le h) (by positivity)) (Real.exp_pos _).le)
        (by positivity))
  refine hc.trans ?_
  have hw' : (1-7/8:ℝ)/w ≤ Real.log X := by
    dsimp [w]; rw [div_div_eq_mul_div]; norm_num; linarith
  calc
    _ ≤ (1+Real.log X)*W := mul_le_mul_of_nonneg_right (by linarith) hW
    _ = _ := by dsimp [W]; ring

end GoldbachCentralSeven.Density

end


-- Sidon.NumberTheory.JensenDensityGeometry
section

noncomputable section

namespace Sidon

theorem jensen_disc_window {σ δ y : ℝ} {ρ : ℂ}
    (_hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : σ + δ ≤ ρ.re) (hβhi : ρ.re ≤ 1)
    (hy : |y - ρ.im| ≤ δ) :
    ‖((2 : ℂ) + (y : ℂ) * Complex.I) - ρ‖ ≤ (2 - σ) - δ / 2 := by
  have hR : 0 ≤ (2 - σ) - δ / 2 := by linarith
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.sub_im, Complex.add_im, Complex.mul_im,
    mul_one]
  norm_num
  change (2 - ρ.re) * (2 - ρ.re) + (y - ρ.im) * (y - ρ.im) ≤
    ((2 - σ) - δ / 2) ^ 2
  have hreal : 0 ≤ 2 - ρ.re := by linarith
  have hreal' : 2 - ρ.re ≤ (2 - σ) - δ := by linarith
  have him := sq_le_sq₀ (abs_nonneg (y - ρ.im)) hδ0 |>.mpr hy
  rw [sq_abs] at him
  have hsq := mul_self_le_mul_self hreal hreal'
  have hdR := mul_le_mul_of_nonneg_left hσ1 hδ0
  have hdδ := mul_le_mul_of_nonneg_left hδ1 hδ0
  nlinarith

theorem jensen_log_weight_lower {R d δ : ℝ} (hR0 : 1 ≤ R) (hR1 : R ≤ 3 / 2)
    (hd : 0 < d) (hδ : 0 ≤ δ) (hreserve : d ≤ R - δ / 2) :
    δ / 3 ≤ Real.log (R / d) := by
  have hR : 0 < R := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hR hd)
  rw [inv_div] at hlog
  have hdiv : d / R ≤ 1 - δ / (2 * R) := by
    apply (div_le_iff₀ hR).mpr
    field_simp
    nlinarith
  have hδdiv : δ / 3 ≤ δ / (2 * R) := by
    apply div_le_div_of_nonneg_left hδ (by positivity)
    linarith
  linarith

def jensenCenter (y : ℝ) : ℂ := 2 + (y : ℂ) * Complex.I

def jensenVerticalWeight (R : ℝ) (ρ : ℂ) (y : ℝ) : ℝ :=
  max 0 (Real.log R - Real.log ‖jensenCenter y - ρ‖)

theorem one_le_norm_jensenCenter_sub {ρ : ℂ} (hρ : ρ.re ≤ 1) (y : ℝ) :
    1 ≤ ‖jensenCenter y - ρ‖ := by
  have hh := Complex.re_le_norm (jensenCenter y - ρ)
  have hre : (jensenCenter y - ρ).re = 2 - ρ.re := by
    simp [jensenCenter]
  rw [hre] at hh
  linarith

theorem continuous_jensenVerticalWeight (R : ℝ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    Continuous (jensenVerticalWeight R ρ) := by
  have hc : Continuous (fun y : ℝ => ‖jensenCenter y - ρ‖) := by
    unfold jensenCenter
    fun_prop
  exact continuous_const.max (continuous_const.sub (hc.log (fun y =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_norm_jensenCenter_sub hρ y)))))

theorem jensenVerticalWeight_lower {σ δ y : ℝ} {ρ : ℂ}
    (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : σ + δ ≤ ρ.re) (hβhi : ρ.re ≤ 1)
    (hy : |y - ρ.im| ≤ δ) :
    δ / 3 ≤ jensenVerticalWeight (2 - σ) ρ y := by
  have hd : 0 < ‖jensenCenter y - ρ‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_jensenCenter_sub hβhi y)
  have hh := jensen_log_weight_lower (R := 2 - σ)
    (by linarith) (by linarith) hd hδ0
    (jensen_disc_window hσ0 hσ1 hδ0 hδ1 hβlo hβhi hy)
  rw [Real.log_div (by linarith) hd.ne'] at hh
  exact hh.trans (le_max_right _ _)

theorem jensenVerticalWeight_integral_lower {σ δ T : ℝ} {ρ : ℂ}
    (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : σ + δ ≤ ρ.re) (hβhi : ρ.re ≤ 1)
    (hγlo : 4 ≤ ρ.im) (hγhi : ρ.im ≤ T) :
    2 * δ ^ 2 / 3 ≤ ∫ y in (3 : ℝ)..T + 1, jensenVerticalWeight (2 - σ) ρ y := by
  have hc := continuous_jensenVerticalWeight (2 - σ) hβhi
  have hab : ρ.im - δ ≤ ρ.im + δ := by linarith
  have hlocal : (∫ _ in ρ.im - δ..ρ.im + δ, δ / 3) ≤
      ∫ y in ρ.im - δ..ρ.im + δ, jensenVerticalWeight (2 - σ) ρ y := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (hc.intervalIntegrable _ _)
    intro y hy
    apply jensenVerticalWeight_lower hσ0 hσ1 hδ0 hδ1 hβlo hβhi
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hglobal := intervalIntegral.integral_mono_interval
    (μ := MeasureTheory.volume)
    (by linarith : (3 : ℝ) ≤ ρ.im - δ) hab
    (by linarith : ρ.im + δ ≤ T + 1)
    (f := jensenVerticalWeight (2 - σ) ρ)
    (MeasureTheory.ae_of_all _ (fun y => le_max_left 0 _)) (hc.intervalIntegrable _ _)
  calc
    2 * δ ^ 2 / 3 = ∫ _ in ρ.im - δ..ρ.im + δ, δ / 3 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := hlocal
    _ ≤ _ := hglobal

theorem card_mul_jensen_mass_le_integral {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    {σ δ T : ℝ} (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hβlo : ∀ i ∈ S, σ + δ ≤ (ρ i).re)
    (hβhi : ∀ i ∈ S, (ρ i).re ≤ 1)
    (hγlo : ∀ i ∈ S, 4 ≤ (ρ i).im)
    (hγhi : ∀ i ∈ S, (ρ i).im ≤ T) :
    (S.card : ℝ) * (2 * δ ^ 2 / 3) ≤
      ∫ y in (3 : ℝ)..T + 1, ∑ i ∈ S, jensenVerticalWeight (2 - σ) (ρ i) y := by
  calc
    _ = ∑ i ∈ S, (2 * δ ^ 2 / 3) := by simp
    _ ≤ ∑ i ∈ S, ∫ y in (3 : ℝ)..T + 1,
        jensenVerticalWeight (2 - σ) (ρ i) y := by
      apply Finset.sum_le_sum
      intro i hi
      exact jensenVerticalWeight_integral_lower hσ0 hσ1 hδ0 hδ1
        (hβlo i hi) (hβhi i hi) (hγlo i hi) (hγhi i hi)
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      intro i hi
      exact (continuous_jensenVerticalWeight (2 - σ) (hβhi i hi)).intervalIntegrable _ _

end Sidon

end
end


-- Sidon.NumberTheory.CircleAverageVertical
section

noncomputable section

open Set MeasureTheory Complex Real

namespace Sidon

theorem setIntegral_translate_Icc (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (v : ℝ) :
    (∫ y in Icc a b, f (y + v)) = ∫ t in Icc (a + v) (b + v), f t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_add_right]
  rw [intervalIntegral.integral_of_le (show a + v ≤ b + v by linarith),
    ← integral_Icc_eq_integral_Ioc]

theorem integral_angularAverage_le {a b L : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ Icc 0 (2 * π)))
    (hslice : ∀ θ ∈ Icc 0 (2 * π), (∫ y in Icc a b, f y θ) ≤ L) :
    (∫ y in Icc a b, (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), f y θ) ≤ L := by
  have hi : Integrable f.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 (2 * π)))) := by
    rw [Measure.prod_restrict]
    exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [integral_const_mul, integral_integral_swap hi]
  calc
    _ ≤ (2 * π)⁻¹ * ∫ _ in Icc 0 (2 * π), L := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_on hi.integral_prod_right (integrable_const _)
        measurableSet_Icc hslice
    _ = L := by
      simp [mul_assoc, max_eq_left (by positivity : (0 : ℝ) ≤ 2 * π)]

def verticalCircleRectangle (R T : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc (2 - R) (2 + R) ∧ z.im ∈ Icc 1 (T + 3)}

theorem circleMap_vertical_center (y R θ : ℝ) :
    circleMap (2 + (y : ℂ) * I) R θ =
      ((2 + (circleMap 0 R θ).re : ℝ) : ℂ) +
        ((y + (circleMap 0 R θ).im : ℝ) : ℂ) * I := by
  have hh : circleMap (2 + (y : ℂ) * I) R θ =
      (2 + (y : ℂ) * I) + circleMap 0 R θ := by simp [circleMap, add_assoc]
  rw [hh]
  apply Complex.ext <;> simp

theorem circleMap_vertical_mem_rectangle {R T y : ℝ} (hR : 0 ≤ R)
    (hR1 : R ≤ 3 / 2) (hy : y ∈ Icc 3 (T + 1)) (θ : ℝ) :
    circleMap (2 + (y : ℂ) * I) R θ ∈ verticalCircleRectangle R T := by
  have hre := Complex.abs_re_le_norm (circleMap 0 R θ)
  have him := Complex.abs_im_le_norm (circleMap 0 R θ)
  rw [norm_circleMap_zero, abs_of_nonneg hR] at hre him
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hre
  obtain ⟨hilo, hihi⟩ := abs_le.mp him
  rw [circleMap_vertical_center]
  have hh : (2 + (circleMap 0 R θ).re ∈ Icc (2 - R) (2 + R)) ∧
      (y + (circleMap 0 R θ).im ∈ Icc 1 (T + 3)) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  simpa [verticalCircleRectangle] using hh

theorem integrableOn_circleAverage_vertical {F : ℂ → ℝ} {R T : ℝ}
    (hR : 0 ≤ R) (hR1 : R ≤ 3 / 2)
    (hF : ContinuousOn F (verticalCircleRectangle R T)) :
    IntegrableOn (fun y : ℝ => circleAverage F (2 + (y : ℂ) * I) R)
      (Icc 3 (T + 1)) := by
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => F (circleMap (2 + (p.1 : ℂ) * I) R p.2))
      (Icc 3 (T + 1) ×ˢ Icc 0 (2 * π)) := by
    apply hF.comp
    · unfold circleMap
      fun_prop
    · intro p hp
      exact circleMap_vertical_mem_rectangle hR hR1 hp.1 p.2
  have hi : Integrable
      (fun p : ℝ × ℝ => F (circleMap (2 + (p.1 : ℂ) * I) R p.2))
      ((volume.restrict (Icc 3 (T + 1))).prod (volume.restrict (Icc 0 (2 * π)))) := by
    rw [Measure.prod_restrict]
    exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity),
    ← integral_Icc_eq_integral_Ioc]
  exact hi.integral_prod_left.const_mul _

theorem integral_circleAverage_vertical_le {F : ℂ → ℝ} {R T L : ℝ}
    (hR : 0 ≤ R) (hR1 : R ≤ 3 / 2) (hT : 3 ≤ T)
    (hF : ContinuousOn F (verticalCircleRectangle R T))
    (hF0 : ∀ z ∈ verticalCircleRectangle R T, 0 ≤ F z)
    (hslice : ∀ u ∈ Icc (2 - R) (2 + R),
      (∫ t in Icc 1 (T + 3), F ((u : ℂ) + (t : ℂ) * I)) ≤ L) :
    (∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * I) R) ≤ L := by
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => F (circleMap (2 + (p.1 : ℂ) * I) R p.2))
      (Icc 3 (T + 1) ×ˢ Icc 0 (2 * π)) := by
    apply hF.comp
    · unfold circleMap
      fun_prop
    · intro p hp
      exact circleMap_vertical_mem_rectangle hR hR1 hp.1 p.2
  simp_rw [circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_angularAverage_le
    (f := fun y θ => F (circleMap (2 + (y : ℂ) * I) R θ)) hc
  intro θ _
  let u : ℝ := 2 + (circleMap 0 R θ).re
  let v : ℝ := (circleMap 0 R θ).im
  have hre := Complex.abs_re_le_norm (circleMap 0 R θ)
  have him := Complex.abs_im_le_norm (circleMap 0 R θ)
  rw [norm_circleMap_zero, abs_of_nonneg hR] at hre him
  have hu : u ∈ Icc (2 - R) (2 + R) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hre
    exact ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩
  have hv : -R ≤ v ∧ v ≤ R := abs_le.mp him
  have hi : IntegrableOn (fun t : ℝ => F ((u : ℂ) + (t : ℂ) * I))
      (Icc 1 (T + 3)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply hF.comp (by fun_prop)
    intro t ht
    exact ⟨by simpa using hu, by simpa using ht⟩
  have hsub : Icc (3 + v) (T + 1 + v) ⊆ Icc 1 (T + 3) := by
    apply Icc_subset_Icc <;> linarith [hv.1, hv.2]
  calc
    _ = ∫ y in Icc 3 (T + 1), F ((u : ℂ) + ((y + v : ℝ) : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [circleMap_vertical_center]
    _ = ∫ t in Icc (3 + v) (T + 1 + v), F ((u : ℂ) + (t : ℂ) * I) :=
      setIntegral_translate_Icc (fun t => F ((u : ℂ) + (t : ℂ) * I))
        (a := 3) (b := T + 1) (by linarith) v
    _ ≤ ∫ t in Icc 1 (T + 3), F ((u : ℂ) + (t : ℂ) * I) := by
      apply setIntegral_mono_set hi _ hsub.eventuallySubset
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hF0 _ ⟨by simpa using hu, by simpa using ht⟩
    _ ≤ L := hslice u hu

end Sidon

end
end


-- TH8000JensenBridge
section

/- The integrated Jensen geometry and detector comparison are adapted to entire
functions and indexed Dirichlet zeros from TomasOrtega/Sidon at
735de6d7c67b81a28b1e07e3f2661dbc17bb89d6 (Apache-2.0), JensenMollifier,
JensenZeroOccurrences, JensenZeroDensity. -/
namespace GoldbachCentralSeven.Jensen

open Set MeasureTheory MeromorphicOn Metric Real Sidon
open scoped Classical
noncomputable section

def E (f m : ℂ → ℂ) (z : ℂ) := f z * m z - 1
def D (f m : ℂ → ℂ) (z : ℂ) := 1 - (E f m z)^2

private theorem analyticE {f m : ℂ → ℂ} (hf : Differentiable ℂ f) (hm : Differentiable ℂ m)
    (z : ℂ) : AnalyticAt ℂ (E f m) z :=
  ((hf.analyticAt z).mul (hm.analyticAt z)).sub analyticAt_const

private theorem analyticD {f m : ℂ → ℂ} (hf : Differentiable ℂ f) (hm : Differentiable ℂ m)
    (z : ℂ) : AnalyticAt ℂ (D f m) z :=
  analyticAt_const.sub ((analyticE hf hm z).pow 2)

private theorem divisor_le_det {f m : ℂ → ℂ} (hf : Differentiable ℂ f) (hm : Differentiable ℂ m)
    {c : ℂ} {R : ℝ} (hc : D f m c ≠ 0) (z : ℂ) :
    divisor f (closedBall c |R|) z ≤ divisor (D f m) (closedBall c |R|) z := by
  let U := closedBall c |R|
  let g := fun w => m w*(2-f w*m w)
  have hfg : (fun w => f w * g w) = D f m := by
    funext w; dsimp [g,D,E]; ring
  have hF : AnalyticOnNhd ℂ f U := fun w _ => hf.analyticAt w
  have hG : AnalyticOnNhd ℂ g U := fun w _ =>
    (hm.analyticAt w).mul (analyticAt_const.sub ((hf.analyticAt w).mul (hm.analyticAt w)))
  have hfgc : f c * g c ≠ 0 := by simpa only [congrFun hfg c] using hc
  have hcU : c ∈ U := mem_closedBall_self (abs_nonneg R)
  have finiteOrd (F : ℂ → ℂ) (h : AnalyticOnNhd ℂ F U) (hFc : F c ≠ 0) :
      ∀ w ∈ U, meromorphicOrderAt F w ≠ ⊤ := by
    intro w hw
    apply h.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c |R|).isPreconnected hcU hw
    rw [(h c hcU).meromorphicOrderAt_eq, (h c hcU).analyticOrderAt_eq_zero.mpr hFc]
    simp
  have hdiv := divisor_fun_mul hF.meromorphicOn hG.meromorphicOn
    (finiteOrd _ hF (mul_ne_zero_iff.mp hfgc).1) (finiteOrd _ hG (mul_ne_zero_iff.mp hfgc).2)
  rw [hfg] at hdiv
  change divisor f U z ≤ divisor (D f m) U z
  rw [hdiv]
  exact le_add_of_nonneg_right (hG.divisor_nonneg z)

private theorem jensen_det {f m : ℂ → ℂ} (hf : Differentiable ℂ f) (hm : Differentiable ℂ m)
    {c : ℂ} {R : ℝ} (hc : D f m c ≠ 0) :
    (∑ᶠ z, (divisor (D f m) (closedBall c |R|) z : ℝ)*Real.log (R*‖c-z‖⁻¹)) ≤
      circleAverage (fun z => ‖E f m z‖^2) c R - Real.log ‖D f m c‖ := by
  have hd : AnalyticOnNhd ℂ (D f m) (closedBall c |R|) := fun w _ => analyticD hf hm w
  have he : AnalyticOnNhd ℂ (E f m) (closedBall c |R|) := fun w _ => analyticE hf hm w
  have hlog := hd.circleAverage_log_norm hc
  have hmono : circleAverage (fun z => Real.log ‖D f m z‖) c R ≤
      circleAverage (fun z => ‖E f m z‖^2) c R := by
    apply circleAverage_mono
    · exact (hd.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · exact ((he.continuousOn.mono sphere_subset_closedBall).norm.pow 2).circleIntegrable'
    · intro z _
      change Real.log ‖1 - (E f m z)^2‖ ≤ ‖E f m z‖^2
      by_cases hzero : ‖1 - (E f m z)^2‖ = 0
      · rw [hzero, Real.log_zero]; positivity
      · have hh := Real.log_le_sub_one_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero))
        have htri := norm_sub_le (1:ℂ) ((E f m z)^2)
        rw [norm_one, norm_pow] at htri
        linarith
  linarith

theorem pointwise_sum {f m : ℂ → ℂ} (hf : Differentiable ℂ f) (hm : Differentiable ℂ m)
    (hfin : ∀ z, analyticOrderAt f z ≠ ⊤) {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    (hmult : ∀ z, ((S.filter fun i => ρ i = z).card) ≤ analyticOrderNatAt f z)
    (hβ : ∀ i ∈ S, (ρ i).re ≤ 1) {R y : ℝ} (hR : 0 < R) (hc : D f m (jensenCenter y) ≠ 0) :
    (∑ i ∈ S, jensenVerticalWeight R (ρ i) y) ≤
      circleAverage (fun z => ‖E f m z‖^2) (jensenCenter y) R - Real.log ‖D f m (jensenCenter y)‖ := by
  classical
  let c := jensenCenter y
  let U := closedBall c |R|
  let dv := divisor (D f m) U
  let term := fun z : ℂ => (dv z : ℝ)*Real.log (R*‖c-z‖⁻¹)
  have hF : AnalyticOnNhd ℂ f U := fun z _ => hf.analyticAt z
  have hD : AnalyticOnNhd ℂ (D f m) U := fun z _ => analyticD hf hm z
  have hnon (z : ℂ) : 0 ≤ term z := by
    by_cases hz : z ∈ U
    · have hp : (0:ℝ) ≤ dv z := by exact_mod_cast hD.divisor_nonneg z
      by_cases heq : ‖c-z‖=0
      · simp [term,heq]
      · have hd := lt_of_le_of_ne (norm_nonneg _) (Ne.symm heq)
        have hnorm : ‖c-z‖ ≤ R := by simpa only [U, mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hz
        exact mul_nonneg hp (by rw [← div_eq_mul_inv]; exact Real.log_nonneg ((one_le_div hd).mpr hnorm))
    · simp [term, dv, hz]
  have hone (z : ℂ) (hz : z ∈ S.image ρ) :
      ((S.filter (fun i => ρ i = z)).card:ℝ)*jensenVerticalWeight R z y ≤ term z := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hdist : 0 < ‖c - ρ i‖ := zero_lt_one.trans_le (one_le_norm_jensenCenter_sub (hβ i hi) y)
    by_cases hnorm : ‖c - ρ i‖ ≤ R
    · have hmem : ρ i ∈ U := by simpa only [U, mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hnorm
      have hs : divisor f U (ρ i) = (analyticOrderNatAt f (ρ i) : ℤ) := by
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfin (ρ i))
        rw [hF.divisor_apply hmem]
        simp [analyticOrderNatAt, ← hn]
      have hdom := divisor_le_det hf hm (R := R) hc (ρ i)
      change divisor f U (ρ i) ≤ dv (ρ i) at hdom
      rw [hs] at hdom
      have hle : ((S.filter (fun j => ρ j = ρ i)).card : ℝ) ≤ dv (ρ i) := by
        exact_mod_cast (Int.ofNat_le.mpr (hmult _)).trans hdom
      have hlog := Real.log_nonneg ((one_le_div hdist).mpr hnorm)
      have hw : jensenVerticalWeight R (ρ i) y = Real.log (R / ‖c - ρ i‖) := by
        rw [jensenVerticalWeight, Real.log_div hR.ne' hdist.ne'] at *
        exact max_eq_right hlog
      rw [hw]; exact mul_le_mul_of_nonneg_right hle (by simpa [div_eq_mul_inv] using hlog)
    · have hw : jensenVerticalWeight R (ρ i) y = 0 := by
        apply max_eq_left
        have h := Real.log_le_log hR (le_of_not_ge hnorm)
        change Real.log R - Real.log ‖c-ρ i‖ ≤ 0; linarith
      simpa [hw] using hnon (ρ i)
  let V := S.image ρ ∪ (dv.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hsupport : Function.support term ⊆ (V:Set ℂ) := by
    intro z hz
    apply Finset.mem_union_right
    have h : z ∈ dv.support := by
      change dv z ≠ 0
      intro h0
      exact hz (by simp [term,h0])
    simpa only [Set.Finite.mem_toFinset] using h
  apply le_trans _ (jensen_det hf hm hc)
  change _ ≤ ∑ᶠ z, term z
  rw [finsum_eq_finsetSum_of_support_subset term hsupport]
  calc
    _ = ∑ z ∈ S.image ρ, ∑ i ∈ S.filter (fun i => ρ i = z), jensenVerticalWeight R (ρ i) y :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ρ hi) _).symm
    _ = ∑ z ∈ S.image ρ, ((S.filter (fun i => ρ i=z)).card:ℝ)*jensenVerticalWeight R z y := by
      apply Finset.sum_congr rfl
      intro z _
      calc
        _ = ∑ _i ∈ S.filter (fun i => ρ i=z), jensenVerticalWeight R z y :=
          Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
        _ = _ := by simp
    _ ≤ ∑ z ∈ S.image ρ, term z := Finset.sum_le_sum hone
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hnon z)

theorem count_from_slices {f m : ℂ → ℂ} (hf : Differentiable ℂ f) (hm : Differentiable ℂ m)
    (hfin : ∀ z, analyticOrderAt f z ≠ ⊤) {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    (hmult : ∀ z, (S.filter fun i => ρ i = z).card ≤ analyticOrderNatAt f z)
    {σ δ T L C : ℝ} (hσ0 : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1/4) (hT : 3 ≤ T)
    (hβ : ∀ i ∈ S, σ+δ ≤ (ρ i).re) (hβ' : ∀ i ∈ S, (ρ i).re ≤ 1)
    (hγ : ∀ i ∈ S, 4 ≤ (ρ i).im) (hγ' : ∀ i ∈ S, (ρ i).im ≤ T)
    (hcenter : ∀ y ∈ Icc 3 (T+1), D f m (jensenCenter y) ≠ 0 ∧
      -Real.log ‖D f m (jensenCenter y)‖ ≤ C)
    (hslice : ∀ u ∈ Icc σ (4-σ),
      (∫ t in Icc 1 (T+3), ‖E f m ((u:ℂ)+(t:ℂ)*Complex.I)‖^2) ≤ L) :
    (S.card:ℝ)*(2*δ^2/3) ≤ L + (T-2)*C := by
  let R : ℝ := 2-σ
  let F := fun z => ‖E f m z‖^2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R ≤ 3/2 := by dsimp [R]; linarith
  have hY : (3:ℝ) ≤ T+1 := by linarith
  have hF : ContinuousOn F (verticalCircleRectangle R T) := fun z _ =>
    ((analyticE hf hm z).continuousAt.norm.pow 2).continuousWithinAt
  have hiF := integrableOn_circleAverage_vertical hR.le hR1 hF
  have hiC : IntegrableOn (fun _ : ℝ => C) (Icc 3 (T+1)) := integrable_const _
  have hws : Continuous (fun y : ℝ => ∑ i ∈ S, jensenVerticalWeight R (ρ i) y) :=
    continuous_finsetSum _ fun i hi => continuous_jensenVerticalWeight R (hβ' _ hi)
  have hcount := card_mul_jensen_mass_le_integral S ρ hσ0 hσ1 hδ0 hδ1 hβ hβ' hγ hγ'
  rw [intervalIntegral.integral_of_le hY, ← integral_Icc_eq_integral_Ioc] at hcount
  have hpoint (y : ℝ) (hy : y ∈ Icc 3 (T+1)) :
      (∑ i ∈ S, jensenVerticalWeight R (ρ i) y) ≤ circleAverage F (2+(y:ℂ)*Complex.I) R + C := by
    obtain ⟨hnz, hc⟩ := hcenter y hy
    have hh := pointwise_sum hf hm hfin S ρ hmult hβ' hR hnz
    change _ ≤ circleAverage F (jensenCenter y) R + C
    change _ ≤ circleAverage F (jensenCenter y) R - _ at hh
    linarith
  have hcircle : (∫ y in Icc 3 (T+1), circleAverage F (2+(y:ℂ)*Complex.I) R) ≤ L := by
    apply integral_circleAverage_vertical_le hR.le hR1 hT hF (fun z _ => sq_nonneg _)
    intro u hu
    apply hslice u
    simpa only [R, sub_sub_cancel, show (2:ℝ)+(2-σ)=4-σ by ring] using hu
  have hconst : (∫ _ in Icc (3:ℝ) (T+1), C) = (T-2)*C := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]; ring
  calc
    _ ≤ ∫ y in Icc 3 (T+1), ∑ i ∈ S, jensenVerticalWeight R (ρ i) y := hcount
    _ ≤ ∫ y in Icc 3 (T+1), circleAverage F (2+(y:ℂ)*Complex.I) R + C :=
      setIntegral_mono_on (hws.continuousOn.integrableOn_compact isCompact_Icc)
        (hiF.add hiC) measurableSet_Icc hpoint
    _ = (∫ y in Icc 3 (T+1), circleAverage F (2+(y:ℂ)*Complex.I) R) + (T-2)*C := by
      rw [integral_add hiF hiC, hconst]
    _ ≤ _ := add_le_add hcircle le_rfl

theorem character_count_from_slices (χ : OAI.Ostmann.PrimitiveComplexCharacter)
    (m : ℂ → ℂ) (hm : Differentiable ℂ m) {σ δ T L C : ℝ}
    (hσ0 : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/4) (hT : 3 ≤ T)
    (S : Finset ℕ)
    (hβ : ∀ i ∈ S, σ+δ ≤ ((OAI.Ostmann.V1 χ).zeros i).re)
    (hγ : ∀ i ∈ S, 4 ≤ ((OAI.Ostmann.V1 χ).zeros i).im)
    (hγ' : ∀ i ∈ S, ((OAI.Ostmann.V1 χ).zeros i).im ≤ T)
    (hcenter : ∀ y ∈ Icc 3 (T+1), D χ.L m (jensenCenter y) ≠ 0 ∧
      -Real.log ‖D χ.L m (jensenCenter y)‖ ≤ C)
    (hslice : ∀ u ∈ Icc σ (4-σ),
      (∫ t in Icc 1 (T+3), ‖E χ.L m ((u:ℂ)+(t:ℂ)*Complex.I)‖^2) ≤ L) :
    (S.card:ℝ)*(2*δ^2/3) ≤ L+(T-2)*C := by
  exact count_from_slices (fun z => (χ.V4s z).differentiableAt) hm χ.Vz8 S
    (OAI.Ostmann.V1 χ).zeros (OAI.Ostmann.V52 χ S) hσ0 hσ1 hδ0 hδ1 hT hβ
    (fun i _ => ((OAI.Ostmann.V1 χ).in_strip i).2.le) hγ hγ' hcenter hslice

end
end GoldbachCentralSeven.Jensen

end


-- TH8000JensenHeights
section

namespace GoldbachCentralSeven.Jensen
open OAI.Ostmann Finset Set
open scoped Classical ComplexConjugate
noncomputable section

theorem conj_fibre (χ : PrimitiveComplexCharacter) (S : Finset ℕ) (z : ℂ) :
    (S.filter (fun i => conj ((V1 χ).zeros i) = z)).card ≤ analyticOrderNatAt χ.inverse.L z := by
  have hh : S.filter (fun i => conj ((V1 χ).zeros i)=z) =
      S.filter (fun i => (V1 χ).zeros i=conj z) := by
    ext i
    simp only [mem_filter, and_congr_right_iff]
    intro _
    constructor <;> intro h <;> simpa using congrArg conj h
  have hm := χ.V1z8 (conj z)
  rw [Complex.conj_conj] at hm
  rw [hh, analyticOrderNatAt, hm]
  exact V52 χ S (conj z)

theorem crude_height_count (χ : PrimitiveComplexCharacter) (S : Finset ℕ)
    {T : ℝ} (hT : 2 ≤ T) (hβ : ∀ i ∈ S, 1/2 ≤ ((V1 χ).zeros i).re)
    (hγ : ∀ i ∈ S, |((V1 χ).zeros i).im| ≤ T) :
    (S.card:ℝ) ≤ (2*T+3)*(8/Real.log (14/13))*Real.log ((χ.modulus:ℝ)*T) := by
  let b := fun i => ⌊((V1 χ).zeros i).im⌋
  let U := Finset.Icc (-⌈T⌉) ⌈T⌉
  let C := (8/Real.log (14/13))*Real.log ((χ.modulus:ℝ)*T)
  have hc : 0 ≤ C := by
    have hp : 1 ≤ (χ.modulus:ℝ) := by exact_mod_cast χ.positive
    have hlog := Real.log_nonneg (show 1 ≤ (χ.modulus:ℝ)*T by nlinarith)
    have hden := Real.log_pos (by norm_num : (1:ℝ) < 14/13)
    exact mul_nonneg (div_nonneg (by norm_num) hden.le) hlog
  have hb (i : ℕ) (hi : i ∈ S) : b i ∈ U := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hγ i hi)
    have ht := Int.le_ceil T
    refine Finset.mem_Icc.mpr ⟨Int.le_floor.mpr ?_, ?_⟩
    · push_cast; linarith
    · exact_mod_cast ((Int.floor_le ((V1 χ).zeros i).im).trans (hhi.trans ht))
  have hbound (n : ℤ) :
      (((S.filter fun i => b i = n).card):ℝ) ≤ C := by
    by_cases he : (S.filter fun i => b i = n).Nonempty
    · obtain ⟨i, hi⟩ := he
      obtain ⟨hi, hi'⟩ := mem_filter.mp hi
      apply Vn6 χ.modulus χ.positive T hT χ le_rfl _ n
        (fun j hj => hβ j (mem_filter.mp hj).1) (fun j hj => (mem_filter.mp hj).2)
      obtain ⟨hl,hu⟩ := abs_le.mp (hγ i hi)
      dsimp [b] at hi'
      rw [← hi']
      apply abs_le.mpr
      constructor <;> linarith [Int.floor_le ((V1 χ).zeros i).im, Int.lt_floor_add_one ((V1 χ).zeros i).im]
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]; simpa using hc
  have hU : (U.card:ℝ) ≤ 2*T+3 := by
    have hceil : 0 ≤ ⌈T⌉ := Int.ceil_nonneg (by linarith)
    simp only [U, Int.card_Icc, sub_neg_eq_add]
    rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith [Int.ceil_lt_add_one T]
  calc
    _ = ∑ n ∈ U, ((S.filter (fun i => b i = n)).card:ℝ) := by
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise hb)
    _ ≤ ∑ _n ∈ U, C := sum_le_sum fun n _ => hbound n
    _ ≤ (2*T+3)*C := by simpa using mul_le_mul_of_nonneg_right hU hc
    _ = _ := by dsimp [C]; ring

theorem all_heights_from_slices (χ : PrimitiveComplexCharacter)
    {σ δ T L C : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/4)
    (hT : 4 ≤ T)
    (H : ∀ ψ : PrimitiveComplexCharacter, ψ = χ ∨ ψ = χ.inverse → ∃ m : ℂ → ℂ,
      Differentiable ℂ m ∧ (∀ y ∈ Icc 3 (T+1), D ψ.L m (Sidon.jensenCenter y) ≠ 0 ∧
        -Real.log ‖D ψ.L m (Sidon.jensenCenter y)‖ ≤ C) ∧
      ∀ u ∈ Icc σ (4-σ), (∫ t in Icc 1 (T+3), ‖E ψ.L m ((u:ℂ)+(t:ℂ)*Complex.I)‖^2) ≤ L) :
    (((V1 χ).count (σ+δ) T):ℝ)*(2*δ^2/3) ≤
      2*(L+(T-2)*C) + 11*(8/Real.log (14/13))*Real.log ((χ.modulus:ℝ)*4)*(2*δ^2/3) := by
  let Z := V1 χ
  let S := (Z.V14 T).filter (fun i => σ+δ ≤ (Z.zeros i).re)
  let P := S.filter (fun i => 4 ≤ (Z.zeros i).im)
  let R := S.filter (fun i => ¬4 ≤ (Z.zeros i).im)
  let M := R.filter (fun i => (Z.zeros i).im ≤ -4)
  let B := R.filter (fun i => ¬(Z.zeros i).im ≤ -4)
  have hβ (i : ℕ) (h : i ∈ S) := (mem_filter.mp h).2
  have hγ (i : ℕ) (h : i ∈ S) := (Z.V2r T i).mp (mem_filter.mp h).1
  obtain ⟨m, hm, hce, hsl⟩ := H χ (Or.inl rfl)
  have hp : (P.card:ℝ)*(2*δ^2/3) ≤ L+(T-2)*C :=
    character_count_from_slices χ m hm hσ hσ' hδ hδ' (by linarith) P
      (fun i h => hβ i (mem_filter.mp h).1) (fun i h => (mem_filter.mp h).2)
      (fun i h => (abs_le.mp (hγ i (mem_filter.mp h).1)).2) hce hsl
  obtain ⟨n, hn, hc', hs'⟩ := H χ.inverse (Or.inr rfl)
  have hm' : (M.card:ℝ)*(2*δ^2/3) ≤ L+(T-2)*C := by
    apply count_from_slices (fun z => (χ.inverse.V4s z).differentiableAt) hn χ.inverse.Vz8 M
      (fun i => conj (Z.zeros i)) (conj_fibre χ M) hσ hσ' hδ hδ' (by linarith)
    · exact fun i h => hβ i (mem_filter.mp (mem_filter.mp h).1).1
    · intro i _; simpa only [Complex.conj_re] using (Z.in_strip i).2.le
    · intro i h; rw [Complex.conj_im]; linarith [(mem_filter.mp h).2]
    · intro i h; rw [Complex.conj_im]; linarith [(abs_le.mp (hγ i (mem_filter.mp (mem_filter.mp h).1).1)).1]
    · exact hc'
    · exact hs'
  have hb := crude_height_count χ B (T := 4) (by norm_num) (fun i h => by
    dsimp [Z] at *
    linarith [hβ i (mem_filter.mp (mem_filter.mp h).1).1]) (fun i h => by
    obtain ⟨hi, h1⟩ := mem_filter.mp h
    have h2 := (mem_filter.mp hi).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have hS : P.card + M.card + B.card = S.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := S) (p := fun i => 4 ≤ (Z.zeros i).im)
    have h2 := Finset.card_filter_add_card_filter_not (s := R) (p := fun i => (Z.zeros i).im ≤ -4)
    change P.card + R.card = S.card at h1
    change M.card + B.card = R.card at h2
    omega
  change (S.card:ℝ)*_ ≤ _
  rw [← hS]
  push_cast
  nlinarith only [hp,hm',mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2*δ^2/3)]

end
end GoldbachCentralSeven.Jensen

end


-- TH8000JensenDensity
section

namespace GoldbachCentralSeven.Jensen
open OAI.Ostmann Finset Filter Set MeasureTheory
open scoped Classical
noncomputable section

def UniformSliceInput (K T₀ : ℝ) : Prop :=
  ∀ χ : PrimitiveComplexCharacter, ∀ T : ℝ, T₀ ≤ T → ∀ σ₀ : ℝ, 1/2 ≤ σ₀ → σ₀ ≤ 1 →
    ∃ m : ℂ → ℂ, Differentiable ℂ m ∧
      (∀ y ∈ Icc 3 (T+1), D χ.L m (Sidon.jensenCenter y) ≠ 0 ∧
        -Real.log ‖D χ.L m (Sidon.jensenCenter y)‖ ≤ 131072/T) ∧
      ∀ u ∈ Icc σ₀ (4-σ₀),
        (∫ t in Icc 1 (T+3), ‖E χ.L m ((u:ℂ)+(t:ℂ)*Complex.I)‖^2) ≤
        K * (χ.modulus:ℝ)^6 * T^((11/4:ℝ)*(1-σ₀)) * (Real.log T)^9

private theorem shift_power {T : ℝ} (hT : 1 < T) (a σ : ℝ) :
    T^(a*(1-(σ-1/Real.log T))) = Real.exp a * T^(a*(1-σ)) := by
  have hp := zero_lt_one.trans hT
  have hlog := (Real.log_pos hT).ne'
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem uniform_character_density_of_slices {K T₀ : ℝ} (hK : 0 < K) (hs : UniformSliceInput K T₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₁ : ℝ, ∀ (χ : PrimitiveComplexCharacter) (T σ : ℝ),
      T₁ ≤ T → 1/2 ≤ σ → σ ≤ 1 →
      (((V1 χ).count σ T):ℝ) ≤
        C*(χ.modulus:ℝ)^6 * T^((23/8:ℝ)*(1-σ))*(Real.log T)^11 := by
  let J := 8/Real.log (14/13)
  have hJ : 0 < J := div_pos (by norm_num) (Real.log_pos (by norm_num))
  let C₁ := 8*J*Real.exp (23/8)
  let C₂ := 2*K*Real.exp (11/4) + 262144 + 44*J
  refine ⟨C₁+2*C₂, by dsimp [C₁,C₂]; positivity, max T₀ (Real.exp 4), ?_⟩
  intro χ T σ hT₁ hσ hσ'
  have hT₀ := (le_max_left T₀ (Real.exp 4)).trans hT₁
  have hTe := (le_max_right T₀ (Real.exp 4)).trans hT₁
  have hT4 : 4 ≤ T := by linarith [Real.add_one_le_exp (4:ℝ)]
  have hT : 1 < T := by linarith
  have hTp := zero_lt_one.trans hT
  let ℓ := Real.log T
  let ε := 1/ℓ
  let W := (χ.modulus:ℝ)^6
  let P := T^((23/8:ℝ)*(1-σ))
  have hℓ4 : 4 ≤ ℓ := by simpa only [ℓ, Real.log_exp] using Real.log_le_log (Real.exp_pos _) hTe
  have hℓ : 1 ≤ ℓ := by linarith
  have hℓp : 0 < ℓ := by linarith
  have hε : 0 < ε := one_div_pos.mpr hℓp
  have hε4 : ε ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hℓ4
  have hq : 1 ≤ (χ.modulus:ℝ) := by exact_mod_cast χ.positive
  have hW : 1 ≤ W := one_le_pow₀ hq
  have hqW : (χ.modulus:ℝ) ≤ W := by
    simpa only [pow_one] using (pow_le_pow_right₀ hq (by norm_num : 1 ≤ 6))
  have hP : 1 ≤ P := Real.one_le_rpow hT.le (by nlinarith)
  have hWP : 1 ≤ W*P := one_le_mul_of_one_le_of_one_le hW hP
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  change _ ≤ (C₁+2*C₂)*W*P*ℓ^11
  by_cases hlo : σ ≤ 1/2+ε
  · have hTbound : T ≤ Real.exp (23/8)*P := by
      have he : 1 ≤ (23/8:ℝ)*(1-(σ-ε)) := by linarith
      have hb := Real.rpow_le_rpow_of_exponent_le hT.le he
      simpa only [Real.rpow_one, ε, ℓ, shift_power hT, P] using hb
    have hcr := crude_height_count χ ((V1 χ).V14 T |>.filter (fun i => σ ≤ ((V1 χ).zeros i).re))
      (by linarith : 2 ≤ T)
      (fun i hi => hσ.trans (mem_filter.mp hi).2)
      (fun i hi => ((V1 χ).V2r T i).mp (mem_filter.mp hi).1)
    have hlog : Real.log ((χ.modulus:ℝ)*T) ≤ 2*W*ℓ := by
      rw [Real.log_mul (by linarith : (χ.modulus:ℝ) ≠ 0) hTp.ne']
      have hqlog := Real.log_le_sub_one_of_pos (by linarith : 0 < (χ.modulus:ℝ))
      change Real.log (χ.modulus:ℝ)+ℓ ≤ _
      nlinarith only [hqlog,hqW,mul_le_mul_of_nonneg_left hℓ (by linarith : 0 ≤ W),
        mul_le_mul_of_nonneg_right hW hℓp.le]
    change ((V1 χ).count σ T : ℝ) ≤ (2*T+3)*J*Real.log ((χ.modulus:ℝ)*T) at hcr
    calc
      _ ≤ _ := hcr
      _ ≤ (4*(Real.exp (23/8)*P))*J*(2*W*ℓ) := by
        apply mul_le_mul _ hlog (Real.log_nonneg (by nlinarith)) (by positivity)
        apply mul_le_mul_of_nonneg_right _ hJ.le
        linarith
      _ = C₁*W*P*ℓ := by dsimp [C₁]; ring
      _ ≤ (C₁+2*C₂)*W*P*ℓ^11 := by
        gcongr
        · linarith
        · simpa only [pow_one] using (pow_le_pow_right₀ hℓ (by norm_num : 1 ≤ 11))
  · let s := σ-ε
    have hs0 : 1/2 ≤ s := by dsimp [s]; linarith
    have hs1 : s ≤ 1 := by dsimp [s]; linarith
    have hstep := all_heights_from_slices χ hs0 hs1 hε.le hε4 hT4
      (L := K*W*T^((11/4:ℝ)*(1-s))*ℓ^9) (C := 131072/T) (by
        intro ψ hψ
        obtain ⟨m,hm,hc,hsl⟩ := hs ψ T hT₀ s hs0 hs1
        refine ⟨m,hm,hc,?_⟩
        rcases hψ with rfl|rfl
        · exact hsl
        · exact hsl)
    rw [show s+ε=σ by dsimp [s];ring] at hstep
    have hpow : T^((11/4:ℝ)*(1-s)) ≤ Real.exp (11/4)*P := by
      dsimp only [s, ε, ℓ]
      rw [shift_power hT]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_le hT.le (by nlinarith)
    let U := W*P*ℓ^9
    have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hWP (one_le_pow₀ hℓ)
    have hWU : W ≤ U := by
      apply le_trans (le_mul_of_one_le_right (by linarith : 0 ≤ W) hP)
      exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ hℓ)
    have hmain : K*W*T^((11/4:ℝ)*(1-s))*ℓ^9 ≤ (K*Real.exp (11/4))*U := by
      calc
        _ ≤ K*W*(Real.exp (11/4)*P)*ℓ^9 := by gcongr
        _ = _ := by dsimp [U];ring
    have hcenter : (T-2)*(131072/T) ≤ 131072 := by
      rw [mul_div_assoc', div_le_iff₀ hTp]; linarith
    have hlowlog : Real.log ((χ.modulus:ℝ)*4) ≤ 4*U :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hz : 0 ≤ 2*ε^2/3 := by positivity
    have hz1 : 2*ε^2/3 ≤ 1 := by nlinarith only [sq_nonneg (ε-1/4),mul_self_le_mul_self hε.le hε4]
    have hlow : 11*J*Real.log ((χ.modulus:ℝ)*4)*(2*ε^2/3) ≤ 44*J*U := by
      calc
        _ ≤ 11*J*(4*U)*1 := mul_le_mul (mul_le_mul_of_nonneg_left hlowlog (by positivity))
          hz1 hz (by positivity)
        _ = _ := by ring
    have hpay : ((V1 χ).count σ T:ℝ)*(2*ε^2/3) ≤ C₂*U := by
      dsimp only [C₂]
      change _ ≤ 2*(K*W*T^((11/4:ℝ)*(1-s))*ℓ^9+(T-2)*(131072/T))+
        11*J*Real.log ((χ.modulus:ℝ)*4)*(2*ε^2/3) at hstep
      nlinarith only [hstep,hmain,hcenter,hlow,hU]
    have hident : ((V1 χ).count σ T:ℝ) = (3/2:ℝ)*ℓ^2*(((V1 χ).count σ T:ℝ)*(2*ε^2/3)) := by
      dsimp [ε];field_simp
    calc
      _ = _ := hident
      _ ≤ (3/2:ℝ)*ℓ^2*(C₂*U) := mul_le_mul_of_nonneg_left hpay (by positivity)
      _ = (3/2:ℝ)*C₂*W*P*ℓ^11 := by dsimp [U];ring
      _ ≤ (C₁+2*C₂)*W*P*ℓ^11 := by gcongr; linarith

end
end GoldbachCentralSeven.Jensen

end


-- TH8000HybridNearOne
section

namespace GoldbachCentralSeven.Density

theorem individual_small_conductor {u r t : ℝ} (hu : 0 ≤ u) (hr : r ≤ u/256)
    (ht : t ≤ 1/3+1/1024) :
    7*r+((23/8:ℝ)*t-1)*u ≤ -u/128 := by
  have h := mul_le_mul_of_nonneg_right ht hu
  nlinarith only [h,hr,hu]

theorem mixed_larger_conductor {u r t : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/8)
    (hr : u/256 ≤ r) (ht : t ≤ 1/3+1/1024) :
    exponent r t (1-u) ≤ -u/1152 := by
  apply le_of_mul_le_mul_right (a := 1+u) _ (by linarith)
  rw [exponent_identity _ _ _ hu]
  have h1 := mul_le_mul_of_nonpos_right hr (show 5*u-1 ≤ 0 by linarith)
  have h2 := mul_le_mul_of_nonneg_right (by linarith : 3*t-1 ≤ 3/1024) hu
  nlinarith only [h1,h2,hu,sq_nonneg u]

theorem hybrid_near_one_exponent {σ r t : ℝ} (hσ : 7/8 ≤ σ) (hσ' : σ ≤ 1)
    (ht : t ≤ 1/3+1/1024) :
    min (7*r+((23/8:ℝ)*t-1)*(1-σ)) (exponent r t σ) ≤ -(1-σ)/1152 := by
  have hu : 0 ≤ 1-σ := by linarith
  have hu' : 1-σ ≤ 1/8 := by linarith
  by_cases hr : r ≤ (1-σ)/256
  · exact (min_le_left ..).trans ((individual_small_conductor hu hr ht).trans (by linarith))
  · exact (min_le_right ..).trans (by
      simpa only [sub_sub_cancel] using mixed_larger_conductor hu hu' (le_of_not_ge hr) ht)

end GoldbachCentralSeven.Density

end


-- TH8000NearOneBin
section

namespace GoldbachCentralSeven.Density
open Finset Filter OAI.Ostmann
open scoped Classical

theorem individual_weighted_bin {ι : Type*} (F : Finset ι) (R : ι → Finset ℕ)
    (β : ι → ℕ → ℝ) (q : ι → ℕ) (Q : ℕ) {X r T σ w C : ℝ}
    (hX : 1 < X) (hL : 1 ≤ Real.log X) (hC : 0 ≤ C)
    (hT : 2 ≤ T) (hT' : T ≤ X^2) (hσ : 7/8 ≤ σ) (hσ' : σ ≤ 1)
    (hQpos : 1 ≤ Q) (hQu : (Q:ℝ) ≤ X^r) (hQl : X^r ≤ 2*(Q:ℝ))
    (hq : ∀ j ∈ F, Q ≤ 2*q j)
    (hcount : (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
      C*(Q:ℝ)^8*T^((23/8:ℝ)*(1-σ))*(Real.log T)^11) :
    (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w),
      damping X T * X^(β j i-1)/(q j:ℝ)) ≤
      4*C*X^(7*r+((23/8:ℝ)/3-1)*(1-σ)+w)*(3*Real.log X)^13 := by
  have hx := zero_lt_one.trans hX
  have hbase := Real.rpow_pos_of_pos hx r
  have hQ1 : 1 ≤ (Q:ℝ) := by exact_mod_cast hQpos
  let e := (23/8:ℝ)*(1-σ)
  have he : 0 ≤ e := by dsimp [e]; nlinarith
  have he' : e ≤ 1 := by dsimp [e]; nlinarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogTX : Real.log T ≤ 3*Real.log X := by
    have hh := Real.log_le_log (by linarith : 0<T) hT'
    rw [Real.log_pow] at hh; norm_num at hh; linarith
  have hLogs : (Real.log T)^11 ≤ (3*Real.log X)^13 :=
    (pow_le_pow_left₀ hlogT hlogTX 11).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 3*Real.log X) (by decide))
  have hd := damping_nonneg hx.le (by linarith : 0 ≤ T)
  have hp : damping X T*T^e ≤ X^((1/3:ℝ)*e) := by
    simpa only [one_mul, Real.rpow_mul hx.le] using damped_power hx (by linarith) zero_le_one he he'
  have hmod : (Q:ℝ)^8 ≤ X^(8*r) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQu 8
    rw [mul_comm (8:ℝ) r, Real.rpow_mul hx.le, show (8:ℝ) = ((8:ℕ):ℝ) by norm_num,
      Real.rpow_natCast]
    exact hh
  have hcnt : damping X T * (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ)) ≤
      C*X^(8*r+(1/3:ℝ)*e)*(3*Real.log X)^13 := by
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount hd
      _ = C*((Q:ℝ)^8 * (damping X T*T^e))*(Real.log T)^11 := by dsimp [e];ring
      _ ≤ C*(X^(8*r)*X^((1/3:ℝ)*e))*(3*Real.log X)^13 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hmod hp (by positivity)
          (by positivity)) hC) hLogs (pow_nonneg hlogT _) (by positivity)
      _ = _ := by rw [Real.rpow_add hx]
  let K := 4*X^(σ+w-1-r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hk (j : ι) (hj : j ∈ F) (i : ℕ) (hi : β j i ≤ σ+w) : X^(β j i-1)/(q j:ℝ) ≤ K := by
    have hq' : (Q:ℝ) ≤ 2*(q j:ℝ) := by exact_mod_cast hq j hj
    have hqpos : 0 < (q j:ℝ) := by linarith
    have hratio : X^r ≤ 4*(q j:ℝ) := by linarith
    have ha := Real.rpow_le_rpow_of_exponent_le hX.le (sub_le_sub_right hi 1)
    apply (div_le_iff₀ hqpos).mpr
    refine ha.trans ?_
    dsimp [K]
    rw [Real.rpow_sub hx (σ+w-1) r, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hbase]
    nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hx.le (σ+w-1))]
  calc
    _ ≤ ∑ j ∈ F, (damping X T*K)*(((R j).filter (fun i => σ ≤ β j i)).card : ℝ) := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ _i ∈ (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w), damping X T*K := by
          apply sum_le_sum
          intro i hi
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (hk j hj i (mem_filter.mp hi).2.2) hd
        _ ≤ _ := by
          simp only [sum_const,nsmul_eq_mul]
          rw [mul_comm (damping X T*K)]
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hd hK)
          exact_mod_cast card_le_card
            (show (R j).filter (fun i => σ ≤ β j i ∧ β j i ≤ σ+w) ⊆
                (R j).filter (fun i => σ ≤ β j i) from fun i hi =>
              mem_filter.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hi).2.1⟩)
    _ = K * (damping X T * (∑ j ∈ F, (((R j).filter (fun i => σ ≤ β j i)).card : ℝ))) := by
      rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcnt hK
    _ = _ := by
      have hh : 7*r+((23/8:ℝ)/3-1)*(1-σ)+w = σ+w-1-r+(8*r+(1/3)*e) := by dsimp [e]; ring
      rw [hh,Real.rpow_add hx (σ+w-1-r) (8*r+(1/3)*e)]
      dsimp [K]; ring

private theorem individual_joint {r σ : ℝ} (hσ : σ ≤ 1) (hr : r ≤ (1-σ)/256) :
    7*r+((23/8:ℝ)/3-1)*(1-σ) ≤ -r/16-(1-σ)/2048 := by linarith

private theorem mixed_joint {r σ : ℝ} (hσ : 7/8 ≤ σ) (hσ' : σ ≤ 1) (hr : (1-σ)/256 ≤ r) :
    exponent r (1/3) σ ≤ -r/16-(1-σ)/2048 := by
  let u := 1-σ
  have hu : 0 ≤ u := by dsimp [u];linarith
  have hu' : u ≤ 1/8 := by dsimp [u];linarith
  have hmul := mul_le_mul_of_nonpos_right
    (show u/256 ≤ r from hr) (show 5*u-1+(1+u)/16 ≤ 0 by linarith)
  have hi := exponent_identity r (1/3) u hu
  rw [show 1-u=σ by dsimp [u];ring] at hi
  change exponent r (1/3) σ ≤ -r/16-u/2048
  apply le_of_mul_le_mul_right (a := 1+u) _ (by linarith)
  rw [hi]
  nlinarith only [hmul,hu,sq_nonneg u]

theorem hybrid_actual_bin {K T₀ : ℝ} (hK : 0 < K) (hs : Jensen.UniformSliceInput K T₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₁ : ℝ, ∀ (X r T σ w : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      1 < X → 1 ≤ Real.log X → 0 ≤ r → r ≤ 5/32 → T₁ ≤ T → T ≤ X^2 →
      7/8 ≤ σ → σ ≤ 1 → 1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i =>
          σ ≤ ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ σ+w),
          damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
        C*X^(-r/16-(1-σ)/2048+w)*(3*Real.log X)^13 := by
  obtain ⟨A, hA, U, hInd⟩ := Jensen.uniform_character_density_of_slices hK hs
  obtain ⟨B, hB, hMix⟩ := V1f0
  refine ⟨4*(A+B), by positivity, max 2 U, ?_⟩
  intro X r T σ w Q F hX hL hr hr' hT hTX hσ hσ' hQ hQu hQl hF
  have ht := (le_max_left 2 U).trans hT
  have hβ : 1/2 ≤ σ := by linarith
  have hLs : 0 ≤ (3*Real.log X)^13 := by positivity
  by_cases hsmall : r ≤ (1-σ)/256
  · have hcard : (F.card:ℝ) ≤ (Q:ℝ)^2 := by exact_mod_cast V14i F Q (fun χ hχ => (hF χ hχ).1)
    have hcnt :
        (∑ χ ∈ F, ((V1 χ).count σ T:ℝ)) ≤ A*(Q:ℝ)^8*T^((23/8:ℝ)*(1-σ))*(Real.log T)^11 := by
      calc
        _ ≤ ∑ _χ ∈ F, A*(Q:ℝ)^6*T^((23/8:ℝ)*(1-σ))*(Real.log T)^11 := by
          refine sum_le_sum fun χ hχ => (hInd χ T σ ((le_max_right 2 U).trans hT) hβ hσ').trans ?_
          have hc : (χ.modulus:ℝ) ≤ Q := by exact_mod_cast (hF χ hχ).1
          have hl := Real.log_nonneg (by linarith : 1 ≤ T)
          gcongr
        _ = (F.card:ℝ)*(A*(Q:ℝ)^6*T^((23/8:ℝ)*(1-σ))*(Real.log T)^11) := by simp
        _ ≤ (Q:ℝ)^2*(A*(Q:ℝ)^6*T^((23/8:ℝ)*(1-σ))*(Real.log T)^11) := by
          have hl := Real.log_nonneg (by linarith : 1 ≤ T)
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring
    refine (individual_weighted_bin F (fun χ => (V1 χ).V14 T) (fun χ i => ((V1 χ).zeros i).re)
      PrimitiveComplexCharacter.modulus Q hX hL hA.le ht hTX hσ hσ' hQ hQu hQl
      (fun χ hχ => (hF χ hχ).2) hcnt (w := w)).trans ?_
    apply mul_le_mul_of_nonneg_right _ hLs
    apply mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hX.le
      (add_le_add (individual_joint hσ' hsmall) le_rfl)) <;> positivity
  · refine (weighted_bin F (fun χ => (V1 χ).V14 T) (fun χ i => ((V1 χ).zeros i).re)
      PrimitiveComplexCharacter.modulus Q hX hB.le hr hr' ht hTX hβ hσ' hQ hQu hQl
      (fun χ hχ => (hF χ hχ).2) (hMix Q hQ T σ ht hβ hσ' F (fun χ hχ => (hF χ hχ).1)) (w := w)).trans ?_
    apply mul_le_mul_of_nonneg_right _ hLs
    apply mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hX.le
      (add_le_add (mixed_joint hσ hσ' (le_of_not_ge hsmall)) le_rfl)) <;> positivity

end GoldbachCentralSeven.Density

end


-- THHighZerosAssembly
section

namespace GoldbachCentralSeven.Density
open Finset Filter OAI.Ostmann

private lemma mesh_log_cost {X : ℝ} (hx : 1 < X) :
    X^(1/Real.log X) = Real.exp 1 := by
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hx)]
  congr 1
  field_simp [ne_of_gt (Real.log_pos hx)]

lemma combine_strip {ι : Type*} (F : Finset ι) (R : ι → Finset ℕ)
    (β m : ι → ℕ → ℝ) {X lo hi C v : ℝ}
    (hx : 1 < X) (hc : 0 ≤ C) (hlo : lo ≤ hi) (hlen : hi-lo ≤ 1)
    (hm : ∀ j i, 0 ≤ m j i)
    (hb : ∀ σ : ℝ, lo ≤ σ → σ ≤ hi →
      (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i =>
        σ ≤ β j i ∧ β j i ≤ σ+1/Real.log X), m j i) ≤
          C*X^(v+1/Real.log X)*(3*Real.log X)^13) :
    (∑ j ∈ F, ∑ i ∈ (R j).filter (fun i => lo ≤ β j i ∧ β j i ≤ hi), m j i) ≤
      (Real.exp 1*C)*(1+Real.log X)*X^v*(3*Real.log X)^13 := by
  have hL := Real.log_pos hx
  have hp := lt_trans zero_lt_one hx
  have hh := sum_mesh F R β m (w:=1/Real.log X) (by positivity) hlo hm
    (show 0≤C*X^(v+1/Real.log X)*(3*Real.log X)^13 by positivity) hb
  have hmesh : (hi-lo)/(1/Real.log X) ≤ Real.log X := by
    rw [div_div_eq_mul_div,div_one]
    simpa using mul_le_mul_of_nonneg_right hlen hL.le
  refine hh.trans ?_
  calc
    _ ≤ (1+Real.log X)*(C*X^(v+1/Real.log X)*(3*Real.log X)^13) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by rw [Real.rpow_add hp,mesh_log_cost hx]; ring

theorem actual_middle_all_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r T : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      1 < X → 0 ≤ r → r ≤ 5/32 → 2 ≤ T → T ≤ X^2 →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i =>
        1/2 ≤ ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ 7/8),
        damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          C*(1+Real.log X)*X^(-(1/1024:ℝ))*(3*Real.log X)^13 := by
  obtain ⟨K,hK,hden⟩ := V1f0
  refine ⟨Real.exp 1*(4*K),by positivity,?_⟩
  intro X r T Q F hx hr hr' ht ht' hQ hQu hQl hF
  have hp := zero_lt_one.trans hx
  have hl := Real.log_pos hx
  apply combine_strip (C:=4*K) _ _ _ _ hx (by positivity) (by norm_num) (by norm_num)
    (fun χ i => div_nonneg (mul_nonneg (damping_nonneg hp.le (by linarith)) (by positivity))
      (Nat.cast_nonneg _))
  intro σ hs hs'
  have h := weighted_bin F (fun χ => (V1 χ).V14 T) (fun χ i => ((V1 χ).zeros i).re)
    PrimitiveComplexCharacter.modulus Q (w:=1/Real.log X) hx hK.le hr hr' ht ht' hs (by linarith)
    hQ hQu hQl (fun χ hχ => (hF χ hχ).2) (hden Q hQ T σ ht hs (by linarith) F
      (fun χ hχ => (hF χ hχ).1))
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx.le (by
      have he := medium_strip_margin (t:=(1/3:ℝ)) hr hr' (by norm_num) hs hs'
      linarith)) (by positivity)) (by positivity))

theorem actual_near_one_all_heights {K T₀ : ℝ} (hK : 0 < K)
    (hs : Jensen.UniformSliceInput K T₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₁ : ℝ, ∀ (X r T δ : ℝ) (Q : ℕ)
      (F : Finset PrimitiveComplexCharacter), 1 < X → 1 ≤ Real.log X →
      0 ≤ r → r ≤ 5/32 → T₁ ≤ T → T ≤ X^2 → 0 ≤ δ → δ ≤ 1/8 →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i =>
        7/8 ≤ ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ 1-δ),
        damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          C*(1+Real.log X)*X^(-r/16-δ/2048)*(3*Real.log X)^13 := by
  obtain ⟨A,hA,U,hb⟩ := hybrid_actual_bin hK hs
  refine ⟨Real.exp 1*A,by positivity,max 2 U,?_⟩
  intro X r T δ Q F hx hl hr hr' ht ht' hd hd' hQ hQu hQl hF
  have hp := zero_lt_one.trans hx
  have ht0 : 0 ≤ T := by linarith [(le_max_left 2 U).trans ht]
  have hlog := Real.log_pos hx
  apply combine_strip (C:=A) _ _ _ _ hx hA.le (by linarith) (by linarith)
    (fun χ i => div_nonneg (mul_nonneg (damping_nonneg hp.le ht0) (by positivity)) (Nat.cast_nonneg _))
  intro σ hσlo hσhi
  refine (hb X r T σ (1/Real.log X) Q F hx hl hr hr' ((le_max_right _ _).trans ht)
    ht' hσlo (by linarith) hQ hQu hQl hF).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hA.le) (by positivity)

theorem actual_low_all_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r T : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      2 ≤ X → 0 ≤ r → r ≤ 5/32 → 2 ≤ T → T ≤ X^2 →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ ((V1 χ).V14 T).filter (fun i => ((V1 χ).zeros i).re ≤ 1/2),
        damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          C*X^(-(1/96:ℝ))*Real.log X := by
  let K := 32 / Real.log (14/13:ℝ)
  have hK : 0 < K := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨16*K,by positivity,?_⟩
  intro X r T Q F hX hr hr' ht ht' hQ hQu hQl hF
  have hx : 1 < X := by linarith
  have hp : 0 < X := by linarith
  have hl := Real.log_pos hx
  have hD := damping_nonneg hp.le (by linarith : 0 ≤ T)
  have hqr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQX : (Q:ℝ) ≤ X := hQu.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : r ≤ 1))
  have hlog : Real.log ((Q:ℝ)*(T+2)) ≤ 4*Real.log X := by
    calc
      _ ≤ Real.log (X^4) := Real.log_le_log (by positivity) (by
        calc
          (Q:ℝ)*(T+2) ≤ X*(X^2+2) := mul_le_mul hQX (by linarith) (by linarith) hp.le
          _ ≤ X*(X^3) := by gcongr; nlinarith [mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hX)]
          _ = X^4 := by ring)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hcnt := V15e K hK.le (fun χ U hU => (V1 χ).Vd8 (V52 χ) U hU)
    Q hQ T (by linarith) F (fun χ hχ => (hF χ hχ).1)
  let W := damping X T * X^(-(1/2:ℝ)) * 2/(Q:ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hrow (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∑ i ∈ ((V1 χ).V14 T).filter (fun i => ((V1 χ).zeros i).re ≤ 1/2),
        damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          W*((V1 χ).count 0 T:ℝ) := by
    rw [ComplexZeroEnumeration.Vgd]
    calc
      _ ≤ ∑ _i ∈ ((V1 χ).V14 T).filter (fun i => ((V1 χ).zeros i).re ≤ 1/2), W := by
        apply sum_le_sum
        intro i hi
        have hq : (Q:ℝ) ≤ 2*(χ.modulus:ℝ) := by exact_mod_cast (hF χ hχ).2
        have hqpos : 0 < (χ.modulus:ℝ) := by exact_mod_cast χ.positive
        have hpow := Real.rpow_le_rpow_of_exponent_le hx.le
          (show ((V1 χ).zeros i).re-1 ≤ -(1/2:ℝ) by linarith [(mem_filter.mp hi).2])
        dsimp [W]
        apply (div_le_div_iff₀ hqpos (by positivity : 0 < (Q:ℝ))).mpr
        calc
          _ ≤ (damping X T*X^(-(1/2:ℝ)))*Q := by gcongr
          _ ≤ _ := by
            have h := mul_le_mul_of_nonneg_left hq
              (mul_nonneg hD (Real.rpow_nonneg hp.le (-(1/2:ℝ))))
            linarith
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul]
        rw [mul_comm W]; gcongr
        exact filter_subset _ _
  have hdamp : damping X T*(T+1) ≤ 2*X^(1/3:ℝ) := by
    dsimp [damping]
    calc
      _ ≤ X^(1/3:ℝ)/T*(T+1) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
      _ ≤ X^(1/3:ℝ)/T*(2*T) := by gcongr; linarith
      _ = _ := by field_simp
  have hpow : X^(-(1/2:ℝ))*(Q:ℝ)*X^(1/3:ℝ) ≤ X^(-(1/96:ℝ)) := by
    calc
      _ ≤ X^(-(1/2:ℝ))*X^r*X^(1/3:ℝ) := by gcongr
      _ = X^(-(1/2:ℝ)+r+1/3) := by rw [Real.rpow_add hp, Real.rpow_add hp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  calc
    _ ≤ ∑ χ ∈ F, W*((V1 χ).count 0 T:ℝ) := sum_le_sum hrow
    _ = W*(∑ χ ∈ F, ((V1 χ).count 0 T:ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcnt hW
    _ = (2*K)*(X^(-(1/2:ℝ))*(Q:ℝ))*(damping X T*(T+1))*Real.log ((Q:ℝ)*(T+2)) := by
      dsimp [W]; field_simp <;> ring
    _ ≤ (2*K)*(X^(-(1/2:ℝ))*(Q:ℝ))*(2*X^(1/3:ℝ))*(4*Real.log X) := by
      have hpos : 0 ≤ Real.log ((Q:ℝ)*(T+2)) := Real.log_nonneg (by nlinarith)
      gcongr
    _ = (16*K)*(X^(-(1/2:ℝ))*(Q:ℝ)*X^(1/3:ℝ))*Real.log X := by ring
    _ ≤ _ := by gcongr

end GoldbachCentralSeven.Density

end


-- Sidon.NumberTheory.VerticalL2Interpolation
section

noncomputable section

open Set MeasureTheory Complex Complex.HadamardThreeLines
open scoped Topology

namespace Sidon

theorem continuousOn_compact_integral {S : Set ℂ} (hS : IsClosed S)
    {K : Set ℝ} (hK : IsCompact K) {F : ℂ → ℝ → ℂ}
    (hF : ContinuousOn F.uncurry (S ×ˢ univ)) :
    ContinuousOn (fun z => ∫ t in K, F z t) S := by
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  have hc : Continuous (fun p : S × ℝ => F p.1.val p.2) := by
    change Continuous (F.uncurry ∘ (fun p : S × ℝ => (p.1.val, p.2)))
    exact hF.comp_continuous (by fun_prop)
      (fun p => ⟨p.1.property, mem_univ _⟩)
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun x : S => fun t : ℝ => F x.val t) hc hK
  exact continuousOn_iff_continuous_domRestrict.mpr hi

theorem differentiableOn_compact_integral {U : Set ℂ} (hU : IsOpen U)
    {K : Set ℝ} (hK : IsCompact K) {F F' : ℂ → ℝ → ℂ}
    (hF : ContinuousOn F.uncurry (U ×ˢ univ))
    (hF' : ContinuousOn F'.uncurry (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t ∈ K, HasDerivAt (fun w => F w t) (F' z t) z) :
    DifferentiableOn ℂ (fun z => ∫ t in K, F z t) U := by
  intro z hz
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (F w) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw, mem_univ t⟩)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (F' w) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw, mem_univ t⟩)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  have hcp := (isCompact_closedBall z r).prod hK
  have hcont : ContinuousOn F'.uncurry (Metric.closedBall z r ×ˢ K) := by
    apply hF'.mono
    intro p hp
    exact ⟨hball hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hcp.bddAbove_image hcont.norm
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (F := F) (F' := F') (bound := fun _ => M)
    (Metric.ball_mem_nhds z hr)
    (Filter.Eventually.mono (hU.mem_nhds hz) (fun w hw => (hc w hw).aestronglyMeasurable))
    ((hc z hz).continuousOn.integrableOn_compact hK)
    (hc' z hz).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
      intro w hw
      exact hM (show ‖F' w t‖ ∈ (fun p : ℂ × ℝ => ‖F' p.1 p.2‖) ''
        (Metric.closedBall z r ×ˢ K) from
        ⟨(w, t), ⟨Metric.mem_closedBall.mpr hw.le, ht⟩, rfl⟩))
    (integrableOn_const hK.measure_ne_top)
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
      intro w hw
      exact hd w (hball (Metric.mem_closedBall.mpr hw.le)) t ht)
  exact hderiv.2.differentiableAt.differentiableWithinAt

def verticalPairing (Φ : ℂ → ℂ) (g : ℝ → ℂ) (c d : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc c d, Φ (z + (t : ℂ) * I) * star (g t)

theorem continuousOn_verticalPairing_integrand {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) :
    ContinuousOn (fun p : ℂ × ℝ => Φ (p.1 + (p.2 : ℂ) * I) * star (g p.2))
      (verticalClosedStrip a b ×ˢ univ) := by
  apply ContinuousOn.mul
  · apply hΦ.comp (by fun_prop)
    intro p hp
    simpa only [verticalClosedStrip, mem_preimage, add_re, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero] using hp.1
  · exact (continuous_star.comp (hg.comp continuous_snd)).continuousOn

theorem continuousOn_verticalPairing {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    ContinuousOn (verticalPairing Φ g c d) (verticalClosedStrip a b) :=
  continuousOn_compact_integral (isClosed_Icc.preimage continuous_re) isCompact_Icc
    (continuousOn_verticalPairing_integrand hΦ hg)

set_option maxHeartbeats 2000000 in
theorem diffContOnCl_verticalPairing {Φ : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    DiffContOnCl ℂ (verticalPairing Φ g c d) (verticalStrip a b) := by
  have hsub : verticalStrip a b ×ˢ (univ : Set ℝ) ⊆
      verticalClosedStrip a b ×ˢ univ := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  constructor
  · apply differentiableOn_compact_integral
      (F := fun z t => Φ (z + (t : ℂ) * I) * star (g t))
      (F' := fun z t => deriv Φ (z + (t : ℂ) * I) * star (g t))
      (isOpen_Ioo.preimage continuous_re) isCompact_Icc
      ((continuousOn_verticalPairing_integrand hΦ.continuousOn hg).mono hsub)
      ((continuousOn_verticalPairing_integrand hΦ.deriv.continuousOn hg).mono hsub)
    intro z hz t _
    have hzt : z + (t : ℂ) * I ∈ verticalClosedStrip a b := by
      simpa [verticalClosedStrip] using
        (show a ≤ z.re ∧ z.re ≤ b from ⟨hz.1.le, hz.2.le⟩)
    simpa using (((hΦ _ hzt).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).add_const ((t : ℂ) * I))).mul_const (star (g t))
  · have hcl : closure (verticalStrip a b) = verticalClosedStrip a b := by
      rw [verticalStrip, closure_preimage_re, closure_Ioo hab.ne]
      rfl
    rw [hcl]
    exact continuousOn_verticalPairing hΦ.continuousOn hg c d

theorem norm_compact_pairing_le {K : Set ℝ} (hK : IsCompact K) {f g : ℝ → ℂ}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hf₂ : Integrable (fun t => ‖f t‖ ^ 2)) :
    ‖∫ t in K, f t * star (g t)‖ ≤
      (∫ t : ℝ, ‖f t‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ t in K, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hfm : MemLp f 2 (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable hK.measurableSet)).mpr
      (hf₂.mono_measure Measure.restrict_le_self)
  have hgm : MemLp g 2 (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm (hg.aestronglyMeasurable hK.measurableSet)).mpr
      (hg.norm.pow 2 |>.integrableOn_compact hK)
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hfm)
    (by simpa only [ENNReal.ofReal_ofNat] using hgm)
  norm_num only [Real.rpow_two] at hholder
  calc
    _ ≤ ∫ t in K, ‖f t * star (g t)‖ := norm_integral_le_integral_norm _
    _ = ∫ t in K, ‖f t‖ * ‖g t‖ := by simp only [norm_mul, norm_star]
    _ ≤ _ := hholder
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow (integral_nonneg (fun t => sq_nonneg _))
          (setIntegral_le_integral hf₂ (Filter.Eventually.of_forall (fun t => sq_nonneg _)))
          (by norm_num)
      · positivity

def verticalL2 (Φ : ℂ → ℂ) (u : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2

theorem verticalL2_nonneg (Φ : ℂ → ℂ) (u : ℝ) : 0 ≤ verticalL2 Φ u :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem vertical_translate (z : ℂ) (t : ℝ) :
    z + (t : ℂ) * I = (z.re : ℂ) + ((z.im + t : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem integral_sq_vertical_translate (Φ : ℂ → ℂ) (z : ℂ) :
    (∫ t : ℝ, ‖Φ (z + (t : ℂ) * I)‖ ^ 2) = verticalL2 Φ z.re := by
  have heq : (fun t : ℝ => ‖Φ (z + (t : ℂ) * I)‖ ^ 2) =
      (fun t : ℝ => ‖Φ ((z.re : ℂ) + ((z.im + t : ℝ) : ℂ) * I)‖ ^ 2) := by
    funext t
    rw [vertical_translate z t]
  rw [heq]
  exact integral_add_left_eq_self (μ := volume)
    (fun t : ℝ => ‖Φ ((z.re : ℂ) + (t : ℂ) * I)‖ ^ 2) z.im

theorem norm_verticalPairing_le {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip a b) :
    ‖verticalPairing Φ g c d z‖ ≤ (verticalL2 Φ z.re) ^ (1 / 2 : ℝ) *
      (∫ t in Icc c d, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hc : Continuous (fun t : ℝ => Φ (z + (t : ℂ) * I)) := by
    apply hΦ.comp_continuous (by fun_prop)
    intro t
    simpa [verticalClosedStrip] using hz
  have hi : Integrable (fun t : ℝ => ‖Φ (z + (t : ℂ) * I)‖ ^ 2) := by
    convert (hsq z.re hz).comp_add_left z.im using 1
    funext t
    rw [vertical_translate z t]
  have hh := norm_compact_pairing_le (K := Icc c d) isCompact_Icc
    hc.continuousOn hg.continuousOn hi
  rw [integral_sq_vertical_translate] at hh
  exact hh

theorem bddAbove_verticalPairing {Φ : ℂ → ℂ} {a b : ℝ}
    (hΦ : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    BddAbove ((norm ∘ verticalPairing Φ g c d) '' verticalClosedStrip a b) := by
  obtain ⟨M, hM⟩ := hΦ
  obtain ⟨G, hG⟩ := isCompact_Icc.bddAbove_image (hg.norm.continuousOn :
    ContinuousOn (fun t => ‖g t‖) (Icc c d))
  refine ⟨(max M 0 * max G 0) * volume.real (Icc c d), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro t ht
  rw [norm_mul, norm_star]
  apply mul_le_mul
  · apply (hM ?_).trans (le_max_left _ _)
    refine ⟨z + (t : ℂ) * I, ?_, rfl⟩
    simpa [verticalClosedStrip] using hz
  · exact (hG (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · positivity
  · positivity

theorem norm_verticalPairing_interpolate {Φ : ℂ → ℂ} {a b σ A B : ℝ}
    (hab : a < b) (hσ : σ ∈ Icc a b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    (hbound : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : verticalL2 Φ a ≤ A ^ 2) (hright : verticalL2 Φ b ≤ B ^ 2)
    {g : ℝ → ℂ} (hg : Continuous g) (c d : ℝ) :
    ‖verticalPairing Φ g c d (σ : ℂ)‖ ≤
      (A * (∫ t in Icc c d, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ)) ^
          (1 - (σ - a) / (b - a)) *
      (B * (∫ t in Icc c d, ‖g t‖ ^ 2) ^ (1 / 2 : ℝ)) ^
          ((σ - a) / (b - a)) := by
  apply norm_le_interp_of_mem_verticalClosedStrip' hab hσ
    (diffContOnCl_verticalPairing hab hΦ hg c d)
    (bddAbove_verticalPairing hbound hg c d)
  · intro z hz
    have hh := norm_verticalPairing_le hΦ.continuousOn hsq hg c d
      (z := z) (by simpa only [verticalClosedStrip, mem_preimage, mem_Icc] using
        (show a ≤ z.re ∧ z.re ≤ b from
        ⟨le_of_eq hz.symm, (le_of_eq hz).trans hab.le⟩))
    change z.re = a at hz
    rw [hz] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg
      (fun t => sq_nonneg _)) _)
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_left hA).mpr hleft
  · intro z hz
    have hh := norm_verticalPairing_le hΦ.continuousOn hsq hg c d
      (z := z) (by simpa only [verticalClosedStrip, mem_preimage, mem_Icc] using
        (show a ≤ z.re ∧ z.re ≤ b from
        ⟨hab.le.trans (le_of_eq hz.symm), le_of_eq hz⟩))
    change z.re = b at hz
    rw [hz] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg
      (fun t => sq_nonneg _)) _)
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_left hB).mpr hright

theorem self_test_interpolation {J A B θ : ℝ} (hJ : 0 ≤ J) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : J ≤ (A * J ^ (1 / 2 : ℝ)) ^ (1 - θ) *
      (B * J ^ (1 / 2 : ℝ)) ^ θ) :
    J ≤ (A ^ (1 - θ) * B ^ θ) ^ 2 := by
  by_cases hzero : J = 0
  · rw [hzero]
    positivity
  have hpos : 0 < Real.sqrt J := Real.sqrt_pos.mpr (lt_of_le_of_ne hJ (Ne.symm hzero))
  have hsq := Real.sq_sqrt hJ
  rw [← Real.sqrt_eq_rpow] at h
  have hfactor : (A * Real.sqrt J) ^ (1 - θ) * (B * Real.sqrt J) ^ θ =
      (A ^ (1 - θ) * B ^ θ) * Real.sqrt J := by
    rw [Real.mul_rpow hA hpos.le, Real.mul_rpow hB hpos.le]
    calc
      _ = (A ^ (1 - θ) * B ^ θ) *
          (Real.sqrt J ^ (1 - θ) * Real.sqrt J ^ θ) := by ring
      _ = _ := by rw [← Real.rpow_add hpos]; simp
  rw [hfactor] at h
  have hroot : Real.sqrt J ≤ A ^ (1 - θ) * B ^ θ := by nlinarith
  have hC : 0 ≤ A ^ (1 - θ) * B ^ θ := by positivity
  nlinarith

theorem verticalPairing_self (Φ : ℂ → ℂ) (σ c d : ℝ) :
    ‖verticalPairing Φ (fun t => Φ ((σ : ℂ) + (t : ℂ) * I)) c d (σ : ℂ)‖ =
      ∫ t in Icc c d, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have heq : verticalPairing Φ (fun t => Φ ((σ : ℂ) + (t : ℂ) * I)) c d (σ : ℂ) =
      Complex.ofReal (∫ t in Icc c d, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
    unfold verticalPairing
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem verticalL2_le_interpolation {Φ : ℂ → ℂ} {a b σ A B : ℝ}
    (hab : a < b) (hσ : σ ∈ Icc a b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    (hbound : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : verticalL2 Φ a ≤ A ^ 2) (hright : verticalL2 Φ b ≤ B ^ 2) :
    verticalL2 Φ σ ≤
      (A ^ (1 - (σ - a) / (b - a)) * B ^ ((σ - a) / (b - a))) ^ 2 := by
  have hc : Continuous (fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * I)) := by
    apply hΦ.continuousOn.comp_continuous (by fun_prop)
    intro t
    simpa [verticalClosedStrip] using hσ
  have hfinite (c d : ℝ) : (∫ t in Icc c d, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (A ^ (1 - (σ - a) / (b - a)) * B ^ ((σ - a) / (b - a))) ^ 2 := by
    have hh := norm_verticalPairing_interpolate hab hσ hΦ hbound hsq
      hA hB hleft hright hc c d
    rw [verticalPairing_self] at hh
    exact self_test_interpolation (integral_nonneg (fun _ => sq_nonneg _)) hA hB hh
  have hmono : Monotone (fun L : ℝ => Icc (-L) L) := by
    intro L M hLM
    exact Icc_subset_Icc (neg_le_neg hLM) hLM
  have hunion : (⋃ L : ℝ, Icc (-L) L) = univ := by
    apply eq_univ_of_forall
    intro t
    exact mem_iUnion.mpr ⟨|t|, neg_abs_le t, le_abs_self t⟩
  have ht := tendsto_setIntegral_of_monotone
    (μ := volume) (f := fun t : ℝ => ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (fun L : ℝ => measurableSet_Icc) hmono
    (by rw [hunion]; simpa using hsq σ hσ)
  have hlim : Filter.Tendsto
      (fun L : ℝ => ∫ t in Icc (-L) L, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      Filter.atTop (𝓝 (verticalL2 Φ σ)) := by
    simpa only [hunion, Measure.restrict_univ, verticalL2] using ht
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun L => hfinite (-L) L))

theorem verticalL2_logConvex {Φ : ℂ → ℂ} {a b σ : ℝ}
    (hab : a < b) (hσ : σ ∈ Icc a b)
    (hΦ : AnalyticOnNhd ℂ Φ (verticalClosedStrip a b))
    (hbound : BddAbove ((norm ∘ Φ) '' verticalClosedStrip a b))
    (hsq : ∀ u ∈ Icc a b, Integrable (fun t : ℝ =>
      ‖Φ ((u : ℂ) + (t : ℂ) * I)‖ ^ 2)) :
    verticalL2 Φ σ ≤
      verticalL2 Φ a ^ (1 - (σ - a) / (b - a)) *
        verticalL2 Φ b ^ ((σ - a) / (b - a)) := by
  have hJa := verticalL2_nonneg Φ a
  have hJb := verticalL2_nonneg Φ b
  have hh := verticalL2_le_interpolation hab hσ hΦ hbound hsq
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (le_of_eq (Real.sq_sqrt hJa).symm) (le_of_eq (Real.sq_sqrt hJb).symm)
  rw [mul_pow, Real.rpow_pow_comm (Real.sqrt_nonneg _),
    Real.rpow_pow_comm (Real.sqrt_nonneg _), Real.sq_sqrt hJa, Real.sq_sqrt hJb] at hh
  exact hh

end Sidon

end
end


-- Sidon.NumberTheory.GaussianCumulative
section

noncomputable section

open Set MeasureTheory

namespace Sidon

def gaussianAnnulus (R : ℝ) (n : ℕ) : Set ℝ :=
  {t | Nat.floor (|t| / R) = n}

theorem measurableSet_gaussianAnnulus (R : ℝ) (n : ℕ) :
    MeasurableSet (gaussianAnnulus R n) := by
  unfold gaussianAnnulus
  have hm : Measurable (fun t : ℝ => |t| / R) := by fun_prop
  exact (Nat.measurable_floor.comp hm) (measurableSet_singleton n)

theorem gaussianAnnulus_bounds {R t : ℝ} (hR : 0 < R) {n : ℕ}
    (ht : t ∈ gaussianAnnulus R n) :
    (n : ℝ) * R ≤ |t| ∧ |t| ≤ ((n : ℝ) + 1) * R := by
  have hnonneg : 0 ≤ |t| / R := div_nonneg (abs_nonneg _) hR.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one (|t| / R)
  change Nat.floor (|t| / R) = n at ht
  rw [ht] at hlo hhi
  exact ⟨(le_div_iff₀ hR).mp hlo, ((div_lt_iff₀ hR).mp hhi).le⟩

theorem gaussianAnnulus_subset {R : ℝ} (hR : 0 < R) (n : ℕ) :
    gaussianAnnulus R n ⊆ Icc (-(((n : ℝ) + 1) * R)) (((n : ℝ) + 1) * R) := by
  intro t ht
  exact abs_le.mp (gaussianAnnulus_bounds hR ht).2

theorem gaussianAnnulus_cover (R : ℝ) : (⋃ n : ℕ, gaussianAnnulus R n) = univ := by
  apply eq_univ_of_forall
  intro t
  exact mem_iUnion.mpr ⟨Nat.floor (|t| / R), rfl⟩

theorem gaussianAnnulus_disjoint (R : ℝ) :
    Pairwise (fun m n => Disjoint (gaussianAnnulus R m) (gaussianAnnulus R n)) := by
  intro m n hmn
  apply disjoint_left.mpr
  intro t htm htn
  exact hmn (htm.symm.trans htn)

theorem gaussian_weight_le_on_annulus {R t : ℝ} (hR : 0 < R) {n : ℕ}
    (ht : t ∈ gaussianAnnulus R n) :
    Real.exp (-2 * t ^ 2 / R ^ 2) ≤ Real.exp (-(n : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hlo := (gaussianAnnulus_bounds hR ht).1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : (0 : ℝ) < R ^ 2 := sq_pos_of_pos hR
  apply (div_le_iff₀ hr).mpr
  have hsq := mul_self_le_mul_self (mul_nonneg hn hR.le) hlo
  rw [← sq, ← sq, sq_abs, mul_pow] at hsq
  by_cases hzero : n = 0
  · rw [hzero]
    norm_num only [Nat.cast_zero, zero_mul, neg_zero]
    nlinarith [sq_nonneg t]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hh : (n : ℝ) ≤ 2 * n ^ 2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hh hr.le
    nlinarith

theorem summable_gaussianAnnulus_majorant :
    Summable (fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) := by
  have h₂ := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 1)
  have h₁ := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h₀ := Real.summable_exp_neg_nat
  have hh := h₂.add ((h₁.mul_left 4).add (h₀.mul_left 4))
  convert hh using 1
  funext n
  simp only [neg_mul, one_mul, pow_one]
  ring

theorem gaussian_cumulative_polynomial_le {R N p : ℝ} (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (((n : ℝ) + 1) * R + N) * (1 + ((n : ℝ) + 1) * R) ^ p ≤
      (R + N) * R ^ p * ((n : ℝ) + 2) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlinear : ((n : ℝ) + 1) * R + N ≤ ((n : ℝ) + 2) * (R + N) := by
    nlinarith
  have hbase : 1 + ((n : ℝ) + 1) * R ≤ ((n : ℝ) + 2) * R := by nlinarith
  have hpower : (1 + ((n : ℝ) + 1) * R) ^ p ≤ ((n : ℝ) + 2) * R ^ p := by
    calc
      _ ≤ (((n : ℝ) + 2) * R) ^ p := Real.rpow_le_rpow (by positivity) hbase hp
      _ = ((n : ℝ) + 2) ^ p * R ^ p := Real.mul_rpow (by positivity) (by linarith)
      _ ≤ ((n : ℝ) + 2) * R ^ p := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n + 2) hp1
  calc
    _ ≤ (((n : ℝ) + 2) * (R + N)) * (((n : ℝ) + 2) * R ^ p) :=
      mul_le_mul hlinear hpower (by positivity) (by positivity)
    _ = _ := by ring

theorem integral_gaussianAnnulus_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgnonneg : ∀ t, 0 ≤ g t) {K R N p : ℝ} (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcum : ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc (-U) U, g t) ≤ K * (U + N) * (1 + U) ^ p) (n : ℕ) :
    (∫ t in gaussianAnnulus R n, Real.exp (-2 * t ^ 2 / R ^ 2) * g t) ≤
      (K * (R + N) * R ^ p) *
        (Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) := by
  have hR0 : 0 < R := by linarith
  let U : ℝ := ((n : ℝ) + 1) * R
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hsub : gaussianAnnulus R n ⊆ Icc (-U) U := gaussianAnnulus_subset hR0 n
  have hgi : IntegrableOn g (Icc (-U) U) := hg.continuousOn.integrableOn_compact isCompact_Icc
  have hwi : IntegrableOn (fun t => Real.exp (-2 * t ^ 2 / R ^ 2) * g t)
      (gaussianAnnulus R n) := by
    have hc : Continuous (fun t => Real.exp (-2 * t ^ 2 / R ^ 2) * g t) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hmass : (∫ t in gaussianAnnulus R n, g t) ≤ ∫ t in Icc (-U) U, g t := by
    exact setIntegral_mono_set hgi (Filter.Eventually.of_forall hgnonneg) hsub.eventuallySubset
  calc
    _ ≤ ∫ t in gaussianAnnulus R n, Real.exp (-(n : ℝ)) * g t := by
      apply setIntegral_mono_on hwi ((hgi.mono_set hsub).const_mul _)
        (measurableSet_gaussianAnnulus R n)
      intro t ht
      exact mul_le_mul_of_nonneg_right (gaussian_weight_le_on_annulus hR0 ht) (hgnonneg t)
    _ = Real.exp (-(n : ℝ)) * ∫ t in gaussianAnnulus R n, g t := integral_const_mul _ _
    _ ≤ Real.exp (-(n : ℝ)) * (K * (U + N) * (1 + U) ^ p) := by
      gcongr
      exact hmass.trans (hcum U hU)
    _ ≤ Real.exp (-(n : ℝ)) *
        (K * ((R + N) * R ^ p * ((n : ℝ) + 2) ^ 2)) := by
      have hh := mul_le_mul_of_nonneg_left
        (gaussian_cumulative_polynomial_le hR hN hp hp1 n) hK
      simpa only [U, mul_assoc] using
        mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (-(n : ℝ)))
    _ = _ := by ring

def gaussianCumulativeConstant : ℝ :=
  1 + ∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2

theorem gaussianCumulativeConstant_pos : 0 < gaussianCumulativeConstant := by
  unfold gaussianCumulativeConstant
  have hh : 0 ≤ ∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2 :=
    tsum_nonneg (fun _ => by positivity)
  linarith

theorem gaussian_integral_of_cumulative {g : ℝ → ℝ} (hg : Continuous g)
    (hgnonneg : ∀ t, 0 ≤ g t) {K R N p : ℝ} (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcum : ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc (-U) U, g t) ≤ K * (U + N) * (1 + U) ^ p) :
    Integrable (fun t : ℝ => Real.exp (-2 * t ^ 2 / R ^ 2) * g t) ∧
      (∫ t : ℝ, Real.exp (-2 * t ^ 2 / R ^ 2) * g t) ≤
        gaussianCumulativeConstant * K * (R + N) * R ^ p := by
  let w : ℝ → ℝ := fun t => Real.exp (-2 * t ^ 2 / R ^ 2) * g t
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hwnonneg (t : ℝ) : 0 ≤ w t := mul_nonneg (Real.exp_nonneg _) (hgnonneg t)
  have hnorm : (fun t => ‖w t‖) = w :=
    funext (fun t => Real.norm_of_nonneg (hwnonneg t))
  have hi (n : ℕ) : IntegrableOn w (gaussianAnnulus R n) := by
    exact (hw.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (gaussianAnnulus_subset (by linarith : 0 < R) n)
  have hfactor : 0 ≤ K * (R + N) * R ^ p := by positivity
  have hmajorant := summable_gaussianAnnulus_majorant.mul_left (K * (R + N) * R ^ p)
  have hs : Summable (fun n : ℕ => ∫ t in gaussianAnnulus R n, w t) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg hwnonneg) _ hmajorant
    intro n
    exact integral_gaussianAnnulus_le hg hgnonneg hK hR hN hp hp1 hcum n
  have hiunion := integrableOn_iUnion_of_summable_integral_norm hi (by
    simpa only [hnorm] using hs)
  have higlobal : Integrable w := by
    simpa only [gaussianAnnulus_cover, integrableOn_univ] using hiunion
  refine ⟨higlobal, ?_⟩
  have heq : (∫ t : ℝ, w t) = ∑' n : ℕ, ∫ t in gaussianAnnulus R n, w t := by
    simpa only [gaussianAnnulus_cover, Measure.restrict_univ] using
      (integral_iUnion (measurableSet_gaussianAnnulus R) (gaussianAnnulus_disjoint R) hiunion)
  calc
    _ = _ := heq
    _ ≤ ∑' n : ℕ, (K * (R + N) * R ^ p) *
        (Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) :=
      Summable.tsum_le_tsum
        (integral_gaussianAnnulus_le hg hgnonneg hK hR hN hp hp1 hcum) hs hmajorant
    _ = (K * (R + N) * R ^ p) *
        (∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) := tsum_mul_left
    _ ≤ (K * (R + N) * R ^ p) * gaussianCumulativeConstant := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      unfold gaussianCumulativeConstant
      linarith
    _ = _ := by ring

end Sidon

end
end


-- THAnalyticWindow
section

/- Gaussian interpolation adapted from TomasOrtega/Sidon,
revision 735de6d7c67b81a28b1e07e3f2661dbc17bb89d6.
The function being localized is entire and has no pole in the strip. -/
namespace CentralWindowInterpolation
open Set MeasureTheory Complex.HadamardThreeLines Sidon
open scoped Topology

noncomputable def G (F : ℂ → ℂ) (R : ℝ) (s : ℂ) :=
  F s * Complex.exp ((s / (R : ℂ)) ^ 2)

theorem norm_G (F : ℂ → ℂ) {R : ℝ} (hR : R ≠ 0) (s : ℂ) :
    ‖G F R s‖ = ‖F s‖ * Real.exp ((s.re^2-s.im^2)/R^2) := by
  rw [G, norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.mul_re, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

theorem quadratic_mul_gaussian_le {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (1 + t ^ 2) * Real.exp (-b * t ^ 2) ≤ 1 + 1 / b := by
  have hx : b * t ^ 2 * Real.exp (-b * t ^ 2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right
      (show b * t ^ 2 ≤ Real.exp (b * t ^ 2) by linarith [Real.add_one_le_exp (b * t ^ 2)])
      (Real.exp_nonneg (-b * t ^ 2))
    simpa only [← Real.exp_add, add_neg_cancel_left, Real.exp_zero, mul_neg,
      neg_mul, add_neg_cancel] using hh
  have hterm : t ^ 2 * Real.exp (-b * t ^ 2) ≤ 1 / b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith
  have he : Real.exp (-b * t ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  nlinarith

noncomputable def envelope (K R : ℝ) := K * Real.exp 3 * (1+2*R^2)

def QuadGrowth (F : ℂ → ℂ) (K : ℝ) : Prop :=
  ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → ‖F s‖ ≤ K*(1+s.im^2)

theorem decay {F : ℂ → ℂ} {K R : ℝ} (hK : 0 ≤ K) (hF : QuadGrowth F K)
    (hR : 1 ≤ R) {s : ℂ} (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 3/2) :
    ‖G F R s‖ ≤ envelope K R * Real.exp (-s.im^2/(2*R^2)) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hu : s.re ^ 2 / R ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  have hquad := quadratic_mul_gaussian_le (b := 1 / (2 * R ^ 2)) (by positivity) s.im
  have hq : (1 + s.im ^ 2) * Real.exp (-s.im ^ 2 / (2 * R ^ 2)) ≤ 1 + 2 * R ^ 2 := by
    have he : -(1 / (2 * R ^ 2)) * s.im ^ 2 = -s.im ^ 2 / (2 * R ^ 2) := by ring
    have he' : 1 / (1 / (2 * R ^ 2)) = 2 * R ^ 2 := by simp
    rw [he, he'] at hquad
    exact hquad
  rw [norm_G F hR0.ne']
  calc
    _ ≤ ((K) * (1 + s.im ^ 2)) *
        Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2) := by
      gcongr
      exact hF s hs hs'
    _ = (K) * Real.exp (s.re ^ 2 / R ^ 2) *
        ((1 + s.im ^ 2) * Real.exp (-s.im ^ 2 / (2 * R ^ 2))) *
          Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by
      have he : (s.re ^ 2 - s.im ^ 2) / R ^ 2 = s.re ^ 2 / R ^ 2 +
          (-s.im ^ 2 / (2 * R ^ 2)) + (-s.im ^ 2 / (2 * R ^ 2)) := by ring
      rw [he, Real.exp_add, Real.exp_add]
      ring
    _ ≤ (K) * Real.exp 3 * (1 + 2 * R ^ 2) *
        Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by gcongr
    _ = _ := rfl

theorem diff_G {F : ℂ → ℂ} (hf : Differentiable ℂ F) (R : ℝ) :
    Differentiable ℂ (G F R) := by unfold G; fun_prop

theorem bounded_G {F : ℂ → ℂ} {K R a b : ℝ} (hK : 0 ≤ K) (hF : QuadGrowth F K)
    (hR : 1 ≤ R) (ha : 1/2 ≤ a) (hb : b ≤ 3/2) :
    BddAbove ((norm ∘ G F R) '' verticalClosedStrip a b) := by
  refine ⟨envelope K R, ?_⟩
  rintro _ ⟨s,hs,rfl⟩
  apply (decay hK hF hR (ha.trans hs.1) (hs.2.trans hb)).trans
  apply mul_le_of_le_one_right (by unfold envelope; positivity)
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))

theorem G_integrable {F : ℂ → ℂ} {K R σ : ℝ} (hf : Differentiable ℂ F) (hK : 0 ≤ K)
    (hF : QuadGrowth F K) (hR : 1 ≤ R) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 3/2) :
    Integrable (fun t : ℝ => ‖G F R ((σ:ℂ)+t*Complex.I)‖^2) := by
  have hR0 : 0 < R := by linarith
  have hc : Continuous (fun t : ℝ => G F R ((σ:ℂ)+t*Complex.I)) :=
    (diff_G hf R).continuous.comp (by fun_prop)
  have hi := (integrable_exp_neg_mul_sq (b := 1/R^2) (by positivity)).const_mul
    (envelope K R ^ 2)
  apply hi.mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := decay hK hF hR (s := (σ:ℂ)+t*Complex.I)
    (by simpa using hσ) (by simpa using hσ')
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [mul_pow, ← Real.exp_nat_mul, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one,
    zero_mul, add_zero, zero_add] at hsquare
  convert hsquare using 1 <;> congr 1 <;> ring

private theorem G_sq (F : ℂ → ℂ) {R σ t : ℝ} (hR : 1 ≤ R) (hσ : 1/2≤σ) (hσ' : σ≤3/2) :
    ‖G F R ((σ:ℂ)+t*Complex.I)‖^2 ≤ Real.exp 6 *
      (Real.exp (-2*t^2/R^2) * ‖F ((σ:ℂ)+t*Complex.I)‖^2) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R^2 := by nlinarith
  have hu : 2*σ^2/R^2 ≤ 6 := (div_le_iff₀ (sq_pos_of_pos hR0)).2 (by nlinarith)
  rw [norm_G F hR0.ne', mul_pow, ← Real.exp_nat_mul]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    mul_one, one_mul, sub_self, add_zero, zero_add, Nat.cast_ofNat]
  calc
    _ = ‖F ((σ:ℂ)+t*Complex.I)‖^2 * (Real.exp (2*σ^2/R^2)*Real.exp (-2*t^2/R^2)) := by
      rw [← Real.exp_add]; congr 2 <;> ring
    _ ≤ _ := by
      calc
        _ ≤ ‖F ((σ:ℂ)+t*Complex.I)‖^2 * (Real.exp 6*Real.exp (-2*t^2/R^2)) := by gcongr
        _ = _ := by ring

theorem vertical_of_cumulative {F : ℂ → ℂ} {K R σ N L p : ℝ}
    (hf : Differentiable ℂ F) (hK : 0 ≤ K) (hF : QuadGrowth F K)
    (hR : 1≤R) (hσ : 1/2 ≤σ) (hσ' : σ≤3/2) (hN : 0≤N)
    (hL : 0≤L) (hp : 0≤p) (hp' : p≤1)
    (hcum : ∀ U : ℝ, 0 ≤ U → (∫ t in Icc (-U) U, ‖F ((σ:ℂ)+t*Complex.I)‖^2) ≤
      L*(U+N)*(1+U)^p) :
    verticalL2 (G F R) σ ≤ Real.exp 6 * gaussianCumulativeConstant * L * (R+N) * R^p := by
  have hc : Continuous (fun t : ℝ => ‖F ((σ:ℂ)+t*Complex.I)‖^2) :=
    ((hf.continuous.comp (by fun_prop)).norm.pow 2)
  obtain ⟨hi,hb⟩ := gaussian_integral_of_cumulative hc (fun _ => sq_nonneg _) hL hR hN hp hp' hcum
  unfold verticalL2
  calc
    _ ≤ ∫ t : ℝ, Real.exp 6 * (Real.exp (-2*t^2/R^2) * ‖F ((σ:ℂ)+t*Complex.I)‖^2) := by
      apply integral_mono (G_integrable hf hK hF hR hσ hσ') (hi.const_mul _)
      exact fun t => G_sq F hR hσ hσ'
    _ ≤ _ := by rw [integral_const_mul]; nlinarith [mul_le_mul_of_nonneg_left hb (Real.exp_pos 6).le]

end CentralWindowInterpolation

end


-- THAnalyticInterpolation
section

/- The scalar interpolation and rounding estimates are adapted from
TomasOrtega/Sidon, MollifierOptimization.lean, revision
735de6d7c67b81a28b1e07e3f2661dbc17bb89d6. -/
namespace CentralWindowInterpolation
open Set MeasureTheory Sidon Complex.HadamardThreeLines
open scoped Topology
theorem mollifier_interpolation_power_bound {R L B σ₀ σ : ℝ}
    (hR : 1 ≤ R) (hlog : 2 ≤ Real.log R) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ ≤ 1) (hσ : σ₀ ≤ σ)
    (hσ1 : σ ≤ 1 + 1 / Real.log R) :
    (L * Real.log R * R ^ ((11 : ℝ) / 8)) ^
        (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
      (B * Real.log R ^ 8) ^
        ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) ≤
      L * B * Real.exp (11 / 4) * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  have hR0 : 0 < R := by linarith
  have hlog0 : 0 < Real.log R := by linarith
  let θ := (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)
  have hden : 0 < 1 + 1 / Real.log R - 1 / 2 := by
    linarith [one_div_pos.mpr hlog0]
  have hθ : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one hden).mpr (by linarith)
  have hq : 0 ≤ 1 - θ := by linarith
  have hq1 : 1 - θ ≤ 1 := by linarith
  have hqbound : 1 - θ ≤ 2 * (1 - σ₀ + 1 / Real.log R) := by
    have heq : 1 - θ = (1 + 1 / Real.log R - σ) /
        (1 + 1 / Real.log R - 1 / 2) := by
      dsimp [θ]
      rw [one_sub_div hden.ne']
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ (1 + 1 / Real.log R - σ) / (1 / 2) := by
        apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
        linarith [one_div_pos.mpr hlog0]
      _ ≤ _ := by norm_num; linarith
  have hfactor : 1 ≤ L * Real.log R := by nlinarith
  have hleft : (L * Real.log R * R ^ ((11 : ℝ) / 8)) ^ (1 - θ) ≤
      (L * Real.log R) * R ^ (((11 : ℝ) / 8) * (1 - θ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR0.le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hfactor hq1) (by positivity)
  have hright : (B * Real.log R ^ 8) ^ θ ≤ B * Real.log R ^ 8 := by
    apply Real.rpow_le_self_of_one_le _ hθ1
    have hp : 1 ≤ Real.log R ^ 8 := one_le_pow₀ (by linarith : 1 ≤ Real.log R)
    nlinarith
  have hpower : R ^ (((11 : ℝ) / 8) * (1 - θ)) ≤
      R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.exp (11 / 4) := by
    calc
      _ ≤ R ^ ((11 / 4 : ℝ) * (1 - σ₀) + (11 / 4 : ℝ) / Real.log R) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        have hh := mul_le_mul_of_nonneg_left hqbound (by norm_num : (0 : ℝ) ≤ 11 / 8)
        convert hh using 1 <;> ring
      _ = _ := by
        rw [Real.rpow_add hR0]
        congr 1
        rw [Real.rpow_def_of_pos hR0]
        congr 1
        field_simp
  change (_ ^ (1 - θ) * _ ^ θ) ≤ _
  calc
    _ ≤ ((L * Real.log R) * R ^ (((11 : ℝ) / 8) * (1 - θ))) *
        (B * Real.log R ^ 8) := mul_le_mul hleft hright (by positivity) (by positivity)
    _ ≤ ((L * Real.log R) * (R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.exp (11 / 4))) *
        (B * Real.log R ^ 8) := by gcongr
    _ = _ := by ring

theorem ceil_mollifier_parameters {R : ℝ} (hR : 1 ≤ R) (hlog : 2 ≤ Real.log R) :
    1 ≤ ⌈R⌉₊ ∧ R ≤ (⌈R⌉₊ : ℝ) ∧ (⌈R⌉₊ : ℝ) ≤ 2 * R ∧
      1 + Real.log (⌈R⌉₊ : ℝ) ≤ 2 * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hRN : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hN1 : (1 : ℝ) ≤ ⌈R⌉₊ := hR.trans hRN
  have hNR : (⌈R⌉₊ : ℝ) ≤ 2 * R := by
    have hh := Nat.ceil_lt_add_one hR0.le
    linarith
  refine ⟨by exact_mod_cast hN1, hRN, hNR, ?_⟩
  have hlogN := Real.log_le_log (by linarith : (0 : ℝ) < ⌈R⌉₊) hNR
  rw [Real.log_mul (by norm_num) hR0.ne'] at hlogN
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

theorem interval_le_vertical {F : ℂ → ℂ} {R σ K : ℝ} (hf : Differentiable ℂ F)
    (hK : 0≤K) (hF : QuadGrowth F K) (hR : 1≤R) (hσ : 1/2≤σ) (hσ' : σ≤3/2) :
    (∫ t in Icc 1 R, ‖F ((σ:ℂ)+t*Complex.I)‖^2) ≤ Real.exp 2 * verticalL2 (G F R) σ := by
  have hr := (show 0<(1:ℝ) by norm_num).trans_le hR
  have hc : Continuous (fun t : ℝ => F ((σ:ℂ)+t*Complex.I)) := hf.continuous.comp (by fun_prop)
  have hig := G_integrable hf hK hF hR hσ hσ'
  have hpt (t : ℝ) (ht : t ∈ Icc 1 R) :
      ‖F ((σ:ℂ)+t*Complex.I)‖^2 ≤ Real.exp 2 * ‖G F R ((σ:ℂ)+t*Complex.I)‖^2 := by
    rw [norm_G F hr.ne', mul_pow, ← Real.exp_nat_mul]
    have he : 1 ≤ Real.exp (2:ℝ) * Real.exp (2*((σ^2-t^2)/R^2)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hsq := sq_le_sq₀ (show 0≤t by linarith [ht.1]) hr.le |>.mpr ht.2
      have hh : -1 ≤ (σ^2-t^2)/R^2 := (le_div_iff₀ (sq_pos_of_pos hr)).2 (by nlinarith [sq_nonneg σ])
      linarith
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_self, add_zero, zero_add, Nat.cast_ofNat]
    linarith only [mul_le_mul_of_nonneg_right he (sq_nonneg ‖F ((σ:ℂ)+t*Complex.I)‖)]
  calc
    _ ≤ ∫ t in Icc 1 R, Real.exp 2 * ‖G F R ((σ:ℂ)+t*Complex.I)‖^2 := by
      apply setIntegral_mono_on (hc.norm.pow 2 |>.continuousOn.integrableOn_compact isCompact_Icc)
        (hig.const_mul _).integrableOn measurableSet_Icc hpt
    _ = _ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hig (Filter.Eventually.of_forall fun _ => sq_nonneg _)) (Real.exp_pos _).le

theorem strip_bound {F : ℂ → ℂ} {K R σ₀ u L B : ℝ}
    (hf : Differentiable ℂ F) (hK : 0≤K) (hF : QuadGrowth F K)
    (hR : 1≤R) (hlog : 2 ≤ Real.log R) (hL : 1≤L) (hB : 1≤B)
    (hσ₀ : 1/2≤σ₀) (hσ₀' : σ₀≤1) (hu : σ₀≤u) (hu' : u≤1+1/Real.log R)
    (hl : verticalL2 (G F R) (1/2) ≤ L * Real.log R * R^(11/8:ℝ))
    (hb : verticalL2 (G F R) (1+1/Real.log R) ≤ B*(Real.log R)^8) :
    (∫ t in Icc 1 R, ‖F ((u:ℂ)+t*Complex.I)‖^2) ≤
      Real.exp 2 * (L*B*Real.exp (11/4)*(R^((11/4:ℝ)*(1-σ₀)))*(Real.log R)^9) := by
  have hδp : 0 < 1/Real.log R := by positivity
  have hδh : 1/Real.log R ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hlog
  have hui : u ∈ Icc (1/2:ℝ) (1+1/Real.log R) := ⟨hσ₀.trans hu,hu'⟩
  have hI := interval_le_vertical hf hK hF hR hui.1 (by linarith)
  apply hI.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have he := verticalL2_logConvex (Φ := G F R) (by linarith : (1/2:ℝ)<1+1/Real.log R) hui
    (fun _ _ => (diff_G hf R).analyticAt _)
    (bounded_G hK hF hR le_rfl (by linarith))
    (fun x hx => G_integrable hf hK hF hR hx.1 (by linarith [hx.2]))
  apply he.trans
  apply le_trans _ (mollifier_interpolation_power_bound hR hlog hL hB hσ₀ hσ₀' hu hu')
  have hden : 0 < 1+1/Real.log R-1/2 := by linarith
  have htheta : 0 ≤ (u-1/2)/(1+1/Real.log R-1/2) := div_nonneg (by linarith [hui.1]) hden.le
  have htheta' : 0 ≤ 1-(u-1/2)/(1+1/Real.log R-1/2) :=
    sub_nonneg.mpr ((div_le_one hden).mpr (by linarith [hui.2]))
  exact mul_le_mul (Real.rpow_le_rpow (verticalL2_nonneg ..) hl htheta')
    (Real.rpow_le_rpow (verticalL2_nonneg ..) hb htheta)
    (Real.rpow_nonneg (verticalL2_nonneg ..) _) (Real.rpow_nonneg (by positivity) _)

end CentralWindowInterpolation

end


-- Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DerivativePowerExponents
noncomputable section

def alpha (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (k + 2) - 2)

def amp (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ k

def beta (k : ℕ) : ℝ := 1 - amp k

theorem denominator_ge_two (k : ℕ) : 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  have h : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  linarith

theorem alpha_pos (k : ℕ) : 0 < alpha k := by
  unfold alpha
  have h := denominator_ge_two k
  positivity

theorem alpha_le_half (k : ℕ) : alpha k ≤ 1 / 2 := by
  have h := denominator_ge_two k
  unfold alpha
  apply (div_le_iff₀ (by linarith : 0 < (2 : ℝ) ^ (k + 2) - 2)).mpr
  linarith

theorem alpha_zero : alpha 0 = 1 / 2 := by norm_num [alpha]

theorem alpha_succ (k : ℕ) : alpha (k + 1) = alpha k / (2 + 2 * alpha k) := by
  have h := denominator_ge_two k
  unfold alpha
  rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hB : -1 + (2 : ℝ) ^ k * 4 ≠ 0 := by nlinarith
  field_simp
  ring_nf
  field_simp

theorem alpha_balance (k : ℕ) : alpha k * (1 - 2 * alpha (k + 1)) = 2 * alpha (k + 1) := by
  rw [alpha_succ]
  have h := alpha_pos k
  field_simp
  ring

theorem amp_pos (k : ℕ) : 0 < amp k := by
  unfold amp
  positivity

theorem amp_le_one (k : ℕ) : amp k ≤ 1 := by
  unfold amp
  exact (div_le_one (by positivity : 0 < (2 : ℝ) ^ k)).mpr (one_le_pow₀ (by norm_num))

theorem amp_zero : amp 0 = 1 := by norm_num [amp]

theorem amp_succ (k : ℕ) : amp (k + 1) = amp k / 2 := by
  unfold amp
  rw [pow_succ]
  ring

theorem beta_nonneg (k : ℕ) : 0 ≤ beta k := sub_nonneg.mpr (amp_le_one k)

theorem beta_zero : beta 0 = 0 := by norm_num [beta, amp]

theorem beta_succ (k : ℕ) : beta (k + 1) = (beta k + 1) / 2 := by
  unfold beta
  rw [amp_succ]
  ring

end
end RiemannGaussian.DerivativePowerExponents

end


-- Sidon.NumberTheory.RiemannGaussian.DerivativeRecursionBudget
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DerivativeRecursionBudget
noncomputable section
open scoped Classical

abbrev Cutoffs := ℕ → ℕ → ℝ → ℝ → ℕ

def shiftCount (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) : ℕ := κ k L ℓ A + 1

theorem shiftCount_pos (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) :
    0 < shiftCount κ k L ℓ A := Nat.zero_lt_succ _

def budget (κ : Cutoffs) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, L, ℓ, A =>
      if 0 < ℓ ∧ ℓ ≤ 1 then
        min (L : ℝ) ((A * L * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
          (3 + 2 * Real.pi))
      else L
  | k + 1, L, ℓ, A =>
      let H := shiftCount κ k L ℓ A
      min (L : ℝ) (Real.sqrt ((((L : ℝ) + H - 1) * ((H : ℝ) * L +
        2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
          budget κ k L (((j : ℝ) + 1) * ℓ) A)) / (H : ℝ) ^ 2))

theorem nonneg (κ : Cutoffs) (k L : ℕ) (ℓ : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ budget κ k L ℓ A := by
  cases k with
  | zero =>
    rw [budget]
    split_ifs with h
    · apply le_min (Nat.cast_nonneg _)
      have hℓ := h.1
      positivity
    · positivity
  | succ k =>
    rw [budget]
    exact le_min (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

theorem le_length (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) :
    budget κ k L ℓ A ≤ L := by
  cases k with
  | zero =>
    rw [budget]
    split_ifs
    · exact min_le_left _ _
    · rfl
  | succ k =>
    rw [budget]
    exact min_le_left _ _

theorem base_le (κ : Cutoffs) (L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget κ 0 L ℓ A ≤
      (A * L * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
        (3 + 2 * Real.pi) := by
  rw [budget]
  by_cases hℓ1 : ℓ ≤ 1
  · rw [ite_eq_left ⟨hℓ, hℓ1⟩]
    exact min_le_right _ _
  · rw [ite_eq_right (fun h ↦ hℓ1 h.2)]
    have hs1 : 1 ≤ Real.sqrt ℓ := Real.one_le_sqrt.mpr (by linarith)
    have hA0 : 0 ≤ A := by linarith
    have hL : (L : ℝ) ≤ A * L := by nlinarith [Nat.cast_nonneg (α := ℝ) L]
    have hp := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hA0 (Nat.cast_nonneg (α := ℝ) L))
    simp only [mul_one] at hp
    calc
      _ ≤ A * L * Real.sqrt ℓ := hL.trans hp
      _ = (A * L * Real.sqrt ℓ / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul
        · exact le_add_of_nonneg_right (by positivity)
        · linarith
        · positivity
        · positivity

end
end RiemannGaussian.DerivativeRecursionBudget

end


-- Sidon.NumberTheory.RiemannGaussian.AnalyticDerivativeCutoff
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.AnalyticDerivativeCutoff
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DerivativeRecursionBudget
def ideal (k : ℕ) (ℓ : ℝ) : ℝ := ℓ ^ (-2 * alpha (k + 1))

def cutoffs : Cutoffs := fun k _ ℓ _ ↦ ⌈ideal k ℓ⌉₊ - 1

theorem ideal_pos (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < ideal k ℓ :=
  Real.rpow_pos_of_pos hℓ _

theorem count_eq (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    shiftCount cutoffs k L ℓ A = ⌈ideal k ℓ⌉₊ := by
  unfold shiftCount cutoffs
  exact Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr (ideal_pos k hℓ))

theorem one_le_ideal (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    1 ≤ ideal k ℓ :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hℓ hℓ1 (by nlinarith [alpha_pos (k + 1)])

theorem ideal_le_count (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    ideal k ℓ ≤ (shiftCount cutoffs k L ℓ A : ℝ) := by
  rw [count_eq k L hℓ A]
  exact Nat.le_ceil _

theorem count_le_twice (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (A : ℝ) :
    (shiftCount cutoffs k L ℓ A : ℝ) ≤ 2 * ideal k ℓ := by
  rw [count_eq k L hℓ A]
  have h := Nat.ceil_lt_add_one (ideal_pos k hℓ).le
  linarith [one_le_ideal k hℓ hℓ1]

theorem length_lt_ideal (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ)
    (hL : L < shiftCount cutoffs k L ℓ A) : (L : ℝ) < ideal k ℓ := by
  rw [count_eq k L hℓ A] at hL
  exact Nat.lt_ceil.mp hL

theorem ideal_mul (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ideal k ℓ * ℓ = ℓ ^ (1 - 2 * alpha (k + 1)) := by
  rw [show 1 - 2 * alpha (k + 1) = -2 * alpha (k + 1) + 1 by ring,
    Real.rpow_add hℓ, Real.rpow_one]
  rfl

theorem ideal_positive_power (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (ideal k ℓ * ℓ) ^ alpha k = ℓ ^ (2 * alpha (k + 1)) := by
  rw [ideal_mul k hℓ, ← Real.rpow_mul hℓ.le]
  rw [mul_comm, alpha_balance]

theorem ideal_negative_power (k : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (ideal k ℓ * ℓ) ^ (-alpha k) = ideal k ℓ := by
  rw [Real.rpow_neg (mul_nonneg (ideal_pos k hℓ).le hℓ.le), ideal_positive_power k hℓ,
    ← Real.rpow_neg hℓ.le]
  unfold ideal
  congr 1
  ring

theorem count_positive_power (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (A : ℝ) :
    ((shiftCount cutoffs k L ℓ A : ℝ) * ℓ) ^ alpha k ≤
      2 * ℓ ^ (2 * alpha (k + 1)) := by
  have hc := count_le_twice k L hℓ hℓ1 A
  have htwo : (2 : ℝ) ^ alpha k ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show alpha k ≤ 1 by linarith [alpha_le_half k])
  calc
    _ ≤ (2 * (ideal k ℓ * ℓ)) ^ alpha k := by
      apply Real.rpow_le_rpow (by positivity) _ (alpha_pos k).le
      nlinarith [mul_le_mul_of_nonneg_right hc hℓ.le]
    _ = (2 : ℝ) ^ alpha k * ℓ ^ (2 * alpha (k + 1)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg (ideal_pos k hℓ).le hℓ.le), ideal_positive_power k hℓ]
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)

theorem count_negative_power (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    ((shiftCount cutoffs k L ℓ A : ℝ) * ℓ) ^ (-alpha k) ≤ ideal k ℓ := by
  rw [← ideal_negative_power k hℓ]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos (ideal_pos k hℓ) hℓ)
    (mul_le_mul_of_nonneg_right (ideal_le_count k L hℓ A) hℓ.le)
    (by linarith [alpha_pos k])

theorem inv_count_le (k L : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (A : ℝ) :
    1 / (shiftCount cutoffs k L ℓ A : ℝ) ≤ ℓ ^ (2 * alpha (k + 1)) := by
  calc
    _ ≤ 1 / ideal k ℓ := one_div_le_one_div_of_le (ideal_pos k hℓ) (ideal_le_count k L hℓ A)
    _ = _ := by
      unfold ideal
      rw [show -2 * alpha (k + 1) = -(2 * alpha (k + 1)) by ring,
        Real.rpow_neg hℓ.le, one_div, inv_inv]

end
end RiemannGaussian.AnalyticDerivativeCutoff

end


-- Sidon.NumberTheory.RiemannGaussian.DerivativePowerEnvelope
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DerivativePowerEnvelope
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativeRecursionBudget
def mainTerm (k : ℕ) (L ℓ A : ℝ) : ℝ := A ^ amp k * L * ℓ ^ alpha k

def errorTerm (k : ℕ) (L ℓ : ℝ) : ℝ := L ^ beta k * ℓ ^ (-alpha k)

def envelope (k : ℕ) (L ℓ A : ℝ) : ℝ := 32 * (mainTerm k L ℓ A + errorTerm k L ℓ)

theorem main_nonneg (k : ℕ) {L ℓ A : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    0 ≤ mainTerm k L ℓ A := by unfold mainTerm; positivity

theorem error_nonneg (k : ℕ) {L ℓ : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) :
    0 ≤ errorTerm k L ℓ := by unfold errorTerm; positivity

theorem main_square (k : ℕ) (L : ℝ) {ℓ A : ℝ} (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    mainTerm (k + 1) L ℓ A ^ 2 = A ^ amp k * L ^ 2 * ℓ ^ (2 * alpha (k + 1)) := by
  unfold mainTerm
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hA, ← Real.rpow_mul_natCast hℓ, amp_succ]
  have hp : amp k / 2 * (2 : ℝ) = amp k := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hp, mul_comm (alpha (k + 1)) 2]

set_option maxHeartbeats 2000000 in
theorem error_square (k : ℕ) {L ℓ : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) :
    errorTerm (k + 1) L ℓ ^ 2 = L ^ (beta k + 1) * ideal k ℓ := by
  unfold errorTerm ideal
  rw [mul_pow, ← Real.rpow_mul_natCast hL, ← Real.rpow_mul_natCast hℓ, beta_succ]
  congr 1 <;> congr 1 <;> ring

theorem main_ge_length (k : ℕ) {L ℓ A : ℝ} (hL : 0 ≤ L) (hℓ : 1 ≤ ℓ) (hA : 1 ≤ A) :
    L ≤ mainTerm k L ℓ A := by
  have ha := Real.one_le_rpow hA (amp_pos k).le
  have hl := Real.one_le_rpow hℓ (alpha_pos k).le
  have hp := mul_le_mul ha hl (by norm_num : (0 : ℝ) ≤ 1)
    (Real.rpow_nonneg (by linarith : 0 ≤ A) (amp k))
  have h := mul_le_mul_of_nonneg_left hp hL
  unfold mainTerm
  nlinarith

theorem error_ge_length (k : ℕ) {L ℓ : ℝ} (hL : 1 ≤ L) (hℓ : 0 < ℓ)
    (hLu : L ≤ ideal k ℓ) : L ≤ errorTerm (k + 1) L ℓ := by
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  apply (sq_le_sq₀ hL0 (error_nonneg _ hL0 hℓ.le)).mp
  rw [error_square k hL0 hℓ.le, Real.rpow_add hLp, Real.rpow_one]
  have hp := Real.one_le_rpow hL (beta_nonneg k)
  calc
    L ^ 2 = (1 * L) * L := by ring
    _ ≤ (L ^ beta k * L) * ideal k ℓ :=
      mul_le_mul (mul_le_mul_of_nonneg_right hp hL0) hLu hL0 (by positivity)

theorem nonneg (k : ℕ) {L ℓ A : ℝ} (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    0 ≤ envelope k L ℓ A := by
  unfold envelope
  exact mul_nonneg (by norm_num) (add_nonneg (main_nonneg k hL hℓ hA) (error_nonneg k hL hℓ))

theorem base_bound (κ : Cutoffs) (L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget κ 0 L ℓ A ≤ envelope 0 L ℓ A := by
  apply (DerivativeRecursionBudget.base_le κ L hℓ hA).trans
  have hA0 : 0 ≤ A := by linarith
  have hc : (3 + 2 * Real.pi) / (2 * Real.pi) ≤ 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.two_le_pi]
  have hc' : 2 * (3 + 2 * Real.pi) ≤ (32 : ℝ) := by linarith [Real.pi_le_four]
  have hs : 0 ≤ A * (L : ℝ) * Real.sqrt ℓ := by positivity
  have hi : 0 ≤ (Real.sqrt ℓ)⁻¹ := by positivity
  have hb := add_le_add (mul_le_mul_of_nonneg_right hc hs) (mul_le_mul_of_nonneg_right hc' hi)
  unfold envelope mainTerm errorTerm
  rw [amp_zero, beta_zero, alpha_zero, Real.rpow_one, Real.rpow_zero, one_mul,
    Real.rpow_neg hℓ.le, ← Real.sqrt_eq_rpow]
  convert! hb using 1 <;> ring

end
end RiemannGaussian.DerivativePowerEnvelope

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteLagPowerBounds
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteLagPowerBounds
noncomputable section
open scoped Classical

theorem positive_sum (H : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ α) ≤ (H : ℝ) * (H : ℝ) ^ α := by
  calc
    _ ≤ ∑ _j ∈ Finset.range H, (H : ℝ) ^ α := by
      apply Finset.sum_le_sum
      intro j hj
      have hjH : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      exact Real.rpow_le_rpow (by positivity) hjH hα
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem negative_sum_integral (H : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    (∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ (-α)) ≤
      (H : ℝ) ^ (1 - α) / (1 - α) := by
  cases H with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      Real.zero_rpow (by linarith : 1 - α ≠ 0), zero_div, le_refl]
  | succ H =>
    have hm : AntitoneOn (fun x : ℝ ↦ x ^ (-α)) (Set.Icc 1 (1 + H)) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hs := hm.sum_le_integral
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))] at hs
    have he : (∑ j ∈ Finset.range (H + 1), ((j : ℝ) + 1) ^ (-α)) =
        (∑ j ∈ Finset.range H, (1 + ((j + 1 : ℕ) : ℝ)) ^ (-α)) + 1 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, Real.one_rpow]
      congr 2
      funext j
      congr 1
      ring
    rw [he]
    have heq : -α + 1 = 1 - α := by ring
    rw [heq, Real.one_rpow] at hs
    have hden : 0 < 1 - α := by linarith
    calc
      _ ≤ ((1 + (H : ℝ)) ^ (1 - α) - 1) / (1 - α) + 1 := by linarith
      _ ≤ (1 + (H : ℝ)) ^ (1 - α) / (1 - α) := by
        apply (le_div_iff₀ hden).mpr
        field_simp
        nlinarith
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, add_comm (H : ℝ) 1]

theorem negative_sum (H : ℕ) {α : ℝ} (hα : 0 ≤ α) (hαh : α ≤ 1 / 2) :
    (∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ (-α)) ≤
      2 * (H : ℝ) * (H : ℝ) ^ (-α) := by
  by_cases hH : H = 0
  · subst H
    simp
  have hHp : 0 < (H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hH
  apply (negative_sum_integral H hα (by linarith)).trans
  have he : (H : ℝ) ^ (1 - α) = (H : ℝ) * (H : ℝ) ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hHp, Real.rpow_one]
  rw [he]
  apply (div_le_iff₀ (by linarith : 0 < 1 - α)).mpr
  have hp : 0 ≤ (H : ℝ) * (H : ℝ) ^ (-α) := by positivity
  nlinarith [mul_nonneg hp (show 0 ≤ 1 - 2 * α by linarith)]

theorem weighted_positive (H : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ α) ≤
      (H : ℝ) ^ 2 * (H : ℝ) ^ α := by
  calc
    _ ≤ ∑ j ∈ Finset.range H, (H : ℝ) * ((j : ℝ) + 1) ^ α := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) j])
        (Real.rpow_nonneg (by positivity) _)
    _ = (H : ℝ) * ∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ α := (Finset.mul_sum _ _ _).symm
    _ ≤ (H : ℝ) * ((H : ℝ) * (H : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_left (positive_sum H hα) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem weighted_negative (H : ℕ) {α : ℝ} (hα : 0 ≤ α) (hαh : α ≤ 1 / 2) :
    (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ (-α)) ≤
      2 * (H : ℝ) ^ 2 * (H : ℝ) ^ (-α) := by
  calc
    _ ≤ ∑ j ∈ Finset.range H, (H : ℝ) * ((j : ℝ) + 1) ^ (-α) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) j])
        (Real.rpow_nonneg (by positivity) _)
    _ = (H : ℝ) * ∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ (-α) := (Finset.mul_sum _ _ _).symm
    _ ≤ (H : ℝ) * (2 * (H : ℝ) * (H : ℝ) ^ (-α)) :=
      mul_le_mul_of_nonneg_left (negative_sum H hα hαh) (Nat.cast_nonneg _)
    _ = _ := by ring

end
end RiemannGaussian.FiniteLagPowerBounds

end


-- Sidon.NumberTheory.RiemannGaussian.DerivativePowerStep
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DerivativePowerStep
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativeRecursionBudget
open RiemannGaussian.DerivativePowerEnvelope
open scoped Classical

def argument (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) : ℝ :=
  let H := shiftCount κ k L ℓ A
  (((L : ℝ) + H - 1) * ((H : ℝ) * L +
    2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
      budget κ k L (((j : ℝ) + 1) * ℓ) A)) / (H : ℝ) ^ 2

theorem weighted_budget_le (κ : Cutoffs) (k L H : ℕ) {ℓ A : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (hI : ∀ j ∈ Finset.range H, budget κ k L (((j : ℝ) + 1) * ℓ) A ≤
      envelope k L (((j : ℝ) + 1) * ℓ) A) :
    (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
      budget κ k L (((j : ℝ) + 1) * ℓ) A) ≤
        32 * A ^ amp k * L * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ alpha k +
          64 * (L : ℝ) ^ beta k * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ (-alpha k) := by
  let P := 32 * A ^ amp k * L * ℓ ^ alpha k
  let Q := 32 * (L : ℝ) ^ beta k * ℓ ^ (-alpha k)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have he (j : ℕ) : envelope k L (((j : ℝ) + 1) * ℓ) A =
      P * ((j : ℝ) + 1) ^ alpha k + Q * ((j : ℝ) + 1) ^ (-alpha k) := by
    unfold envelope mainTerm errorTerm
    rw [Real.mul_rpow (by positivity : 0 ≤ (j : ℝ) + 1) hℓ.le,
      Real.mul_rpow (by positivity : 0 ≤ (j : ℝ) + 1) hℓ.le]
    dsimp [P, Q]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
        (P * ((j : ℝ) + 1) ^ alpha k + Q * ((j : ℝ) + 1) ^ (-alpha k)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjR : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      rw [← he]
      exact mul_le_mul_of_nonneg_left (hI j hj) (by linarith)
    _ = P * (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ alpha k) +
        Q * (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ (-alpha k)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ P * ((H : ℝ) ^ 2 * (H : ℝ) ^ alpha k) +
        Q * (2 * (H : ℝ) ^ 2 * (H : ℝ) ^ (-alpha k)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (FiniteLagPowerBounds.weighted_positive H (alpha_pos k).le) hP)
        (mul_le_mul_of_nonneg_left
          (FiniteLagPowerBounds.weighted_negative H (alpha_pos k).le (alpha_le_half k)) hQ)
    _ = _ := by
      rw [Real.mul_rpow (Nat.cast_nonneg (α := ℝ) H) hℓ.le,
        Real.mul_rpow (Nat.cast_nonneg (α := ℝ) H) hℓ.le]
      dsimp [P, Q]
      ring

theorem argument_le (κ : Cutoffs) (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (hH : shiftCount κ k L ℓ A ≤ L)
    (hI : ∀ j ∈ Finset.range (shiftCount κ k L ℓ A),
      budget κ k L (((j : ℝ) + 1) * ℓ) A ≤ envelope k L (((j : ℝ) + 1) * ℓ) A) :
    argument κ k L ℓ A ≤
      2 * (L : ℝ) ^ 2 / (shiftCount κ k L ℓ A : ℝ) +
        128 * A ^ amp k * (L : ℝ) ^ 2 * ((shiftCount κ k L ℓ A : ℝ) * ℓ) ^ alpha k +
          256 * (L : ℝ) ^ (beta k + 1) *
            ((shiftCount κ k L ℓ A : ℝ) * ℓ) ^ (-alpha k) := by
  let H := shiftCount κ k L ℓ A
  have hHp : 0 < (H : ℝ) := by exact_mod_cast shiftCount_pos κ k L ℓ A
  have hHL : (H : ℝ) ≤ L := by exact_mod_cast hH
  have hLp : 0 < (L : ℝ) := hHp.trans_le hHL
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast shiftCount_pos κ k L ℓ A
  let T := 32 * A ^ amp k * L * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ alpha k +
    64 * (L : ℝ) ^ beta k * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ (-alpha k)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hs := weighted_budget_le κ k L H hℓ hA hI
  change argument κ k L ℓ A ≤ 2 * (L : ℝ) ^ 2 / (H : ℝ) +
    128 * A ^ amp k * (L : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ alpha k +
      256 * (L : ℝ) ^ (beta k + 1) * ((H : ℝ) * ℓ) ^ (-alpha k)
  calc
    _ ≤ (((L : ℝ) + H - 1) * ((H : ℝ) * L + 2 * T)) / (H : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ (2 * (L : ℝ) * ((H : ℝ) * L + 2 * T)) / (H : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by
      dsimp [T]
      rw [Real.rpow_add hLp, Real.rpow_one]
      field_simp
      ring

theorem argument_le_squares (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hA : 1 ≤ A)
    (hH : shiftCount cutoffs k L ℓ A ≤ L)
    (hI : ∀ j ∈ Finset.range (shiftCount cutoffs k L ℓ A),
      budget cutoffs k L (((j : ℝ) + 1) * ℓ) A ≤ envelope k L (((j : ℝ) + 1) * ℓ) A) :
    argument cutoffs k L ℓ A ≤
      258 * mainTerm (k + 1) L ℓ A ^ 2 + 256 * errorTerm (k + 1) L ℓ ^ 2 := by
  have hA0 : 0 ≤ A := by linarith
  have hAP := Real.one_le_rpow hA (amp_pos k).le
  have hp := count_positive_power k L hℓ hℓ1 A
  have hn := count_negative_power k L hℓ A
  have hi := inv_count_le k L hℓ A
  have hmain : 0 ≤ A ^ amp k * (L : ℝ) ^ 2 := by positivity
  have hbase : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ (2 * alpha (k + 1)) := by positivity
  have h1 : 2 * (L : ℝ) ^ 2 / (shiftCount cutoffs k L ℓ A : ℝ) ≤
      2 * (A ^ amp k * (L : ℝ) ^ 2 * ℓ ^ (2 * alpha (k + 1))) := by
    have h := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * (L : ℝ) ^ 2 by positivity)
    have h' := mul_le_mul_of_nonneg_right hAP hbase
    calc
      _ = 2 * (L : ℝ) ^ 2 * (1 / (shiftCount cutoffs k L ℓ A : ℝ)) := by ring
      _ ≤ 2 * (L : ℝ) ^ 2 * ℓ ^ (2 * alpha (k + 1)) := h
      _ ≤ _ := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 128 * A ^ amp k * (L : ℝ) ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hn (show 0 ≤ 256 * (L : ℝ) ^ (beta k + 1) by positivity)
  apply (argument_le cutoffs k L hℓ hA0 hH hI).trans
  rw [main_square k _ hℓ.le hA0, error_square k (Nat.cast_nonneg _) hℓ.le]
  nlinarith

theorem successor_bound (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hA : 1 ≤ A)
    (hH : shiftCount cutoffs k L ℓ A ≤ L)
    (hI : ∀ j ∈ Finset.range (shiftCount cutoffs k L ℓ A),
      budget cutoffs k L (((j : ℝ) + 1) * ℓ) A ≤ envelope k L (((j : ℝ) + 1) * ℓ) A) :
    budget cutoffs (k + 1) L ℓ A ≤ envelope (k + 1) L ℓ A := by
  have hA0 : 0 ≤ A := by linarith
  have hm := main_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le hA0
  have he := error_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le
  have hq : argument cutoffs k L ℓ A ≤ envelope (k + 1) L ℓ A ^ 2 := by
    apply (argument_le_squares k L hℓ hℓ1 hA hH hI).trans
    unfold envelope
    nlinarith [sq_nonneg (mainTerm (k + 1) L ℓ A), sq_nonneg (errorTerm (k + 1) L ℓ),
      mul_nonneg hm he]
  calc
    _ ≤ Real.sqrt (argument cutoffs k L ℓ A) := min_le_right _ _
    _ ≤ Real.sqrt (envelope (k + 1) L ℓ A ^ 2) := Real.sqrt_le_sqrt hq
    _ = _ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
        (DerivativePowerEnvelope.nonneg (k + 1) (Nat.cast_nonneg _) hℓ.le hA0)]

end
end RiemannGaussian.DerivativePowerStep

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaCoreSummand (s : ℂ) (n : ℕ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)

def pairedEtaCore (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaCoreSummand s n

lemma pairedEtaCoreSummand_eq_integral (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      s * ∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
        ((x : ℂ) ^ (-s - 1)) := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hderiv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) x := by
    by_cases hs : s = 0
    · subst s
      simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ)))
    · convert hasDerivAt_ofReal_cpow_const (x := x)
        (by
          rw [uIcc_of_le (by
            dsimp [a, b]
            exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))] at hx
          exact (ha.trans_le hx.1).ne')
        (neg_ne_zero.mpr hs) using 1
  have hint : IntervalIntegrable
      (fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hp : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (uIcc a b) := by
      apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
      intro x hx
      rw [uIcc_of_le (by
        dsimp [a, b]
        exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))] at hx
      exact Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)
    exact continuousOn_const.mul hp
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hfund
  dsimp [pairedEtaCoreSummand, a, b]
  have hs : (-s) *
        (∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
          (x : ℂ) ^ (-s - 1)) =
      ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
    simpa only using hfund
  calc
    ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) =
        -((-s) *
          (∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
            (x : ℂ) ^ (-s - 1))) := by rw [hs]; ring
    _ = s * ∫ x : ℝ in ((2 * n + 1 : ℕ) : ℝ)..((2 * n + 2 : ℕ) : ℝ),
          (x : ℂ) ^ (-s - 1) := by ring

lemma norm_pairedEtaCoreSummand_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖pairedEtaCoreSummand s n‖ ≤
      ‖s‖ * (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega)
  rw [pairedEtaCoreSummand_eq_integral, norm_mul]
  have hIntegral :
      ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤
        a ^ (-s.re - 1) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
    simp only [neg_re, sub_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos ha hx.1.le (by linarith)
  calc
    ‖s‖ * ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤
        ‖s‖ * (a ^ (-s.re - 1) * |b - a|) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ = ‖s‖ * a ^ (-s.re - 1) := by
      have hba : b - a = 1 := by
        dsimp [a, b]
        push_cast
        ring
      rw [hba, abs_one]
      ring
    _ = ‖s‖ * (a ^ (s.re + 1))⁻¹ := by
      rw [← Real.rpow_neg ha.le]
      congr 2
      ring
    _ = ‖s‖ * (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := rfl

lemma summable_pairedEtaCoreSummand {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaCoreSummand s) := by
  have hfull : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (s.re + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (s.re + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hfull.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  apply Summable.of_norm_bounded (hodd.mul_left ‖s‖)
  exact norm_pairedEtaCoreSummand_le hs

lemma differentiableOn_pairedEtaCore :
    DifferentiableOn ℂ pairedEtaCore {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let delta : ℝ := z.re / 2
  let radius : ℝ := z.re / 2
  let K : ℝ := ‖z‖ + radius
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbase : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (delta + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (delta + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hbase.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have hmajor : Summable
      (fun n : ℕ => K *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) :=
    hodd.mul_left K
  have hterms (n : ℕ) :
      DifferentiableOn ℂ (fun w : ℂ => pairedEtaCoreSummand w n)
        (Metric.ball z radius) := by
    unfold pairedEtaCoreSummand
    have hleft : Differentiable ℂ
        (fun w : ℂ => ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-w)) :=
      differentiable_neg.const_cpow (Or.inl (by
        exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)))
    have hright : Differentiable ℂ
        (fun w : ℂ => ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-w)) :=
      differentiable_neg.const_cpow (Or.inl (by
        exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)))
    exact (hleft.sub hright).differentiableOn
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball z radius) :
      ‖pairedEtaCoreSummand w n‖ ≤
        K * ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹ := by
    have hdist : dist w z < radius := by simpa [Metric.mem_ball] using hw
    have hreNorm : |w.re - z.re| ≤ dist w z := by
      calc
        |w.re - z.re| = |(w - z).re| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ = dist w z := by rw [dist_eq_norm]
    have hwre : delta < w.re := by
      dsimp [delta, radius] at *
      linarith [neg_le_abs (w.re - z.re)]
    have hwNorm : ‖w‖ ≤ K := by
      calc
        ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ K := by dsimp [K]; linarith
    have hraw := norm_pairedEtaCoreSummand_le (s := w) (hdelta.trans hwre) n
    let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    have ha1 : 1 ≤ a := by dsimp [a]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hpow : a ^ (-w.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    rw [← Real.rpow_neg ha0, show -(w.re + 1) = -w.re - 1 by ring] at hraw
    rw [← Real.rpow_neg ha0, show -(delta + 1) = -delta - 1 by ring]
    calc
      ‖pairedEtaCoreSummand w n‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
        simpa [a] using hraw
      _ ≤ K * a ^ (-delta - 1) :=
        mul_le_mul hwNorm hpow (Real.rpow_nonneg ha0 _) hK
  have hlocal : DifferentiableOn ℂ pairedEtaCore (Metric.ball z radius) := by
    unfold pairedEtaCore
    exact Complex.differentiableOn_tsum_of_summable_norm
      hmajor hterms Metric.isOpen_ball hbound
  exact (hlocal.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hradius))).differentiableWithinAt

lemma analyticOnNhd_pairedEtaCore :
    AnalyticOnNhd ℂ pairedEtaCore {s : ℂ | 0 < s.re} :=
  differentiableOn_pairedEtaCore.analyticOnNhd (Complex.isOpen_re_gt 0)

lemma hasSum_nat_add_one_cpow_neg_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s))
      (riemannZeta s) := by
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1 : ℝ)) (by norm_num : (1 : ℝ) ∈ Icc 0 1) hs
  have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨1, by norm_num⟩
  rw [hone, HurwitzZeta.hurwitzZeta_zero] at h
  simpa [Complex.cpow_neg] using h

lemma pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => ((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)
  have hfull : HasSum f (riemannZeta s) := by
    simpa [f] using hasSum_nat_add_one_cpow_neg_riemannZeta hs
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hfull.summable.comp_injective (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hfull.summable.comp_injective (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel h))
  have hevenSum : HasSum (fun n : ℕ => f (2 * n + 1))
      ((2 : ℂ) ^ (-s) * riemannZeta s) := by
    apply (hfull.mul_left ((2 : ℂ) ^ (-s))).congr_fun
    intro n
    dsimp [f]
    calc
      ((((2 * n + 1 + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) =
          ((((2 : ℝ) * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) ^ (-s) := by
        congr 2
        push_cast
        ring
      _ = (((2 : ℝ) : ℂ)) ^ (-s) *
          (((((n + 1 : ℕ) : ℝ)) : ℂ)) ^ (-s) := by
        simpa only [Complex.ofReal_mul] using
          (Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ))
            (b := ((n + 1 : ℕ) : ℝ)) (by norm_num) (by positivity) (-s))
      _ = (2 : ℂ) ^ (-s) * (((n + 1 : ℕ) : ℂ)) ^ (-s) := by norm_num
  have hsplit :
      (∑' n : ℕ, f (2 * n)) +
          (2 : ℂ) ^ (-s) * riemannZeta s = riemannZeta s := by
    exact (HasSum.even_add_odd hodd.hasSum hevenSum).unique hfull
  have hpaired : pairedEtaCore s =
      (∑' n : ℕ, f (2 * n)) -
        ∑' n : ℕ, f (2 * n + 1) := by
    unfold pairedEtaCore
    rw [← hodd.tsum_sub heven]
    apply tsum_congr
    intro n
    dsimp [pairedEtaCoreSummand, f]
  rw [hpaired, hevenSum.tsum_eq]
  linear_combination hsplit

def pairedEtaUpperRightDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ 0 < s.im}

lemma isOpen_pairedEtaUpperRightDomain : IsOpen pairedEtaUpperRightDomain := by
  rw [pairedEtaUpperRightDomain, ofPred_and]
  exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_im_gt 0)

lemma isPreconnected_pairedEtaUpperRightDomain :
    IsPreconnected pairedEtaUpperRightDomain := by
  apply Convex.isPreconnected
  rw [pairedEtaUpperRightDomain, ofPred_and]
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    {s : ℂ} (hsre : 0 < s.re) (hsim : 0 < s.im) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let rhs : ℂ → ℂ := fun w =>
    (1 - 2 * (2 : ℂ) ^ (-w)) * riemannZeta w
  have hlhs : AnalyticOnNhd ℂ pairedEtaCore pairedEtaUpperRightDomain :=
    analyticOnNhd_pairedEtaCore.mono (by
      intro w hw
      exact hw.1)
  have hrhsDiff : DifferentiableOn ℂ rhs pairedEtaUpperRightDomain := by
    intro w hw
    have hfactor : DifferentiableAt ℂ
        (fun u : ℂ => 1 - 2 * (2 : ℂ) ^ (-u)) w := by
      fun_prop (disch := norm_num)
    have hwone : w ≠ 1 := by
      intro h
      subst w
      simpa [pairedEtaUpperRightDomain] using hw.2
    exact hfactor.mul (differentiableAt_riemannZeta hwone) |>.differentiableWithinAt
  have hrhs : AnalyticOnNhd ℂ rhs pairedEtaUpperRightDomain :=
    hrhsDiff.analyticOnNhd isOpen_pairedEtaUpperRightDomain
  let z0 : ℂ := 2 + Complex.I
  have hz0 : z0 ∈ pairedEtaUpperRightDomain := by
    simp [z0, pairedEtaUpperRightDomain]
  have hevent : pairedEtaCore =ᶠ[𝓝 z0] rhs := by
    filter_upwards [
      (Complex.isOpen_re_gt 1).mem_nhds
        (show 1 < z0.re by simp [z0])] with w hw
    exact pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re hw
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs
    isPreconnected_pairedEtaUpperRightDomain hz0 hevent ⟨hsre, hsim⟩

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaCorePartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaCoreSummand s n

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex ComplexConjugate Matrix
open scoped Classical Topology ComplexOrder

namespace RiemannGaussian

noncomputable section

def zetaPrimeFeature (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(s * (Real.log n : ℂ)))

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

def zetaPrimeExpWeight (σ : ℝ) (m : ℕ) : ℝ := Real.exp (-σ * Real.log m)

theorem norm_zetaPrimeFeature (s : ℂ) (m : ℕ) :
    ‖zetaPrimeFeature s m‖ = zetaPrimeExpWeight s.re m := by
  simp only [zetaPrimeFeature, zetaPrimeExpWeight, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletDyadicBlocks
noncomputable section
open scoped Classical

def positivePrefix (s : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 M, zetaPrimeFeature s n

def block (s : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (2 ^ j), zetaPrimeFeature s (2 ^ j + n)

theorem feature_eq_cpow (s : ℂ) {n : ℕ} (hn : 0 < n) :
    zetaPrimeFeature s n = (n : ℂ) ^ (-s) := by
  rw [zetaPrimeFeature, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne'),
    ← Complex.natCast_log]
  congr 1
  ring

theorem feature_mul (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    zetaPrimeFeature s (m * n) = zetaPrimeFeature s m * zetaPrimeFeature s n := by
  unfold zetaPrimeFeature
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne'),
    Complex.ofReal_add, mul_add, neg_add, Complex.exp_add]

theorem weight_eq_rpow (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    zetaPrimeExpWeight σ n = (n : ℝ) ^ (-σ) := by
  rw [zetaPrimeExpWeight, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

theorem prefix_succ (s : ℂ) {M : ℕ} (hM : 1 ≤ M) :
    positivePrefix s (M + 1) = positivePrefix s M + zetaPrimeFeature s M :=
  Finset.sum_Ico_succ_top hM _

theorem block_eq_Ico (s : ℂ) (j : ℕ) :
    block s j = ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), zetaPrimeFeature s n := by
  rw [Finset.sum_Ico_eq_sum_range]
  have he : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
  rw [he]
  rfl

theorem prefix_pow_two (s : ℂ) (J : ℕ) :
    positivePrefix s (2 ^ J) = ∑ j ∈ Finset.range J, block s j := by
  induction J with
  | zero => simp [positivePrefix]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, block_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (one_le_pow₀ (by norm_num))
      (by rw [pow_succ]; omega)).symm

theorem eta_pair_eq_features (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      zetaPrimeFeature s (2 * n + 1) - zetaPrimeFeature s (2 * n + 2) := by
  rw [feature_eq_cpow s (by omega), feature_eq_cpow s (by omega)]
  simp only [pairedEtaCoreSummand, Complex.ofReal_natCast]

theorem eta_eq_prefix (s : ℂ) (N : ℕ) :
    pairedEtaCorePartialSum N s = positivePrefix s (2 * N + 1) -
      2 * zetaPrimeFeature s 2 * positivePrefix s (N + 1) := by
  induction N with
  | zero => simp [pairedEtaCorePartialSum, positivePrefix]
  | succ N ih =>
    have hη : pairedEtaCorePartialSum (N + 1) s =
        pairedEtaCorePartialSum N s + pairedEtaCoreSummand s N :=
      Finset.sum_range_succ _ _
    rw [hη, eta_pair_eq_features, ih]
    rw [show 2 * (N + 1) + 1 = (2 * N + 1 + 1) + 1 by omega]
    conv_rhs =>
      rw [prefix_succ s (M := 2 * N + 1 + 1) (by omega),
        prefix_succ s (M := 2 * N + 1) (by omega),
        prefix_succ s (M := N + 1) (by omega)]
    have hmul := feature_mul s (m := 2) (n := N + 1) (by norm_num) (by omega)
    rw [show 2 * (N + 1) = 2 * N + 2 by omega] at hmul
    rw [show 2 * N + 1 + 1 = 2 * N + 2 by omega]
    rw [hmul]
    ring

theorem eta_pow_two_eq_blocks (s : ℂ) (J : ℕ) :
    pairedEtaCorePartialSum (2 ^ J) s =
      (∑ j ∈ Finset.range (J + 1), block s j) -
        2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
          zetaPrimeFeature s (2 ^ (J + 1)) := by
  have hN : 1 ≤ (2 : ℕ) ^ J := one_le_pow₀ (by norm_num)
  have htwo : 2 * (2 : ℕ) ^ J = 2 ^ (J + 1) := by rw [pow_succ]; ring
  have hmul := feature_mul s (m := 2) (n := 2 ^ J) (by norm_num) (by positivity)
  rw [htwo] at hmul
  rw [eta_eq_prefix, htwo,
    prefix_succ s (M := 2 ^ (J + 1)) (one_le_pow₀ (by norm_num)),
    prefix_succ s hN,
    prefix_pow_two, prefix_pow_two, hmul]
  ring

end
end RiemannGaussian.DirichletDyadicBlocks

end


-- Sidon.NumberTheory.RiemannGaussian.PhaseIncrementInverse
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.PhaseIncrementInverse
noncomputable section

def rotation (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

def inverseStep (x : ℝ) : ℂ := (rotation x - 1)⁻¹

theorem norm_rotation (x : ℝ) : ‖rotation x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem rotation_add (x y : ℝ) : rotation (x + y) = rotation x * rotation y := by
  simp only [rotation, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem norm_rotation_sub_one (x : ℝ) :
    ‖rotation x - 1‖ = 2 * |Real.sin (x / 2)| := by
  rw [rotation, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem rotation_sub_one_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    rotation x - 1 ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_rotation_sub_one]
  have hs : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  positivity

private theorem inverseStep_two_mul (x : ℝ) (hx : Real.sin x ≠ 0) :
    inverseStep (2 * x) = ⟨-(1 / 2 : ℝ), -Real.cot x / 2⟩ := by
  unfold inverseStep
  apply inv_eq_of_mul_eq_one_right
  simp only [rotation, Complex.exp_ofReal_mul_I,
    Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, Real.cot_eq_cos_div_sin]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, add_zero, sub_zero] <;>
    field_simp <;> nlinarith [Real.sin_sq_add_cos_sq x]

theorem inverseStep_eq {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    inverseStep x = ⟨-(1 / 2 : ℝ), -Real.cot (x / 2) / 2⟩ := by
  have hs : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    inverseStep_two_mul (x / 2) hs

theorem inverseStep_re {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    (inverseStep x).re = -(1 / 2 : ℝ) := by
  rw [inverseStep_eq hx]

theorem inverseStep_im {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    (inverseStep x).im = -Real.cot (x / 2) / 2 := by
  rw [inverseStep_eq hx]

theorem cot_antitoneOn : AntitoneOn Real.cot (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
    (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)).mpr
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy)
    (show y - x ≤ Real.pi by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hs
  nlinarith

theorem inverseStep_im_monotoneOn :
    MonotoneOn (fun x ↦ (inverseStep x).im) (Set.Ioo 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  change (inverseStep x).im ≤ (inverseStep y).im
  rw [inverseStep_im hx, inverseStep_im hy]
  have hc := cot_antitoneOn
    (show x / 2 ∈ Set.Ioo 0 Real.pi by constructor <;> linarith [hx.1, hx.2])
    (show y / 2 ∈ Set.Ioo 0 Real.pi by constructor <;> linarith [hy.1, hy.2])
    (show x / 2 ≤ y / 2 by linarith)
  linarith

theorem sin_half_lower {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Set.Icc η (2 * Real.pi - η)) : η / Real.pi ≤ Real.sin (x / 2) := by
  by_cases hc : x ≤ Real.pi
  · have hs := Real.mul_le_sin (show 0 ≤ x / 2 by linarith [hx.1])
      (show x / 2 ≤ Real.pi / 2 by linarith)
    have he : 2 / Real.pi * (x / 2) = x / Real.pi := by ring
    rw [he] at hs
    exact (div_le_div_of_nonneg_right hx.1 Real.pi_pos.le).trans hs
  · have hs := Real.mul_le_sin (show 0 ≤ Real.pi - x / 2 by linarith [hx.2])
      (show Real.pi - x / 2 ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hs
    have hh : η / Real.pi ≤ 2 / Real.pi * (Real.pi - x / 2) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      field_simp
      linarith [hx.2]
    exact hh.trans hs

theorem norm_inverseStep_le {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Set.Icc η (2 * Real.pi - η)) :
    ‖inverseStep x‖ ≤ Real.pi / (2 * η) := by
  have hs := sin_half_lower hη hx
  have hsp : 0 < Real.sin (x / 2) := lt_of_lt_of_le (div_pos hη Real.pi_pos) hs
  rw [inverseStep, norm_inv, norm_rotation_sub_one, abs_of_pos hsp]
  have hb := one_div_le_one_div_of_le (mul_pos (by norm_num : (0 : ℝ) < 2)
    (div_pos hη Real.pi_pos)) (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  calc
    (2 * Real.sin (x / 2))⁻¹ ≤ 1 / (2 * (η / Real.pi)) := by
      simpa only [one_div] using hb
    _ = Real.pi / (2 * η) := by field_simp

end
end RiemannGaussian.PhaseIncrementInverse

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteKuzminLandau
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteKuzminLandau
noncomputable section
open RiemannGaussian.PhaseIncrementInverse
open scoped Classical

theorem summation_by_parts (c z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), c n * (z (n + 1) - z n)) =
      c N * z (N + 1) - c 0 * z 0 +
        ∑ n ∈ Finset.range N, (c n - c (n + 1)) * z (n + 1) := by
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private theorem norm_sub_vertical {z w : ℂ} (hre : z.re = w.re) :
    ‖z - w‖ = |z.im - w.im| := by
  have he : z - w = ((z.im - w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem variation_le (c : ℕ → ℂ) (N : ℕ) {M : ℝ}
    (hre : ∀ n ≤ N, (c n).re = (c 0).re)
    (hnorm : ∀ n ≤ N, ‖c n‖ ≤ M)
    (hmono : MonotoneOn (fun n ↦ (c n).im) (Set.Icc 0 N) ∨
      AntitoneOn (fun n ↦ (c n).im) (Set.Icc 0 N)) :
    (∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖) ≤ 2 * M := by
  have hn (n : ℕ) (hn : n < N) :
      ‖c n - c (n + 1)‖ = |(c n).im - (c (n + 1)).im| :=
    norm_sub_vertical ((hre n (by omega)).trans (hre (n + 1) (by omega)).symm)
  have hzero := abs_le.mp ((Complex.abs_im_le_norm (c 0)).trans (hnorm 0 (by omega)))
  have hlast := abs_le.mp ((Complex.abs_im_le_norm (c N)).trans (hnorm N le_rfl))
  rcases hmono with hmono | hanti
  · have he : (∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖) = (c N).im - (c 0).im := by
      rw [← Finset.sum_range_sub (fun n ↦ (c n).im) N]
      apply Finset.sum_congr rfl
      intro n hmem
      have hn' := Finset.mem_range.mp hmem
      rw [hn n hn', abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    rw [he]
    linarith [hzero.1, hlast.2]
  · have he : (∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖) = (c 0).im - (c N).im := by
      rw [← Finset.sum_range_sub' (fun n ↦ (c n).im) N]
      apply Finset.sum_congr rfl
      intro n hmem
      have hn' := Finset.mem_range.mp hmem
      rw [hn n hn', abs_of_nonneg]
      exact sub_nonneg.mpr (hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    rw [he]
    linarith [hzero.2, hlast.1]

def increment (φ : ℕ → ℝ) (n : ℕ) : ℝ := φ (n + 1) - φ n

theorem inverseStep_mul_difference {a b : ℝ}
    (hab : b - a ∈ Set.Ioo 0 (2 * Real.pi)) :
    inverseStep (b - a) * (rotation b - rotation a) = rotation a := by
  calc
    _ = inverseStep (b - a) * ((rotation (b - a) - 1) * rotation a) := by
      rw [sub_mul, one_mul, ← rotation_add, sub_add_cancel]
    _ = _ := by
      rw [← mul_assoc, inverseStep, inv_mul_cancel₀ (rotation_sub_one_ne_zero hab), one_mul]

theorem phase_sum_identity (φ : ℕ → ℝ) (N : ℕ)
    (hd : ∀ n ≤ N, increment φ n ∈ Set.Ioo 0 (2 * Real.pi)) :
    (∑ n ∈ Finset.range (N + 1), rotation (φ n)) =
      inverseStep (increment φ N) * rotation (φ (N + 1)) -
        inverseStep (increment φ 0) * rotation (φ 0) +
          ∑ n ∈ Finset.range N,
            (inverseStep (increment φ n) - inverseStep (increment φ (n + 1))) *
              rotation (φ (n + 1)) := by
  calc
    _ = ∑ n ∈ Finset.range (N + 1), inverseStep (increment φ n) *
        (rotation (φ (n + 1)) - rotation (φ n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (inverseStep_mul_difference (hd n (by simpa using Finset.mem_range.mp hn))).symm
    _ = _ := summation_by_parts (fun n ↦ inverseStep (increment φ n)) (fun n ↦ rotation (φ n)) N

theorem bound (φ : ℕ → ℝ) (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n ≤ N, increment φ n ∈ Set.Icc η (2 * Real.pi - η))
    (hmono : MonotoneOn (increment φ) (Set.Icc 0 N) ∨
      AntitoneOn (increment φ) (Set.Icc 0 N)) :
    ‖∑ n ∈ Finset.range (N + 1), rotation (φ n)‖ ≤ 2 * Real.pi / η := by
  let c : ℕ → ℂ := fun n ↦ inverseStep (increment φ n)
  let M : ℝ := Real.pi / (2 * η)
  have hdom (n : ℕ) (hn : n ≤ N) : increment φ n ∈ Set.Ioo 0 (2 * Real.pi) :=
    ⟨by linarith [(hd n hn).1], by linarith [(hd n hn).2]⟩
  have hcnorm (n : ℕ) (hn : n ≤ N) : ‖c n‖ ≤ M := norm_inverseStep_le hη (hd n hn)
  have hcre (n : ℕ) (hn : n ≤ N) : (c n).re = (c 0).re := by
    rw [inverseStep_re (hdom n hn), inverseStep_re (hdom 0 (by omega))]
  have hcmono : MonotoneOn (fun n ↦ (c n).im) (Set.Icc 0 N) ∨
      AntitoneOn (fun n ↦ (c n).im) (Set.Icc 0 N) := by
    rcases hmono with hm | hm
    · left
      intro i hi j hj hij
      exact inverseStep_im_monotoneOn (hdom i hi.2) (hdom j hj.2) (hm hi hj hij)
    · right
      intro i hi j hj hij
      exact inverseStep_im_monotoneOn (hdom j hj.2) (hdom i hi.2) (hm hi hj hij)
  have hv := variation_le c N hcre hcnorm hcmono
  have hid := phase_sum_identity φ N hdom
  change (∑ n ∈ Finset.range (N + 1), rotation (φ n)) =
    c N * rotation (φ (N + 1)) - c 0 * rotation (φ 0) +
      ∑ n ∈ Finset.range N, (c n - c (n + 1)) * rotation (φ (n + 1)) at hid
  rw [hid]
  calc
    _ ≤ ‖c N * rotation (φ (N + 1)) - c 0 * rotation (φ 0)‖ +
        ‖∑ n ∈ Finset.range N, (c n - c (n + 1)) * rotation (φ (n + 1))‖ := norm_add_le _ _
    _ ≤ (‖c N * rotation (φ (N + 1))‖ + ‖c 0 * rotation (φ 0)‖) +
        ∑ n ∈ Finset.range N, ‖(c n - c (n + 1)) * rotation (φ (n + 1))‖ := by
      exact add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ = (‖c N‖ + ‖c 0‖) + ∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖ := by
      simp only [norm_mul, norm_rotation, mul_one]
    _ ≤ (M + M) + 2 * M := add_le_add (add_le_add (hcnorm N le_rfl) (hcnorm 0 (by omega))) hv
    _ = _ := by dsimp [M]; ring

end
end RiemannGaussian.FiniteKuzminLandau

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteAbelVariation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteAbelVariation
noncomputable section
open scoped Classical

theorem weighted_sum_eq (w z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n * z n) =
      w N * (∑ n ∈ Finset.range (N + 1), z n) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ k ∈ Finset.range (n + 1), z k) := by
  have h := FiniteKuzminLandau.summation_by_parts w
    (fun n ↦ ∑ k ∈ Finset.range n, z k) N
  simpa only [Finset.sum_range_succ, add_sub_cancel_left, Finset.range_zero,
    Finset.sum_empty, mul_zero, sub_zero] using h

theorem weighted_bound (w z : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hB : ∀ n ≤ N, ‖∑ k ∈ Finset.range (n + 1), z k‖ ≤ B) :
    ‖∑ n ∈ Finset.range (N + 1), w n * z n‖ ≤
      B * (‖w N‖ + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖) := by
  rw [weighted_sum_eq]
  calc
    _ ≤ ‖w N * (∑ n ∈ Finset.range (N + 1), z n)‖ +
        ‖∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ k ∈ Finset.range (n + 1), z k)‖ := norm_add_le _ _
    _ ≤ ‖w N‖ * B + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB n (by have := Finset.mem_range.mp hn; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem decreasing_budget (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N)) :
    ‖(w N : ℂ)‖ + (∑ n ∈ Finset.range N, ‖(w n : ℂ) - (w (n + 1) : ℂ)‖) = w 0 := by
  have hs : (∑ n ∈ Finset.range N, ‖(w n : ℂ) - (w (n + 1) : ℂ)‖) = w 0 - w N := by
    rw [← Finset.sum_range_sub' w N]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact sub_nonneg.mpr (hm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N le_rfl)]
  ring

theorem decreasing_bound (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N))
    (hB : ∀ n ≤ N, ‖∑ k ∈ Finset.range (n + 1), z k‖ ≤ B) :
    ‖∑ n ∈ Finset.range (N + 1), (w n : ℂ) * z n‖ ≤ B * w 0 := by
  have h := weighted_bound (fun n ↦ (w n : ℂ)) z N hB
  rwa [decreasing_budget w N hw hm] at h

end
end RiemannGaussian.FiniteAbelVariation

end


-- Sidon.NumberTheory.RiemannGaussian.LogarithmicShiftPhase
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.LogarithmicShiftPhase
noncomputable section

def phase (t x : ℝ) : ℝ := -t * Real.log x

theorem hasDerivAt_phase (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (phase t) (-t / x) x := by
  unfold phase
  convert! (Real.hasDerivAt_log hx.ne').const_mul (-t) using 1

end
end RiemannGaussian.LogarithmicShiftPhase

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteKuzminLandauPeriodic
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteKuzminLandauPeriodic
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.FiniteKuzminLandau
open scoped Classical

theorem rotation_int_period (x : ℝ) (m : ℤ) :
    RiemannGaussian.PhaseIncrementInverse.rotation (x + (m : ℝ) * (2 * Real.pi)) = RiemannGaussian.PhaseIncrementInverse.rotation x := by
  rw [rotation_add]
  have he : RiemannGaussian.PhaseIncrementInverse.rotation ((m : ℝ) * (2 * Real.pi)) = 1 := by
    unfold PhaseIncrementInverse.rotation
    convert Complex.exp_int_mul_two_pi_mul_I m using 1
    push_cast
    congr 1
    ring
  rw [he, mul_one]

def twist (φ : ℕ → ℝ) (m : ℤ) (n : ℕ) : ℝ :=
  φ n - (m : ℝ) * (2 * Real.pi) * n

theorem rotation_twist (φ : ℕ → ℝ) (m : ℤ) (n : ℕ) :
    RiemannGaussian.PhaseIncrementInverse.rotation (twist φ m n) = RiemannGaussian.PhaseIncrementInverse.rotation (φ n) := by
  have he : twist φ m n = φ n + (((-m * (n : ℤ) : ℤ) : ℝ)) * (2 * Real.pi) := by
    unfold twist
    push_cast
    ring
  rw [he, rotation_int_period]

theorem increment_twist (φ : ℕ → ℝ) (m : ℤ) (n : ℕ) :
    increment (twist φ m) n = increment φ n - (m : ℝ) * (2 * Real.pi) := by
  unfold increment twist
  push_cast
  ring

theorem bound_period (φ : ℕ → ℝ) (N : ℕ) (m : ℤ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n ≤ N, increment φ n ∈ Set.Icc
      ((m : ℝ) * (2 * Real.pi) + η) ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η))
    (hm : MonotoneOn (increment φ) (Set.Icc 0 N) ∨
      AntitoneOn (increment φ) (Set.Icc 0 N)) :
    ‖∑ n ∈ Finset.range (N + 1), RiemannGaussian.PhaseIncrementInverse.rotation (φ n)‖ ≤ 2 * Real.pi / η := by
  have hdr (n : ℕ) (hn : n ≤ N) :
      increment (twist φ m) n ∈ Set.Icc η (2 * Real.pi - η) := by
    rw [increment_twist]
    constructor <;> linarith [(hd n hn).1, (hd n hn).2]
  have hmr : MonotoneOn (increment (twist φ m)) (Set.Icc 0 N) ∨
      AntitoneOn (increment (twist φ m)) (Set.Icc 0 N) := by
    rcases hm with hm | hm
    · left
      intro i hi j hj hij
      simp only [increment_twist]
      exact sub_le_sub_right (hm hi hj hij) _
    · right
      intro i hi j hj hij
      simp only [increment_twist]
      exact sub_le_sub_right (hm hi hj hij) _
  simpa only [rotation_twist] using FiniteKuzminLandau.bound (twist φ m) N hη hdr hmr

theorem bound_Ico (φ : ℕ → ℝ) (a b : ℕ) (m : ℤ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n ∈ Finset.Ico a b, increment φ n ∈ Set.Icc
      ((m : ℝ) * (2 * Real.pi) + η) ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η))
    (hm : MonotoneOn (increment φ) (Set.Ico a b) ∨
      AntitoneOn (increment φ) (Set.Ico a b)) :
    ‖∑ n ∈ Finset.Ico a b, RiemannGaussian.PhaseIncrementInverse.rotation (φ n)‖ ≤ 2 * Real.pi / η := by
  by_cases hab : a < b
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, b = a + (N + 1) := ⟨b - a - 1, by omega⟩
    have hi (n : ℕ) (hn : n ≤ N) : a + n ∈ Finset.Ico a (a + (N + 1)) := by
      simp only [Finset.mem_Ico]
      omega
    have hd' (n : ℕ) (hn : n ≤ N) : increment (fun k ↦ φ (a + k)) n ∈ Set.Icc
        ((m : ℝ) * (2 * Real.pi) + η) ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η) := by
      simpa only [increment, Nat.add_assoc] using hd (a + n) (hi n hn)
    have hm' : MonotoneOn (increment (fun k ↦ φ (a + k))) (Set.Icc 0 N) ∨
        AntitoneOn (increment (fun k ↦ φ (a + k))) (Set.Icc 0 N) := by
      rcases hm with hm | hm
      · left
        intro i hi' j hj' hij
        simpa only [increment, Nat.add_assoc] using
          hm (Finset.mem_Ico.mp (hi i hi'.2)) (Finset.mem_Ico.mp (hi j hj'.2))
            (Nat.add_le_add_left hij a)
      · right
        intro i hi' j hj' hij
        simpa only [increment, Nat.add_assoc] using
          hm (Finset.mem_Ico.mp (hi i hi'.2)) (Finset.mem_Ico.mp (hi j hj'.2))
            (Nat.add_le_add_left hij a)
    have h := bound_period (fun k ↦ φ (a + k)) N m hη hd' hm'
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_sub_cancel_left] using h
  · rw [Finset.Ico_eq_empty hab, Finset.sum_empty, norm_zero]
    positivity

end
end RiemannGaussian.FiniteKuzminLandauPeriodic

end


-- Sidon.NumberTheory.RiemannGaussian.MonotonePhaseBlocks
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.MonotonePhaseBlocks
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.FiniteKuzminLandau
open scoped Classical

def band (d : ℕ → ℝ) (N : ℕ) (u v : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun n ↦ u ≤ d n ∧ d n < v)

theorem mem_band (d : ℕ → ℝ) (N : ℕ) (u v : ℝ) (n : ℕ) :
    n ∈ band d N u v ↔ n < N ∧ u ≤ d n ∧ d n < v := by
  simp only [band, Finset.mem_filter, Finset.mem_range]

theorem band_eq_Ico {d : ℕ → ℝ} {N : ℕ} {u v : ℝ}
    (hd : MonotoneOn d (Set.Iio N)) (hne : (band d N u v).Nonempty) :
    ∃ a b : ℕ, a < b ∧ b ≤ N ∧ band d N u v = Finset.Ico a b := by
  let T := band d N u v
  let a := T.min' hne
  let z := T.max' hne
  have ha : a ∈ T := Finset.min'_mem T hne
  have hz : z ∈ T := Finset.max'_mem T hne
  have haz : a ≤ z := Finset.min'_le T z hz
  have ha' := (mem_band d N u v a).mp ha
  have hz' := (mem_band d N u v z).mp hz
  refine ⟨a, z + 1, by omega, by omega, ?_⟩
  ext n
  constructor
  · intro hn
    have hl := Finset.min'_le T n hn
    have hu := Finset.le_max' T n hn
    simp only [Finset.mem_Ico]
    change a ≤ n ∧ n < z + 1
    exact ⟨hl, by omega⟩
  · intro hn
    have hn' := Finset.mem_Ico.mp hn
    have hnN : n < N := by omega
    apply (mem_band d N u v n).mpr
    exact ⟨hnN, ha'.2.1.trans (hd ha'.1 hnN hn'.1),
      (hd hnN hz'.1 (by omega)).trans_lt hz'.2.2⟩

theorem band_card_le {d : ℕ → ℝ} {N : ℕ} {u v ℓ : ℝ} (hℓ : 0 < ℓ) (huv : u ≤ v)
    (hd : MonotoneOn d (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → ℓ * ((j : ℝ) - i) ≤ d j - d i) :
    ((band d N u v).card : ℝ) ≤ (v - u) / ℓ + 1 := by
  by_cases hne : (band d N u v).Nonempty
  · obtain ⟨a, b, hab, hbN, he⟩ := band_eq_Ico hd hne
    have ha : a ∈ band d N u v := by rw [he]; exact Finset.mem_Ico.mpr ⟨le_rfl, hab⟩
    have hz : b - 1 ∈ band d N u v := by rw [he]; simp only [Finset.mem_Ico]; omega
    have ha' := (mem_band d N u v a).mp ha
    have hz' := (mem_band d N u v (b - 1)).mp hz
    have hs := hsep a ha'.1 (b - 1) hz'.1 (by omega)
    have hc : ((band d N u v).card : ℝ) = (b : ℝ) - a := by
      rw [he, Nat.card_Ico, Nat.cast_sub (by omega : a ≤ b)]
    have hbcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
    rw [hbcast] at hs
    rw [hc]
    have heq : (v - u) / ℓ + 1 = (v - u + ℓ) / ℓ := by field_simp
    rw [heq, le_div_iff₀ hℓ]
    nlinarith [ha'.2.1, hz'.2.2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    have hwidth : 0 ≤ v - u := sub_nonneg.mpr huv
    positivity

theorem nonresonant_band_bound (φ : ℕ → ℝ) (N : ℕ) (m : ℤ) {η : ℝ} (hη : 0 < η)
    (hd : MonotoneOn (increment φ) (Set.Iio N)) :
    ‖∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) + η)
      ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η), rotation (φ n)‖ ≤
        2 * Real.pi / η := by
  let T := band (increment φ) N ((m : ℝ) * (2 * Real.pi) + η)
    ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η)
  by_cases hne : T.Nonempty
  · obtain ⟨a, b, _, _, he⟩ := band_eq_Ico hd hne
    change T = _ at he
    change ‖∑ n ∈ T, rotation (φ n)‖ ≤ _
    rw [he]
    apply FiniteKuzminLandauPeriodic.bound_Ico φ a b m hη
    · intro n hn
      rw [← he] at hn
      have h := (mem_band _ _ _ _ n).mp hn
      exact ⟨h.2.1, h.2.2.le⟩
    · left
      intro i hi j hj hij
      have hi' : i ∈ T := by rw [he]; exact Finset.mem_Ico.mpr hi
      have hj' : j ∈ T := by rw [he]; exact Finset.mem_Ico.mpr hj
      exact hd ((mem_band _ _ _ _ i).mp hi').1 ((mem_band _ _ _ _ j).mp hj').1 hij
  · change ‖∑ n ∈ T, rotation (φ n)‖ ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero]
    positivity

end
end RiemannGaussian.MonotonePhaseBlocks

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteResonancePartition
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteResonancePartition
noncomputable section
open RiemannGaussian.MonotonePhaseBlocks
open scoped Classical

def cellIndex (η x : ℝ) : ℤ := ⌊(x + η) / (2 * Real.pi)⌋

def cells (d : ℕ → ℝ) (N : ℕ) (η : ℝ) : Finset ℤ :=
  Finset.Icc (cellIndex η (d 0)) (cellIndex η (d (N - 1)))

theorem cellIndex_mono (η : ℝ) : Monotone (cellIndex η) := by
  intro x y hxy
  exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith : x + η ≤ y + η)
    (by positivity : 0 ≤ 2 * Real.pi))

theorem cellIndex_eq_iff (η x : ℝ) (m : ℤ) :
    cellIndex η x = m ↔ (m : ℝ) * (2 * Real.pi) - η ≤ x ∧
      x < (m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η := by
  rw [cellIndex, Int.floor_eq_iff,
    le_div_iff₀ (by positivity : 0 < 2 * Real.pi),
    div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem cellIndex_mem_cells {d : ℕ → ℝ} {N : ℕ} (hd : MonotoneOn d (Set.Iio N))
    (η : ℝ) {n : ℕ} (hn : n < N) : cellIndex η (d n) ∈ cells d N η := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact cellIndex_mono η (hd (show 0 < N by omega) hn (Nat.zero_le n))
  · exact cellIndex_mono η (hd hn (show N - 1 < N by omega) (by omega))

theorem cell_eq_filter (d : ℕ → ℝ) (N : ℕ) (η : ℝ) (m : ℤ) :
    band d N ((m : ℝ) * (2 * Real.pi) - η)
      ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η) =
        (Finset.range N).filter (fun n ↦ cellIndex η (d n) = m) := by
  ext n
  simp only [mem_band, Finset.mem_filter, Finset.mem_range, cellIndex_eq_iff]

theorem band_sum_split (d : ℕ → ℝ) (N : ℕ) (f : ℕ → ℂ) {u w v : ℝ}
    (huw : u ≤ w) (hwv : w ≤ v) :
    (∑ n ∈ band d N u v, f n) =
      (∑ n ∈ band d N u w, f n) + ∑ n ∈ band d N w v, f n := by
  have hl : (band d N u v).filter (fun n ↦ d n < w) = band d N u w := by
    ext n
    simp only [Finset.mem_filter, mem_band]
    constructor
    · rintro ⟨⟨hn, hu, _⟩, hw⟩
      exact ⟨hn, hu, hw⟩
    · rintro ⟨hn, hu, hw⟩
      exact ⟨⟨hn, hu, hw.trans_le hwv⟩, hw⟩
  have hr : (band d N u v).filter (fun n ↦ ¬d n < w) = band d N w v := by
    ext n
    simp only [Finset.mem_filter, mem_band, not_lt]
    constructor
    · rintro ⟨⟨hn, _, hv⟩, hw⟩
      exact ⟨hn, hw, hv⟩
    · rintro ⟨hn, hw, hv⟩
      exact ⟨⟨hn, huw.trans hw, hv⟩, hw⟩
  have h := Finset.sum_filter_add_sum_filter_not (band d N u v) (fun n ↦ d n < w) f
  rw [hl, hr] at h
  exact h.symm

theorem sum_eq_bands (d : ℕ → ℝ) (N : ℕ) (f : ℕ → ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hηπ : η ≤ Real.pi) (hd : MonotoneOn d (Set.Iio N)) :
    (∑ n ∈ Finset.range N, f n) =
      ∑ m ∈ cells d N η,
        ((∑ n ∈ band d N ((m : ℝ) * (2 * Real.pi) - η)
          ((m : ℝ) * (2 * Real.pi) + η), f n) +
            ∑ n ∈ band d N ((m : ℝ) * (2 * Real.pi) + η)
              ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η), f n) := by
  have hmap : ∀ n ∈ Finset.range N, cellIndex η (d n) ∈ cells d N η :=
    fun _ hn ↦ cellIndex_mem_cells hd η (Finset.mem_range.mp hn)
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  apply Finset.sum_congr rfl
  intro m _
  rw [← cell_eq_filter]
  exact band_sum_split d N f (by linarith) (by linarith)

theorem cells_card_le {d : ℕ → ℝ} {N : ℕ} (η : ℝ) (hd : MonotoneOn d (Set.Iio N)) :
    ((cells d N η).card : ℝ) ≤ (d (N - 1) - d 0) / (2 * Real.pi) + 2 := by
  by_cases hN : N = 0
  · subst N
    simp [cells]
  have hlohi : cellIndex η (d 0) ≤ cellIndex η (d (N - 1)) :=
    cellIndex_mono η (hd (show 0 < N by omega)
      (show N - 1 < N by omega) (Nat.zero_le _))
  have hc : ((cells d N η).card : ℝ) =
      (cellIndex η (d (N - 1)) : ℝ) + 1 - (cellIndex η (d 0) : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le (cellIndex η (d 0)) (cellIndex η (d (N - 1)))
      (by omega)
  rw [hc]
  have hi := Int.floor_le ((d (N - 1) + η) / (2 * Real.pi))
  have hl := Int.lt_floor_add_one ((d 0 + η) / (2 * Real.pi))
  change (cellIndex η (d (N - 1)) : ℝ) ≤ _ at hi
  change _ < (cellIndex η (d 0) : ℝ) + 1 at hl
  have he : (d (N - 1) - d 0) / (2 * Real.pi) =
      (d (N - 1) + η) / (2 * Real.pi) - (d 0 + η) / (2 * Real.pi) := by ring
  rw [he]
  linarith

end
end RiemannGaussian.FiniteResonancePartition

end


-- Sidon.NumberTheory.RiemannGaussian.DiscreteSecondDerivativeTest
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DiscreteSecondDerivativeTest
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.FiniteKuzminLandau RiemannGaussian.MonotonePhaseBlocks
open RiemannGaussian.FiniteResonancePartition
open scoped Classical

theorem monotone_of_separation {d : ℕ → ℝ} {N : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → ℓ * ((j : ℝ) - i) ≤ d j - d i) :
    MonotoneOn d (Set.Iio N) := by
  intro i hi j hj hij
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hs := hsep i hi j hj hij
  have hp := mul_nonneg hℓ (sub_nonneg.mpr hijR)
  linarith

theorem resonant_band_bound (φ : ℕ → ℝ) (N : ℕ) (m : ℤ) {η ℓ : ℝ}
    (hη : 0 ≤ η) (hℓ : 0 < ℓ)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      ℓ * ((j : ℝ) - i) ≤ increment φ j - increment φ i) :
    ‖∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) - η)
      ((m : ℝ) * (2 * Real.pi) + η), rotation (φ n)‖ ≤ 2 * η / ℓ + 1 := by
  have hc := band_card_le hℓ
    (show (m : ℝ) * (2 * Real.pi) - η ≤ (m : ℝ) * (2 * Real.pi) + η by linarith)
    (monotone_of_separation hℓ.le hsep) hsep
  have hn := norm_sum_le (band (increment φ) N ((m : ℝ) * (2 * Real.pi) - η)
    ((m : ℝ) * (2 * Real.pi) + η)) (fun n ↦ rotation (φ n))
  simp only [norm_rotation, Finset.sum_const, nsmul_eq_mul, mul_one] at hn
  have he : (m : ℝ) * (2 * Real.pi) + η - ((m : ℝ) * (2 * Real.pi) - η) =
      2 * η := by ring
  rw [he] at hc
  exact hn.trans hc

theorem cells_card_le_of_separation {d : ℕ → ℝ} {N : ℕ} (η : ℝ) {U : ℝ}
    (hU : 0 ≤ U) (hd : MonotoneOn d (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → d j - d i ≤ U * ((j : ℝ) - i)) :
    ((cells d N η).card : ℝ) ≤ U * N / (2 * Real.pi) + 2 := by
  apply (cells_card_le η hd).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * Real.pi)
  by_cases hN : N = 0
  · subst N
    simp
  have hs := hsep 0 (by omega) (N - 1) (by omega) (Nat.zero_le _)
  have hn : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  simp only [Nat.cast_zero, sub_zero] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hn hU)

theorem bound (φ : ℕ → ℝ) (N : ℕ) {η ℓ U : ℝ}
    (hη : 0 < η) (hηπ : η ≤ Real.pi) (hℓ : 0 < ℓ) (hU : 0 ≤ U)
    (hlo : ∀ i < N, ∀ j < N, i ≤ j →
      ℓ * ((j : ℝ) - i) ≤ increment φ j - increment φ i)
    (hhi : ∀ i < N, ∀ j < N, i ≤ j →
      increment φ j - increment φ i ≤ U * ((j : ℝ) - i)) :
    ‖∑ n ∈ Finset.range N, rotation (φ n)‖ ≤
      (U * N / (2 * Real.pi) + 2) * (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
  have hd := monotone_of_separation hℓ.le hlo
  rw [sum_eq_bands (increment φ) N (fun n ↦ rotation (φ n)) hη.le hηπ hd]
  calc
    _ ≤ ∑ m ∈ cells (increment φ) N η,
        ‖(∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) - η)
          ((m : ℝ) * (2 * Real.pi) + η), rotation (φ n)) +
            ∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) + η)
              ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η), rotation (φ n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ cells (increment φ) N η, (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
      apply Finset.sum_le_sum
      intro m _
      exact (norm_add_le _ _).trans (add_le_add
        (resonant_band_bound φ N m hη.le hℓ hlo)
        (nonresonant_band_bound φ N m hη hd))
    _ = ((cells (increment φ) N η).card : ℝ) *
        (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (cells_card_le_of_separation η hU hd hhi)
      (by positivity)

end
end RiemannGaussian.DiscreteSecondDerivativeTest

end


-- Sidon.NumberTheory.RiemannGaussian.SecondDerivativeIncrements
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.SecondDerivativeIncrements
noncomputable section
open RiemannGaussian.FiniteKuzminLandau
theorem difference_bounds (f f' : ℝ → ℝ) {a b ℓ U : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hr : ∀ x ∈ Set.Icc a b, ℓ ≤ f' x ∧ f' x ≤ U) :
    ℓ * (b - a) ≤ f b - f a ∧ f b - f a ≤ U * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy ↦ hd y (Set.Ioo_subset_Icc_self hy))
  have he' : f' x * (b - a) = f b - f a :=
    (eq_div_iff (sub_pos.mpr hab).ne').mp he
  have hr' := hr x (Set.Ioo_subset_Icc_self hx)
  constructor <;> nlinarith [hr'.1, hr'.2]

def unitIncrement (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 1) - f x

theorem hasDerivAt_unitIncrement (f f' : ℝ → ℝ) (x : ℝ)
    (h0 : HasDerivAt f (f' x) x) (h1 : HasDerivAt f (f' (x + 1)) (x + 1)) :
    HasDerivAt (unitIncrement f) (f' (x + 1) - f' x) x := by
  convert! (h1.comp x ((hasDerivAt_id x).add_const 1)).sub h0 using 1
  simp only [mul_one]

theorem unitIncrement_eq (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    unitIncrement f (a + n) = increment (fun k ↦ f (a + k)) n := by
  simp only [unitIncrement, increment, Nat.cast_add, Nat.cast_one, add_assoc]

theorem increment_gap_bounds (f f' f'' : ℝ → ℝ) (a : ℝ) (N : ℕ) {ℓ U : ℝ}
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hd' : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f' (f'' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ f'' x ∧ f'' x ≤ U)
    {i j : ℕ} (hj : j < N) (hij : i ≤ j) :
    ℓ * ((j : ℝ) - i) ≤
        increment (fun k ↦ f (a + k)) j - increment (fun k ↦ f (a + k)) i ∧
      increment (fun k ↦ f (a + k)) j - increment (fun k ↦ f (a + k)) i ≤
        U * ((j : ℝ) - i) := by
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hjR : (j : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_iff.mpr hj
  have hsub {x : ℝ} (hx : x ∈ Set.Icc (a + i) (a + j)) :
      Set.Icc x (x + 1) ⊆ Set.Icc a (a + N) := by
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Nat.cast_nonneg (α := ℝ) i]
  have hg : ∀ x ∈ Set.Icc (a + i) (a + j),
      HasDerivAt (unitIncrement f) (f' (x + 1) - f' x) x := by
    intro x hx
    exact hasDerivAt_unitIncrement f f' x
      (hd x (hsub hx ⟨le_rfl, by linarith⟩))
      (hd (x + 1) (hsub hx ⟨by linarith, le_rfl⟩))
  have hgr : ∀ x ∈ Set.Icc (a + i) (a + j),
      ℓ ≤ f' (x + 1) - f' x ∧ f' (x + 1) - f' x ≤ U := by
    intro x hx
    have h := difference_bounds f' f'' (show x ≤ x + 1 by linarith)
      (fun y hy ↦ hd' y (hsub hx hy)) (fun y hy ↦ hr y (hsub hx hy))
    simpa only [add_sub_cancel_left, mul_one] using h
  have h := difference_bounds (unitIncrement f) (fun x ↦ f' (x + 1) - f' x)
    (show a + (i : ℝ) ≤ a + j by linarith) hg hgr
  simpa only [unitIncrement_eq, add_sub_add_left_eq_sub] using h

end
end RiemannGaussian.SecondDerivativeIncrements

end


-- Sidon.NumberTheory.RiemannGaussian.SecondDerivativeTest
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.SecondDerivativeTest
noncomputable section
open RiemannGaussian.PhaseIncrementInverse
theorem bound (f f' f'' : ℝ → ℝ) (a : ℝ) (N : ℕ) {η ℓ U : ℝ}
    (hη : 0 < η) (hηπ : η ≤ Real.pi) (hℓ : 0 < ℓ) (hU : 0 ≤ U)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hd' : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f' (f'' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ f'' x ∧ f'' x ≤ U) :
    ‖∑ n ∈ Finset.range N, rotation (f (a + n))‖ ≤
      (U * N / (2 * Real.pi) + 2) * (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
  apply DiscreteSecondDerivativeTest.bound _ N hη hηπ hℓ hU
  · intro i _ j hj hij
    exact (SecondDerivativeIncrements.increment_gap_bounds f f' f'' a N hd hd' hr hj hij).1
  · intro i _ j hj hij
    exact (SecondDerivativeIncrements.increment_gap_bounds f f' f'' a N hd hd' hr hj hij).2

theorem square_root_bound (f f' f'' : ℝ → ℝ) (a : ℝ) (N : ℕ) {ℓ A : ℝ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hA : 0 ≤ A)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hd' : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f' (f'' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ f'' x ∧ f'' x ≤ A * ℓ) :
    ‖∑ n ∈ Finset.range N, rotation (f (a + n))‖ ≤
      (A * N * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
        (3 + 2 * Real.pi) := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hs1 : Real.sqrt ℓ ≤ 1 := Real.sqrt_le_one.mpr hℓ1
  have hsπ : Real.sqrt ℓ ≤ Real.pi := hs1.trans (by linarith [Real.two_le_pi])
  have hs2 := Real.sq_sqrt hℓ.le
  have h := bound f f' f'' a N hs hsπ hℓ (mul_nonneg hA hℓ.le) hd hd' hr
  have hi : 2 * Real.sqrt ℓ / ℓ + 1 + 2 * Real.pi / Real.sqrt ℓ ≤
      (3 + 2 * Real.pi) / Real.sqrt ℓ := by
    apply (le_div_iff₀ hs).mpr
    have he : (2 * Real.sqrt ℓ / ℓ + 1 + 2 * Real.pi / Real.sqrt ℓ) * Real.sqrt ℓ =
        2 + Real.sqrt ℓ + 2 * Real.pi := by
      field_simp
      nlinarith [hs2]
    rw [he]
    linarith
  have he : (A * ℓ * N / (2 * Real.pi) + 2) *
      ((3 + 2 * Real.pi) / Real.sqrt ℓ) =
        (A * N * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
          (3 + 2 * Real.pi) := by
    field_simp
    rw [hs2]
    ring
  exact (h.trans (mul_le_mul_of_nonneg_left hi (by positivity))).trans_eq he

end
end RiemannGaussian.SecondDerivativeTest

end


-- Sidon.NumberTheory.RiemannGaussian.LogarithmicSecondDerivativeTest
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.LogarithmicSecondDerivativeTest
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.LogarithmicShiftPhase
theorem hasDerivAt_first (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ -t / y) (t / x ^ 2) x := by
  convert! (hasDerivAt_const x (-t)).div (hasDerivAt_id x) hx.ne' using 1
  simp only [zero_mul, mul_one, zero_sub, neg_neg, id_eq]

theorem curvature_bounds {t x X : ℝ} (ht : 0 ≤ t) (hX : 0 < X)
    (hl : X ≤ x) (hu : x ≤ 2 * X) :
    t / (4 * X ^ 2) ≤ t / x ^ 2 ∧ t / x ^ 2 ≤ t / X ^ 2 := by
  have hx : 0 < x := hX.trans_le hl
  have hlo : X ^ 2 ≤ x ^ 2 := sq_le_sq₀ hX.le hx.le |>.mpr hl
  have hhi : x ^ 2 ≤ 4 * X ^ 2 := by nlinarith
  exact ⟨div_le_div_of_nonneg_left ht (sq_pos_of_pos hx) hhi,
    div_le_div_of_nonneg_left ht (sq_pos_of_pos hX) hlo⟩

theorem square_root_bound {t X a : ℝ} (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) (htX : t ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N, rotation (phase t (a + n))‖ ≤
      (4 * N * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
        2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi) := by
  have hdom {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) :
      0 < x ∧ X ≤ x ∧ x ≤ 2 * X := ⟨hX.trans_le (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  have he : 4 * (t / (4 * X ^ 2)) = t / X ^ 2 := by ring
  apply SecondDerivativeTest.square_root_bound (phase t) (fun x ↦ -t / x)
    (fun x ↦ t / x ^ 2) a N (by positivity)
    ((div_le_one (by positivity : 0 < 4 * X ^ 2)).mpr htX) (by norm_num)
    (fun _ hx ↦ hasDerivAt_phase t (hdom hx).1)
    (fun _ hx ↦ hasDerivAt_first t (hdom hx).1)
  intro x hx
  rw [he]
  exact curvature_bounds ht.le hX (hdom hx).2.1 (hdom hx).2.2

end
end RiemannGaussian.LogarithmicSecondDerivativeTest

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaFiniteDifferencing
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaFiniteDifferencing
noncomputable section
open Complex RiemannGaussian.LogarithmicShiftPhase
open scoped Classical

theorem feature_polar (s : ℂ) (n : ℕ) :
    zetaPrimeFeature s n = (zetaPrimeExpWeight s.re n : ℂ) *
      Complex.exp (((phase s.im (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [zetaPrimeFeature, zetaPrimeExpWeight, phase, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

end
end RiemannGaussian.ZetaFiniteDifferencing

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletSecondDerivativeBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletSecondDerivativeBound
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.LogarithmicShiftPhase
open scoped Classical

theorem damping_antitoneOn {σ : ℝ} (hσ : 0 ≤ σ) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-σ * Real.log x)) (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (Real.log_le_log hx hxy) (neg_nonpos.mpr hσ))

theorem damped_bound {σ t X a : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) (htX : t ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N,
      (Real.exp (-σ * Real.log (a + n)) : ℂ) * rotation (phase t (a + n))‖ ≤
        ((4 * N * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
          2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi)) *
            Real.exp (-σ * Real.log a) := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  | succ N =>
    have hw : ∀ n ≤ N, 0 ≤ Real.exp (-σ * Real.log (a + n)) :=
      fun _ _ ↦ (Real.exp_pos _).le
    have hm : AntitoneOn (fun n : ℕ ↦ Real.exp (-σ * Real.log (a + n)))
        (Set.Icc 0 N) := by
      intro i _ j _ hij
      apply damping_antitoneOn hσ
      · change 0 < a + (i : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) i]
      · change 0 < a + (j : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      · have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
    have hp (n : ℕ) (hn : n ≤ N) :
        ‖∑ k ∈ Finset.range (n + 1), rotation (phase t (a + k))‖ ≤
          (4 * (N + 1 : ℕ) * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
            2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi) := by
      have hb' : a + (n + 1 : ℕ) ≤ 2 * X := by
        have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
        push_cast at hb ⊢
        linarith
      apply (LogarithmicSecondDerivativeTest.square_root_bound ht hX ha (n + 1) hb' htX).trans
      gcongr
    simpa only [Nat.cast_zero, add_zero, Nat.succ_eq_add_one] using
      FiniteAbelVariation.decreasing_bound (fun n ↦ Real.exp (-σ * Real.log (a + n)))
        (fun n ↦ rotation (phase t (a + n))) N hw hm hp

theorem feature_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ))
    (hb : (a : ℝ) + N ≤ 2 * X) (htX : s.im ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      ((4 * N * Real.sqrt (s.im / (4 * X ^ 2)) / (2 * Real.pi) +
        2 / Real.sqrt (s.im / (4 * X ^ 2))) * (3 + 2 * Real.pi)) *
          zetaPrimeExpWeight s.re a := by
  simpa only [ZetaFiniteDifferencing.feature_polar, zetaPrimeExpWeight, Nat.cast_add,
    PhaseIncrementInverse.rotation] using damped_bound hσ ht hX ha N hb htX

end
end RiemannGaussian.DirichletSecondDerivativeBound

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteDiscreteSobolev
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ ‖f i‖) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
  apply ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i)))).mpr
    (norm_sum_le _ _)).trans
  simpa only [mul_one, mul_comm] using h

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteShiftCorrelation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteShiftCorrelation
noncomputable section
open Complex Filter Topology
open scoped Classical

def correlation (f : ℤ → ℂ) (h : ℤ) : ℂ :=
  ∑' n : ℤ, f (n + h) * starRingEnd ℂ (f n)

def shiftedSum (f : ℤ → ℂ) (H : ℕ) (n : ℤ) : ℂ :=
  ∑ h ∈ Finset.range H, f (n + h)

private theorem finite_shift {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    Function.HasFiniteSupport (fun n ↦ f (n + h)) :=
  hf.fun_comp_of_injective (Equiv.addRight h).injective

private theorem finite_pair {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h k : ℤ) :
    Function.HasFiniteSupport (fun n ↦ f (n + h) * starRingEnd ℂ (f (n + k))) :=
  (finite_shift hf h).fun_mul_left _

theorem summable_correlation {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    Summable (fun n : ℤ ↦ f (n + h) * starRingEnd ℂ (f n)) :=
  summable_of_hasFiniteSupport ((finite_shift hf h).fun_mul_left _)

theorem correlation_re {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    (correlation f h).re = ∑' n : ℤ, (f (n + h) * starRingEnd ℂ (f n)).re :=
  Complex.re_tsum (summable_correlation hf h)

theorem correlation_zero {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) :
    (correlation f 0).re = ∑' n : ℤ, ‖f n‖ ^ 2 := by
  rw [correlation_re hf]
  simp only [add_zero, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem mixed_shift_eq (f : ℤ → ℂ) (h k : ℤ) :
    (∑' n : ℤ, f (n + h) * starRingEnd ℂ (f (n + k))) = correlation f (h - k) := by
  calc
    _ = ∑' n : ℤ, f ((n + k) + (h - k)) * starRingEnd ℂ (f (n + k)) := by
      apply tsum_congr
      intro n
      congr 2
      ring
    _ = _ := (Equiv.addRight k).tsum_eq
      (fun n : ℤ ↦ f (n + (h - k)) * starRingEnd ℂ (f n))

theorem correlation_neg (f : ℤ → ℂ) (h : ℤ) :
    correlation f (-h) = starRingEnd ℂ (correlation f h) := by
  simp only [correlation, Complex.conj_tsum]
  calc
    _ = ∑' n : ℤ, f n * starRingEnd ℂ (f (n + h)) := by
      simpa only [zero_sub, add_zero, correlation] using (mixed_shift_eq f 0 h).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [map_mul, starRingEnd_self_apply, mul_comm]

theorem correlation_neg_re (f : ℤ → ℂ) (h : ℤ) :
    (correlation f (-h)).re = (correlation f h).re := by
  rw [correlation_neg, Complex.conj_re]

theorem shiftedSum_mass {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, shiftedSum f H n) = (H : ℂ) * ∑' n : ℤ, f n := by
  unfold shiftedSum
  rw [Summable.tsum_finsetSum (s := Finset.range H)
    (fun (h : ℕ) _ ↦ summable_of_hasFiniteSupport (finite_shift hf (h : ℤ)))]
  have hshift (h : ℕ) : (∑' n : ℤ, f (n + h)) = ∑' n : ℤ, f n :=
    (Equiv.addRight (h : ℤ)).tsum_eq f
  simp only [hshift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem norm_sq_shiftedSum_eq (f : ℤ → ℂ) (H : ℕ) (n : ℤ) :
    ‖shiftedSum f H n‖ ^ 2 = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
      (f (n + h) * starRingEnd ℂ (f (n + k))).re := by
  calc
    _ = (shiftedSum f H n * starRingEnd ℂ (shiftedSum f H n)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    _ = _ := by
      simp only [shiftedSum, map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Complex.re_sum]

theorem shiftedSum_energy {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, ‖shiftedSum f H n‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
  have hp (h k : ℕ) : Function.HasFiniteSupport
      (fun n : ℤ ↦ (f (n + h) * starRingEnd ℂ (f (n + k))).re) :=
    (finite_pair hf h k).fun_comp (by simp)
  have hi (h : ℕ) : Summable
      (fun n : ℤ ↦ ∑ k ∈ Finset.range H, (f (n + h) * starRingEnd ℂ (f (n + k))).re) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.sum (hp h) (Finset.range H))
  simp_rw [norm_sq_shiftedSum_eq]
  rw [Summable.tsum_finsetSum (fun h _ ↦ hi h)]
  apply Finset.sum_congr rfl
  intro h _
  rw [Summable.tsum_finsetSum (fun k _ ↦ summable_of_hasFiniteSupport (hp h k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.re_tsum (summable_of_hasFiniteSupport (finite_pair hf h k)), mixed_shift_eq]

theorem shiftedSum_eq_zero_outside {f : ℤ → ℂ} {a : ℤ} {N H : ℕ}
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    ∀ n ∉ Finset.Ico (a - H + 1) (a + N), shiftedSum f H n = 0 := by
  intro n hn
  apply Finset.sum_eq_zero
  intro h hh
  apply hf
  intro hm
  apply hn
  simp only [Finset.mem_Ico] at hm ⊢
  have hh' := Finset.mem_range.mp hh
  omega

theorem norm_sum_sq_le_correlation_matrix {f : ℤ → ℂ} {a : ℤ} {N H : ℕ}
    (hH : 0 < H) (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) *
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
  have hfinite : Function.HasFiniteSupport f :=
    (Finset.Ico a (a + N)).finite_toSet.subset (by
      intro n hn
      by_contra h
      exact hn (hf n h))
  let S := Finset.Ico (a - H + 1) (a + N)
  have hs := shiftedSum_eq_zero_outside (H := H) hf
  have hmass : (∑ n ∈ S, shiftedSum f H n) =
      (H : ℂ) * ∑ n ∈ Finset.Ico a (a + N), f n := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ) hs,
      shiftedSum_mass hfinite, tsum_eq_sum hf]
  have henergy : (∑ n ∈ S, ‖shiftedSum f H n‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (fun n hn ↦ by rw [hs n hn, norm_zero, zero_pow (by decide)])]
    exact shiftedSum_energy hfinite H
  have hcard : (S.card : ℝ) = (N : ℝ) + H - 1 := by
    have h := Int.card_Ico_of_le (a := a - H + 1) (b := a + N) (by omega)
    have hc : (S.card : ℤ) = (N : ℤ) + H - 1 := by dsimp [S]; linarith
    exact_mod_cast hc
  have h := norm_sum_sq_le_card_mul_sum_norm_sq S (shiftedSum f H)
  rw [hmass, henergy, hcard, norm_mul, Complex.norm_natCast, mul_pow] at h
  exact h

end
end RiemannGaussian.FiniteShiftCorrelation

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteVanDerCorput
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteVanDerCorput
noncomputable section
open Complex Filter Topology RiemannGaussian.FiniteShiftCorrelation
open scoped Classical

private theorem sum_reverse_lags (g : ℤ → ℝ) (H : ℕ) :
    (∑ k ∈ Finset.range H, g ((H : ℤ) - k)) =
      ∑ k ∈ Finset.range H, g ((k : ℤ) + 1) := by
  calc
    _ = ∑ k ∈ Finset.range H, g (((H - 1 - k : ℕ) : ℤ) + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      have hk' := Finset.mem_range.mp hk
      omega
    _ = _ := Finset.sum_range_reflect (fun k : ℕ ↦ g ((k : ℤ) + 1)) H

theorem toeplitz_sum_eq (g : ℤ → ℝ) (hg : ∀ h : ℤ, g (-h) = g h) (H : ℕ) :
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, g ((h : ℤ) - k)) =
      (H : ℝ) * g 0 +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * g ((h : ℤ) + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hs : (∑ h ∈ Finset.range H, g ((h : ℤ) - H)) =
        ∑ h ∈ Finset.range H, g ((H : ℤ) - h) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [show (h : ℤ) - H = -((H : ℤ) - h) by ring, hg]
    have hD : (∑ h ∈ Finset.range (H + 1), ∑ k ∈ Finset.range (H + 1),
        g ((h : ℤ) - k)) =
          (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, g ((h : ℤ) - k)) +
            2 * (∑ h ∈ Finset.range H, g ((h : ℤ) + 1)) + g 0 := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
      rw [hs, sum_reverse_lags]
      ring
    have hW : (∑ h ∈ Finset.range (H + 1),
        (((H + 1 : ℕ) : ℝ) - h - 1) * g ((h : ℤ) + 1)) =
          (∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * g ((h : ℤ) + 1)) +
            ∑ h ∈ Finset.range H, g ((h : ℤ) + 1) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (H : ℝ) + 1 - H - 1 = 0 by ring, zero_mul, add_zero,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun h _ ↦ by ring)
    rw [hD, ih, hW]
    push_cast
    ring

theorem signed_bound {f : ℤ → ℂ} {a : ℤ} {N H : ℕ} (hH : 0 < H)
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖f n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * (correlation f ((h : ℤ) + 1)).re) := by
  have hfinite : Function.HasFiniteSupport f :=
    (Finset.Ico a (a + N)).finite_toSet.subset (by
      intro n hn
      by_contra h
      exact hn (hf n h))
  have h := norm_sum_sq_le_correlation_matrix hH hf
  rw [toeplitz_sum_eq (fun h ↦ (correlation f h).re) (correlation_neg_re f),
    correlation_zero hfinite,
    tsum_eq_sum (fun n hn ↦ by rw [hf n hn, norm_zero, zero_pow (by decide)])] at h
  exact h

theorem absolute_bound {f : ℤ → ℂ} {a : ℤ} {N H : ℕ} (hH : 0 < H)
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖f n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) * ‖correlation f ((h : ℤ) + 1)‖) := by
  apply (signed_bound hH hf).trans
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast Nat.succ_le_iff.mpr hH
  apply mul_le_mul_of_nonneg_left _
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : 0 ≤ (N : ℝ) + H - 1)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro h hh
  have hh' : (h : ℝ) + 1 ≤ H := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hh)
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by linarith)

end
end RiemannGaussian.FiniteVanDerCorput

end


-- Sidon.NumberTheory.RiemannGaussian.FiniteVanDerCorputPhase
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.FiniteVanDerCorputPhase
noncomputable section
open Complex RiemannGaussian.FiniteShiftCorrelation
open scoped Classical

def windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ico a (a + N) then b n else 0

theorem windowed_on (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {n : ℤ}
    (hn : n ∈ Finset.Ico a (a + N)) : windowed a N b n = b n := by
  simp only [windowed, ite_eq_left hn]

theorem windowed_outside (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    ∀ n ∉ Finset.Ico a (a + N), windowed a N b n = 0 := by
  intro n hn
  simp only [windowed, ite_eq_right hn]

theorem sum_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), windowed a N b n) =
      ∑ n ∈ Finset.Ico a (a + N), b n :=
  Finset.sum_congr rfl (fun _ hn ↦ windowed_on a N b hn)

theorem energy_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), ‖windowed a N b n‖ ^ 2) =
      ∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2 :=
  Finset.sum_congr rfl (fun _ hn ↦ by rw [windowed_on a N b hn])

theorem correlation_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {h : ℤ} (hh : 0 ≤ h) :
    correlation (windowed a N b) h =
      ∑ n ∈ Finset.Ico a (a + N - h), b (n + h) * starRingEnd ℂ (b n) := by
  calc
    _ = ∑ n ∈ Finset.Ico a (a + N - h),
        windowed a N b (n + h) * starRingEnd ℂ (windowed a N b n) := by
      apply tsum_eq_sum
      intro n hn
      by_cases hb : n ∈ Finset.Ico a (a + N)
      · have hs : n + h ∉ Finset.Ico a (a + N) := by
          simp only [Finset.mem_Ico] at hb hn ⊢
          omega
        simp only [windowed, ite_eq_right hs, zero_mul]
      · simp only [windowed, ite_eq_right hb, map_zero, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hb : n ∈ Finset.Ico a (a + N) := by
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      have hs : n + h ∈ Finset.Ico a (a + N) := by
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      rw [windowed_on a N b hb, windowed_on a N b hs]

theorem absolute_window_bound (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), b n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            b (n + ((h : ℤ) + 1)) * starRingEnd ℂ (b n)‖) := by
  have h := FiniteVanDerCorput.absolute_bound hH (windowed_outside a N b)
  rw [sum_windowed, energy_windowed] at h
  have hc (k : ℕ) := correlation_windowed a N b (h := (k : ℤ) + 1) (by omega)
  simpa only [hc] using h

def phaseTerm (w : ℤ → ℂ) (φ : ℤ → ℝ) (n : ℤ) : ℂ :=
  w n * Complex.exp ((φ n : ℂ) * Complex.I)

theorem norm_phaseTerm (w : ℤ → ℂ) (φ : ℤ → ℝ) (n : ℤ) :
    ‖phaseTerm w φ n‖ = ‖w n‖ := by
  rw [phaseTerm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem phaseTerm_pair (w : ℤ → ℂ) (φ : ℤ → ℝ) (n h : ℤ) :
    phaseTerm w φ (n + h) * starRingEnd ℂ (phaseTerm w φ n) =
      (w (n + h) * starRingEnd ℂ (w n)) *
        Complex.exp (((φ (n + h) - φ n : ℝ) : ℂ) * Complex.I) := by
  simp only [phaseTerm, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem absolute_phase_bound (a : ℤ) (N : ℕ) (w : ℤ → ℂ) (φ : ℤ → ℝ)
    {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), phaseTerm w φ n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖w n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            (w (n + ((h : ℤ) + 1)) * starRingEnd ℂ (w n)) *
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)‖) := by
  simpa only [norm_phaseTerm, phaseTerm_pair] using
    absolute_window_bound a N (phaseTerm w φ) hH

theorem unit_phase_bound (a : ℤ) (N : ℕ) (φ : ℤ → ℝ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N),
      Complex.exp ((φ n : ℂ) * Complex.I)‖ ^ 2 ≤
        ((N : ℝ) + H - 1) * ((H : ℝ) * N +
          2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
            ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)‖) := by
  have hc : (Finset.Ico a (a + N)).card = N := by
    rw [Int.card_Ico]
    simp
  simpa only [phaseTerm, map_one, one_mul, norm_one, one_pow,
    Finset.sum_const, hc, nsmul_eq_mul, mul_one] using
      absolute_phase_bound a N (fun _ ↦ 1) φ hH

end
end RiemannGaussian.FiniteVanDerCorputPhase

end


-- Sidon.NumberTheory.RiemannGaussian.NatPhaseDifferencing
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.NatPhaseDifferencing
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.FiniteVanDerCorputPhase
open scoped Classical

theorem sum_Ico_zero (N : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico 0 (N : ℤ), f n) = ∑ n ∈ Finset.range N, f n := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp

theorem overlap_eq (φ : ℕ → ℝ) (N h : ℕ) :
    (∑ n ∈ Finset.Ico 0 ((N : ℤ) - h),
      rotation (φ (n + h).toNat - φ n.toNat)) =
        ∑ n ∈ Finset.range (N - h), rotation (φ (n + h) - φ n) := by
  by_cases hh : h ≤ N
  · rw [show (N : ℤ) - h = ((N - h : ℕ) : ℤ) by omega, sum_Ico_zero]
    apply Finset.sum_congr rfl
    intro n _
    simp only [← Int.natCast_add, Int.toNat_natCast]
  · rw [Finset.Ico_eq_empty (by omega), Nat.sub_eq_zero_of_le (by omega),
      Finset.range_zero, Finset.sum_empty, Finset.sum_empty]

theorem trivial_bound (φ : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, rotation (φ n)‖ ≤ N := by
  simpa only [norm_rotation, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    using norm_sum_le (Finset.range N) (fun n ↦ rotation (φ n))

theorem bound (φ : ℕ → ℝ) (N : ℕ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, rotation (φ n)‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * N +
        2 * ∑ k ∈ Finset.range H, ((H : ℝ) - k - 1) *
          ‖∑ n ∈ Finset.range (N - (k + 1)), rotation (φ (n + (k + 1)) - φ n)‖) := by
  have hv := unit_phase_bound 0 N (fun n : ℤ ↦ φ n.toNat) hH
  simp only [zero_add, sum_Ico_zero,
    Int.toNat_natCast] at hv
  have he (k : ℕ) : (∑ n ∈ Finset.Ico 0 ((N : ℤ) - ((k : ℤ) + 1)),
      rotation (φ (n + ((k : ℤ) + 1)).toNat - φ n.toNat)) =
        ∑ n ∈ Finset.range (N - (k + 1)), rotation (φ (n + (k + 1)) - φ n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using overlap_eq φ N (k + 1)
  simp only [PhaseIncrementInverse.rotation] at he
  simpa only [he, PhaseIncrementInverse.rotation] using hv

end
end RiemannGaussian.NatPhaseDifferencing

end


-- Sidon.NumberTheory.RiemannGaussian.ShiftedDerivativeFamily
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ShiftedDerivativeFamily
noncomputable section

def difference (F : ℕ → ℝ → ℝ) (h : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  F r (x + h) - F r x

theorem hasDerivAt_difference (F : ℕ → ℝ → ℝ) (h : ℝ) (r : ℕ) (x : ℝ)
    (h0 : HasDerivAt (F r) (F (r + 1) x) x)
    (h1 : HasDerivAt (F r) (F (r + 1) (x + h)) (x + h)) :
    HasDerivAt (difference F h r) (difference F h (r + 1) x) x := by
  convert! (h1.comp x ((hasDerivAt_id x).add_const h)).sub h0 using 1
  simp only [difference, mul_one]

theorem overlap_subset (a : ℝ) {N h : ℕ} (hh : h ≤ N) {x : ℝ}
    (hx : x ∈ Set.Icc a (a + (N - h : ℕ))) :
    Set.Icc x (x + h) ⊆ Set.Icc a (a + N) := by
  have hc : ((N - h : ℕ) : ℝ) = (N : ℝ) - h := Nat.cast_sub hh
  rw [hc] at hx
  intro y hy
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem derivative_family (F : ℕ → ℝ → ℝ) (a : ℝ) (N q h : ℕ) (hh : h ≤ N)
    (hd : ∀ r < q, ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F r) (F (r + 1) x) x) :
    ∀ r < q, ∀ x ∈ Set.Icc a (a + (N - h : ℕ)),
      HasDerivAt (difference F h r) (difference F h (r + 1) x) x := by
  intro r hr x hx
  have hsub := overlap_subset a hh hx
  exact hasDerivAt_difference F h r x
    (hd r hr x (hsub ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) h]⟩))
    (hd r hr (x + h) (hsub ⟨by linarith [Nat.cast_nonneg (α := ℝ) h], le_rfl⟩))

theorem top_bounds (F : ℕ → ℝ → ℝ) (a : ℝ) (N q h : ℕ) (hh : h ≤ N)
    {ℓ A : ℝ}
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ F (q + 1) x ∧ F (q + 1) x ≤ A * ℓ) :
    ∀ x ∈ Set.Icc a (a + (N - h : ℕ)),
      (h : ℝ) * ℓ ≤ difference F h q x ∧ difference F h q x ≤ A * ((h : ℝ) * ℓ) := by
  intro x hx
  have hsub := overlap_subset a hh hx
  have hb := SecondDerivativeIncrements.difference_bounds (F q) (F (q + 1))
    (show x ≤ x + (h : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) h])
    (fun y hy ↦ hd y (hsub hy)) (fun y hy ↦ hr y (hsub hy))
  simpa only [difference, add_sub_cancel_left, mul_comm ℓ (h : ℝ),
    mul_assoc, mul_comm ℓ (h : ℝ)] using hb

end
end RiemannGaussian.ShiftedDerivativeFamily

end


-- Sidon.NumberTheory.RiemannGaussian.HigherDerivativeTest
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.HigherDerivativeTest
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.DerivativeRecursionBudget RiemannGaussian.ShiftedDerivativeFamily
open scoped Classical

theorem bound (κ : Cutoffs) (k L : ℕ) (F : ℕ → ℝ → ℝ) (a : ℝ) (N : ℕ)
    {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hNL : N ≤ L)
    (hd : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F r) (F (r + 1) x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ F (k + 2) x ∧ F (k + 2) x ≤ A * ℓ) :
    ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ≤ budget κ k L ℓ A := by
  induction k generalizing F a N ℓ with
  | zero =>
    have hNLr : (N : ℝ) ≤ L := by exact_mod_cast hNL
    have ht := (NatPhaseDifferencing.trivial_bound (fun n ↦ F 0 (a + n)) N).trans hNLr
    rw [budget]
    by_cases hℓ1 : ℓ ≤ 1
    · rw [ite_eq_left ⟨hℓ, hℓ1⟩]
      apply le_min ht
      apply (SecondDerivativeTest.square_root_bound (F 0) (F 1) (F 2) a N hℓ hℓ1 hA
        (hd 0 (by omega)) (hd 1 (by omega)) hr).trans
      gcongr
    · rw [ite_eq_right (fun h ↦ hℓ1 h.2)]
      exact ht
  | succ k ih =>
    have hNLr : (N : ℝ) ≤ L := by exact_mod_cast hNL
    have ht := (NatPhaseDifferencing.trivial_bound (fun n ↦ F 0 (a + n)) N).trans hNLr
    let H := shiftCount κ k L ℓ A
    have hH : 0 < H := shiftCount_pos κ k L ℓ A
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    let C (j : ℕ) := budget κ k L (((j : ℝ) + 1) * ℓ) A
    have hc (j : ℕ) :
        ‖∑ n ∈ Finset.range (N - (j + 1)),
          rotation (F 0 (a + (n + (j + 1) : ℕ)) - F 0 (a + n))‖ ≤ C j := by
      by_cases hj : j + 1 ≤ N
      · let G := difference F (j + 1 : ℕ)
        have hdG : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + (N - (j + 1) : ℕ)),
            HasDerivAt (G r) (G (r + 1) x) x :=
          derivative_family F a N (k + 2) (j + 1) hj (fun r hr ↦ hd r (by omega))
        have hrG := top_bounds F a N (k + 2) (j + 1) hj
          (hd (k + 2) (by omega)) hr
        have he : (∑ n ∈ Finset.range (N - (j + 1)),
            rotation (F 0 (a + (n + (j + 1) : ℕ)) - F 0 (a + n))) =
              ∑ n ∈ Finset.range (N - (j + 1)), rotation (G 0 (a + n)) := by
          apply Finset.sum_congr rfl
          intro n _
          simp only [G, difference, Nat.cast_add, Nat.cast_one, add_assoc]
        rw [he]
        have hi := ih G a (N - (j + 1)) (by positivity : 0 < (j + 1 : ℕ) * ℓ)
          (by omega) hdG hrG
        simpa only [C, Nat.cast_add, Nat.cast_one] using hi
      · rw [Nat.sub_eq_zero_of_le (by omega), Finset.range_zero, Finset.sum_empty, norm_zero]
        exact DerivativeRecursionBudget.nonneg κ k L _ hA
    let S := ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * C j
    have hS : 0 ≤ S := by
      apply Finset.sum_nonneg
      intro j hj
      have hjR : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      exact mul_nonneg (by linarith) (DerivativeRecursionBudget.nonneg κ k L _ hA)
    have hv := NatPhaseDifferencing.bound (fun n ↦ F 0 (a + n)) N hH
    have hinner : (H : ℝ) * N +
        2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
          ‖∑ n ∈ Finset.range (N - (j + 1)),
            rotation (F 0 (a + (n + (j + 1) : ℕ)) - F 0 (a + n))‖ ≤
              (H : ℝ) * L + 2 * S := by
      apply add_le_add (mul_le_mul_of_nonneg_left hNLr (by positivity))
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro j hj
      have hjR : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      exact mul_le_mul_of_nonneg_left (hc j) (by linarith)
    have hu : (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ^ 2 ≤
        ((L : ℝ) + H - 1) * ((H : ℝ) * L + 2 * S) := by
      apply hv.trans
      exact (mul_le_mul_of_nonneg_left hinner
        (by linarith [Nat.cast_nonneg (α := ℝ) N])).trans
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have hHpos : 0 < (H : ℝ) ^ 2 := by positivity
    have hsq : ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ^ 2 ≤
        (((L : ℝ) + H - 1) * ((H : ℝ) * L + 2 * S)) / (H : ℝ) ^ 2 := by
      apply (le_div_iff₀ hHpos).mpr
      simpa only [mul_comm] using hu
    have hq := (sq_nonneg ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖).trans hsq
    rw [budget]
    apply le_min ht
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hq]
    exact hsq

end
end RiemannGaussian.HigherDerivativeTest

end


-- Sidon.NumberTheory.RiemannGaussian.PhaseConjugation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.PhaseConjugation
noncomputable section
open RiemannGaussian.PhaseIncrementInverse
open scoped Classical

theorem rotation_neg (x : ℝ) :
    rotation (-x) = starRingEnd ℂ (rotation x) := by
  simp only [PhaseIncrementInverse.rotation, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

theorem norm_sum_neg {ι : Type*} (S : Finset ι) (φ : ι → ℝ) :
    ‖∑ n ∈ S, rotation (-φ n)‖ = ‖∑ n ∈ S, rotation (φ n)‖ := by
  simp only [rotation_neg, ← map_sum, Complex.norm_conj]

theorem norm_sum_neg_one_pow {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (k : ℕ) :
    ‖∑ n ∈ S, rotation ((-1 : ℝ) ^ k * φ n)‖ = ‖∑ n ∈ S, rotation (φ n)‖ := by
  induction k with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
    simp only [pow_succ, mul_neg_one, neg_mul]
    rw [norm_sum_neg]
    exact ih

theorem neg_one_pow_mul_self (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  simpa only [mul_pow, one_pow] using
    congrArg (fun x : ℝ ↦ x ^ k) (show (-1 : ℝ) * -1 = 1 by norm_num)

end
end RiemannGaussian.PhaseConjugation

end


-- Sidon.NumberTheory.RiemannGaussian.LogarithmicDerivativeFamily
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.LogarithmicDerivativeFamily
noncomputable section
open RiemannGaussian.LogarithmicShiftPhase
def jet (t : ℝ) : ℕ → ℝ → ℝ
  | 0, x => phase t x
  | r + 1, x => (-1 : ℝ) ^ (r + 1) * t * (r.factorial : ℝ) / x ^ (r + 1)

theorem hasDerivAt_jet (t : ℝ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet t r) (jet t (r + 1) x) x := by
  cases r with
  | zero =>
    convert! hasDerivAt_phase t hx using 1
    norm_num [jet]
  | succ r =>
    have hd := (hasDerivAt_const x ((-1 : ℝ) ^ (r + 1) * t * (r.factorial : ℝ))).div
      ((hasDerivAt_id x).pow (r + 1)) (pow_ne_zero _ hx.ne')
    convert! hd using 1
    dsimp [jet]
    simp only [zero_mul, zero_sub, mul_one, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp

def oriented (t : ℝ) (m r : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ m * jet t r x

theorem hasDerivAt_oriented (t : ℝ) (m r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (oriented t m r) (oriented t m (r + 1) x) x :=
  (hasDerivAt_jet t r hx).const_mul _

theorem oriented_top (t : ℝ) (r : ℕ) (x : ℝ) :
    oriented t (r + 1) (r + 1) x = t * (r.factorial : ℝ) / x ^ (r + 1) := by
  unfold oriented
  rw [jet]
  calc
    _ = ((-1 : ℝ) ^ (r + 1) * (-1 : ℝ) ^ (r + 1)) * t * (r.factorial : ℝ) /
        x ^ (r + 1) := by ring
    _ = _ := by rw [PhaseConjugation.neg_one_pow_mul_self, one_mul]

def lowerScale (t X : ℝ) (k : ℕ) : ℝ :=
  t * ((k + 1).factorial : ℝ) / (2 * X) ^ (k + 2)

def ratio (k : ℕ) : ℝ := (2 : ℝ) ^ (k + 2)

theorem lowerScale_pos {t X : ℝ} (ht : 0 < t) (hX : 0 < X) (k : ℕ) :
    0 < lowerScale t X k := by
  unfold lowerScale
  positivity

theorem ratio_pos (k : ℕ) : 0 < ratio k := by
  unfold ratio
  positivity

theorem dyadic_bounds {t X x : ℝ} (ht : 0 ≤ t) (hX : 0 < X) (k : ℕ)
    (hl : X ≤ x) (hu : x ≤ 2 * X) :
    lowerScale t X k ≤ oriented t (k + 2) (k + 2) x ∧
      oriented t (k + 2) (k + 2) x ≤ ratio k * lowerScale t X k := by
  have hx : 0 < x := hX.trans_le hl
  have he : ratio k * lowerScale t X k = t * ((k + 1).factorial : ℝ) / X ^ (k + 2) := by
    unfold ratio lowerScale
    rw [mul_pow]
    field_simp
  change lowerScale t X k ≤ oriented t ((k + 1) + 1) ((k + 1) + 1) x ∧ _
  rw [oriented_top, he]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < x ^ (k + 2))
    gcongr
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < X ^ (k + 2))
    gcongr

end
end RiemannGaussian.LogarithmicDerivativeFamily

end


-- Sidon.NumberTheory.RiemannGaussian.HigherLogarithmicDerivativeBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.HigherLogarithmicDerivativeBound
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.LogarithmicShiftPhase RiemannGaussian.LogarithmicDerivativeFamily
open RiemannGaussian.DerivativeRecursionBudget
theorem bound (κ : Cutoffs) (k L : ℕ) {t X a : ℝ} (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hNL : N ≤ L) (hb : a + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, rotation (phase t (a + n))‖ ≤
      budget κ k L (lowerScale t X k) (ratio k) := by
  have hdom {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) :
      0 < x ∧ X ≤ x ∧ x ≤ 2 * X :=
    ⟨hX.trans_le (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  have hd : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + N),
      HasDerivAt (oriented t (k + 2) r) (oriented t (k + 2) (r + 1) x) x :=
    fun r _ _ hx ↦ hasDerivAt_oriented t (k + 2) r (hdom hx).1
  have hr : ∀ x ∈ Set.Icc a (a + N),
      lowerScale t X k ≤ oriented t (k + 2) (k + 2) x ∧
        oriented t (k + 2) (k + 2) x ≤ ratio k * lowerScale t X k :=
    fun _ hx ↦ dyadic_bounds ht.le hX k (hdom hx).2.1 (hdom hx).2.2
  have h := HigherDerivativeTest.bound κ k L (oriented t (k + 2)) a N
    (lowerScale_pos ht hX k) (ratio_pos k).le hNL hd hr
  change ‖∑ n ∈ Finset.range N, rotation ((-1 : ℝ) ^ (k + 2) * phase t (a + n))‖ ≤ _ at h
  rw [PhaseConjugation.norm_sum_neg_one_pow] at h
  exact h

end
end RiemannGaussian.HigherLogarithmicDerivativeBound

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletHigherDerivativeBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletHigherDerivativeBound
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.LogarithmicShiftPhase RiemannGaussian.LogarithmicDerivativeFamily
open RiemannGaussian.DerivativeRecursionBudget
open scoped Classical

theorem damped_bound (κ : Cutoffs) (k : ℕ) {σ t X a : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N,
      (Real.exp (-σ * Real.log (a + n)) : ℂ) * rotation (phase t (a + n))‖ ≤
        budget κ k N (lowerScale t X k) (ratio k) *
          Real.exp (-σ * Real.log a) := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (DerivativeRecursionBudget.nonneg κ k 0 _ (ratio_pos k).le)
      (Real.exp_pos _).le
  | succ N =>
    have hw : ∀ n ≤ N, 0 ≤ Real.exp (-σ * Real.log (a + n)) :=
      fun _ _ ↦ (Real.exp_pos _).le
    have hm : AntitoneOn (fun n : ℕ ↦ Real.exp (-σ * Real.log (a + n)))
        (Set.Icc 0 N) := by
      intro i _ j _ hij
      apply DirichletSecondDerivativeBound.damping_antitoneOn hσ
      · change 0 < a + (i : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) i]
      · change 0 < a + (j : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      · have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
    have hp (n : ℕ) (hn : n ≤ N) :
        ‖∑ k ∈ Finset.range (n + 1), rotation (phase t (a + k))‖ ≤
          budget κ k (N + 1) (lowerScale t X k) (ratio k) := by
      have hb' : a + (n + 1 : ℕ) ≤ 2 * X := by
        have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
        push_cast at hb ⊢
        linarith
      exact HigherLogarithmicDerivativeBound.bound κ k (N + 1) ht hX ha (n + 1)
        (by omega) hb'
    simpa only [Nat.cast_zero, add_zero, Nat.succ_eq_add_one] using
      FiniteAbelVariation.decreasing_bound (fun n ↦ Real.exp (-σ * Real.log (a + n)))
        (fun n ↦ rotation (phase t (a + n))) N hw hm hp

theorem feature_bound (κ : Cutoffs) (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ))
    (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      budget κ k N (lowerScale s.im X k) (ratio k) *
          zetaPrimeExpWeight s.re a := by
  simpa only [ZetaFiniteDifferencing.feature_polar, zetaPrimeExpWeight, Nat.cast_add,
    PhaseIncrementInverse.rotation] using damped_bound κ k hσ ht hX ha N hb

end
end RiemannGaussian.DirichletHigherDerivativeBound

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletPowerParameters
noncomputable section
open RiemannGaussian.DerivativePowerExponents
def line (k : ℕ) : ℝ := 1 - ((k : ℝ) + 2) * alpha k

def slope (k : ℕ) : ℝ := 2 * ((k : ℝ) + 2) * alpha k - amp k

def transition (k : ℕ) : ℝ := 1 / ((k : ℝ) + amp k)

theorem denominator_ge_order (k : ℕ) : (k : ℝ) + 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem order_mul_alpha_le_one (k : ℕ) : ((k : ℝ) + 2) * alpha k ≤ 1 := by
  have hd := denominator_ge_two k
  unfold alpha
  rw [mul_one_div]
  apply (div_le_one (by linarith)).mpr
  exact denominator_ge_order k

theorem line_nonneg (k : ℕ) : 0 ≤ line k := by
  unfold line
  linarith [order_mul_alpha_le_one k]

theorem line_lt_one (k : ℕ) : line k < 1 := by
  unfold line
  have hp : 0 < ((k : ℝ) + 2) * alpha k := mul_pos (by positivity) (alpha_pos k)
  linarith

theorem half_le_line_succ (k : ℕ) : 1 / 2 ≤ line (k + 1) := by
  have hb : ∀ j : ℕ, 2 * ((j : ℝ) + 3) + 2 ≤ (2 : ℝ) ^ (j + 3) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show j + 1 + 3 = (j + 3) + 1 by omega, pow_succ]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hd := denominator_ge_two (k + 1)
  have h : ((k : ℝ) + 3) * alpha (k + 1) ≤ 1 / 2 := by
    unfold alpha
    rw [mul_one_div]
    apply (div_le_iff₀ (by linarith)).mpr
    have h := hb k
    rw [show k + 1 + 2 = k + 3 by omega]
    linarith
  unfold line
  push_cast
  linarith

theorem amp_alpha_identity (k : ℕ) : amp k * (1 + 2 * alpha k) = 4 * alpha k := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hd := denominator_ge_two k
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hD : -2 + (2 : ℝ) ^ k * 4 ≠ 0 := by nlinarith
  unfold amp alpha
  rw [pow_add]
  norm_num
  field_simp
  ring_nf
  field_simp
  ring

theorem slope_eq (k : ℕ) : slope k = 2 * alpha k * ((k : ℝ) + amp k) := by
  unfold slope
  nlinarith [amp_alpha_identity k]

theorem slope_pos (k : ℕ) : 0 < slope k := by
  rw [slope_eq]
  have hp := amp_pos k
  have ha := alpha_pos k
  positivity

theorem transition_balance (k : ℕ) : transition k * slope k = 2 * alpha k := by
  rw [transition, slope_eq]
  have hp : (k : ℝ) + amp k ≠ 0 := ne_of_gt (by have h := amp_pos k; positivity)
  field_simp

end
end RiemannGaussian.DirichletPowerParameters

end


-- Sidon.NumberTheory.RiemannGaussian.UniformDerivativePowerBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.UniformDerivativePowerBound
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativeRecursionBudget
open RiemannGaussian.DerivativePowerEnvelope
open scoped Classical

theorem budget_bound (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget cutoffs k L ℓ A ≤ envelope k L ℓ A := by
  have hA0 : 0 ≤ A := by linarith
  by_cases hL : L = 0
  · subst L
    have hz := le_length cutoffs k 0 ℓ A
    simp only [Nat.cast_zero] at hz ⊢
    exact hz.trans (DerivativePowerEnvelope.nonneg k (by norm_num : (0 : ℝ) ≤ 0) hℓ.le hA0)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
  induction k generalizing ℓ with
  | zero => exact base_bound cutoffs L hℓ hA
  | succ k ih =>
    have hm := main_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le hA0
    have he := error_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le
    by_cases hlarge : 1 ≤ ℓ
    · have hmain := main_ge_length (k + 1) (Nat.cast_nonneg (α := ℝ) L) hlarge hA
      apply (le_length cutoffs (k + 1) L ℓ A).trans
      unfold envelope
      nlinarith
    have hsmall : ℓ ≤ 1 := le_of_lt (lt_of_not_ge hlarge)
    by_cases hH : shiftCount cutoffs k L ℓ A ≤ L
    · apply DerivativePowerStep.successor_bound k L hℓ hsmall hA hH
      intro j _
      exact ih (by positivity : 0 < ((j : ℝ) + 1) * ℓ)
    · have hLu := length_lt_ideal k L hℓ A (by omega)
      have herror := error_ge_length k hLr hℓ hLu.le
      apply (le_length cutoffs (k + 1) L ℓ A).trans
      unfold envelope
      nlinarith

end
end RiemannGaussian.UniformDerivativePowerBound

end


-- Sidon.NumberTheory.RiemannGaussian.UniformDirichletPowerBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.UniformDirichletPowerBound
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativePowerEnvelope
open RiemannGaussian.LogarithmicDerivativeFamily
theorem ratio_amp_le_four (k : ℕ) : (ratio k) ^ amp k ≤ 4 := by
  have hg : ∀ j : ℕ, ((j + 2 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      push_cast at ih ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have he : ((k + 2 : ℕ) : ℝ) * amp k ≤ 2 := by
    unfold amp
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mpr (hg k)
  unfold ratio
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at h ⊢
  exact h

theorem feature_bound (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ)) (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      envelope k N (lowerScale s.im X k) (ratio k) * zetaPrimeExpWeight s.re a := by
  have hratio : 1 ≤ ratio k := by
    unfold ratio
    exact one_le_pow₀ (by norm_num)
  apply (DirichletHigherDerivativeBound.feature_bound cutoffs k hσ ht hX a N ha hb).trans
  exact mul_le_mul_of_nonneg_right
    (UniformDerivativePowerBound.budget_bound k N (lowerScale_pos ht hX k) hratio)
    (Real.exp_pos _).le

theorem uniform_bound (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ)) (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      32 * (4 * N * (lowerScale s.im X k) ^ alpha k +
        (N : ℝ) ^ beta k * (lowerScale s.im X k) ^ (-alpha k)) *
          zetaPrimeExpWeight s.re a := by
  apply (feature_bound k hσ ht hX a N ha hb).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  unfold envelope mainTerm errorTerm
  have hscale := lowerScale_pos ht hX k
  gcongr
  exact ratio_amp_le_four k

end
end RiemannGaussian.UniformDirichletPowerBound

end


-- TH8000DerivativeTools
section

namespace RiemannGaussian.FirstDerivativeTest
noncomputable section
open RiemannGaussian.FiniteKuzminLandau RiemannGaussian.PhaseIncrementInverse
open scoped Classical

theorem increment_witness (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hd : ∀ x ∈ Set.Icc a (a + N + 1), HasDerivAt f (f' x) x)
    {n : ℕ} (hn : n ≤ N) :
    ∃ x ∈ Set.Ioo (a + n) (a + n + 1),
      f' x = increment (fun k ↦ f (a + k)) n := by
  have hsub : Set.Icc (a + n) (a + n + 1) ⊆ Set.Icc a (a + N + 1) := by
    intro x hx
    have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
    constructor <;> linarith [hx.1, hx.2, Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f'
    (show a + (n : ℝ) < a + n + 1 by linarith)
    (fun y hy ↦ (hd y (hsub hy)).continuousAt.continuousWithinAt)
    (fun y hy ↦ hd y (hsub (Set.Ioo_subset_Icc_self hy)))
  refine ⟨x, hx, ?_⟩
  rw [show a + (n : ℝ) + 1 - (a + n) = 1 by ring, div_one] at he
  simpa only [increment, Nat.cast_add, Nat.cast_one, add_assoc] using he

theorem bound_succ (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ x ∈ Set.Icc a (a + N + 1), HasDerivAt f (f' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N + 1), f' x ∈ Set.Icc η (2 * Real.pi - η))
    (hm : MonotoneOn f' (Set.Icc a (a + N + 1)) ∨
      AntitoneOn f' (Set.Icc a (a + N + 1))) :
    ‖∑ n ∈ Finset.range (N + 1), rotation (f (a + n))‖ ≤ 2 * Real.pi / η := by
  have hsub {n : ℕ} (hn : n ≤ N) {x : ℝ}
      (hx : x ∈ Set.Ioo (a + n) (a + n + 1)) : x ∈ Set.Icc a (a + N + 1) := by
    have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
    constructor <;> linarith [hx.1, hx.2, Nat.cast_nonneg (α := ℝ) n]
  apply FiniteKuzminLandau.bound (fun n ↦ f (a + n)) N hη
  · intro n hn
    obtain ⟨x, hx, he⟩ := increment_witness f f' a N hd hn
    rw [← he]
    exact hr x (hsub hn hx)
  · have hord {i j : ℕ} (hij : i < j) {x y : ℝ}
        (hx : x ∈ Set.Ioo (a + i) (a + i + 1))
        (hy : y ∈ Set.Ioo (a + j) (a + j + 1)) : x ≤ y := by
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr hij
      linarith [hx.2, hy.1]
    rcases hm with hm | hm
    · left
      intro i hi j hj hij
      rcases hij.eq_or_lt with rfl | hij
      · rfl
      obtain ⟨x, hx, he⟩ := increment_witness f f' a N hd hi.2
      obtain ⟨y, hy, hf⟩ := increment_witness f f' a N hd hj.2
      rw [← he, ← hf]
      exact hm (hsub hi.2 hx) (hsub hj.2 hy) (hord hij hx hy)
    · right
      intro i hi j hj hij
      rcases hij.eq_or_lt with rfl | hij
      · rfl
      obtain ⟨x, hx, he⟩ := increment_witness f f' a N hd hi.2
      obtain ⟨y, hy, hf⟩ := increment_witness f f' a N hd hj.2
      rw [← he, ← hf]
      exact hm (hsub hi.2 hx) (hsub hj.2 hy) (hord hij hx hy)

theorem bound (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), f' x ∈ Set.Icc η (2 * Real.pi - η))
    (hm : MonotoneOn f' (Set.Icc a (a + N)) ∨ AntitoneOn f' (Set.Icc a (a + N))) :
    ‖∑ n ∈ Finset.range N, rotation (f (a + n))‖ ≤ 2 * Real.pi / η := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  | succ N =>
    apply bound_succ f f' a N hη
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using hd
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using hr
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using hm

end
end RiemannGaussian.FirstDerivativeTest

end


-- TH8000LongBlock
section

namespace GoldbachHurwitz
open Real Finset
open RiemannGaussian PhaseIncrementInverse LogarithmicShiftPhase

theorem long_unweighted {T X a : ℝ} (hT : 0 < T) (hTX : T ≤ X) (ha : X ≤ a)
    (N : ℕ) (hb : a+N ≤ 2*X) :
    ‖∑ n ∈ range N, PhaseIncrementInverse.rotation (phase T (a+n))‖ ≤ 4*π*X/T := by
  let η := T/(2*X)
  have hX := hT.trans_le hTX
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one (by positivity)]
    linarith
  have hD (x : ℝ) (hx : x ∈ Set.Icc a (a+N)) :
      HasDerivAt (fun u : ℝ => T*log u) (T/x) x := by
    have ht := (Real.hasDerivAt_log (lt_of_lt_of_le hX (ha.trans hx.1)).ne').const_mul T
    simpa only [div_eq_mul_inv] using ht
  have hr (x : ℝ) (hx : x ∈ Set.Icc a (a+N)) : T/x ∈ Set.Icc η (2*π-η) := by
    have hx0 := hX.trans_le (ha.trans hx.1)
    refine ⟨div_le_div_of_nonneg_left hT.le hx0 (hx.2.trans hb), ?_⟩
    have h1 := (div_le_one hx0).mpr (hTX.trans (ha.trans hx.1))
    linarith [Real.pi_gt_three]
  have hmono : AntitoneOn (fun x : ℝ => T/x) (Set.Icc a (a+N)) := by
    intro x hx y _ hxy
    exact div_le_div_of_nonneg_left hT.le (hX.trans_le (ha.trans hx.1)) hxy
  have H := FirstDerivativeTest.bound _ _ a N hη hD hr (Or.inr hmono)
  calc
    _ = ‖∑ n ∈ range N, PhaseIncrementInverse.rotation (T*log (a+n))‖ := by
      simpa only [phase, neg_mul] using
        PhaseConjugation.norm_sum_neg (range N) (fun n : ℕ => T*log (a+n))
    _ ≤ 2*π/η := H
    _ = 4*π*X/T := by dsimp [η]; field_simp; ring

theorem long_critical_block {T X a : ℝ} (hT : 0 < T) (hTX : T ≤ X) (ha : X ≤ a)
    (N : ℕ) (hb : a+N ≤ 2*X) :
    ‖∑ n ∈ range N, (Real.exp (-(1/2:ℝ)*log (a+n)) : ℂ) *
        PhaseIncrementInverse.rotation (phase T (a+n))‖ ≤
      4*π*X/T * Real.exp (-(1/2:ℝ)*log a) := by
  have hX := hT.trans_le hTX
  cases N with
  | zero => simp only [range_zero, sum_empty, norm_zero]; positivity
  | succ N =>
    have hw : ∀ n ≤ N, 0 ≤ Real.exp (-(1/2:ℝ)*log (a+n)) := fun _ _ => (exp_pos _).le
    have hm : AntitoneOn (fun n : ℕ => Real.exp (-(1/2:ℝ)*log (a+n))) (Set.Icc 0 N) := by
      intro i _ j _ hij
      apply DirichletSecondDerivativeBound.damping_antitoneOn (by norm_num : (0:ℝ)≤1/2)
      · exact add_pos_of_pos_of_nonneg (hX.trans_le ha) (Nat.cast_nonneg i)
      · exact add_pos_of_pos_of_nonneg (hX.trans_le ha) (Nat.cast_nonneg j)
      · gcongr
    have hp (n : ℕ) (hn : n ≤ N) :
        ‖∑ k ∈ range (n+1), PhaseIncrementInverse.rotation (phase T (a+k))‖ ≤ 4*π*X/T := by
      apply long_unweighted hT hTX ha
      have hc : ((n+1:ℕ):ℝ) ≤ ((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ hn
      linarith
    simpa only [Nat.cast_zero, add_zero, Nat.succ_eq_add_one] using
      FiniteAbelVariation.decreasing_bound (fun n : ℕ => Real.exp (-(1/2:ℝ)*log (a+n)))
        (fun n => PhaseIncrementInverse.rotation (phase T (a+n))) N hw hm hp

theorem long_critical_capped {T X a : ℝ} (hT : 1 ≤ T) (hTX : T ≤ X) (ha : X ≤ a)
    (N : ℕ) (hb : a+N ≤ 2*X) (hcap : X ≤ 9*T^2) :
    ‖∑ n ∈ range N, (Real.exp (-(1/2:ℝ)*log (a+n)) : ℂ) *
        PhaseIncrementInverse.rotation (phase T (a+n))‖ ≤ 12*π := by
  have ht : 0 < T := by linarith
  have hx := ht.trans_le hTX
  have hmul : Real.exp (-(1/2:ℝ)*log a) ≤ (Real.sqrt X)⁻¹ := by
    rw [show -(1/2:ℝ)*log a = -(log a * (1/2)) by ring, Real.exp_neg,
      ← Real.rpow_def_of_pos (hx.trans_le ha), ← Real.sqrt_eq_rpow]
    exact inv_anti₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt ha)
  have hs : Real.sqrt X ≤ 3*T := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have hsq := Real.sq_sqrt hx.le
  calc
    _ ≤ _ := long_critical_block ht hTX ha N hb
    _ ≤ 4*π*X/T * (Real.sqrt X)⁻¹ := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 4*π*(Real.sqrt X)/T := by field_simp [(Real.sqrt_pos.mpr hx).ne', ht.ne']; nlinarith
    _ ≤ 12*π := (div_le_iff₀ ht).mpr (by nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le])

end GoldbachHurwitz

end


-- TH8000ShiftScale
section

namespace GoldbachCentralSeven.ShiftWeyl

theorem third_scale {a t : ℝ} (ht : 1 ≤ t) (h : a ≤ t^(2/3:ℝ)) :
    Real.sqrt a*t^(-(1/6:ℝ)) ≤ t^(1/6:ℝ) := by
  have htpos := zero_lt_one.trans_le ht
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_eq_rpow (t^(2/3:ℝ)), ← Real.rpow_mul htpos.le,
    show (2/3:ℝ)*(1/2) = 1/3 by norm_num] at hs
  apply (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg htpos.le _)).trans_eq
  rw [← Real.rpow_add htpos]
  norm_num

theorem second_scale {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t)
    (hlo : t^(2/3:ℝ) ≤ a) (hhi : a ≤ t^(4/3:ℝ)) :
    t ≤ 4*a^2 ∧ Real.sqrt (t/a) ≤ t^(1/6:ℝ) ∧ Real.sqrt (a/t) ≤ t^(1/6:ℝ) := by
  have htp := zero_lt_one.trans_le ht
  have hsq : t ≤ a^2 := by
    calc
      _ ≤ t^(4/3:ℝ) := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1:ℝ) ≤ 4/3)
      _ = (t^(2/3:ℝ))^2 := by rw [← Real.rpow_two, ← Real.rpow_mul htp.le]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg htp.le _) hlo 2
  have htd : t/a ≤ t^(1/3:ℝ) := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ = t^(1/3:ℝ)*t^(2/3:ℝ) := by rw [← Real.rpow_add htp]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg htp.le _)
  have had : a/t ≤ t^(1/3:ℝ) := by
    apply (div_le_iff₀ htp).mpr
    apply hhi.trans_eq
    rw [show (4/3:ℝ) = 1/3+1 by norm_num, Real.rpow_add htp, Real.rpow_one]
  have hs : Real.sqrt (t^(1/3:ℝ)) = t^(1/6:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul htp.le]; norm_num
  exact ⟨by nlinarith only [hsq, sq_nonneg a], (Real.sqrt_le_sqrt htd).trans_eq hs,
    (Real.sqrt_le_sqrt had).trans_eq hs⟩

end GoldbachCentralSeven.ShiftWeyl

end


-- TH8000ShiftWeyl
section

namespace GoldbachCentralSeven.ShiftWeyl

open RiemannGaussian
open RiemannGaussian.LogarithmicShiftPhase RiemannGaussian.PhaseIncrementInverse
open RiemannGaussian.LogarithmicDerivativeFamily RiemannGaussian.AnalyticDerivativeCutoff
open RiemannGaussian.DerivativePowerEnvelope RiemannGaussian.DerivativePowerExponents

noncomputable def block (a t : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.range L,
    (Real.exp (-(1/2:ℝ) * Real.log (a+n)) : ℂ) *
      RiemannGaussian.PhaseIncrementInverse.rotation (phase t (a+n))

private theorem damp_eq {a : ℝ} (ha : 0 < a) :
    Real.exp (-(1/2:ℝ)*Real.log a) = a^(-(1/2:ℝ)) := by
  rw [Real.rpow_def_of_pos ha]; congr 1; ring

private theorem scale_rpow {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (s : ℝ) :
    (lowerScale t a 1)^s = (4:ℝ)^(-s)*t^s*a^(-3*s) := by
  have hscale : lowerScale t a 1 = (4:ℝ)^(-(1:ℝ))*t*a^(-(3:ℝ)) := by
    unfold lowerScale
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), Real.rpow_neg ha.le, Real.rpow_one]
    norm_num [Nat.factorial]
    field_simp
    ring
  rw [hscale, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) ht.le, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4),
    ← Real.rpow_mul ha.le]
  congr 2
  ring

theorem third_derivative {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (L : ℕ) (hL : (L:ℝ) ≤ a) :
    ‖block a t L‖ ≤ 128*(t^(1/6:ℝ) + Real.sqrt a*t^(-(1/6:ℝ))) := by
  let s := lowerScale t a 1
  have hs : 0 < s := lowerScale_pos ht ha 1
  have h := DirichletHigherDerivativeBound.damped_bound cutoffs 1
    (σ := (1/2:ℝ)) (by norm_num) ht ha le_rfl L (by linarith)
  have hb := UniformDerivativePowerBound.budget_bound 1 L hs (by norm_num [ratio] : 1 ≤ ratio 1)
  have hnum := UniformDirichletPowerBound.ratio_amp_le_four 1
  have henv : envelope 1 L s (ratio 1) ≤
      32*(4*a*s^(1/6:ℝ) + a^(1/2:ℝ)*s^(-(1/6:ℝ))) := by
    have ha1 : alpha 1 = 1/6 := by norm_num [alpha]
    have hb1 : beta 1 = 1/2 := by norm_num [beta, amp]
    simp only [envelope, mainTerm, errorTerm, ha1, hb1]
    gcongr
  change ‖block a t L‖ ≤ _ at h
  rw [damp_eq ha] at h
  have hw := h.trans (mul_le_mul_of_nonneg_right (hb.trans henv) (by positivity))
  have hp1 : (4:ℝ)^(-(1/6:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hp2 : (4:ℝ)^(1/6:ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (1/6:ℝ) ≤ 1)
  have hprod : a * a^(-(1/2:ℝ)) * a^(-(1/2:ℝ)) = 1 := by
    rw [mul_assoc, ← Real.rpow_add ha, show -(1/2:ℝ) + -(1/2) = -1 by norm_num,
      Real.rpow_neg_one, mul_inv_cancel₀ ha.ne']
  have hcancel : a^(1/2:ℝ) * a^(-(1/2:ℝ)) = 1 := by rw [← Real.rpow_add ha]; norm_num
  apply hw.trans
  dsimp only [s]
  rw [scale_rpow ha ht, scale_rpow ha ht, neg_neg,
    show (-3:ℝ)*(1/6) = -(1/2) by norm_num,
    show (-3:ℝ)*(-(1/6)) = 1/2 by norm_num, Real.sqrt_eq_rpow]
  calc
    _ = 128*((4:ℝ)^(-(1/6:ℝ))*t^(1/6:ℝ))*(a*a^(-(1/2:ℝ))*a^(-(1/2:ℝ))) +
        32*((4:ℝ)^(1/6:ℝ)*t^(-(1/6:ℝ)))*a^(1/2:ℝ)*(a^(1/2:ℝ)*a^(-(1/2:ℝ))) := by ring
    _ ≤ _ := by
      rw [hprod, hcancel, mul_one, mul_one]
      nlinarith only [mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg ht.le (1/6:ℝ)),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp2
          (Real.rpow_nonneg ht.le (-(1/6:ℝ)))) (Real.rpow_nonneg ha.le (1/2:ℝ))]

theorem second_derivative {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (L : ℕ) (hL : (L:ℝ) ≤ a)
    (htA : t ≤ 4*a^2) :
    ‖block a t L‖ ≤ 44*(Real.sqrt (t/a) + Real.sqrt (a/t)) := by
  have h := DirichletSecondDerivativeBound.damped_bound (σ := (1/2:ℝ))
    (by norm_num) ht ha le_rfl L (by linarith) htA
  change ‖block a t L‖ ≤ _ at h
  have hs : Real.sqrt (t/(4*a^2)) = Real.sqrt t / (2*a) := by
    rw [Real.sqrt_div ht.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq ha.le]
    norm_num
  rw [damp_eq ha, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow, hs] at h
  rw [Real.sqrt_div ht.le, Real.sqrt_div ha.le]
  have hst := Real.sqrt_pos.mpr ht
  have hsa := Real.sqrt_pos.mpr ha
  have hpi : (0:ℝ) < 2*Real.pi := by positivity
  apply h.trans
  calc
    _ ≤ (4*a*(Real.sqrt t/(2*a))/(2*Real.pi)+2/(Real.sqrt t/(2*a)))*
        (3+2*Real.pi)*(Real.sqrt a)⁻¹ := by gcongr
    _ = ((Real.sqrt t / Real.sqrt a)/Real.pi + 4*(Real.sqrt a/Real.sqrt t))*
        (3+2*Real.pi) := by
      generalize he : Real.sqrt a = u
      have hsq : u^2 = a := he ▸ Real.sq_sqrt ha.le
      have hu : 0 < u := he ▸ hsa
      rw [← hsq]
      field_simp
      ring
    _ ≤ _ := by
      have hdiv : (Real.sqrt t / Real.sqrt a)/Real.pi ≤ Real.sqrt t / Real.sqrt a :=
        div_le_self (by positivity) (by linarith [Real.pi_gt_three])
      have h2 : 3+2*Real.pi ≤ 11 := by linarith [Real.pi_lt_four]
      have hh := mul_le_mul (add_le_add_right hdiv (4*(Real.sqrt a/Real.sqrt t))) h2
        (by positivity) (by positivity)
      nlinarith only [hh, (show 0 ≤ Real.sqrt t / Real.sqrt a by positivity)]

theorem critical_sixth {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t) (L : ℕ) (hL : (L:ℝ) ≤ a)
    (hupper : a ≤ t^(4/3:ℝ)) :
    ‖block a t L‖ ≤ 256*t^(1/6:ℝ) := by
  have htp := zero_lt_one.trans_le ht
  by_cases hsmall : a ≤ t^(2/3:ℝ)
  · linarith only [third_derivative ha htp L hL, third_scale ht hsmall]
  · obtain ⟨hT, h1, h2⟩ := second_scale ha ht (le_of_not_ge hsmall) hupper
    linarith only [second_derivative ha htp L hL hT, h1, h2,
      Real.rpow_nonneg htp.le (1/6:ℝ)]

theorem cpow_eq_polar {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x:ℂ)^(-(1/2+(t:ℂ)*Complex.I)) =
      (Real.exp (-(1/2:ℝ)*Real.log x):ℂ) * PhaseIncrementInverse.rotation (phase t x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  unfold PhaseIncrementInverse.rotation phase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cpow_sum_eq_block {a : ℝ} (ha : 0 < a) (t : ℝ) (L : ℕ) :
    (∑ n ∈ Finset.range L, (((a+n:ℝ):ℂ)^(-(1/2 + (t:ℂ)*Complex.I)))) = block a t L := by
  exact Finset.sum_congr rfl fun n _ => cpow_eq_polar
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) t

theorem critical_cpow_sixth {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t) (L : ℕ)
    (hL : (L:ℝ) ≤ a) (hupper : a ≤ t^(4/3:ℝ)) :
    ‖∑ n ∈ Finset.range L, (((a+n:ℝ):ℂ)^(-(1/2 + (t:ℂ)*Complex.I)))‖ ≤
      256*t^(1/6:ℝ) := by
  rw [cpow_sum_eq_block ha t L]
  exact critical_sixth ha ht L hL hupper

end GoldbachCentralSeven.ShiftWeyl

end


-- TH8000AllBlocks
section

namespace GoldbachHurwitz
open Finset Real Complex
open scoped ComplexConjugate
open GoldbachCentralSeven.ShiftWeyl

private theorem positive_height {a T : ℝ} (ha : 0 < a) (ht : 1 ≤ T) (L : ℕ)
    (hL : (L:ℝ) ≤ a) (hcap : a ≤ 9*T^2) :
    ‖∑ n ∈ range L, ((a+n:ℝ):ℂ)^(-(1/2+(T:ℂ)*I))‖ ≤ 256*T^(1/6:ℝ) := by
  by_cases h : a ≤ T^(4/3:ℝ)
  · exact critical_cpow_sixth ha ht L hL h
  have hT : T ≤ T^(4/3:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1:ℝ) ≤ 4/3)
  rw [cpow_sum_eq_block ha T L]
  apply (long_critical_capped ht (hT.trans (le_of_not_ge h)) le_rfl L (by linarith) hcap).trans
  have h1 : 1 ≤ T^(1/6:ℝ) := Real.one_le_rpow ht (by norm_num)
  linarith [Real.pi_lt_four]

private theorem conj_power {x : ℝ} (hx : 0 < x) (s : ℂ) :
    conj ((x:ℂ)^(-s)) = (x:ℂ)^(-conj s) := by
  simp only [Complex.cpow_def_of_ne_zero (show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_neg]

theorem critical_blocks {T : ℝ} (ht : 1 ≤ T) (N H : ℕ) (hN : 1 ≤ N) (hH : H ≤ N)
    (hcap : (N:ℝ) ≤ 4*T^2) (α : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1)
    (s : ℂ) (hσ : s.re=1/2) (him : |s.im|=T) :
    ‖∑ n ∈ range H, (((N:ℝ)+α+n:ℝ):ℂ)^(-s)‖ ≤ 256*T^(1/6:ℝ) := by
  let a : ℝ := N+α
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := by dsimp [a]; linarith [hα.1]
  have hl : (H:ℝ) ≤ a := by dsimp [a]; linarith [hα.1, (Nat.cast_le.mpr hH : (H:ℝ) ≤ N)]
  have hc : a ≤ 9*T^2 := by dsimp [a]; nlinarith [hα.2, sq_nonneg (T-1)]
  have h := positive_height ha ht H hl hc
  rcases abs_cases s.im with ⟨him', _⟩ | ⟨him',_⟩
  · have heq : s = (1/2+(T:ℂ)*I) := by
      apply Complex.ext <;> simp [hσ, ←him,him']
    simpa only [heq] using h
  · have heq : conj s = (1/2+(T:ℂ)*I) := by
      apply Complex.ext <;> simp [hσ, ←him,him']
    rw [← heq] at h
    have hsum : (∑ n ∈ range H, ((a+n:ℝ):ℂ)^(-conj s)) =
        conj (∑ n ∈ range H, ((a+n:ℝ):ℂ)^(-s)) := by
      rw [map_sum]
      apply sum_congr rfl
      intro n _
      exact (conj_power (by linarith [Nat.cast_nonneg (α:=ℝ) n]) s).symm
    rwa [hsum, Complex.norm_conj] at h

end GoldbachHurwitz

end


-- TH8000CriticalHurwitz
section

open Finset Filter Complex HurwitzZeta
open OAI.V2

namespace TH8000CriticalHurwitz

def CriticalBlockBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 100 ≤ T →
    ∀ N H : ℕ, 1 ≤ N → H ≤ N → (N:ℝ) ≤ 4*T^2 →
    ∀ a : ℝ, a ∈ Set.Icc 0 1 → ∀ s : ℂ, s.re = 1/2 → |s.im| = T →
      ‖∑ n ∈ Finset.range H, (((N:ℝ)+a+n:ℝ):ℂ)^(-s)‖ ≤ C*T^(1/6:ℝ)

private lemma criticalRemainder {N E : ℝ} (hE : 1≤ E)
    (hNlo : E^2≤ N) (hNhi : N≤4*E^2) {s : ℂ}
    (hσ : 1/2≤ s.re) (hσhi : s.re≤2) (ht : |s.im|=E) :
    N^(1-s.re)/‖1-s‖+N^(-s.re)/2+2*‖s‖*N^(-s.re)/s.re≤15 := by
  have hE0 : 0<E := by linarith
  have hN : 1≤ N := by nlinarith
  have hN0 : 0<N := by linarith
  have hσ0 : 0<s.re := by linarith
  have hden : E≤‖1-s‖ := by
    have hh := Complex.abs_im_le_norm (1-s)
    simpa only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg,ht] using hh
  have hden0 : 0<‖1-s‖ := hE0.trans_le hden
  have hnorm : ‖s‖≤3*E := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hσ0.le,ht] at hh
    linarith
  have hrootlo : E≤ Real.sqrt N := (Real.le_sqrt hE0.le hN0.le).mpr hNlo
  have hroothi : Real.sqrt N≤2*E := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  have hneg : N^(-s.re)≤1/E := by
    calc
      _ ≤ N^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = 1/Real.sqrt N := by rw [Real.rpow_neg hN0.le,← Real.sqrt_eq_rpow]; simp only [one_div]
      _ ≤ _ := one_div_le_one_div_of_le hE0 hrootlo
  have hpos : N^(1-s.re)≤2*E := by
    calc
      _ ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
      _ ≤ _ := hroothi
  have hfirst : N^(1-s.re)/‖1-s‖≤2 := by
    apply (div_le_iff₀ hden0).mpr
    linarith
  have hsecond : N^(-s.re)/2≤1/2 := by
    have hh : 1/E≤1 := (div_le_one hE0).mpr hE
    linarith
  have hthird : 2*‖s‖*N^(-s.re)/s.re≤12 := by
    apply (div_le_iff₀ hσ0).mpr
    have hmul := mul_le_mul hnorm hneg (Real.rpow_nonneg hN0.le _) (by positivity : 0≤3*E)
    have heq : (3*E)*(1/E)=3 := by field_simp
    rw [heq] at hmul
    linarith
  linarith

theorem hurwitz_of_blocks (hb : CriticalBlockBound) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ T : ℝ, Real.exp 100 ≤ T →
      ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ s : ℂ, s.re = 1/2 → |s.im| = T →
        ‖hurwitzZeta (a:UnitAddCircle) s - V29 a s‖ ≤ A*T^(3/16:ℝ) := by
  obtain ⟨C,hC,hblocks⟩ := hb
  refine ⟨15+192*C, by linarith, ?_⟩
  intro T hT a ha s hσ ht
  have hT0 : 0 < T := (Real.exp_pos 100).trans_le hT
  have hT1 : 1 ≤ T := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 100)).trans hT
  let L := Real.log T
  have hL : 100 ≤ L := (Real.le_log_iff_exp_le hT0).mpr hT
  let K := Vce L
  let N := 2^K-1
  obtain ⟨hN,_,hKhi,hsq,hmul⟩ := V1fu hL
  have hKNlo : T^2 ≤ (N:ℝ) := by simpa only [L, Real.exp_log hT0] using hsq
  have hKNhi : (N:ℝ) ≤ 4*T^2 := by simpa only [L, Real.exp_log hT0] using hmul
  have hpoly : ‖∑ n ∈ range N, (((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖ ≤ ((K:ℝ)+1)*(C*T^(1/6:ℝ)) := by
    let f : ℕ → ℂ := fun n => if n=0 then 0 else (((n:ℝ)+a:ℝ):ℂ)^(-s)
    have hB : 0 ≤ C*T^(1/6:ℝ) := mul_nonneg hC.le (Real.rpow_nonneg hT0.le _)
    have hdyad : ∀ k<K, ∀ H : ℕ, H ≤ 2^k → ‖∑ i ∈ range H, f (2^k+i)‖ ≤ C*T^(1/6:ℝ) := by
      intro k hk H hH
      have hkpos : 1 ≤ (2:ℕ)^k := Nat.one_le_pow k 2 (by norm_num)
      have hkN : (2:ℕ)^k ≤ N := by
        have h := Nat.pow_lt_pow_right (by decide : 1 < 2) hk
        dsimp only [N]
        omega
      have hkT := (show (((2:ℕ)^k:ℕ):ℝ) ≤ (N:ℝ) by exact_mod_cast hkN).trans hKNhi
      have heq : (∑ i ∈ range H, f (2^k+i)) =
          ∑ i ∈ range H, (((((2:ℕ)^k:ℕ):ℝ)+a+i:ℝ):ℂ)^(-s) := by
        apply sum_congr rfl
        intro i _
        have hn : 2^k+i ≠ 0 := by omega
        simp only [f,ite_eq_right hn,Nat.cast_add]
        congr 2
        ring
      rw [heq]
      exact hblocks T hT _ H hkpos hH hkT a ha s hσ ht
    have h0 : ‖f 0‖ ≤ C*T^(1/6:ℝ) := by simpa [f] using hB
    have hsum := V1vg f hB h0 K hdyad (2^K) le_rfl
    have hshift : (∑ n ∈ range (2^K), f n) =
        ∑ n ∈ range (2^K-1), (((n+1:ℕ):ℝ)+a:ℂ)^(-s) := by
      have hk : 2^K = (2^K-1)+1 := by have := Nat.one_le_pow K 2 (by norm_num); omega
      rw [hk,sum_range_succ']
      simp only [f,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,ite_true,Nat.add_sub_cancel,
        Complex.ofReal_add,Nat.cast_zero,add_zero]
    rwa [hshift] at hsum
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hσ
  have hcut := V1tf ha (by linarith : (1/10:ℝ) < s.re) hs1 hN
  have hrest := criticalRemainder hT1 hKNlo hKNhi hσ.ge (by linarith) ht
  let P := ∑ n ∈ range N, (((n+1:ℕ):ℝ)+a:ℂ)^(-s)
  have hdiff : ‖hurwitzZeta (a:UnitAddCircle) s - V29 a s - P‖ ≤ 15 := hcut.trans hrest
  have hcost : ‖hurwitzZeta (a:UnitAddCircle) s - V29 a s‖ ≤ 15 + ((K:ℝ)+1)*(C*T^(1/6:ℝ)) := by
    calc
      _ = ‖(hurwitzZeta (a:UnitAddCircle) s - V29 a s - P) + P‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hdiff hpoly)
  have hlog : L+1 ≤ 48*T^(1/48:ℝ) := by
    rw [Real.rpow_def_of_pos hT0]
    have h := Real.add_one_le_exp (L*(1/48:ℝ))
    dsimp only [L] at h ⊢
    linarith
  have hKr : (K:ℝ) ≤ 4*L+2 := hKhi
  have hKfin : (K:ℝ)+1 ≤ 192*T^(1/48:ℝ) := by linarith
  have hpow : T^(1/48:ℝ)*T^(1/6:ℝ)=T^(3/16:ℝ) := by
    rw [←Real.rpow_add hT0]
    norm_num
  have hlarge : 1 ≤ T^(3/16:ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_right hKfin (mul_nonneg hC.le (Real.rpow_nonneg hT0.le (1/6:ℝ)))
  calc
    _ ≤ _ := hcost
    _ ≤ 15 + (192*T^(1/48:ℝ))*(C*T^(1/6:ℝ)) := by linarith only [hscaled]
    _ = 15 + 192*C*T^(3/16:ℝ) := by rw [←hpow]; ring
    _ ≤ _ := by linarith only [hlarge]

theorem character_of_blocks (hb : CriticalBlockBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 100 ≤ T →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      s.re = 1/2 → |s.im| = T →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C*(q:ℝ)^3*T^(3/16:ℝ) := by
  obtain ⟨A,hA,h⟩ := hurwitz_of_blocks hb
  refine ⟨1+A,by linarith,?_⟩
  intro T hT q _ χ s hσ ht
  have hh := OAI.Vg.V14m χ (by linarith) (by linarith) (fun a ha => h T hT a ha s hσ ht)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hT1 : 1 ≤ T := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 100)).trans hT
  have hpow : 1 ≤ T^(3/16:ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hq3 : (q:ℝ) ≤ (q:ℝ)^3 := by simpa using (pow_le_pow_right₀ hq (by norm_num : 1 ≤ 3))
  have hlarge := le_mul_of_one_le_right (pow_nonneg hq0 3) hpow
  have hweight := mul_le_mul_of_nonneg_right hq3
    (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hpow))
  apply hh.trans
  nlinarith only [hlarge,hweight]

theorem actual_blocks : CriticalBlockBound := by
  refine ⟨256, by norm_num, ?_⟩
  intro T hT N H hN hH hcap a ha s hσ ht
  have hT1 : 1 ≤ T := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 100)).trans hT
  exact GoldbachHurwitz.critical_blocks hT1 N H hN hH hcap a ha s hσ ht

theorem critical_character_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 100 ≤ T →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      s.re = 1/2 → |s.im| = T →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C*(q:ℝ)^3*T^(3/16:ℝ) :=
  character_of_blocks actual_blocks

end TH8000CriticalHurwitz

end


-- Sidon.NumberTheory.DirichletMeanSquare
section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

def frequencyChar (ω t : ℝ) : ℂ := Complex.exp ((ω : ℂ) * t * Complex.I)

@[simp] theorem frequencyChar_zero (t : ℝ) : frequencyChar 0 t = 1 := by
  simp [frequencyChar]

@[simp] theorem norm_frequencyChar (ω t : ℝ) : ‖frequencyChar ω t‖ = 1 := by
  simp [frequencyChar, Complex.norm_exp]

theorem continuous_frequencyChar (ω : ℝ) : Continuous (frequencyChar ω) := by
  unfold frequencyChar
  fun_prop

theorem frequencyChar_mul_conj (u v t : ℝ) :
    frequencyChar u t * conj (frequencyChar v t) = frequencyChar (u - v) t := by
  unfold frequencyChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

theorem norm_integral_frequencyChar_le {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, frequencyChar ω t‖ ≤ 2 / |ω| := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have heq : (fun t : ℝ => frequencyChar ω t) =
      (fun t : ℝ => Complex.exp (((ω : ℂ) * Complex.I) * t)) := by
    funext t
    unfold frequencyChar
    congr 1
    ring
  rw [heq, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_div, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg ω)
  calc
    _ ≤ ‖Complex.exp (((ω : ℂ) * Complex.I) * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp]

def finiteFrequencySum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ)
    (t : ℝ) : ℂ := ∑ i ∈ s, a i * frequencyChar (ω i) t

theorem continuous_finiteFrequencySum {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) : Continuous (finiteFrequencySum s a ω) := by
  unfold finiteFrequencySum frequencyChar
  fun_prop

theorem finiteFrequencySum_norm_sq {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    (‖finiteFrequencySum s a ω t‖ ^ 2 : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [finiteFrequencySum, map_sum, map_mul, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← frequencyChar_mul_conj]
  ring

theorem integral_finiteFrequencySum_norm_sq {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖finiteFrequencySum s a ω t‖ ^ 2) =
      (∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) *
        ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t).re := by
  have hpoint (t : ℝ) : ‖finiteFrequencySum s a ω t‖ ^ 2 =
      (∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t).re := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
      congrArg Complex.re (finiteFrequencySum_norm_sq s a ω t)
  simp_rw [hpoint]
  rw [show (∫ t in (0 : ℝ)..T,
      (∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t).re) =
      (∫ t in (0 : ℝ)..T,
        ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t).re from
    Complex.reCLM.intervalIntegral_comp_comm
      ((by unfold frequencyChar; fun_prop : Continuous (fun t : ℝ =>
        ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t)).intervalIntegrable 0 T)]
  congr 1
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (by unfold frequencyChar; fun_prop : Continuous (fun t : ℝ =>
      ∑ j ∈ s, (a i * conj (a j)) * frequencyChar (ω i - ω j) t)).intervalIntegrable 0 T)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (by unfold frequencyChar; fun_prop : Continuous (fun t : ℝ =>
      (a i * conj (a j)) * frequencyChar (ω i - ω j) t)).intervalIntegrable 0 T)]
  simp_rw [intervalIntegral.integral_const_mul]

theorem integral_finiteFrequencySum_norm_sq_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (T : ℝ) (hω : Set.InjOn ω (s : Set ι)) :
    (∫ t in (0 : ℝ)..T, ‖finiteFrequencySum s a ω t‖ ^ 2) ≤
      T * ∑ i ∈ s, ‖a i‖ ^ 2 +
        ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else
          2 * ‖a i‖ * ‖a j‖ / |ω i - ω j| := by
  classical
  rw [integral_finiteFrequencySum_norm_sq]
  simp only [Complex.re_sum]
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ((a i * conj (a j)) * ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t).re ≤
        (if i = j then T * ‖a i‖ ^ 2 else 0) +
        (if i = j then 0 else 2 * ‖a i‖ * ‖a j‖ / |ω i - ω j|) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, frequencyChar_zero, intervalIntegral.integral_const,
        sub_zero, Complex.real_smul, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        ite_true, add_zero]
      simp [← Complex.ofReal_pow, mul_comm]
    · simp only [hij, ite_false, zero_add]
      have hgap : ω i - ω j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hω hi hj h))
      calc
        _ ≤ ‖(a i * conj (a j)) * ∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t‖ :=
          Complex.re_le_norm _
        _ = (‖a i‖ * ‖a j‖) * ‖∫ t in (0 : ℝ)..T, frequencyChar (ω i - ω j) t‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
        _ ≤ (‖a i‖ * ‖a j‖) * (2 / |ω i - ω j|) :=
          mul_le_mul_of_nonneg_left (norm_integral_frequencyChar_le hgap T) (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ((if i = j then T * ‖a i‖ ^ 2 else 0) +
         (if i = j then 0 else 2 * ‖a i‖ * ‖a j‖ / |ω i - ω j|)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      exact hpair i hi
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]

end Sidon

end
end


-- Sidon.NumberTheory.LogarithmicMeanSquare
section

noncomputable section

namespace Sidon

theorem logarithmic_kernel_le {m n : ℝ} (hm : 0 < m) (hmn : m < n) :
    1 / (Real.sqrt m * Real.sqrt n * Real.log (n / m)) ≤
      1 / (Real.sqrt m * Real.sqrt n) + 1 / (n - m) := by
  have hn : 0 < n := hm.trans hmn
  have hroot : 0 < Real.sqrt m * Real.sqrt n := mul_pos (Real.sqrt_pos.2 hm) (Real.sqrt_pos.2 hn)
  have hdiff : 0 < n - m := sub_pos.mpr hmn
  have hratio : 1 < n / m := (one_lt_div hm).mpr hmn
  have hlog : 0 < Real.log (n / m) := Real.log_pos hratio
  have hlow : n - m ≤ n * Real.log (n / m) := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
    rw [inv_div] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hn.le
    field_simp at hh'
    nlinarith
  have hmroot : m ≤ Real.sqrt m * Real.sqrt n := by
    calc
      m = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hm.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmn.le) (Real.sqrt_nonneg m)
  calc
    _ ≤ n / ((Real.sqrt m * Real.sqrt n) * (n - m)) := by
      apply (div_le_div_iff₀ (mul_pos hroot hlog) (mul_pos hroot hdiff)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlow hroot.le]
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hroot hdiff)).mpr
      field_simp
      nlinarith

theorem sum_range_inv_sqrt_succ_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / Real.sqrt ((n : ℝ) + 1)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hroot : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hstep : 1 / Real.sqrt ((N : ℝ) + 1) ≤
        2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) := by
      apply (div_le_iff₀ hroot).mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
        Real.sq_sqrt (show 0 ≤ (N : ℝ) + 1 by positivity),
        sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N)]
    push_cast
    linarith

def logarithmicPolynomial (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  finiteFrequencySum s a (fun n => -Real.log n) t

theorem continuous_logarithmicPolynomial (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (logarithmicPolynomial s a) := continuous_finiteFrequencySum s a _

theorem integral_logarithmicPolynomial_norm_sq_le (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial s a t‖ ^ 2) ≤
      T * ∑ n ∈ s, ‖a n‖ ^ 2 +
        ∑ m ∈ s, ∑ n ∈ s, if m = n then 0 else
          2 * ‖a m‖ * ‖a n‖ / |Real.log (n : ℝ) - Real.log m| := by
  have hω : Set.InjOn (fun n : ℕ => -Real.log n) (s : Set ℕ) := by
    intro m hm n hn h
    have he : Real.log (m : ℝ) = Real.log n := neg_injective h
    have hp := Real.log_injOn_pos
      (show (0 : ℝ) < m by exact_mod_cast hs m hm)
      (show (0 : ℝ) < n by exact_mod_cast hs n hn) he
    exact_mod_cast hp
  simpa only [logarithmicPolynomial, neg_sub_neg] using
    integral_finiteFrequencySum_norm_sq_le s a (fun n => -Real.log n) T hω

end Sidon

end
end


-- Sidon.NumberTheory.HarmonicGaps
section

noncomputable section

namespace Sidon

theorem sum_reciprocal_gap_le {N m : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    (∑ n ∈ Finset.Icc 1 N, if m = n then 0 else 1 / |(m : ℝ) - n|) ≤
      2 * (harmonic N : ℝ) := by
  classical
  let S := Finset.Icc 1 N
  have hlo : (∑ n ∈ S.filter (fun n => n < m), ((m - n : ℕ) : ℝ)⁻¹) ≤
      ∑ d ∈ S, (d : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_injOn (fun n => m - n)
    · intro n hn k hk heq
      have hn' := (Finset.mem_filter.mp hn).2
      have hk' := (Finset.mem_filter.mp hk).2
      change m - n = m - k at heq
      omega
    · intro d hd
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hn, hnm⟩ := Finset.mem_filter.mp hn
      dsimp [S] at hm hn ⊢
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n _
      rfl
    · intro d _ _
      positivity
  have hhi : (∑ n ∈ S.filter (fun n => m < n), ((n - m : ℕ) : ℝ)⁻¹) ≤
      ∑ d ∈ S, (d : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_injOn (fun n => n - m)
    · intro n hn k hk heq
      have hn' := (Finset.mem_filter.mp hn).2
      have hk' := (Finset.mem_filter.mp hk).2
      change n - m = k - m at heq
      omega
    · intro d hd
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hn, hmn⟩ := Finset.mem_filter.mp hn
      dsimp [S] at hn ⊢
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n _
      rfl
    · intro d _ _
      positivity
  have heq : (∑ n ∈ S, if m = n then (0 : ℝ) else 1 / |(m : ℝ) - n|) =
      (∑ n ∈ S.filter (fun n => n < m), ((m - n : ℕ) : ℝ)⁻¹) +
      ∑ n ∈ S.filter (fun n => m < n), ((n - m : ℕ) : ℝ)⁻¹ := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rcases lt_trichotomy n m with h | h | h
    · simp only [Nat.cast_sub h.le, h, show ¬m < n by omega,
        show m ≠ n by omega, ite_false, ite_true, add_zero, one_div]
      rw [abs_of_pos (sub_pos.mpr (show (n : ℝ) < m by exact_mod_cast h))]
    · subst n
      simp
    · simp only [Nat.cast_sub h.le, h, show ¬n < m by omega,
        show m ≠ n by omega, ite_false, ite_true, zero_add, one_div]
      rw [abs_of_neg (sub_neg.mpr (show (m : ℝ) < n by exact_mod_cast h)), neg_sub]
  change (∑ n ∈ S, _) ≤ _
  rw [heq]
  have hH : (∑ d ∈ S, (d : ℝ)⁻¹) = (harmonic N : ℝ) := by
    simp only [S, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH] at hlo hhi
  linarith

end Sidon

end
end


-- Sidon.NumberTheory.MollifierEndpoint
section

noncomputable section

namespace Sidon

theorem sum_Icc_inv_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt N := by
  have hh := Finset.sum_Ico_add' (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) 0 N 1
  simp only [Nat.Ico_zero_eq_range, zero_add, Finset.Ico_add_one_right_eq_Icc,
    Nat.cast_add, Nat.cast_one] at hh
  rw [← hh]
  exact sum_range_inv_sqrt_succ_le N

theorem logarithmic_kernel_abs_le {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    1 / (Real.sqrt m * Real.sqrt n * |Real.log n - Real.log m|) ≤
      1 / (Real.sqrt m * Real.sqrt n) + 1 / |n - m| := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hm h)), abs_of_pos (sub_pos.mpr h),
      ← Real.log_div hn.ne' hm.ne']
    exact logarithmic_kernel_le hm h
  · rw [abs_sub_comm (Real.log n), abs_sub_comm n,
      abs_of_pos (sub_pos.mpr (Real.log_lt_log hn h)), abs_of_pos (sub_pos.mpr h),
      ← Real.log_div hm.ne' hn.ne', mul_comm (Real.sqrt m) (Real.sqrt n)]
    exact logarithmic_kernel_le hn h

theorem integral_logarithmicPolynomial_norm_sq_le_harmonic {N : ℕ} {a : ℕ → ℂ} {T : ℝ}
    (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ 1 / Real.sqrt (n : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial (Finset.Icc 1 N) a t‖ ^ 2) ≤
      T * (harmonic N : ℝ) + 8 * N + 4 * N * (harmonic N : ℝ) := by
  let S := Finset.Icc 1 N
  have hpos (n : ℕ) (hn : n ∈ S) : (0 : ℝ) < n := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hdiag : (∑ n ∈ S, ‖a n‖ ^ 2) ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_le_sum
    intro n hn
    have hr := Real.sq_sqrt (hpos n hn).le
    calc
      ‖a n‖ ^ 2 ≤ (1 / Real.sqrt (n : ℝ)) ^ 2 := by gcongr; exact ha n hn
      _ = (n : ℝ)⁻¹ := by rw [div_pow, one_pow, hr, one_div]
  have hpair (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) :
      (if m = n then 0 else 2 * ‖a m‖ * ‖a n‖ / |Real.log (n : ℝ) - Real.log m|) ≤
        2 / (Real.sqrt (m : ℝ) * Real.sqrt n) +
        2 * (if m = n then 0 else 1 / |(m : ℝ) - n|) := by
    by_cases heq : m = n
    · subst n
      simp
      positivity
    · simp only [heq, ite_false]
      have hne : (m : ℝ) ≠ n := by exact_mod_cast heq
      have hh := logarithmic_kernel_abs_le (hpos m hm) (hpos n hn) hne
      calc
        _ ≤ 2 * (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (n : ℝ)) /
            |Real.log (n : ℝ) - Real.log m| := by gcongr <;> exact ha _ (by assumption)
        _ = 2 * (1 / (Real.sqrt (m : ℝ) * Real.sqrt n *
            |Real.log (n : ℝ) - Real.log m|)) := by ring
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
          simpa only [mul_add, mul_one_div, abs_sub_comm] using this
  have hproduct : (∑ m ∈ S, ∑ n ∈ S,
      1 / (Real.sqrt (m : ℝ) * Real.sqrt n)) ≤ 4 * N := by
    have heq : (∑ m ∈ S, ∑ n ∈ S, 1 / (Real.sqrt (m : ℝ) * Real.sqrt n)) =
        (∑ n ∈ S, 1 / Real.sqrt (n : ℝ)) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      simp only [one_div, mul_inv]
    rw [heq]
    have hh := sum_Icc_inv_sqrt_le N
    have hn0 : 0 ≤ ∑ n ∈ S, 1 / Real.sqrt (n : ℝ) := by positivity
    have hsquare := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith
  have hgap : (∑ m ∈ S, ∑ n ∈ S, if m = n then (0 : ℝ) else 1 / |(m : ℝ) - n|) ≤
      2 * N * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ _m ∈ S, 2 * (harmonic N : ℝ) :=
        Finset.sum_le_sum fun m hm => sum_reciprocal_gap_le hm
      _ = _ := by simp [S]; ring
  apply (integral_logarithmicPolynomial_norm_sq_le S a T
    (fun n hn => (Finset.mem_Icc.mp hn).1)).trans
  have hdouble := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hpair m hm n hn
  simp only [Finset.sum_add_distrib, div_eq_mul_inv, one_mul, ← Finset.mul_sum] at hdouble
  have hdiag' := mul_le_mul_of_nonneg_left hdiag hT
  have hproduct' := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 2)
  have hgap' := mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 2)
  simp only [div_eq_mul_inv, one_mul] at hproduct' hgap' ⊢
  linarith

theorem integral_logarithmicPolynomial_norm_sq_le_log {N : ℕ} {a : ℕ → ℂ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ 1 / Real.sqrt (n : ℝ)) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial (Finset.Icc 1 N) a t‖ ^ 2) ≤
      12 * (T + N) * (1 + Real.log N) := by
  have hHone : (1 : ℝ) ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    have hh := Finset.single_le_sum (f := fun n : ℕ => (n : ℝ)⁻¹)
      (fun n (_ : n ∈ Finset.Icc 1 N) => by positivity)
      (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)
    simpa only [Nat.cast_one, inv_one] using hh
  have hlog := harmonic_le_one_add_log N
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc
    _ ≤ T * (harmonic N : ℝ) + 8 * N + 4 * N * (harmonic N : ℝ) :=
      integral_logarithmicPolynomial_norm_sq_le_harmonic hT ha
    _ ≤ (T + 12 * N) * (harmonic N : ℝ) := by nlinarith
    _ ≤ (T + 12 * N) * (1 + Real.log N) := by gcongr
    _ ≤ _ := by nlinarith

def criticalMollifier (N : ℕ) (t : ℝ) : ℂ :=
  logarithmicPolynomial (Finset.Icc 1 N)
    (fun n => (ArithmeticFunction.moebius n : ℂ) / (Real.sqrt n : ℂ)) t

theorem norm_criticalMollifier_coefficient_le (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ) / (Real.sqrt n : ℂ)‖ ≤
      1 / Real.sqrt n := by
  rw [norm_div, Complex.norm_intCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem integral_criticalMollifier_norm_sq_le {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖criticalMollifier N t‖ ^ 2) ≤
      12 * (T + N) * (1 + Real.log N) :=
  integral_logarithmicPolynomial_norm_sq_le_log hN hT
    (fun n _ => norm_criticalMollifier_coefficient_le n)

end Sidon

end
end


-- THTwistedMean
section

noncomputable section

namespace CentralWindowTwist
open Finset MeasureTheory Sidon
open scoped ComplexConjugate

def criticalPoint (t : ℝ) : ℂ := (1/2 : ℂ) + (t:ℂ)*Complex.I

def twistCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * ((ArithmeticFunction.moebius n : ℂ) / (Real.sqrt n : ℂ))

def criticalSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) : ℂ :=
  logarithmicPolynomial (Icc 1 N) (twistCoeff χ) t

lemma twistCoeff_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖twistCoeff χ n‖ ≤ 1/Real.sqrt n := by
  unfold twistCoeff
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
    (norm_criticalMollifier_coefficient_le n)

lemma logpoly_neg_norm (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖logarithmicPolynomial s a (-t)‖ =
      ‖logarithmicPolynomial s (fun n => conj (a n)) t‖ := by
  have h : conj (logarithmicPolynomial s a (-t)) =
      logarithmicPolynomial s (fun n => conj (a n)) t := by
    simp only [logarithmicPolynomial, finiteFrequencySum, map_sum, map_mul, frequencyChar,
      ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, map_neg]
    apply sum_congr rfl
    intro n hn
    congr 2
    push_cast
    ring
  rw [← h, Complex.norm_conj]

lemma symmetric_critical_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {N : ℕ} {T : ℝ} (hN : 1 ≤ N) (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖criticalSum χ N t‖^2) ≤ 24 * (T+N) * (1+Real.log N) := by
  have pos := integral_logarithmicPolynomial_norm_sq_le_log hN hT
    (fun n _ => twistCoeff_bound χ n)
  have neg := integral_logarithmicPolynomial_norm_sq_le_log hN hT
    (a := fun n => conj (twistCoeff χ n)) (fun n _ => by
      rw [Complex.norm_conj]
      exact twistCoeff_bound χ n)
  let f := fun t : ℝ => ‖criticalSum χ N t‖^2
  have hneg : (∫ t in -T..0, f t) ≤ 12 * (T+N) * (1+Real.log N) := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0:ℝ)) (b := T)
    rw [neg_zero] at h
    rw [← h]
    simpa only [f, criticalSum, logpoly_neg_norm] using neg
  have hpos : (∫ t in 0..T, f t) ≤ 12 * (T+N) * (1+Real.log N) := pos
  have hc : Continuous f := (continuous_logarithmicPolynomial _ _).norm.pow 2
  change (∫ t in -T..T, f t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-T) 0)
    (hc.intervalIntegrable 0 T)]
  linarith

theorem critical_mollified_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {N : ℕ} {T G : ℝ} (hN : 1 ≤ N) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hg : ∀ t : ℝ, |t| ≤ T → ‖χ.LFunction (criticalPoint t)‖ ≤ G) :
    (∫ t in -T..T, ‖χ.LFunction (criticalPoint t) * criticalSum χ N t - 1‖^2) ≤
      48 * G^2 * (T+N) * (1+Real.log N) + 4*T := by
  let F := fun t : ℝ => χ.LFunction (criticalPoint t)
  let M := criticalSum χ N
  have hcF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (χ.differentiableAt_LFunction _ (.inl ?_)).continuousAt.comp
    · unfold criticalPoint
      fun_prop
    · intro h
      have hr := congrArg Complex.re h
      simp [criticalPoint] at hr
  have hcM : Continuous M := continuous_logarithmicPolynomial _ _
  have hart : Continuous (fun t => ‖F t * M t - 1‖^2) := ((hcF.mul hcM).sub continuous_const).norm.pow 2
  have hmaj : Continuous (fun t => 2*G^2*‖M t‖^2+2) :=
    ((hcM.norm.pow 2).const_mul _).add continuous_const
  have h := intervalIntegral.integral_mono_on (μ := volume) (show -T ≤ T by linarith)
    (hart.intervalIntegrable _ _) (hmaj.intervalIntegrable _ _) (fun t ht => by
      have b := norm_sub_le (F t * M t) 1
      rw [norm_mul, norm_one] at b
      have g : ‖F t‖ ≤ G := hg t (abs_le.mpr ht)
      have p := mul_le_mul_of_nonneg_right g (norm_nonneg (M t))
      have hb := pow_le_pow_left₀ (norm_nonneg _) (b.trans (add_le_add p (le_refl _))) 2
      nlinarith [hb, sq_nonneg (G*‖M t‖-1)])
  have hleft : IntervalIntegrable (fun u => 2*G^2*‖M u‖^2) volume (-T) T :=
    (((hcM.norm.pow 2).const_mul _).intervalIntegrable _ _)
  have hright : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (-T) T := intervalIntegrable_const
  rw [intervalIntegral.integral_add hleft hright, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h
  have hsm := symmetric_critical_sum χ hN hT
  change (∫ t in -T..T, ‖M t‖^2) ≤ _ at hsm
  change (∫ t in -T..T, ‖F t * M t - 1‖^2) ≤ _
  rw [smul_eq_mul] at h
  calc
    _ ≤ _ := h
    _ ≤ 2*G^2*(24*(T+N)*(1+Real.log N)) + (T - -T)*2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsm (by positivity)) le_rfl
    _ = _ := by ring

lemma interpolation_exponent {R k θ σ : ℝ} (hR : 1 < R) (hk : 0 ≤ k)
    (ht : 1-θ ≤ 2*(1-σ+1/Real.log R)) :
    (R^(1+2*k))^(1-θ) ≤ R^((2+4*k)*(1-σ)) * Real.exp (2+4*k) := by
  have hR0 := lt_trans zero_lt_one hR
  have hl := Real.log_pos hR
  rw [← Real.rpow_mul hR0.le]
  have hlog : R^((2+4*k)/Real.log R) = Real.exp (2+4*k) := by
    rw [Real.rpow_def_of_pos hR0]
    congr 1
    field_simp
  rw [← hlog, ← Real.rpow_add hR0]
  apply Real.rpow_le_rpow_of_exponent_le hR.le
  have hmul := mul_le_mul_of_nonneg_left ht (by linarith : 0≤1+2*k)
  calc
    _ ≤ (1+2*k)*(2*(1-σ+1/Real.log R)) := hmul
    _ = _ := by ring

theorem admissible_height {k : ℝ} (hk : 0 ≤ k) (hsc : k < 1/4) :
    ∃ A t : ℝ, 8/3 ≤ A ∧ 2+4*k < A ∧ A < 3 ∧ 1/3 < t ∧ A*t < 1 := by
  let A := (max (8/3:ℝ) (2+4*k) + 3)/2
  have hm : max (8/3:ℝ) (2+4*k) < 3 := max_lt (by norm_num) (by linarith)
  have hmax : max (8/3:ℝ) (2+4*k) < A := by dsimp [A]; linarith
  have ha := (le_max_left (8/3:ℝ) (2+4*k)).trans hmax.le
  have hA : A < 3 := by dsimp [A]; linarith
  have hA0 : 0 < A := by linarith
  have hrec : 1/3 < 1/A := one_div_lt_one_div_of_lt hA0 hA
  refine ⟨A,(1/3+1/A)/2,ha,(le_max_right _ _).trans_lt hmax,hA,by linarith,?_⟩
  have ht : (1/3+1/A)/2 < 1/A := by linarith
  have hp := mul_lt_mul_of_pos_left ht hA0
  simpa [hA0.ne'] using hp

end CentralWindowTwist

end
end


-- TH8000CriticalAll
section

open Complex Finset HurwitzZeta MeasureTheory
open OAI.V2 CentralWindowTwist

namespace TH8000CriticalAll

private theorem small_hurwitz {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    {s : ℂ} (hs : s.re = 1/2) (ht : |s.im| ≤ Real.exp 100) :
    ‖hurwitzZeta (a:UnitAddCircle) s-V29 a s‖ ≤ 6 + 4*Real.exp 100 := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hden : (1/2:ℝ) ≤ ‖1-s‖ := by
    have h := Complex.abs_re_le_norm (1-s)
    simpa only [Complex.sub_re, Complex.one_re, hs, show (1:ℝ)-1/2=1/2 by norm_num,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] using h
  have hrec : 1/‖1-s‖ ≤ 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hden)).mpr
    linarith
  have hnorm : ‖s‖ ≤ 1/2+Real.exp 100 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
    linarith
  let P := ∑ n ∈ range 1, (((n+1:ℕ):ℝ)+a:ℂ)^(-s)
  have hP : ‖P‖ ≤ 1 := by
    simp only [P, sum_range_one, Nat.zero_add, Nat.cast_one]
    rw [← Complex.ofReal_add]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [ha.1] : (0:ℝ)<1+a), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ha.1]) (by linarith)
  have he := V1tf ha (by linarith : (1/10:ℝ) < s.re) hs1 (N:=1) le_rfl
  change ‖hurwitzZeta (a:UnitAddCircle) s - V29 a s - P‖ ≤ _ at he
  simp only [Nat.cast_one, Real.one_rpow, hs, mul_one] at he
  calc
    _ = ‖(hurwitzZeta (a:UnitAddCircle) s - V29 a s - P) + P‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hP)
    _ ≤ _ := by linarith only [hrec,hnorm]

theorem all_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      s.re = 1/2 → ‖χ.LFunction s‖ ≤ C*(q:ℝ)^3*(1+|s.im|)^(3/16:ℝ) := by
  obtain ⟨B,hB,hbound⟩ := TH8000CriticalHurwitz.critical_character_bound
  let A : ℝ := 6+4*Real.exp 100
  have hA : 0 < A := by dsimp only [A]; positivity
  let C := max B (1+A)
  refine ⟨C,hB.trans_le (le_max_left _ _),?_⟩
  intro q _ χ s hs
  have hq : (1:ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hT : (1:ℝ) ≤ 1+|s.im| := by linarith [abs_nonneg s.im]
  have hh : 1 ≤ (1+|s.im|)^(3/16:ℝ) := Real.one_le_rpow hT (by norm_num)
  by_cases hlarge : Real.exp 100 ≤ |s.im|
  · apply (hbound _ hlarge q χ s hs rfl).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hq0 _))
      (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num))
      (Real.rpow_nonneg (abs_nonneg _) _) (by dsimp only [C]; positivity)
  · have h := OAI.Vg.V14m χ (by linarith) (by linarith)
        (fun a ha => small_hurwitz ha hs (le_of_not_ge hlarge))
    have hq3 : (q:ℝ) ≤ (q:ℝ)^3 := by simpa using pow_le_pow_right₀ hq (by norm_num : 1 ≤ 3)
    have hAq := mul_le_mul_of_nonneg_right hq3 hA.le
    calc
      _ ≤ (q:ℝ)*((q:ℝ)^2+A) := h
      _ ≤ (1+A)*(q:ℝ)^3 := by nlinarith only [hAq]
      _ ≤ C*(q:ℝ)^3 := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hq0 _)
      _ ≤ _ := le_mul_of_one_le_right (by dsimp only [C]; positivity) hh

theorem mollified_left_mean :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N : ℕ) (T : ℝ), 1 ≤ N → 0 ≤ T →
      (∫ t in -T..T, ‖χ.LFunction (criticalPoint t) * criticalSum χ N t - 1‖^2) ≤
        A*(q:ℝ)^6*(1+T)^(3/8:ℝ)*(T+N)*(1+Real.log N) + 4*T := by
  obtain ⟨C,hC,h⟩ := all_heights
  refine ⟨48*C^2,by positivity,?_⟩
  intro q _ χ N T hN hT
  let G := C*(q:ℝ)^3*(1+T)^(3/16:ℝ)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have bound := critical_mollified_bound χ hN hT hG (fun t ht => by
    have hs : (criticalPoint t).re = 1/2 := by simp [criticalPoint]
    have hi : (criticalPoint t).im = t := by simp [criticalPoint]
    have est := h q χ _ hs
    rw [hi] at est
    exact est.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [abs_nonneg t]) (by linarith) (by norm_num)) (by positivity)))
  have hp : ((1+T)^(3/16:ℝ))^2 = (1+T)^(3/8:ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by linarith)]
    norm_num
  convert bound using 1
  dsimp only [G]
  rw [mul_pow, mul_pow, hp]
  ring

end TH8000CriticalAll

end


-- Sidon.NumberTheory.LogarithmicGapMeanSquare
section

noncomputable section

namespace Sidon

def nearReciprocalGap (m n : ℕ) : ℝ :=
  if m = n then 0 else if n ≤ 2 * m ∧ m ≤ 2 * n then 1 / |(m : ℝ) - n| else 0

theorem nearReciprocalGap_nonneg (m n : ℕ) : 0 ≤ nearReciprocalGap m n := by
  unfold nearReciprocalGap
  split_ifs <;> positivity

theorem nearReciprocalGap_symm (m n : ℕ) :
    nearReciprocalGap m n = nearReciprocalGap n m := by
  unfold nearReciprocalGap
  by_cases h : m = n
  · subst n
    simp
  · simp only [h, Ne.symm h, ite_false]
    by_cases hnear : n ≤ 2 * m ∧ m ≤ 2 * n
    · simp only [hnear, and_comm.mp hnear, ite_true, abs_sub_comm]
    · simp only [hnear, show ¬(m ≤ 2 * n ∧ n ≤ 2 * m) by tauto, ite_false]

theorem sum_nearReciprocalGap_le (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ s, nearReciprocalGap m n) ≤ 4 * (1 + Real.log m) := by
  classical
  have hext : (∑ n ∈ s, nearReciprocalGap m n) ≤
      ∑ n ∈ Finset.Icc 1 (2 * m), if m = n then 0 else 1 / |(m : ℝ) - n| := by
    calc
      _ = ∑ n ∈ s.filter (fun n => n ≤ 2 * m ∧ m ≤ 2 * n),
          if m = n then 0 else 1 / |(m : ℝ) - n| := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        unfold nearReciprocalGap
        split_ifs <;> rfl
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn, hnm, _⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Icc.mpr ⟨hs n hn, hnm⟩
        · intro n _ _
          split_ifs <;> positivity
  have hg := sum_reciprocal_gap_le (m := m) (N := 2 * m)
    (Finset.mem_Icc.mpr ⟨hm, by omega⟩)
  have hh := harmonic_le_one_add_log (2 * m)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hlogtwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog : Real.log (2 * m : ℕ) = Real.log 2 + Real.log m := by
    push_cast
    rw [Real.log_mul (by norm_num) hm0.ne']
  rw [hlog] at hh
  exact hext.trans (hg.trans (by nlinarith))

theorem ordered_logarithmic_offDiagonal_le {m n a b : ℝ}
    (hm : 0 < m) (hmn : m < n) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * a * b / Real.log (n / m) ≤
      4 * a * b + if n ≤ 2 * m then 2 * (m * a ^ 2 + n * b ^ 2) / (n - m) else 0 := by
  have hn : 0 < n := hm.trans hmn
  have hlog : 0 < Real.log (n / m) := Real.log_pos ((one_lt_div hm).mpr hmn)
  have hlow : n - m ≤ n * Real.log (n / m) := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
    rw [inv_div] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hn.le
    field_simp at hh'
    nlinarith
  by_cases hnear : n ≤ 2 * m
  · rw [if_pos hnear]
    have hnum : 2 * n * a * b ≤ 2 * (m * a ^ 2 + n * b ^ 2) := by
      have hsq := mul_nonneg hn.le (sq_nonneg (a - b))
      have hrem := mul_nonneg (show 0 ≤ 2 * m - n by linarith) (sq_nonneg a)
      nlinarith
    have hfrac : 2 * a * b / Real.log (n / m) ≤ 2 * n * a * b / (n - m) := by
      apply (div_le_div_iff₀ hlog (sub_pos.mpr hmn)).mpr
      have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * a * b by positivity)
      nlinarith
    calc
      _ ≤ 2 * n * a * b / (n - m) := hfrac
      _ ≤ 2 * (m * a ^ 2 + n * b ^ 2) / (n - m) :=
        div_le_div_of_nonneg_right hnum (sub_nonneg.mpr hmn.le)
      _ ≤ _ := by linarith [mul_nonneg ha hb]
  · rw [if_neg hnear, add_zero]
    have hratio : 2 ≤ n / m := (le_div_iff₀ hm).mpr (by linarith)
    have hhalf : (1 / 2 : ℝ) ≤ Real.log (n / m) := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh
      exact hh.trans (Real.log_le_log (by norm_num) hratio)
    apply (div_le_iff₀ hlog).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4 * a * b by positivity)
    nlinarith

theorem logarithmic_offDiagonal_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if m = n then 0 else 2 * a * b / |Real.log (n : ℝ) - Real.log m|) ≤
      4 * a * b + 2 * ((m : ℝ) * a ^ 2 + n * b ^ 2) * nearReciprocalGap m n := by
  have ordered {m n : ℕ} (hm : 0 < m) (hmn : m < n) (a b : ℝ)
      (ha : 0 ≤ a) (hb : 0 ≤ b) :
      2 * a * b / |Real.log (n : ℝ) - Real.log m| ≤
        4 * a * b + 2 * ((m : ℝ) * a ^ 2 + n * b ^ 2) * nearReciprocalGap m n := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn0 : (m : ℝ) < n := by exact_mod_cast hmn
    have hn0 : (0 : ℝ) < n := hm0.trans hmn0
    have hlog : Real.log m < Real.log n := Real.log_lt_log hm0 hmn0
    rw [abs_of_pos (sub_pos.mpr hlog), ← Real.log_div hn0.ne' hm0.ne']
    have hh := ordered_logarithmic_offDiagonal_le hm0 hmn0 ha hb
    unfold nearReciprocalGap
    rw [if_neg (by omega : m ≠ n)]
    by_cases hnear : n ≤ 2 * m
    · rw [if_pos ⟨hnear, by omega⟩, abs_of_neg (sub_neg.mpr hmn0), neg_sub]
      have hnear0 : (n : ℝ) ≤ 2 * m := by exact_mod_cast hnear
      rw [if_pos hnear0] at hh
      simpa only [div_eq_mul_inv, one_div, mul_assoc, one_mul] using hh
    · rw [if_neg (by tauto), mul_zero, add_zero]
      have hnear0 : ¬(n : ℝ) ≤ 2 * m := by exact_mod_cast hnear
      simpa only [if_neg hnear0, add_zero] using hh
  rcases lt_trichotomy m n with h | h | h
  · rw [if_neg (by omega : m ≠ n)]
    exact ordered hm h a b ha hb
  · subst n
    simp only [nearReciprocalGap, ite_true, mul_zero, add_zero]
    positivity
  · rw [if_neg (by omega : m ≠ n)]
    have hh := ordered hn h b a hb ha
    rw [abs_sub_comm, nearReciprocalGap_symm n m] at hh
    convert hh using 1 <;> ring

theorem integral_logarithmicPolynomial_norm_sq_le_weighted (s : Finset ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hs : ∀ n ∈ s, 0 < n) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicPolynomial s a t‖ ^ 2) ≤
      T * ∑ n ∈ s, ‖a n‖ ^ 2 + 4 * (∑ n ∈ s, ‖a n‖) ^ 2 +
        16 * ∑ n ∈ s, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
  classical
  let q (n : ℕ) : ℝ := (n : ℝ) * ‖a n‖ ^ 2
  have hrow : (∑ m ∈ s, ∑ n ∈ s, q m * nearReciprocalGap m n) ≤
      4 * ∑ m ∈ s, q m * (1 + Real.log m) := by
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hh := mul_le_mul_of_nonneg_left (sum_nearReciprocalGap_le s hs (hs m hm))
      (show 0 ≤ q m by dsimp [q]; positivity)
    convert hh using 1 <;> ring
  have hcol : (∑ m ∈ s, ∑ n ∈ s, q n * nearReciprocalGap m n) =
      ∑ m ∈ s, ∑ n ∈ s, q m * nearReciprocalGap m n := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    rw [nearReciprocalGap_symm n m]
  have hprod : (∑ m ∈ s, ∑ n ∈ s, 4 * ‖a m‖ * ‖a n‖) =
      4 * (∑ n ∈ s, ‖a n‖) ^ 2 := by
    calc
      _ = 4 * (∑ m ∈ s, ∑ n ∈ s, ‖a m‖ * ‖a n‖) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := by rw [← Finset.sum_mul_sum]; ring
  have hscale (f : ℕ → ℕ → ℝ) :
      (∑ m ∈ s, ∑ n ∈ s, 2 * f m n) = 2 * ∑ m ∈ s, ∑ n ∈ s, f m n := by
    simp only [Finset.mul_sum]
  have hoff : (∑ m ∈ s, ∑ n ∈ s,
      if m = n then 0 else 2 * ‖a m‖ * ‖a n‖ / |Real.log (n : ℝ) - Real.log m|) ≤
      4 * (∑ n ∈ s, ‖a n‖) ^ 2 +
        16 * ∑ n ∈ s, q n * (1 + Real.log n) := by
    calc
      _ ≤ ∑ m ∈ s, ∑ n ∈ s,
          (4 * ‖a m‖ * ‖a n‖ + 2 * (q m + q n) * nearReciprocalGap m n) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact logarithmic_offDiagonal_le (hs m hm) (hs n hn) _ _ (norm_nonneg _) (norm_nonneg _)
      _ = 4 * (∑ n ∈ s, ‖a n‖) ^ 2 +
          2 * (∑ m ∈ s, ∑ n ∈ s, q m * nearReciprocalGap m n) +
          2 * (∑ m ∈ s, ∑ n ∈ s, q n * nearReciprocalGap m n) := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib,
          show ∀ m n, 2 * q m * nearReciprocalGap m n =
            2 * (q m * nearReciprocalGap m n) by intros; ring,
          show ∀ m n, 2 * q n * nearReciprocalGap m n =
            2 * (q n * nearReciprocalGap m n) by intros; ring]
        rw [hprod, hscale, hscale]
        ring
      _ ≤ _ := by rw [hcol]; linarith
  have hh := integral_logarithmicPolynomial_norm_sq_le s a T hs
  exact hh.trans (by dsimp [q] at hoff; linarith)

end Sidon

end
end


-- Sidon.NumberTheory.InfiniteDirichletMeanSquare
section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Sidon

def logarithmicSeries (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a n * frequencyChar (-Real.log n) t

theorem integral_logarithmicSeries_norm_sq_le (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun n => ‖a n‖)) (ha2 : Summable (fun n => ‖a n‖ ^ 2))
    (haw : Summable (fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicSeries a t‖ ^ 2) ≤
      T * ∑' n : ℕ, ‖a n‖ ^ 2 + 4 * (∑' n : ℕ, ‖a n‖) ^ 2 +
        16 * ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
  classical
  let S (M : ℕ) := (Finset.range M).erase 0
  let P (M : ℕ) := logarithmicPolynomial (S M) a
  have hS (M : ℕ) : ∀ n ∈ S M, 0 < n := by
    intro n hn
    have hh := Finset.mem_erase.mp hn
    omega
  have hw0 (n : ℕ) : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hn1])
  have hPnorm (M : ℕ) (t : ℝ) : ‖P M t‖ ≤ ∑' n : ℕ, ‖a n‖ := by
    calc
      _ ≤ ∑ n ∈ S M, ‖a n‖ := by
        dsimp [P, logarithmicPolynomial, finiteFrequencySum]
        exact (norm_sum_le _ _).trans_eq (by simp [norm_mul])
      _ ≤ _ := ha.sum_le_tsum (S M) (fun _ _ => norm_nonneg _)
  have hseries (t : ℝ) : Summable (fun n : ℕ => a n * frequencyChar (-Real.log n) t) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_frequencyChar, mul_one] using ha
  have hPeq (M : ℕ) (t : ℝ) : P M t = ∑ n ∈ Finset.range M,
      a n * frequencyChar (-Real.log n) t := by
    change (∑ n ∈ S M, a n * frequencyChar (-Real.log n) t) = _
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro n hn hnot
    have hn0 : n = 0 := by
      by_contra hh
      exact hnot (Finset.mem_erase.mpr ⟨hh, hn⟩)
    simp [hn0, ha0]
  have hlim (t : ℝ) : Tendsto (fun M => ‖P M t‖ ^ 2) atTop
      (𝓝 (‖logarithmicSeries a t‖ ^ 2)) := by
    simp_rw [hPeq]
    exact (hseries t).hasSum.tendsto_sum_nat.norm.pow 2
  have hint : Tendsto (fun M => ∫ t in (0 : ℝ)..T, ‖P M t‖ ^ 2) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ‖logarithmicSeries a t‖ ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (∑' n : ℕ, ‖a n‖) ^ 2)
    · exact Eventually.of_forall fun M =>
        ((continuous_logarithmicPolynomial (S M) a).norm.pow 2).aestronglyMeasurable
    · exact Eventually.of_forall fun M => Filter.Eventually.of_forall fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hPnorm M t) 2
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => hlim t
  apply le_of_tendsto' hint
  intro M
  calc
    _ ≤ T * ∑ n ∈ S M, ‖a n‖ ^ 2 + 4 * (∑ n ∈ S M, ‖a n‖) ^ 2 +
        16 * ∑ n ∈ S M, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) :=
      integral_logarithmicPolynomial_norm_sq_le_weighted (S M) a T (hS M)
    _ ≤ _ := by
      gcongr
      · exact ha2.sum_le_tsum (S M) (fun n _ => sq_nonneg _)
      · exact ha.sum_le_tsum (S M) (fun n _ => norm_nonneg _)
      · exact haw.sum_le_tsum (S M) (fun n _ => hw0 n)

end Sidon

end
end


-- Sidon.NumberTheory.DirichletMollifier
section

noncomputable section

namespace Sidon

def dirichletMollifier (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))

def mollifierCoefficient (N n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ N), ArithmeticFunction.moebius d

theorem differentiable_dirichletMollifier (N : ℕ) : Differentiable ℂ (dirichletMollifier N) := by
  unfold dirichletMollifier
  fun_prop

@[simp] theorem mollifierCoefficient_zero (N : ℕ) : mollifierCoefficient N 0 = 0 := by
  simp [mollifierCoefficient]

theorem mollifierCoefficient_eq_one_apply {N n : ℕ} (hnN : n ≤ N) :
    mollifierCoefficient N n = if n = 1 then 1 else 0 := by
  have hfilter : n.divisors.filter (fun d => d ≤ N) = n.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact (Nat.divisor_le hd).trans hnN
  rw [mollifierCoefficient, hfilter]
  have hh := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using hh

theorem mollifierCoefficient_eq_zero {N n : ℕ} (hn : n ≠ 1) (hnN : n ≤ N) :
    mollifierCoefficient N n = 0 := by
  rw [mollifierCoefficient_eq_one_apply hnN, if_neg hn]

theorem abs_mollifierCoefficient_le (N n : ℕ) :
    |mollifierCoefficient N n| ≤ (n.divisors.card : ℤ) := by
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ N), |ArithmeticFunction.moebius d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ N), (1 : ℤ) :=
      Finset.sum_le_sum fun _ _ => ArithmeticFunction.abs_moebius_le_one
    _ = ((n.divisors.filter (fun d => d ≤ N)).card : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_filter_le n.divisors (fun d => d ≤ N)

theorem dirichletMollifier_critical (N : ℕ) (t : ℝ) :
    dirichletMollifier N ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = criticalMollifier N t := by
  unfold dirichletMollifier criticalMollifier logarithmicPolynomial finiteFrequencySum
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hreal : Real.exp (-(1 / 2 : ℝ) * Real.log n) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, Real.rpow_def_of_pos hn0]
    congr 1
    ring
  have hcomplex : Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) =
      (Real.sqrt n : ℂ)⁻¹ := by
    calc
      _ = (Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      _ = _ := by rw [hreal, Complex.ofReal_inv]
  have heq : -((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log n : ℂ) =
      -(1 / 2 : ℂ) * (Real.log n : ℂ) + ((-Real.log n : ℝ) : ℂ) * t * Complex.I := by
    push_cast
    ring
  rw [heq, Complex.exp_add, hcomplex]
  unfold frequencyChar
  ring

theorem integral_dirichletMollifier_critical_norm_sq_le {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      ‖dirichletMollifier N ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
        12 * (T + N) * (1 + Real.log N) := by
  simp_rw [dirichletMollifier_critical]
  exact integral_criticalMollifier_norm_sq_le hN hT

end Sidon

end
end


-- Sidon.NumberTheory.MollifierSeries
section

noncomputable section

namespace Sidon

def truncatedMoebius (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ N then (ArithmeticFunction.moebius n : ℂ) else 0, by simp⟩

@[simp] theorem truncatedMoebius_apply (N n : ℕ) :
    truncatedMoebius N n = if n ≤ N then (ArithmeticFunction.moebius n : ℂ) else 0 := rfl

theorem LSeriesHasSum_truncatedMoebius (N : ℕ) (s : ℂ) :
    LSeriesHasSum (truncatedMoebius N) s (dirichletMollifier N s) := by
  have hfinite : ∀ n ∉ Finset.Icc 1 N, LSeries.term (truncatedMoebius N) s n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hNn : ¬n ≤ N := by
        intro h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, h⟩)
      simp [LSeries.term, hn0, truncatedMoebius_apply, hNn]
  have hh : HasSum (LSeries.term (truncatedMoebius N) s)
      (∑ n ∈ Finset.Icc 1 N, LSeries.term (truncatedMoebius N) s n) :=
    hasSum_sum_of_ne_finset_zero hfinite
  have heq : (∑ n ∈ Finset.Icc 1 N, LSeries.term (truncatedMoebius N) s n) =
      dirichletMollifier N s := by
    unfold dirichletMollifier
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp only [LSeries.term, hn0, ite_false, truncatedMoebius_apply, hnN, ite_true]
    rw [div_eq_mul_inv, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hnC,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 2
    ring
  exact heq ▸ hh

theorem zeta_mul_truncatedMoebius_apply (N n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * truncatedMoebius N) n =
      (mollifierCoefficient N n : ℂ) := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  simp only [mollifierCoefficient, Int.cast_sum, Finset.sum_filter, truncatedMoebius_apply,
    Int.cast_ite, Int.cast_zero]

theorem LSeriesHasSum_mollifierCoefficient {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    LSeriesHasSum (fun n => (mollifierCoefficient N n : ℂ)) s
      (riemannZeta s * dirichletMollifier N s) := by
  have hz : LSeriesHasSum ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ)
      s (riemannZeta s) := ArithmeticFunction.LSeriesHasSum_zeta hs
  have hm : LSeriesHasSum (truncatedMoebius N) s (dirichletMollifier N s) :=
    LSeriesHasSum_truncatedMoebius N s
  have hh := hz.convolution hm
  apply (LSeriesHasSum_congr s (riemannZeta s * dirichletMollifier N s)
    (f := fun n => (mollifierCoefficient N n : ℂ))
    (g := LSeries.convolution
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ) (truncatedMoebius N))
    (fun {n} _ => ?_)).mpr hh
  rw [ArithmeticFunction.coe_mul]
  exact (zeta_mul_truncatedMoebius_apply N n).symm

end Sidon

end
end


-- Sidon.NumberTheory.JensenMollifier
section

noncomputable section

open MeasureTheory MeromorphicOn Metric Real

namespace Sidon

def mollifierError (N : ℕ) (s : ℂ) : ℂ := riemannZeta s * dirichletMollifier N s - 1

def mollifierDetector (N : ℕ) (s : ℂ) : ℂ := 1 - mollifierError N s ^ 2

def mollifierCompanion (N : ℕ) (s : ℂ) : ℂ :=
  dirichletMollifier N s * (2 - riemannZeta s * dirichletMollifier N s)

theorem mollifierDetector_factor (N : ℕ) (s : ℂ) :
    mollifierDetector N s = riemannZeta s * mollifierCompanion N s := by
  unfold mollifierDetector mollifierError mollifierCompanion
  ring

theorem analyticAt_mollifierError (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifierError N) s := by
  have hζ := analyticOn_riemannZeta s hs
  have hM : AnalyticAt ℂ (dirichletMollifier N) s := by
    unfold dirichletMollifier
    fun_prop
  exact (hζ.mul hM).sub analyticAt_const

theorem analyticAt_mollifierDetector (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifierDetector N) s :=
  analyticAt_const.sub ((analyticAt_mollifierError N hs).pow 2)

theorem analyticAt_mollifierCompanion (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifierCompanion N) s := by
  have hζ := analyticOn_riemannZeta s hs
  have hM : AnalyticAt ℂ (dirichletMollifier N) s := by
    unfold dirichletMollifier
    fun_prop
  exact hM.mul (analyticAt_const.sub (hζ.mul hM))

theorem zeta_divisor_le_mollifierDetector (N : ℕ) {c : ℂ} {R : ℝ}
    (hdisc : ∀ z ∈ closedBall c |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N c ≠ 0) (z : ℂ) :
    divisor riemannZeta (closedBall c |R|) z ≤
      divisor (mollifierDetector N) (closedBall c |R|) z := by
  let U := closedBall c |R|
  have hζ : AnalyticOnNhd ℂ riemannZeta U := fun z hz => analyticOn_riemannZeta z (hdisc z hz)
  have hM : AnalyticOnNhd ℂ (mollifierCompanion N) U :=
    fun z hz => analyticAt_mollifierCompanion N (hdisc z hz)
  have hcU : c ∈ U := mem_closedBall_self (abs_nonneg R)
  have hprod : riemannZeta c * mollifierCompanion N c ≠ 0 := by
    rw [← mollifierDetector_factor]
    exact hc
  have hζc : riemannZeta c ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hMc : mollifierCompanion N c ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hζfin : ∀ w ∈ U, meromorphicOrderAt riemannZeta w ≠ ⊤ := by
    intro w hw
    apply hζ.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c |R|).isPreconnected hcU hw
    rw [(hζ c hcU).meromorphicOrderAt_eq, (hζ c hcU).analyticOrderAt_eq_zero.mpr hζc]
    simp
  have hMfin : ∀ w ∈ U, meromorphicOrderAt (mollifierCompanion N) w ≠ ⊤ := by
    intro w hw
    apply hM.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c |R|).isPreconnected hcU hw
    rw [(hM c hcU).meromorphicOrderAt_eq, (hM c hcU).analyticOrderAt_eq_zero.mpr hMc]
    simp
  have hdiv := divisor_fun_mul hζ.meromorphicOn hM.meromorphicOn hζfin hMfin
  have hfactor : (fun w => riemannZeta w * mollifierCompanion N w) = mollifierDetector N := by
    funext w
    exact (mollifierDetector_factor N w).symm
  rw [hfactor] at hdiv
  change divisor riemannZeta U z ≤ divisor (mollifierDetector N) U z
  rw [hdiv]
  exact le_add_of_nonneg_right (hM.divisor_nonneg z)

theorem log_norm_one_sub_sq_le (z : ℂ) : Real.log ‖1 - z ^ 2‖ ≤ ‖z‖ ^ 2 := by
  by_cases hz : ‖1 - z ^ 2‖ = 0
  · rw [hz, Real.log_zero]
    positivity
  · have hp : 0 < ‖1 - z ^ 2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hlog := Real.log_le_sub_one_of_pos hp
    have hnorm := norm_sub_le (1 : ℂ) (z ^ 2)
    rw [norm_one, norm_pow] at hnorm
    linarith

theorem jensen_mollifier_detector_le (N : ℕ) {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hdisc : ∀ z ∈ closedBall c |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N c ≠ 0) :
    (∑ᶠ z, (divisor (mollifierDetector N) (closedBall c |R|) z : ℝ) *
      Real.log (R * ‖c - z‖⁻¹)) ≤
        circleAverage (fun z => ‖mollifierError N z‖ ^ 2) c R -
          Real.log ‖mollifierDetector N c‖ := by
  have hd : AnalyticOnNhd ℂ (mollifierDetector N) (closedBall c |R|) :=
    fun z hz => analyticAt_mollifierDetector N (hdisc z hz)
  have he : AnalyticOnNhd ℂ (mollifierError N) (closedBall c |R|) :=
    fun z hz => analyticAt_mollifierError N (hdisc z hz)
  have hlog := hd.circleAverage_log_norm hc
  have hmono : circleAverage (fun z => Real.log ‖mollifierDetector N z‖) c R ≤
      circleAverage (fun z => ‖mollifierError N z‖ ^ 2) c R := by
    apply circleAverage_mono
    · exact (hd.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · exact ((he.continuousOn.mono sphere_subset_closedBall).norm.pow 2).circleIntegrable'
    · intro z _
      exact log_norm_one_sub_sq_le _
  linarith

end Sidon

end
end


-- Sidon.NumberTheory.BalancedMollifierSeries
section

noncomputable section

namespace Sidon

def balancedMollifierCoefficient (N n : ℕ) : ℂ :=
  (mollifierCoefficient N n : ℂ) - if n = 1 then 1 else 0

theorem balancedMollifierCoefficient_eq_zero {N n : ℕ} (hnN : n ≤ N) :
    balancedMollifierCoefficient N n = 0 := by
  unfold balancedMollifierCoefficient
  rw [mollifierCoefficient_eq_one_apply hnN]
  split_ifs <;> simp

theorem norm_balancedMollifierCoefficient_le {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    ‖balancedMollifierCoefficient N n‖ ≤ (n.divisors.card : ℝ) := by
  by_cases hn : n = 1
  · subst n
    rw [balancedMollifierCoefficient_eq_zero hN, norm_zero]
    positivity
  · rw [balancedMollifierCoefficient, if_neg hn, sub_zero, Complex.norm_intCast]
    exact_mod_cast abs_mollifierCoefficient_le N n

theorem LSeriesHasSum_unit_sequence (s : ℂ) :
    LSeriesHasSum (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s 1 := by
  have hh : HasSum
      (LSeries.term (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s)
      (∑ n ∈ ({1} : Finset ℕ),
        LSeries.term (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [LSeries.term, hn]
  change HasSum (LSeries.term (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) s) 1
  simpa [LSeries.term] using hh

theorem LSeriesHasSum_balancedMollifierCoefficient {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    LSeriesHasSum (balancedMollifierCoefficient N) s (mollifierError N s) := by
  have hh := LSeriesHasSum.sub (LSeriesHasSum_mollifierCoefficient hs N) (LSeriesHasSum_unit_sequence s)
  exact hh

end Sidon

end
end


-- Sidon.NumberTheory.ArithmeticConvolutionBounds
section

noncomputable section

namespace Sidon

def normalizeArithmetic (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / n, by simp⟩

@[simp] theorem normalizeArithmetic_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    normalizeArithmetic f n = f n / n := rfl

theorem normalizeArithmetic_mul (f g : ArithmeticFunction ℝ) :
    normalizeArithmetic (f * g) = normalizeArithmetic f * normalizeArithmetic g := by
  ext n
  rw [normalizeArithmetic_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have hmul := (Nat.mem_divisorsAntidiagonal.mp ha).1
  simp only [normalizeArithmetic_apply]
  rw [← hmul, Nat.cast_mul]
  ring

theorem sum_Ioc_convolution_le (f g : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Finset.Ioc 0 N, (f * g) n) ≤
      (∑ n ∈ Finset.Ioc 0 N, f n) * ∑ n ∈ Finset.Ioc 0 N, g n := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, Finset.sum_mul_sum]
  have hh : (∑ a ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun a => a.1 * a.2 ≤ N),
      f a.1 * g a.2) ≤ ∑ a ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N, f a.1 * g a.2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro a _ _
    exact mul_nonneg (hf _) (hg _)
  simpa only [Finset.sum_product] using hh

theorem sum_Ioc_convolution_div_le (f g : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Finset.Ioc 0 N, (f * g) n / n) ≤
      (∑ n ∈ Finset.Ioc 0 N, f n / n) * ∑ n ∈ Finset.Ioc 0 N, g n / n := by
  simpa only [← normalizeArithmetic_mul, normalizeArithmetic_apply] using
    sum_Ioc_convolution_le (normalizeArithmetic f) (normalizeArithmetic g) N
      (fun n => div_nonneg (hf n) (Nat.cast_nonneg n))
      (fun n => div_nonneg (hg n) (Nat.cast_nonneg n))

end Sidon

end
end


-- Sidon.NumberTheory.DivisorMeanSquare
section

noncomputable section

namespace Sidon

open scoped ArithmeticFunction.sigma

def fourDivisor : ArithmeticFunction ℕ := (ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)

theorem divisor_sq_le_fourDivisor_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (ArithmeticFunction.sigma 0 (p ^ e)) ^ 2 ≤ fourDivisor (p ^ e) := by
  rw [fourDivisor, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.sigma 0 a * ArithmeticFunction.sigma 0 b),
    Nat.sum_divisors_prime_pow hp, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  calc
    (e + 1) ^ 2 = ∑ _k ∈ Finset.range (e + 1), (e + 1) := by simp [pow_two]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hke : k ≤ e := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      have hdiv : p ^ e / p ^ k = p ^ (e - k) := Nat.pow_div hke hp.pos
      rw [hdiv, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have heq : e = k + (e - k) := by omega
      nlinarith [Nat.zero_le (k * (e - k))]

theorem divisor_sq_le_fourDivisor (n : ℕ) :
    n.divisors.card ^ 2 ≤ fourDivisor n := by
  by_cases hn : n = 0
  · subst n
    simp [fourDivisor]
  · have hσ := ArithmeticFunction.isMultiplicative_sigma (k := 0)
    have hleft := hσ.pmul hσ
    have hright := hσ.mul hσ
    rw [← ArithmeticFunction.sigma_zero_apply, pow_two]
    change ((ArithmeticFunction.sigma 0).pmul (ArithmeticFunction.sigma 0)) n ≤
      ((ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)) n
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hleft hn,
      ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hright hn]
    unfold Finsupp.prod
    apply Finset.prod_le_prod
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    simpa only [ArithmeticFunction.pmul_apply, pow_two, fourDivisor] using
      divisor_sq_le_fourDivisor_prime_pow hpprime (n.factorization p)

theorem sum_Ioc_nat_convolution_div_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℝ) / n) ≤
      (∑ n ∈ Finset.Ioc 0 N, (f n : ℝ) / n) *
        ∑ n ∈ Finset.Ioc 0 N, (g n : ℝ) / n := by
  simpa only [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply] using
    sum_Ioc_convolution_div_le (f : ArithmeticFunction ℝ) (g : ArithmeticFunction ℝ) N
      (fun n => Nat.cast_nonneg (f n)) (fun n => Nat.cast_nonneg (g n))

theorem sum_Ioc_zeta_div (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.zeta n : ℝ) / n) = (harmonic N : ℝ) := by
  have hI : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
  rw [hI, harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [ArithmeticFunction.zeta_apply_ne hn0, Nat.cast_one, one_div]

theorem sum_Ioc_divisor_div_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) / n) ≤ (harmonic N : ℝ) ^ 2 := by
  have hσ : ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]
  have hh := sum_Ioc_nat_convolution_div_le ArithmeticFunction.zeta ArithmeticFunction.zeta N
  rw [← hσ] at hh
  simpa only [ArithmeticFunction.sigma_zero_apply, sum_Ioc_zeta_div, pow_two] using hh

theorem sum_Ioc_fourDivisor_div_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) / n) ≤ (harmonic N : ℝ) ^ 4 := by
  have hh := sum_Ioc_nat_convolution_div_le (ArithmeticFunction.sigma 0)
    (ArithmeticFunction.sigma 0) N
  have hσ := sum_Ioc_divisor_div_le N
  simp only [ArithmeticFunction.sigma_zero_apply] at hh
  calc
    _ ≤ (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) / n) *
        ∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) / n := hh
    _ ≤ (harmonic N : ℝ) ^ 2 * (harmonic N : ℝ) ^ 2 :=
      mul_le_mul hσ hσ (by positivity) (sq_nonneg _)
    _ = _ := by ring

theorem sum_Ioc_divisor_sq_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 4 := by
  have hpoint : (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      ∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) := by
    apply Finset.sum_le_sum
    intro n _
    exact_mod_cast divisor_sq_le_fourDivisor n
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) := hpoint
    _ ≤ (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (fourDivisor n : ℝ) / n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hn0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hnN (Nat.cast_nonneg (fourDivisor n) :
        (0 : ℝ) ≤ fourDivisor n)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Ioc_fourDivisor_div_le N) (Nat.cast_nonneg N)

end Sidon

end
end


-- Sidon.NumberTheory.DivisorDirichletSeries
section

noncomputable section

namespace Sidon

theorem LSeriesHasSum_nat_convolution {f g : ArithmeticFunction ℕ} {s a b : ℂ}
    (hf : LSeriesHasSum (fun n => (f n : ℂ)) s a)
    (hg : LSeriesHasSum (fun n => (g n : ℂ)) s b) :
    LSeriesHasSum (fun n => ((f * g) n : ℂ)) s (a * b) := by
  have hh := ArithmeticFunction.LSeriesHasSum_mul (f := (f : ArithmeticFunction ℂ))
    (g := (g : ArithmeticFunction ℂ)) hf hg
  simpa only [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply] using hh

theorem LSeriesHasSum_fourDivisor {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (fourDivisor n : ℂ)) s (riemannZeta s ^ 4) := by
  have hz : LSeriesHasSum (fun n => (ArithmeticFunction.zeta n : ℂ)) s (riemannZeta s) :=
    ArithmeticFunction.LSeriesHasSum_zeta hs
  have hσ : ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]
  have htwo := LSeriesHasSum_nat_convolution hz hz
  rw [← hσ] at htwo
  have hfour := LSeriesHasSum_nat_convolution htwo htwo
  change LSeriesHasSum
    (fun n => (((ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0)) n : ℂ))
    s (riemannZeta s ^ 4)
  convert hfour using 1
  ring

theorem LSeriesSummable_fourDivisor {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (fourDivisor n : ℂ)) s :=
  (LSeriesHasSum_fourDivisor hs).LSeriesSummable

theorem hasSum_fourDivisor_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (fourDivisor n : ℝ) / (n : ℝ) ^ σ)
      (riemannZeta (σ : ℂ) ^ 4).re := by
  have hh := Complex.reCLM.hasSum (LSeriesHasSum_fourDivisor
    (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ))
  change HasSum (fun n : ℕ => (fourDivisor n : ℝ) / (n : ℝ) ^ σ)
    (Complex.reCLM (riemannZeta (σ : ℂ) ^ 4))
  convert hh using 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [fourDivisor, LSeries.term]
  · simp only [LSeries.term, hn, ite_false, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_natCast (fourDivisor n),
      ← Complex.ofReal_div, Complex.reCLM_apply, Complex.ofReal_re]

theorem summable_divisor_sq_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (hasSum_fourDivisor_div_rpow hσ).summable
  intro n
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  exact_mod_cast divisor_sq_le_fourDivisor n

theorem tsum_divisor_sq_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ σ) ≤
      (riemannZeta (σ : ℂ) ^ 4).re := by
  rw [← (hasSum_fourDivisor_div_rpow hσ).tsum_eq]
  apply Summable.tsum_le_tsum _ (summable_divisor_sq_div_rpow hσ)
    (hasSum_fourDivisor_div_rpow hσ).summable
  intro n
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  exact_mod_cast divisor_sq_le_fourDivisor n

end Sidon

end
end


-- Sidon.NumberTheory.PSeriesBounds
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/

/-! # Elementary pole bounds for positive Dirichlet series

The real-series proof is adapted from `RiemannGaussian.ZetaEulerReciprocalAllowance`
at revision `6e969fd6e9c639eed280c595732248c106187603`, using only mathlib.
-/

noncomputable section

open MeasureTheory Set

namespace Sidon

theorem pseries_mass_bound {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hq : -σ < -1 := by linarith
  have ha : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by change 1 ≤ x at hx; linarith) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ)) 1
    (by simpa only [Nat.cast_one] using ha) (by simpa only [Nat.cast_one] using hi)
    (by intro y hy; simp only [Nat.cast_one, mem_Ioi] at hy
        exact Real.rpow_nonneg (by linarith) _)
  simp only [Nat.cast_one] at ht
  rw [integral_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)] at ht
  simp only [Real.one_rpow, Nat.add_assoc, Nat.reduceAdd] at ht
  have hs := Real.summable_nat_rpow.mpr hq
  rw [← hs.sum_add_tsum_nat_add 2]
  have hzero : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, hzero, Real.one_rpow, zero_add]
  have he : -(1 : ℝ) / (-σ + 1) = 1 / (σ - 1) := by
    rw [show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq]
  linarith

theorem norm_riemannZeta_le_pole {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hh := ArithmeticFunction.LSeriesHasSum_zeta hs
  have hsum := hh.summable
  have hterm (n : ℕ) :
      ‖LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) s n‖ =
        (n : ℝ) ^ (-s.re) := by
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero, norm_zero, Nat.cast_zero,
        Real.zero_rpow (show -s.re ≠ 0 by linarith)]
    · rw [LSeries.term, if_neg hn, ArithmeticFunction.zeta_apply_ne hn]
      simp only [Nat.cast_one, norm_div, norm_one,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  calc
    _ = ‖∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) s n‖ := by rw [hh.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := tsum_congr hterm
    _ ≤ _ := pseries_mass_bound hs

end Sidon

end
end


-- Sidon.NumberTheory.DivisorSeriesBounds
section

noncomputable section

namespace Sidon

theorem tsum_divisor_sq_div_rpow_le_pole {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) ≤ 16 / δ ^ 4 := by
  have hs : 1 < 1 + δ := by linarith
  have hz := norm_riemannZeta_le_pole (s := ((1 + δ : ℝ) : ℂ))
    (by simpa only [Complex.ofReal_re] using hs)
  simp only [Complex.ofReal_re, add_sub_cancel_left] at hz
  have hbound : 1 + 1 / δ ≤ 2 / δ := by
    apply (le_div_iff₀ hδ).mpr
    field_simp
    linarith
  calc
    _ ≤ (riemannZeta ((1 + δ : ℝ) : ℂ) ^ 4).re := tsum_divisor_sq_div_rpow_le hs
    _ ≤ ‖riemannZeta ((1 + δ : ℝ) : ℂ) ^ 4‖ := Complex.re_le_norm _
    _ = ‖riemannZeta ((1 + δ : ℝ) : ℂ)‖ ^ 4 := norm_pow _ _
    _ ≤ (2 / δ) ^ 4 := by gcongr; exact hz.trans hbound
    _ = _ := by ring

theorem divisor_sq_log_term_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ) ≤
      (2 / δ) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1 hδ.le
    have hlog := Real.log_le_rpow_div hn0.le hδ
    have hlogbound : 1 + Real.log n ≤ (2 / δ) * (n : ℝ) ^ δ := by
      have hfirst : 1 ≤ (n : ℝ) ^ δ / δ :=
        (le_div_iff₀ hδ).mpr (by nlinarith)
      have hh : 1 + Real.log n ≤ 2 * ((n : ℝ) ^ δ / δ) := by linarith
      convert hh using 1 <;> ring
    have heq : (n : ℝ) ^ (1 + 2 * δ) = (n : ℝ) ^ (1 + δ) * (n : ℝ) ^ δ := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ (n.divisors.card : ℝ) ^ 2 * ((2 / δ) * (n : ℝ) ^ δ) /
          ((n : ℝ) ^ (1 + δ) * (n : ℝ) ^ δ) := by gcongr
      _ = _ := by field_simp

theorem summable_divisor_sq_log_div_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable (fun n : ℕ =>
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)) := by
  apply Summable.of_nonneg_of_le _ (divisor_sq_log_term_le hδ hδ1)
    ((summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)).mul_left (2 / δ))
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [Real.log_nonneg hn1]))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem tsum_divisor_sq_log_div_rpow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) /
      (n : ℝ) ^ (1 + 2 * δ)) ≤ 32 / δ ^ 5 := by
  calc
    _ ≤ ∑' n : ℕ, (2 / δ) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) :=
      Summable.tsum_le_tsum (divisor_sq_log_term_le hδ hδ1)
        (summable_divisor_sq_log_div_rpow hδ hδ1)
        ((summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)).mul_left (2 / δ))
    _ = (2 / δ) * ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ) := tsum_mul_left
    _ ≤ (2 / δ) * (16 / δ ^ 4) :=
      mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
    _ = _ := by ring

end Sidon

end
end


-- Sidon.NumberTheory.MollifierRightEndpoint
section

noncomputable section

namespace Sidon

def rightMollifierCoefficient (N : ℕ) (δ : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (balancedMollifierCoefficient N) ((1 + δ : ℝ) : ℂ) n

theorem norm_rightMollifierCoefficient_le {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (n : ℕ) :
    ‖rightMollifierCoefficient N δ n‖ ≤
      (n.divisors.card : ℝ) / (n : ℝ) ^ (1 + δ) := by
  rw [rightMollifierCoefficient, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, Complex.ofReal_re]
    exact div_le_div_of_nonneg_right (norm_balancedMollifierCoefficient_le hN n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem norm_rightMollifierCoefficient_le_sq {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (n : ℕ) :
    ‖rightMollifierCoefficient N δ n‖ ≤
      (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ) := by
  apply (norm_rightMollifierCoefficient_le hN δ n).trans
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  simpa only [pow_two] using
    (show (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * n.divisors.card by
      exact_mod_cast Nat.le_mul_self n.divisors.card)

theorem norm_rightMollifierCoefficient_sq_le {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ‖rightMollifierCoefficient N δ n‖ ^ 2 ≤
      (1 / (N : ℝ)) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)) := by
  by_cases hnN : n ≤ N
  · have hz := balancedMollifierCoefficient_eq_zero hnN
    have hzero : rightMollifierCoefficient N δ n = 0 := by
      simp [rightMollifierCoefficient, LSeries.term, hz]
    rw [hzero, norm_zero]
    norm_num only [zero_pow, OfNat.ofNat_ne_zero]
    positivity
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow0 : 0 < (n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn0 _
    have hpowN : (N : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
      have hh : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
      exact hh.trans (Real.self_le_rpow_of_one_le hn1 (by linarith))
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_rightMollifierCoefficient_le hN δ n) 2
    rw [div_pow] at hh
    apply hh.trans
    calc
      _ = (1 / (n:ℝ)^(1+δ)) * ((n.divisors.card:ℝ)^2/(n:ℝ)^(1+δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hN0 hpowN) (by positivity)

theorem weighted_norm_rightMollifierCoefficient_sq_le {N : ℕ} (hN : 1 ≤ N)
    (δ : ℝ) (n : ℕ) :
    (n : ℝ) * ‖rightMollifierCoefficient N δ n‖ ^ 2 * (1 + Real.log n) ≤
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 ≤ 1 + Real.log n := by linarith [Real.log_nonneg hn1]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_rightMollifierCoefficient_le hN δ n) 2
    calc
      _ ≤ (n : ℝ) * ((n.divisors.card : ℝ) / (n : ℝ) ^ (1 + δ)) ^ 2 *
          (1 + Real.log n) := by gcongr
      _ = _ := by
        have heq : ((n : ℝ) ^ (1 + δ)) ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 + 2 * δ) := by
          calc
            _ = (n : ℝ) ^ ((1 + δ) * 2) := by rw [Real.rpow_mul hn0.le, Real.rpow_two]
            _ = (n : ℝ) ^ (1 + (1 + 2 * δ)) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hn0, Real.rpow_one]
        rw [div_pow, heq]
        field_simp

theorem LSeries_term_vertical (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term f ((σ : ℂ) + t * Complex.I) n =
      LSeries.term f (σ : ℂ) n * frequencyChar (-Real.log n) t := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hnC]
    unfold frequencyChar
    simp_rw [Complex.cpow_def_of_ne_zero hnC,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    rw [div_mul_eq_div_mul_one_div, one_div, ← Complex.exp_neg]
    congr 2
    push_cast
    ring

theorem logarithmicSeries_rightMollifierCoefficient {N : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (t : ℝ) :
    logarithmicSeries (rightMollifierCoefficient N δ) t =
      mollifierError N ((1 + δ : ℝ) + t * Complex.I) := by
  have hh := LSeriesHasSum_balancedMollifierCoefficient
    (s := ((1 + δ : ℝ) : ℂ) + t * Complex.I) (by simp; linarith) N
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro n
  exact (LSeries_term_vertical _ _ _ _).symm

theorem integral_mollifierError_right_norm_sq_le {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
      T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 := by
  let a := rightMollifierCoefficient N δ
  let d (n : ℕ) : ℝ := (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)
  let w (n : ℕ) : ℝ :=
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)
  have hd : Summable d := summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)
  have hw : Summable w := summable_divisor_sq_log_div_rpow hδ hδ1
  have ha : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_rightMollifierCoefficient_le_sq hN δ) hd
  have ha2 : Summable (fun n => ‖a n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (norm_rightMollifierCoefficient_sq_le hN hδ) (hd.mul_left (1 / (N : ℝ)))
  have hw0 (n : ℕ) : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hn1])
  have haw : Summable (fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) :=
    Summable.of_nonneg_of_le hw0 (weighted_norm_rightMollifierCoefficient_sq_le hN δ) hw
  have ha_bound : (∑' n : ℕ, ‖a n‖) ≤ 16 / δ ^ 4 :=
    (Summable.tsum_le_tsum (norm_rightMollifierCoefficient_le_sq hN δ) ha hd).trans
      (tsum_divisor_sq_div_rpow_le_pole hδ hδ1)
  have ha2_bound : (∑' n : ℕ, ‖a n‖ ^ 2) ≤ 16 / ((N : ℝ) * δ ^ 4) := by
    calc
      _ ≤ ∑' n : ℕ, (1 / (N : ℝ)) * d n :=
        Summable.tsum_le_tsum (norm_rightMollifierCoefficient_sq_le hN hδ) ha2
          (hd.mul_left _)
      _ = (1 / (N : ℝ)) * ∑' n : ℕ, d n := tsum_mul_left
      _ ≤ (1 / (N : ℝ)) * (16 / δ ^ 4) :=
        mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
      _ = _ := by ring
  have haw_bound : (∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) ≤ 32 / δ ^ 5 :=
    (Summable.tsum_le_tsum (weighted_norm_rightMollifierCoefficient_sq_le hN δ) haw hw).trans
      (tsum_divisor_sq_log_div_rpow_le hδ hδ1)
  have hh := integral_logarithmicSeries_norm_sq_le a (by simp [a, rightMollifierCoefficient])
    ha ha2 haw hT
  dsimp [a] at hh
  simp_rw [logarithmicSeries_rightMollifierCoefficient hδ] at hh
  calc
    _ ≤ _ := hh
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 4 * (16 / δ ^ 4) ^ 2 + 16 * (32 / δ ^ 5) := by
      gcongr
    _ = _ := by ring

theorem integral_mollifierError_right_norm_sq_le_simple {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
      2048 * (T / (N : ℝ) + 1) / δ ^ 8 := by
  have hδ4 : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h84 : δ ^ 8 ≤ δ ^ 4 := by
    calc
      _ = δ ^ 4 * δ ^ 4 := by ring
      _ ≤ δ ^ 4 * 1 := mul_le_mul_of_nonneg_left hδ4 (by positivity)
      _ = _ := mul_one _
  have h85 : δ ^ 8 ≤ δ ^ 5 := by
    calc
      _ = δ ^ 5 * δ ^ 3 := by ring
      _ ≤ δ ^ 5 * 1 := mul_le_mul_of_nonneg_left hδ3 (by positivity)
      _ = _ := mul_one _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h48 : 1 / δ ^ 4 ≤ 1 / δ ^ 8 :=
    one_div_le_one_div_of_le (by positivity) h84
  have h58 : 1 / δ ^ 5 ≤ 1 / δ ^ 8 :=
    one_div_le_one_div_of_le (by positivity) h85
  calc
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 :=
      integral_mollifierError_right_norm_sq_le hN hδ hδ1 hT
    _ = (16 * T / N) * (1 / δ ^ 4) + 1024 * (1 / δ ^ 8) + 512 * (1 / δ ^ 5) := by ring
    _ ≤ (16 * T / N) * (1 / δ ^ 8) + 1024 * (1 / δ ^ 8) + 512 * (1 / δ ^ 8) := by
      gcongr
    _ = (16 * (T / N) + 1536) / δ ^ 8 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [div_nonneg hT hN0.le]

end Sidon

end
end


-- THTwistedRight
section

noncomputable section
namespace CentralWindowTwist
open Finset Sidon

def arithmeticTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => χ (n : ZMod q) * f n, by simp⟩

@[simp] lemma arithmeticTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) (n : ℕ) :
    arithmeticTwist χ f n = χ (n : ZMod q) * f n := rfl

lemma arithmeticTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℂ) :
    arithmeticTwist χ (f*g) = arithmeticTwist χ f * arithmeticTwist χ g := by
  ext n
  simp only [ArithmeticFunction.mul_apply, arithmeticTwist_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hh : χ (n:ZMod q) = χ (p.1:ZMod q)*χ (p.2:ZMod q) := by
    rw [← map_mul, ← Nat.cast_mul, hm]
  rw [hh]
  ring

def twistedMollifier {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, LSeries.term (arithmeticTwist χ (truncatedMoebius N)) s n

def twistedError {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  χ.LFunction s * twistedMollifier χ N s - 1

lemma hasSum_twistedMollifier {q N : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    LSeriesHasSum (arithmeticTwist χ (truncatedMoebius N)) s (twistedMollifier χ N s) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hNn : ¬ n ≤ N := by
      intro h
      exact hn (mem_Icc.mpr ⟨by omega, h⟩)
    simp [LSeries.term, hn0, truncatedMoebius_apply, hNn]

lemma hasSum_twistedZeta {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesHasSum (arithmeticTwist χ (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
      s (χ.LFunction s) := by
  rw [χ.LFunction_eq_LSeries hs]
  have h : LSeriesSummable (fun n : ℕ => χ (n:ZMod q)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := (1:ℝ)) (fun n _ => χ.norm_le_one _) hs
  apply (LSeriesHasSum_congr _ _ (f := arithmeticTwist χ (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := fun n : ℕ => χ (n:ZMod q)) ?_).mpr h.LSeriesHasSum
  intro n hn
  simp [hn]

lemma hasSum_twistedError {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ => χ (n:ZMod q) * balancedMollifierCoefficient N n)
      s (twistedError χ N s) := by
  have hprod := (hasSum_twistedZeta χ hs).convolution (hasSum_twistedMollifier (N:=N) χ s)
  have hsub := LSeriesHasSum.sub hprod (LSeriesHasSum_unit_sequence s)
  apply (LSeriesHasSum_congr s _ (f := fun n : ℕ => χ (n:ZMod q) * balancedMollifierCoefficient N n)
    (g := _) ?_).mpr hsub
  intro n hn
  change χ (n:ZMod q) * balancedMollifierCoefficient N n =
    LSeries.convolution _ _ n - _
  rw [ArithmeticFunction.coe_mul, ← arithmeticTwist_mul, arithmeticTwist_apply,
    zeta_mul_truncatedMoebius_apply]
  unfold balancedMollifierCoefficient
  by_cases h : n = 1
  · subst n; simp
  · simp [h]

open MeasureTheory

/- Argument adapted from Sidon.MollifierRightEndpoint, Apache-2.0. -/
theorem dominated_right_mean {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T)
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (hdom : ∀ n, ‖a n‖ ≤ ‖rightMollifierCoefficient N δ n‖) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicSeries a t‖ ^ 2) ≤
      T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 := by

  let d (n : ℕ) : ℝ := (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)
  let w (n : ℕ) : ℝ :=
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)
  have hd : Summable d := summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)
  have hw : Summable w := summable_divisor_sq_log_div_rpow hδ hδ1
  have ha : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (hdom n).trans (norm_rightMollifierCoefficient_le_sq hN δ n)) hd
  have ha2 : Summable (fun n => ‖a n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun n => (pow_le_pow_left₀ (norm_nonneg _) (hdom n) 2).trans (norm_rightMollifierCoefficient_sq_le hN hδ n)) (hd.mul_left (1 / (N : ℝ)))
  have hw0 (n : ℕ) : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hn1])
  have haw : Summable (fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) :=
    Summable.of_nonneg_of_le hw0 (fun n => (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdom n) 2) (Nat.cast_nonneg n)) (by linarith [Real.log_natCast_nonneg n] : 0 ≤ 1+Real.log n)).trans (weighted_norm_rightMollifierCoefficient_sq_le hN δ n)) hw
  have ha_bound : (∑' n : ℕ, ‖a n‖) ≤ 16 / δ ^ 4 :=
    (Summable.tsum_le_tsum (fun n => (hdom n).trans (norm_rightMollifierCoefficient_le_sq hN δ n)) ha hd).trans
      (tsum_divisor_sq_div_rpow_le_pole hδ hδ1)
  have ha2_bound : (∑' n : ℕ, ‖a n‖ ^ 2) ≤ 16 / ((N : ℝ) * δ ^ 4) := by
    calc
      _ ≤ ∑' n : ℕ, (1 / (N : ℝ)) * d n :=
        Summable.tsum_le_tsum (fun n => (pow_le_pow_left₀ (norm_nonneg _) (hdom n) 2).trans (norm_rightMollifierCoefficient_sq_le hN hδ n)) ha2
          (hd.mul_left _)
      _ = (1 / (N : ℝ)) * ∑' n : ℕ, d n := tsum_mul_left
      _ ≤ (1 / (N : ℝ)) * (16 / δ ^ 4) :=
        mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
      _ = _ := by ring
  have haw_bound : (∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) ≤ 32 / δ ^ 5 :=
    (Summable.tsum_le_tsum (fun n => (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdom n) 2) (Nat.cast_nonneg n)) (by linarith [Real.log_natCast_nonneg n] : 0 ≤ 1+Real.log n)).trans (weighted_norm_rightMollifierCoefficient_sq_le hN δ n)) haw hw).trans
      (tsum_divisor_sq_log_div_rpow_le hδ hδ1)
  have hh := integral_logarithmicSeries_norm_sq_le a ha0
    ha ha2 haw hT
  calc
    _ ≤ _ := hh
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 4 * (16 / δ ^ 4) ^ 2 + 16 * (32 / δ ^ 5) := by
      gcongr
    _ = _ := by ring

theorem dominated_right_mean_simple {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T)
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (hdom : ∀ n, ‖a n‖ ≤ ‖rightMollifierCoefficient N δ n‖) :
    (∫ t in (0 : ℝ)..T, ‖logarithmicSeries a t‖ ^ 2) ≤
      2048 * (T / (N : ℝ) + 1) / δ ^ 8 := by
  have hδ4 : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h84 : δ ^ 8 ≤ δ ^ 4 := by
    calc
      _ = δ ^ 4 * δ ^ 4 := by ring
      _ ≤ δ ^ 4 * 1 := mul_le_mul_of_nonneg_left hδ4 (by positivity)
      _ = _ := mul_one _
  have h85 : δ ^ 8 ≤ δ ^ 5 := by
    calc
      _ = δ ^ 5 * δ ^ 3 := by ring
      _ ≤ δ ^ 5 * 1 := mul_le_mul_of_nonneg_left hδ3 (by positivity)
      _ = _ := mul_one _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h48 : 1 / δ ^ 4 ≤ 1 / δ ^ 8 :=
    one_div_le_one_div_of_le (by positivity) h84
  have h58 : 1 / δ ^ 5 ≤ 1 / δ ^ 8 :=
    one_div_le_one_div_of_le (by positivity) h85
  calc
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 :=
      dominated_right_mean hN hδ hδ1 hT a ha0 hdom
    _ = (16 * T / N) * (1 / δ ^ 4) + 1024 * (1 / δ ^ 8) + 512 * (1 / δ ^ 5) := by ring
    _ ≤ (16 * T / N) * (1 / δ ^ 8) + 1024 * (1 / δ ^ 8) + 512 * (1 / δ ^ 8) := by
      gcongr
    _ = (16 * (T / N) + 1536) / δ ^ 8 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [div_nonneg hT hN0.le]

open scoped ComplexConjugate

def rightTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (δ : ℝ) (n : ℕ) : ℂ :=
  χ (n:ZMod q) * rightMollifierCoefficient N δ n

lemma series_rightTwist {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    logarithmicSeries (rightTwist χ N δ) t = twistedError χ N ((1 + δ : ℝ) + (t:ℂ)*Complex.I) := by
  have hh := hasSum_twistedError (N:=N) χ
    (s := ((1 + δ : ℝ) : ℂ) + t * Complex.I) (by simp; linarith)
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro n
  rw [LSeries_term_vertical]
  unfold rightTwist rightMollifierCoefficient
  by_cases hn : n = 0
  · subst n; simp
  · simp only [LSeries.term_of_ne_zero hn]
    ring

lemma logSeries_neg_norm (a : ℕ → ℂ) (t : ℝ) :
    ‖logarithmicSeries a (-t)‖ = ‖logarithmicSeries (fun n => conj (a n)) t‖ := by
  have h : conj (logarithmicSeries a (-t)) = logarithmicSeries (fun n => conj (a n)) t := by
    simp only [logarithmicSeries, Complex.conj_tsum, map_mul, frequencyChar,
      ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, map_neg]
    apply tsum_congr
    intro n
    congr 2
    push_cast
    ring
  rw [← h, Complex.norm_conj]

theorem symmetric_right_error {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hN : 1 ≤ N) {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖twistedError χ N ((1 + δ : ℝ) + (t:ℂ)*Complex.I)‖^2) ≤
      4096*(T/(N:ℝ)+1)/δ^8 := by
  let a := rightTwist χ N δ
  have hdom (n : ℕ) : ‖a n‖ ≤ ‖rightMollifierCoefficient N δ n‖ := by
    dsimp [a,rightTwist]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have ha0 : a 0 = 0 := by simp [a,rightTwist,rightMollifierCoefficient]
  have hpos := dominated_right_mean_simple hN hδ hδ1 hT a ha0 hdom
  have hneg := dominated_right_mean_simple hN hδ hδ1 hT (fun n => conj (a n))
    (by rw [ha0,map_zero]) (fun n => by rw [Complex.norm_conj]; exact hdom n)
  let f := fun t : ℝ => ‖logarithmicSeries a t‖^2
  have hneg' : (∫ t in -T..0, f t) ≤ 2048*(T/(N:ℝ)+1)/δ^8 := by
    have hs := intervalIntegral.integral_comp_neg (a:= (0:ℝ)) (b:=T) (f:=f)
    rw [neg_zero] at hs
    rw [← hs]
    simpa only [f,logSeries_neg_norm] using hneg
  have hs : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (hdom n).trans (norm_rightMollifierCoefficient_le_sq hN δ n))
      (summable_divisor_sq_div_rpow (by linarith : 1 < 1+δ))
  have hc : Continuous (logarithmicSeries a) := by
    apply continuous_tsum (fun i => continuous_const.mul (continuous_frequencyChar _)) hs
    intro i x
    simp [a,norm_mul]
  have hci : Continuous f := hc.norm.pow 2
  simp_rw [← series_rightTwist χ hδ]
  change (∫ t in -T..T, f t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hci.intervalIntegrable _ _)
    (hci.intervalIntegrable _ _)]
  change (∫ t in -T..0, f t) + (∫ t in 0..T, ‖logarithmicSeries a t‖ ^ 2) ≤ _
  calc
    _ ≤ 2048*(T/(N:ℝ)+1)/δ^8 + 2048*(T/(N:ℝ)+1)/δ^8 := by
      exact add_le_add hneg' hpos
    _ = _ := by ring

end CentralWindowTwist

end
end


-- THTwistAnalytic
section

noncomputable section
namespace CentralWindowTwist
open Sidon Finset

lemma mollifier_formula {q N : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    twistedMollifier χ N s = ∑ n ∈ Icc 1 N,
      χ (n:ZMod q)*(ArithmeticFunction.moebius n:ℂ)*Complex.exp (-s*(Real.log n:ℂ)) := by
  unfold twistedMollifier
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
  rw [LSeries.term_of_ne_zero hn0, arithmeticTwist_apply, truncatedMoebius_apply,
    if_pos (mem_Icc.mp hn).2, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast n,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 2
  ring

theorem mollifier_entire {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Differentiable ℂ (twistedMollifier χ N) := by
  have hh := funext (mollifier_formula (N:=N) χ)
  rw [hh]
  fun_prop

theorem error_entire {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) :
    Differentiable ℂ (twistedError χ N) :=
  ((DirichletCharacter.differentiable_LFunction hχ).mul (mollifier_entire χ N)).sub
    (differentiable_const _)

lemma mollifier_on_critical_line {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) :
    twistedMollifier χ N (criticalPoint t) = criticalSum χ N t := by
  rw [mollifier_formula]
  unfold criticalSum logarithmicPolynomial finiteFrequencySum
  apply sum_congr rfl
  intro n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have he : Complex.exp (-(criticalPoint t)*(Real.log n:ℂ)) =
      ((Real.sqrt n : ℂ)⁻¹) * frequencyChar (-Real.log n) t := by
    unfold criticalPoint frequencyChar
    rw [show -((1/2:ℂ)+(t:ℂ)*Complex.I)*(Real.log n:ℂ) =
      ((-(1/2:ℝ)*Real.log n:ℝ):ℂ) + ((-Real.log n:ℝ):ℂ)*t*Complex.I by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
    have hreal : Real.exp (-(1/2:ℝ)*Real.log n) = (Real.sqrt n)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, Real.rpow_def_of_pos hn0]
      congr 1
      ring
    rw [hreal,Complex.ofReal_inv]
  rw [he,twistCoeff]
  ring

lemma mollifier_norm_le {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) : ‖twistedMollifier χ N s‖ ≤ N := by
  rw [mollifier_formula]
  refine (norm_sum_le _ _).trans ?_
  have h := Finset.sum_le_sum (s := Icc 1 N)
    (f := fun n : ℕ => ‖χ (n:ZMod q)*(ArithmeticFunction.moebius n:ℂ)*Complex.exp (-s*(Real.log n:ℂ))‖)
    (g := fun _ => (1:ℝ)) (fun n hn => by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hμ : ‖(ArithmeticFunction.moebius n:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
    have hex : ‖Complex.exp (-s*(Real.log n:ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp,Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Real.log_nonneg hn1)
    rw [norm_mul,norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (χ.norm_le_one _) (by positivity) hμ)
      (by positivity) hex)
  simpa using h

theorem strip_growth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 →
      ‖twistedError χ N s‖ ≤ K*(1+s.im^2) := by
  let f := twistedError χ N
  have hcont : Continuous f := (error_entire hχ N).continuous
  obtain ⟨m,hm⟩ := (isCompact_closedBall (0:ℂ) 4).exists_bound_of_continuousOn hcont.continuousOn
  let B := (q:ℝ)*((q:ℝ)^2+12)
  refine ⟨max (max 1 m) (B*N+1), lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans
    (le_max_left _ _)), ?_⟩
  intro s hlo hhi
  have hR : 1 ≤ 1+s.im^2 := by nlinarith [sq_nonneg s.im]
  have hnq : 0 ≤ (q:ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn : ‖s‖ ≤ 2+|s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (show 0 ≤ s.re by linarith)] at h
    linarith
  by_cases ht : |s.im| < 1
  · have hmem : s ∈ Metric.closedBall (0:ℂ) 4 := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    exact ((hm s hmem).trans (le_max_right 1 m)).trans
      ((le_max_left _ _).trans (le_mul_of_one_le_right (by positivity) hR))
  have ht1 : 1 ≤ |s.im| := le_of_not_gt ht
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at ht1
  have ht2 : |s.im| ≤ s.im^2 := by nlinarith [sq_abs s.im, sq_nonneg (|s.im|-1)]
  have hL := OAI.Vg.V14m χ (by linarith : 0 ≤ s.re) (by linarith : s.re ≤ 2)
    (A:=4+4*‖s‖) (fun a ha => by
      have h := OAI.V2.V1tf ha (by linarith : (1/10:ℝ)<s.re) hs1 (N:=1) le_rfl
      norm_num only [Nat.cast_one, Real.one_rpow, sum_range_one, Nat.zero_add] at h
      have hden : 1 ≤ ‖1-s‖ := by
        have hh := Complex.abs_im_le_norm (1-s)
        simpa using ht1.trans (by simpa using hh : |s.im| ≤ ‖1-s‖)
      have hrest : 2*‖s‖/s.re ≤ 4*‖s‖ := by
        apply (div_le_iff₀ (by linarith : 0<s.re)).mpr
        nlinarith [mul_nonneg (norm_nonneg s) (sub_nonneg.mpr hlo)]
      have hunit : ‖(((((1:ℕ):ℝ)+a:ℝ):ℂ)^(-s))‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by have := ha.1; positivity)]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num; linarith [ha.1])
          (by simp; linarith)
      have hh := norm_add_le
        (HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-OAI.V2.V29 a s -
          ((((1:ℕ):ℝ)+a:ℝ):ℂ)^(-s)) (((((1:ℕ):ℝ)+a:ℝ):ℂ)^(-s))
      rw [sub_add_cancel] at hh
      change ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-OAI.V2.V29 a s‖ ≤ _
      have hinv := one_div_le_one_div_of_le zero_lt_one hden
      norm_num at hinv
      norm_num at h
      push_cast at hunit hh
      linarith)
  have hL' : ‖χ.LFunction s‖ ≤ B*(1+s.im^2) := by
    apply hL.trans
    dsimp [B]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hnq
    nlinarith [mul_nonneg (sq_nonneg (q:ℝ)) (sq_nonneg s.im)]
  have hM := mollifier_norm_le (N:=N) χ (by linarith : 0 ≤ s.re)
  change ‖χ.LFunction s * twistedMollifier χ N s - 1‖ ≤ _
  calc
    _ ≤ ‖χ.LFunction s‖ * ‖twistedMollifier χ N s‖ + 1 := by
      simpa only [norm_mul,norm_one] using norm_sub_le (χ.LFunction s * twistedMollifier χ N s) 1
    _ ≤ (B*(1+s.im^2)) * N + 1 := add_le_add (mul_le_mul hL' hM (norm_nonneg _) (by positivity)) le_rfl
    _ ≤ (B*N+1)*(1+s.im^2) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end CentralWindowTwist

end
end


-- TH8000InteriorSlices
section

namespace CentralWindowInterpolation
open Set MeasureTheory Sidon CentralWindowTwist

set_option maxHeartbeats 1200000 in
theorem twisted_left_cumulative :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N : ℕ) (hN : 1≤N) (T : ℝ), 0 ≤ T →
      (∫ t in Icc (-T) T, ‖twistedError χ N (((1/2:ℝ):ℂ)+t*Complex.I)‖^2) ≤
        (C*(q:ℝ)^6*(1+Real.log N))*(T+N)*(1+T)^(3/8:ℝ) := by
  obtain ⟨A,hA,hh⟩ := TH8000CriticalAll.mollified_left_mean
  refine ⟨A+4,by positivity,?_⟩
  intro q _ χ N hN T hT
  have h := hh q χ N T hN hT
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at h
  have hfun (t : ℝ) : twistedError χ N (((1/2:ℝ):ℂ)+t*Complex.I) =
      χ.LFunction (criticalPoint t)*criticalSum χ N t-1 := by
    have he : (((1/2:ℝ):ℂ)+t*Complex.I) = criticalPoint t := by
      unfold criticalPoint
      push_cast
      rfl
    rw [he, twistedError, mollifier_on_critical_line]
  simp_rw [hfun]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq6 : 1 ≤ (q:ℝ)^6 := one_le_pow₀ hq
  have hnR : 0 ≤ (N:ℝ) := by positivity
  have hlog : 1 ≤ 1+Real.log N := by linarith [Real.log_natCast_nonneg N]
  have hpow : 1 ≤ (1+T)^(3/8:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hprod : T ≤ (q:ℝ)^6*(1+Real.log N)*(T+N)*(1+T)^(3/8:ℝ) := by
    calc
      T ≤ T+N := by linarith
      _ ≤ ((q:ℝ)^6*(1+Real.log N))*(T+N) :=
        le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hq6 hlog)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow
  linarith only [h,hprod]

set_option maxHeartbeats 1200000 in
theorem twisted_interior_slices :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ R σ₀ u : ℝ, 1 ≤ R → 2 ≤ Real.log R → 1/2 ≤ σ₀ → σ₀ ≤ 1 →
      σ₀ ≤ u → u ≤ 1+1/Real.log R →
      (∫ t in Icc 1 R, ‖twistedError χ ⌈R⌉₊ ((u:ℂ)+t*Complex.I)‖^2) ≤
        C*(q:ℝ)^6*R^((11/4:ℝ)*(1-σ₀))*(Real.log R)^9 := by
  obtain ⟨A,hA,hleft⟩ := twisted_left_cumulative
  let L := max 1 (6*Real.exp 6*gaussianCumulativeConstant*A)
  let B := max 1 (8192*Real.exp 6*gaussianCumulativeConstant)
  have hL : 1≤L := le_max_left .. 
  have hB : 1≤B := le_max_left ..
  refine ⟨Real.exp 2*L*B*Real.exp (11/4),by positivity,?_⟩
  intro q _ χ hχ R σ₀ u hR hlog hσ₀ hσ₀' hu hu'
  let N := ⌈R⌉₊
  obtain ⟨hN,hRN,hNR,hlogN⟩ := ceil_mollifier_parameters hR hlog
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0<N from hN)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq6 : 1 ≤ (q:ℝ)^6 := one_le_pow₀ hq1
  obtain ⟨K,hK,hgrowth⟩ := strip_growth hχ N
  have hδ : 0 < 1/Real.log R := by positivity
  have hδ' : 1/Real.log R ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hlog
  have hr0 : 0<R := by linarith
  have hlog0 : 0<Real.log R := by linarith
  let F := twistedError χ N
  have hf := error_entire hχ N
  have hG := gaussianCumulativeConstant_pos
  have hl : verticalL2 (G F R) (1/2) ≤ (L*(q:ℝ)^6)*Real.log R*R^(11/8:ℝ) := by
    have hx := vertical_of_cumulative (F:=F) hf hK.le hgrowth hR le_rfl (by norm_num)
      hNp.le (by positivity : 0 ≤ A*(q:ℝ)^6*(1+Real.log N))
      (by norm_num : (0:ℝ)≤3/8) (by norm_num) (hleft q χ N hN)
    have hRN' : R+(N:ℝ) ≤ 3*R := by dsimp [N]; linarith
    have heq : R * R^(3/8:ℝ) = R^(11/8:ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one R]
      rw [← Real.rpow_add hr0]; norm_num
    apply hx.trans
    calc
      _ ≤ Real.exp 6*gaussianCumulativeConstant*(A*(q:ℝ)^6*(2*Real.log R))*(3*R)*R^(3/8:ℝ) := by gcongr
      _ = (6*Real.exp 6*gaussianCumulativeConstant*A)*(q:ℝ)^6*Real.log R*R^(11/8:ℝ) := by
        rw [← heq]; ring
      _ ≤ _ := by gcongr; exact le_max_right .. 
  have hr : verticalL2 (G F R) (1+1/Real.log R) ≤ B*(Real.log R)^8 := by
    let δ := 1/Real.log R
    have hc (T : ℝ) (hT : 0≤T) :
        (∫ t in Icc (-T) T, ‖F (((1+δ:ℝ):ℂ)+t*Complex.I)‖^2) ≤
          (4096/((N:ℝ)*δ^8))*(T+N)*(1+T)^(0:ℝ) := by
      have h := symmetric_right_error (N:=N) (δ:=δ) χ hN hδ
        (show δ≤1 from hδ'.trans (by norm_num)) hT
      rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at h
      apply h.trans_eq
      rw [Real.rpow_zero, mul_one]
      have hnz := hNp.ne'
      have hdz : δ ≠ 0 := hδ.ne'
      field_simp
      <;> ring
    have hδ0 : 0<δ := hδ
    have hx := vertical_of_cumulative (F:=F) hf hK.le hgrowth hR (by dsimp [δ]; linarith : (1/2:ℝ)≤1+δ)
      (by dsimp [δ]; linarith) hNp.le (by positivity) (p:=0) le_rfl (by norm_num) hc
    apply hx.trans
    rw [Real.rpow_zero, mul_one]
    have hRR : R + (N:ℝ) ≤ 2*N := by dsimp [N]; linarith
    calc
      _ ≤ Real.exp 6*gaussianCumulativeConstant*(4096/((N:ℝ)*δ^8))*(2*N) := by gcongr
      _ = (8192*Real.exp 6*gaussianCumulativeConstant)*(Real.log R)^8 := by
        dsimp [δ]; field_simp <;> norm_num
      _ ≤ _ := by gcongr; exact le_max_right ..
  have h := strip_bound hf hK.le hgrowth hR hlog
    (one_le_mul_of_one_le_of_one_le hL hq6) hB hσ₀ hσ₀' hu hu' hl hr
  exact h.trans_eq (by ring)

end CentralWindowInterpolation

end


-- TH8000JensenCenter
section

/- The center and elementary detector-loss estimates are adapted from
TomasOrtega/Sidon at 735de6d7c67b81a28b1e07e3f2661dbc17bb89d6,
Sidon/NumberTheory/MollifierCenter.lean (Apache-2.0). -/
namespace GoldbachCentralSeven.Jensen
open CentralWindowTwist Sidon Set MeasureTheory
noncomputable section

theorem norm_twisted_re_two_le {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hN : 1 ≤ N) {s : ℂ} (hs : s.re = 2) :
    ‖twistedError χ N s‖ ≤ 256 / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hf := hasSum_twistedError (N := N) (s := s) χ (by rw [hs]; norm_num)
  have hterm (n : ℕ) : ‖LSeries.term (fun k : ℕ => χ (k:ZMod q)*balancedMollifierCoefficient N k) s n‖ ≤
      (1 / Real.sqrt N) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    by_cases hnN : n ≤ N
    · have hz := balancedMollifierCoefficient_eq_zero hnN
      simp only [LSeries.term, hz, mul_zero, zero_div, ite_self, norm_zero]
      positivity
    · have hn : 0 < n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hrootle : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ n))
      have hd : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
        simpa only [pow_two] using
          (show (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * n.divisors.card by
            exact_mod_cast Nat.le_mul_self n.divisors.card)
      have heq : (n : ℝ) ^ 2 = (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        norm_num
      rw [LSeries.term, if_neg (by omega : n ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hn, hs, Real.rpow_two]
      calc
        _ ≤ (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          rw [norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
            ((norm_balancedMollifierCoefficient_le hN n).trans hd)
        _ ≤ (n.divisors.card : ℝ) ^ 2 /
            ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt N) := by
          rw [heq]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hrootle (Real.rpow_nonneg hn0.le _)
        _ = _ := by ring
  have hmajor := (summable_divisor_sq_div_rpow (σ := (3 / 2 : ℝ)) (by norm_num)).mul_left
    (1 / Real.sqrt N)
  calc
    _ = ‖∑' n : ℕ, LSeries.term (fun k : ℕ => χ (k:ZMod q)*balancedMollifierCoefficient N k) s n‖ := by rw [hf.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => χ (k:ZMod q)*balancedMollifierCoefficient N k) s n‖ :=
      norm_tsum_le_tsum_norm hf.summable.norm
    _ ≤ ∑' n : ℕ, (1 / Real.sqrt N) *
        ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Summable.tsum_le_tsum hterm hf.summable.norm hmajor
    _ = (1 / Real.sqrt N) *
        ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ (1 / Real.sqrt N) * 256 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := tsum_divisor_sq_div_rpow_le_pole (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at hh
      exact hh
    _ = _ := by ring

theorem neg_log_norm_one_sub_sq_le {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 2) :
    1 - z ^ 2 ≠ 0 ∧ -Real.log ‖1 - z ^ 2‖ ≤ 2 * ‖z‖ ^ 2 := by
  let u := ‖z‖ ^ 2
  let a := ‖1 - z ^ 2‖
  have hu0 : 0 ≤ u := sq_nonneg _
  have ha : 1 - u ≤ a := by
    have hh := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    simpa only [norm_one, norm_pow] using hh
  have ha0 : 0 < a := by dsimp [u] at *; linarith
  have hlog := Real.one_sub_inv_le_log_of_pos ha0
  have hprod : 1 ≤ (1 + 2 * u) * a := by
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1 + 2 * u by positivity)
    have hh' := mul_nonneg hu0 (show 0 ≤ 1 - 2 * u by dsimp [u]; linarith)
    nlinarith
  have hinv : a⁻¹ ≤ 1 + 2 * u := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ ha0).mpr (by nlinarith)
  exact ⟨norm_pos_iff.mp ha0, by change -Real.log a ≤ 2 * u; linarith⟩

theorem twisted_detector_center_bound {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hN : 131072 ≤ N) {s : ℂ}
    (hs : s.re = 2) :
    (1-(twistedError χ N s)^2) ≠ 0 ∧
      -Real.log ‖(1-(twistedError χ N s)^2)‖ ≤ 131072 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlarge : (131072 : ℝ) ≤ N := by exact_mod_cast hN
  have herr := norm_twisted_re_two_le χ (by omega : 1 ≤ N) hs
  have hsq : ‖twistedError χ N s‖ ^ 2 ≤ 65536 / (N : ℝ) := by
    have hh := sq_le_sq₀ (norm_nonneg (twistedError χ N s))
      (show 0 ≤ 256 / Real.sqrt N by positivity) |>.mpr herr
    rw [div_pow, Real.sq_sqrt hNpos.le] at hh
    norm_num at hh ⊢
    exact hh
  have hhalf : ‖twistedError χ N s‖ ^ 2 ≤ 1 / 2 := by
    apply hsq.trans
    exact (div_le_iff₀ hNpos).mpr (by linarith)
  obtain ⟨hne, hlog⟩ := neg_log_norm_one_sub_sq_le hhalf
  refine ⟨hne, hlog.trans ?_⟩
  calc
    2 * ‖twistedError χ N s‖ ^ 2 ≤ 2 * (65536 / (N : ℝ)) := by gcongr
    _ = _ := by ring

end
end GoldbachCentralSeven.Jensen

end


-- TH8000RightSlices
section

/- The far-right pointwise estimate extends the real-part-two proof from
TH8000JensenCenter. Source material from TomasOrtega/Sidon,
735de6d7c67b81a28b1e07e3f2661dbc17bb89d6, Apache License 2.0. -/
noncomputable section
namespace GoldbachCentralSeven.Jensen
open CentralWindowTwist Sidon Set MeasureTheory
theorem norm_twisted_of_two_le {q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hN : 1 ≤ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖twistedError χ N s‖ ≤ 256 / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hf := hasSum_twistedError (N := N) (s := s) χ (by linarith)
  have hterm (n : ℕ) : ‖LSeries.term (fun k : ℕ => χ (k:ZMod q)*balancedMollifierCoefficient N k) s n‖ ≤
      (1 / Real.sqrt N) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    by_cases hnN : n ≤ N
    · have hz := balancedMollifierCoefficient_eq_zero hnN
      simp only [LSeries.term, hz, mul_zero, zero_div, ite_self, norm_zero]
      positivity
    · have hn : 0 < n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hrootle : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ n))
      have hd : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
        simpa only [pow_two] using
          (show (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * n.divisors.card by
            exact_mod_cast Nat.le_mul_self n.divisors.card)
      have heq : (n : ℝ) ^ 2 = (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        norm_num
      rw [LSeries.term, if_neg (by omega : n ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hn]
      calc
        _ ≤ (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ s.re := by
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
          rw [norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
            ((norm_balancedMollifierCoefficient_le hN n).trans hd)
        _ ≤ (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hn0)
          simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (show 1 ≤ n by omega)) hs
        _ ≤ (n.divisors.card : ℝ) ^ 2 /
            ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt N) := by
          rw [heq]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hrootle (Real.rpow_nonneg hn0.le _)
        _ = _ := by ring
  have hmajor := (summable_divisor_sq_div_rpow (σ := (3 / 2 : ℝ)) (by norm_num)).mul_left
    (1 / Real.sqrt N)
  calc
    _ = ‖∑' n : ℕ, LSeries.term (fun k : ℕ => χ (k:ZMod q)*balancedMollifierCoefficient N k) s n‖ := by rw [hf.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun k : ℕ => χ (k:ZMod q)*balancedMollifierCoefficient N k) s n‖ :=
      norm_tsum_le_tsum_norm hf.summable.norm
    _ ≤ ∑' n : ℕ, (1 / Real.sqrt N) *
        ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Summable.tsum_le_tsum hterm hf.summable.norm hmajor
    _ = (1 / Real.sqrt N) *
        ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ (1 / Real.sqrt N) * 256 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := tsum_divisor_sq_div_rpow_le_pole (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at hh
      exact hh
    _ = _ := by ring

private lemma continuous_right_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) {u : ℝ} (hu : 1 < u) :
    Continuous (fun t : ℝ => ‖twistedError χ N ((u:ℂ)+(t:ℂ)*Complex.I)‖^2) := by
  let P := fun t : ℝ => (u:ℂ)+(t:ℂ)*Complex.I
  have cP : Continuous P := by unfold P; fun_prop
  have cL : Continuous (fun t => χ.LFunction (P t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (χ.differentiableAt_LFunction _ (.inl ?_)).continuousAt.comp (cP.continuousAt)
    intro heq
    have := congrArg Complex.re heq
    simp [P] at this
    linarith
  have cM := (mollifier_entire χ N).continuous.comp cP
  exact ((cL.mul cM).sub continuous_const).norm.pow 2

theorem right_slices {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {R u : ℝ} (hR : 4 ≤ R) (hu : 1 + 1/Real.log R ≤ u) :
    (∫ t in Icc 1 R, ‖twistedError χ ⌈R⌉₊ ((u:ℂ)+(t:ℂ)*Complex.I)‖^2) ≤
      65536*(Real.log R)^8 := by
  let N := ⌈R⌉₊
  have hR0 : 0 ≤ R := by linarith
  have hRN : R ≤ (N:ℝ) := Nat.le_ceil _
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1:ℝ) ≤ N by linarith)
  have hNpos : 0 < (N:ℝ) := by linarith
  have hlog : 1 ≤ Real.log R :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hlog0 : 0 < Real.log R := by linarith
  have hpow : 1 ≤ (Real.log R)^8 := one_le_pow₀ hlog
  have hu1 : 1 < u := by linarith [one_div_pos.mpr hlog0]
  let f := fun t : ℝ => ‖twistedError χ N ((u:ℂ)+(t:ℂ)*Complex.I)‖^2
  have hf : Continuous f := continuous_right_line χ N hu1
  change (∫ t in Icc 1 R, f t) ≤ _
  by_cases hu2 : u ≤ 2
  · let δ := u-1
    have hδpos : 0 < δ := by dsimp [δ]; linarith
    have hδhi : δ ≤ 1 := by dsimp [δ]; linarith
    have hδlo : 1/Real.log R ≤ δ := by dsimp [δ]; linarith
    have hinv : 1/δ ≤ Real.log R := by
      apply (div_le_iff₀ hδpos).mpr
      simpa only [mul_comm] using (div_le_iff₀ hlog0).mp hδlo
    have hmean := symmetric_right_error χ hN1 hδpos hδhi hR0
    have hline : 1+δ=u := by dsimp [δ]; ring
    rw [hline,intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      ← integral_Icc_eq_integral_Ioc] at hmean
    have hsub : Icc (1:ℝ) R ⊆ Icc (-R) R := Icc_subset_Icc_left (by linarith)
    have hsubset : (∫ t in Icc 1 R, f t) ≤ ∫ t in Icc (-R) R, f t :=
      setIntegral_mono_set hf.continuousOn.integrableOn_Icc
        (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (Filter.Eventually.of_forall hsub)
    have hquot : R/(N:ℝ) ≤ 1 := (div_le_one hNpos).mpr hRN
    have hinv8 := pow_le_pow_left₀ (show 0 ≤ 1/δ by positivity) hinv 8
    calc
      _ ≤ _ := hsubset.trans hmean
      _ = 4096*(R/(N:ℝ)+1)*(1/δ)^8 := by ring
      _ ≤ 8192*(Real.log R)^8 :=
        mul_le_mul (by linarith) hinv8 (by positivity) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · have huR : 2 ≤ u := (lt_of_not_ge hu2).le
    have hb (t : ℝ) : f t ≤ (256 / Real.sqrt N)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      apply norm_twisted_of_two_le χ hN1
      simpa using huR
    have hint : (∫ t in (1:ℝ)..R, f t) ≤ ∫ _t : ℝ in 1..R, (256 / Real.sqrt N)^2 :=
      intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun t _ => hb t)
    rw [intervalIntegral.integral_const] at hint
    change (∫ t in (1:ℝ)..R, f t) ≤ (R-1)*(256/Real.sqrt N)^2 at hint
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : 1 ≤ R)]
    apply hint.trans
    rw [div_pow, Real.sq_sqrt hNpos.le]
    calc
      _ = 65536*((R-1)/(N:ℝ)) := by ring
      _ ≤ 65536*1 := mul_le_mul_of_nonneg_left ((div_le_one hNpos).mpr (by linarith)) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)

end GoldbachCentralSeven.Jensen

end
end


-- TH8000CharacterDensity
section

namespace GoldbachCentralSeven.Jensen
open Set Filter MeasureTheory OAI.Ostmann CentralWindowTwist CentralWindowInterpolation

theorem uniform_twisted_slices : ∃ K T₀ : ℝ, 0<K ∧ UniformSliceInput K T₀ := by
  obtain ⟨C,hC,hs⟩ := twisted_interior_slices
  let K := max C 65536
  refine ⟨2048*K, max 131072 (Real.exp 4), by dsimp [K]; positivity, ?_⟩
  intro χ T hT σ₀ hσ₀ hσ₀'
  letI : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let R := T+3
  let N := ⌈R⌉₊
  let a := (11/4:ℝ)*(1-σ₀)
  have hN' : (131072:ℝ)≤T := (le_max_left ..).trans hT
  have hT1 : 1≤T := by linarith
  have hTpos : 0<T := by linarith
  have hlogT : 4≤Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 4) ((le_max_right ..).trans hT)
    simpa using hh
  have hR4 : 4≤R := by dsimp [R]; linarith
  have hTR : T≤R := by dsimp [R]; linarith
  have hR2 : R ≤ 2*T := by dsimp [R]; linarith
  have hRL : Real.log T ≤ Real.log R := Real.log_le_log hTpos hTR
  have hLR : Real.log R ≤ 2*Real.log T := by
    have hh := Real.log_le_log (by linarith : 0<R) hR2
    rw [Real.log_mul (by norm_num) hTpos.ne'] at hh
    linarith [Real.log_two_lt_d9]
  have ha : 0≤a := by dsimp [a]; linarith
  have ha2 : a≤2 := by dsimp [a]; linarith
  have hrat : R^a ≤ 4*T^a := calc
    _ ≤ (2*T)^a := Real.rpow_le_rpow (by linarith) hR2 ha
    _ = (2:ℝ)^a*T^a := Real.mul_rpow (by norm_num) hTpos.le
    _ ≤ 4*T^a := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ha2
      rw [Real.rpow_two] at h
      exact mul_le_mul_of_nonneg_right (by nlinarith : (2:ℝ)^a≤4) (Real.rpow_nonneg hTpos.le _)
  have hlogs : (Real.log R)^9 ≤ 512*(Real.log T)^9 := calc
    _ ≤ (2*Real.log T)^9 := pow_le_pow_left₀ (by linarith) hLR _
    _ = _ := by ring
  have hq : (1:ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hq6 : 1 ≤ (χ.modulus:ℝ)^6 := one_le_pow₀ hq
  have hRN : R ≤ (N:ℝ) := Nat.le_ceil _
  have hN : 131072 ≤ N := by exact_mod_cast (show (131072:ℝ)≤N by linarith)
  refine ⟨twistedMollifier χ.character N, mollifier_entire χ.character N, ?_, ?_⟩
  · intro y hy
    have h := twisted_detector_center_bound χ.character hN (s := Sidon.jensenCenter y)
      (by simp [Sidon.jensenCenter])
    exact ⟨h.1,h.2.trans (div_le_div_of_nonneg_left (by positivity) hTpos (hTR.trans hRN))⟩
  · intro u hu
    change (∫ t in Icc 1 R, ‖twistedError χ.character N ((u:ℂ)+t*Complex.I)‖^2) ≤ _
    have hL0 : 1≤Real.log R := by linarith
    have hone : 1≤R^a := Real.one_le_rpow (by linarith) ha
    have hraw :
        (∫ t in Icc 1 R, ‖twistedError χ.character N ((u:ℂ)+t*Complex.I)‖^2) ≤
        K*(χ.modulus:ℝ)^6*R^a*(Real.log R)^9 := by
      rcases le_total u (1+1/Real.log R) with hsmall | hbig
      · have h := hs χ.modulus χ.character χ.nontrivial R σ₀ u (by linarith)
          (by linarith) hσ₀ hσ₀' hu.1 hsmall
        apply h.trans
        gcongr; exact le_max_left ..
      · apply (right_slices χ.character hR4 hbig).trans
        have hbase : (65536:ℝ) ≤ K*(χ.modulus:ℝ)^6*R^a := calc
          _ ≤ K := le_max_right ..
          _ ≤ K*(χ.modulus:ℝ)^6 := le_mul_of_one_le_right (by dsimp [K]; positivity) hq6
          _ ≤ _ := le_mul_of_one_le_right (by dsimp [K]; positivity) hone
        calc
          _ ≤ (K*(χ.modulus:ℝ)^6*R^a)*(Real.log R)^8 :=
            mul_le_mul_of_nonneg_right hbase (by positivity)
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (by dsimp [K]; positivity)
            exact pow_le_pow_right₀ hL0 (by decide)
    apply hraw.trans
    change _ ≤ (2048*K)*(χ.modulus:ℝ)^6*T^a*(Real.log T)^9
    calc
      _ ≤ K*(χ.modulus:ℝ)^6*(4*T^a)*(512*(Real.log T)^9) := by gcongr
      _ = _ := by ring

theorem conductor_uniform_density :
    ∃ C : ℝ, 0 < C ∧ ∃ T₁ : ℝ, ∀ χ : PrimitiveComplexCharacter, ∀ T σ : ℝ,
      T₁ ≤ T → 1/2 ≤ σ → σ ≤ 1 →
      (((V1 χ).count σ T) : ℝ) ≤ C*(χ.modulus:ℝ)^6 *
        T^((23/8:ℝ)*(1-σ))*(Real.log T)^11 := by
  obtain ⟨K,T₀,hK,hs⟩ := uniform_twisted_slices
  exact uniform_character_density_of_slices hK hs

end GoldbachCentralSeven.Jensen

end


-- THZeroBudget
section

namespace GoldbachCentralSeven.Density
open Finset Filter OAI.Ostmann
open scoped Topology

theorem complete_damped_budget :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (X r T δ : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      2 ≤ X → 1 ≤ Real.log X → 0 ≤ r → r ≤ 5/32 → T₀ ≤ T → T ≤ X^2 →
      0 ≤ δ → δ ≤ 1/8 → 1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∀ χ ∈ F, ∀ i ∈ (V1 χ).V14 T, ((V1 χ).zeros i).re ≤ 1-δ) →
      (∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 T,
        damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          C*(Real.log X)^14*(X^(-(1/1024:ℝ)) + X^(-r/16-δ/2048)) := by
  obtain ⟨K,Ts,hK,hsl⟩ := Jensen.uniform_twisted_slices
  obtain ⟨Cl,hCl,hlow⟩ := actual_low_all_heights
  obtain ⟨Cm,hCm,hmid⟩ := actual_middle_all_heights
  obtain ⟨Ch,hCh,U,htop⟩ := actual_near_one_all_heights hK hsl
  let C := Cl+2*3^13*(Cm+Ch)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,max 2 U,le_max_left _ _,?_⟩
  intro X r T δ Q F hx hl hr hr' ht ht' hd hd' hQ hQu hQl hF hcut
  have hx' : 1 < X := by linarith
  have hp : 0 < X := by linarith
  have ht2 := (le_max_left 2 U).trans ht
  let β (χ : PrimitiveComplexCharacter) (i : ℕ) := ((V1 χ).zeros i).re
  let R (χ : PrimitiveComplexCharacter) := (V1 χ).V14 T
  let m (χ : PrimitiveComplexCharacter) (i : ℕ) := damping X T*X^(β χ i-1)/(χ.modulus:ℝ)
  have hn (χ i) : 0 ≤ m χ i :=
    div_nonneg (mul_nonneg (damping_nonneg hp.le (by linarith)) (Real.rpow_nonneg hp.le _))
      (Nat.cast_nonneg _)
  have hrow (χ) (hχ : χ ∈ F) :
      (∑ i ∈ R χ, m χ i) ≤
      (∑ i ∈ (R χ).filter (fun i => β χ i ≤ 1/2), m χ i) +
      (∑ i ∈ (R χ).filter (fun i => 1/2 ≤ β χ i ∧ β χ i ≤ 7/8), m χ i) +
      (∑ i ∈ (R χ).filter (fun i => 7/8 ≤ β χ i ∧ β χ i ≤ 1-δ), m χ i) := by
    simp only [sum_filter,←sum_add_distrib]
    apply sum_le_sum
    intro i hi
    have hh : β χ i ≤ 1-δ := hcut χ hχ i hi
    have p := hn χ i
    split <;> split <;> split <;> grind
  have h := sum_le_sum hrow
  simp only [sum_add_distrib] at h
  have h1 := hlow X r T Q F hx hr hr' ht2 ht' hQ hQu hQl hF
  have h2 := hmid X r T Q F hx' hr hr' ht2 ht' hQ hQu hQl hF
  have h3 := htop X r T δ Q F hx' hl hr hr' ((le_max_right _ _).trans ht) ht'
    hd hd' hQ hQu hQl hF
  have h123 := h.trans (add_le_add (add_le_add h1 h2) h3)
  have hl0 : 0 < Real.log X := by linarith
  have hlpow : Real.log X ≤ (Real.log X)^14 := by
    simpa using pow_le_pow_right₀ hl (by norm_num : 1 ≤ 14)
  have hlowpow : X^(-(1/96:ℝ)) ≤ X^(-(1/1024:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx'.le (by norm_num)
  have hmix : (1+Real.log X)*(3*Real.log X)^13 ≤ 2*3^13*(Real.log X)^14 := by
    calc
      _ ≤ (2*Real.log X)*(3*Real.log X)^13 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hleft := mul_le_mul (mul_le_mul_of_nonneg_left hlowpow hCl.le) hlpow hl0.le (by positivity)
  have hmid' := mul_le_mul_of_nonneg_left hmix
    (mul_nonneg hCm.le (Real.rpow_pos_of_pos hp (-(1/1024:ℝ))).le)
  have htop' := mul_le_mul_of_nonneg_left hmix
    (mul_nonneg hCh.le (Real.rpow_pos_of_pos hp (-r/16-δ/2048)).le)
  refine h123.trans ?_
  dsimp [C]
  nlinarith only [hleft,hmid',htop',
    mul_nonneg (mul_nonneg hCl.le (pow_nonneg hl0.le 14))
      (Real.rpow_pos_of_pos hp (-r/16-δ/2048)).le,
    mul_nonneg (mul_nonneg hCm.le (pow_nonneg hl0.le 14))
      (Real.rpow_pos_of_pos hp (-r/16-δ/2048)).le,
    mul_nonneg (mul_nonneg hCh.le (pow_nonneg hl0.le 14))
      (Real.rpow_pos_of_pos hp (-(1/1024:ℝ))).le]

def LowConductorLogGap : Prop :=
  ∀ A B : ℕ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ χ : PrimitiveComplexCharacter,
    (χ.modulus:ℝ) ≤ (Real.log X)^B → ∀ i : ℕ, |((V1 χ).zeros i).im| ≤ X^2 →
    X^(-(1-((V1 χ).zeros i).re)/2048:ℝ) ≤ ((Real.log X)^A)⁻¹

private lemma exp_log_budget {X : ℝ} (hx : 1 < X) (P : ℕ) :
    X^((P:ℝ)*Real.log (Real.log X)/Real.log X) = (Real.log X)^P := by
  have hp := zero_lt_one.trans hx
  have hl := Real.log_pos hx
  rw [← Real.rpow_natCast (Real.log X) P, Real.rpow_def_of_pos hp,
    Real.rpow_def_of_pos hl]
  congr 1
  field_simp

theorem uniform_band_log_budget (hgap : LowConductorLogGap) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (r T : ℝ) (Q : ℕ) (F : Finset PrimitiveComplexCharacter),
      0 ≤ r → r ≤ 5/32 → 2 ≤ T → T ≤ X^2 →
      1 ≤ Q → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 T,
        damping X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤ ((Real.log X)^A)⁻¹ := by
  obtain ⟨C,hC,T₀,hT₀,hc⟩ := complete_damped_budget
  let P := A+15
  obtain ⟨Y,hY⟩ := hgap P (16*P)
  have hlim : Tendsto (fun X : ℝ => Real.log (Real.log X)/Real.log X)
      atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hsmall : ∀ᶠ X : ℝ in atTop, 2048*((P:ℝ)*Real.log (Real.log X)/Real.log X) ≤ 1/8 := by
    have hh := (tendsto_const_nhds (x:=(2048:ℝ)*(P:ℝ))).mul hlim
    have hv := hh.eventually (gt_mem_nhds (show (2048:ℝ)*(P:ℝ)*0 < 1/8 by norm_num))
    filter_upwards [hv] with X h
    change 2048*(P:ℝ)*(Real.log (Real.log X)/Real.log X) < (1/8:ℝ) at h
    convert h.le using 1 <;> ring
  have hpower := (isLittleO_log_rpow_rpow_atTop (P:ℝ) (by norm_num : 0 < (1/1024:ℝ))).bound
      (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop Y, eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2*C)),
    (tendsto_rpow_atTop (by norm_num : 0 < (1/3:ℝ))).eventually_ge_atTop T₀,
    hsmall,hpower] with X hXY hX hXL hV hsmall hpower
  intro r T Q F hr hr' ht ht' hQ hQu hQl hF
  have hx : 1 < X := by linarith
  have hp := zero_lt_one.trans hx
  have hL := Real.log_pos hx
  have hL1 := (le_max_left (1:ℝ) (2*C)).trans hXL
  have hLC := (le_max_right (1:ℝ) (2*C)).trans hXL
  let z := (P:ℝ)*Real.log (Real.log X)/Real.log X
  have hz : 0 ≤ z := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hL1)) hL.le
  have hzX : X^z = (Real.log X)^P := exp_log_budget hx P
  have hzInv : X^(-z) = ((Real.log X)^P)⁻¹ := by rw [Real.rpow_neg hp.le,hzX]
  have hplain : X^(-(1/1024:ℝ)) ≤ ((Real.log X)^P)⁻¹ := by
    change ‖Real.log X^(P:ℝ)‖ ≤ 1*‖X^(1/1024:ℝ)‖ at hpower
    rw [Real.rpow_natCast,Real.norm_eq_abs,abs_of_pos (pow_pos hL _),one_mul,
      Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hp _)] at hpower
    rw [Real.rpow_neg hp.le]
    exact inv_anti₀ (pow_pos hL _) hpower
  let U := max T₀ T
  have hU2 : U ≤ X^2 := max_le (hV.trans (by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num : (1/3:ℝ)≤2))) ht'
  have hco : ∃ δ : ℝ, 0 ≤ δ ∧ δ ≤ 1/8 ∧ X^(-r/16-δ/2048) ≤ ((Real.log X)^P)⁻¹ ∧
      ∀ χ ∈ F, ∀ i ∈ (V1 χ).V14 U, ((V1 χ).zeros i).re ≤ 1-δ := by
    by_cases hlarge : 16*z ≤ r
    · refine ⟨0,le_rfl,by norm_num,?_,?_⟩
      · rw [← hzInv]
        exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      · intro χ _ i _
        exact (by simpa using ((V1 χ).in_strip i).2.le)
    · refine ⟨2048*z,by positivity,hsmall,?_,?_⟩
      · rw [← hzInv]
        exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      · intro χ hχ i hi
        have hmod : (χ.modulus:ℝ) ≤ (Real.log X)^(16*P) := by
          have hpow16 := exp_log_budget hx (16*P)
          rw [← hpow16]
          have hχQ : (χ.modulus:ℝ) ≤ Q := by exact_mod_cast (hF χ hχ).1
          refine hχQ.trans (hQu.trans (Real.rpow_le_rpow_of_exponent_le hx.le ?_))
          have h' := le_of_not_ge hlarge
          dsimp [z] at h'
          push_cast
          convert h' using 1 <;> ring
        have hg := hY X hXY χ hmod i (((V1 χ).V2r U i).mp hi |>.trans hU2)
        rw [← hzInv] at hg
        have := (Real.rpow_le_rpow_left_iff hx).mp hg
        linarith
  obtain ⟨δ,hd,hd',hpay,hcut⟩ := hco
  have hbound := hc X r U δ Q F hX hL1 hr hr' (le_max_left _ _) hU2 hd hd'
    hQ hQu hQl hF hcut
  have hdeq : damping X T = damping X U := by
    by_cases hs : T₀ ≤ T
    · simp [U,max_eq_right hs]
    · have h₀ : 0 < T₀ := by linarith
      have h₁ : 0 < T := by linarith
      have hle : T ≤ T₀ := le_of_not_ge hs
      simp only [U,max_eq_left hle,damping,min_eq_left ((one_le_div h₁).mpr (hle.trans hV)),
        min_eq_left ((one_le_div h₀).mpr hV)]
  rw [hdeq]
  have hUi : 0 ≤ damping X U := damping_nonneg hp.le (by dsimp [U]; linarith [le_max_right T₀ T])
  calc
    _ ≤ ∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 U, damping X U*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ) := by
      apply sum_le_sum
      intro χ hχ
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact ((V1 χ).V2r U i).mpr ((((V1 χ).V2r T i).mp hi).trans (le_max_right _ _))
      · intro i _ _
        exact div_nonneg (mul_nonneg hUi (by positivity)) (Nat.cast_nonneg _)
    _ ≤ _ := hbound
    _ ≤ C*(Real.log X)^14*(((Real.log X)^P)⁻¹+((Real.log X)^P)⁻¹) := by gcongr
    _ ≤ _ := by
      change C*(Real.log X)^14*(((Real.log X)^(A+15))⁻¹+((Real.log X)^(A+15))⁻¹) ≤ _
      rw [pow_add]
      field_simp
      linarith only [hLC]

end GoldbachCentralSeven.Density

end


-- TH8000PolynomialFormula
section

/-!
Adapted from the finite-difference explicit formula V86.V10t, smoothing
estimate V86.Vja, and logarithm bound Vbt.V1mq from the project's
DyadicCellShortPrimeFloor module, revision ef8ddfa37003c69f326f69188c774106953d3969.
The upstream source and its attribution notices remain accessible in that
module. One estimate retains the original tail. A second uses its bound
before the relaxation by the square of the conductor cutoff.
-/
open Complex Finset MeasureTheory
open scoped Interval BigOperators Classical
namespace TH8000PolynomialFormula
open OAI.Ostmann V82 V6i V1e Vx Vex Vbt V7e V86

theorem log_factor (X q Q u : ℝ)
    (hX : 4≤X) (hq : 1≤q) (hqQ : q≤Q) (hQX : Q≤X)
    (_hu : 1≤u) (huX : u≤3*X) :
    Real.sqrt u*(1+Real.log q)≤52*Real.sqrt X*Real.log X := by
  have hXp : 0<X := by linarith
  have hqp : 0<q := by linarith
  have hLp : 0<Real.log X := Real.log_pos (by linarith)
  have hL : 1≤Real.log X := by
    apply (Real.le_log_iff_exp_le hXp).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hqlog : Real.log q ≤ Real.log X := Real.log_le_log hqp (hqQ.trans hQX)
  have hfactor : 1 + Real.log q ≤ 26 * Real.log X := by linarith
  have hfactor0 : 0≤1+Real.log q := by linarith [Real.log_nonneg hq]
  have hsqrt : Real.sqrt u≤2*Real.sqrt X := by
    calc
      _ ≤ Real.sqrt (4*X) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hm := mul_le_mul hsqrt hfactor hfactor0 (by positivity)
  exact hm.trans_eq (by ring)

theorem smoothing_remainder (f : ℝ → ℂ) (E q Q X y h δ : ℝ)
    (hE : 0≤E) (hq : 1≤q) (hqQ : q≤Q) (hQX : Q≤X)
    (hX : 4≤X) (hy : y∈Set.Icc X (2*X)) (hh : 0≤h) (hhX : h≤X)
    (hδ : 0<δ) (hδX : δ≤X/2)
    (hf : ∀ u:ℝ,1≤u → ‖f u‖≤E*Real.sqrt u*(1+Real.log q)) :
    ‖V1c f y h δ‖≤208*E*(Real.sqrt X*Real.log X/δ) := by
  have hb (u : ℝ) (hu : X/2≤u) (huX : u≤3*X) :
      ‖f u‖≤52*E*Real.sqrt X*Real.log X := by
    have hu1 : 1≤u := by linarith
    calc
      _ ≤ E*Real.sqrt u*(1+Real.log q) := hf u hu1
      _ = E*(Real.sqrt u*(1+Real.log q)) := by ring
      _ ≤ E*(52*Real.sqrt X*Real.log X) := mul_le_mul_of_nonneg_left
        (log_factor X q Q u hX hq hqQ hQX hu1 huX) hE
      _ = _ := by ring
  have he := Vun f y h δ (52*E*Real.sqrt X*Real.log X) hδ
    (hb (y+h) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y+h-δ) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb y (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y-δ) (by linarith [hy.1]) (by linarith [hy.2]))
  exact he.trans_eq (by ring)

theorem polynomial_explicit_formula :
    ∃ D:ℝ,0<D ∧ ∀ Q:ℕ,1≤Q → ∀ (X y δ U:ℝ) (h:ℕ),
      4≤X → y∈Set.Icc X (2*X) → (h:ℝ)≤X → 1≤δ → δ≤X/2 → 2≤U →
      (Q:ℝ)≤X →
      ∀ χ:PrimitiveComplexCharacter,χ.modulus≤Q →
      ‖V4q χ h y+
        V3q (fun u=>∑ i∈(V1 χ).V14 U,
          Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
        D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
          (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
  obtain ⟨E,hE,hbound⟩ := Vt5
  have hT := Vj5
  refine ⟨20+208*E+V38,by positivity,?_⟩
  intro Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ hχ
  have hX2 : 2≤X := by linarith
  have hδp : 0<δ := by linarith
  have hyδ : δ<y := by linarith [hy.1]
  have hh : (0:ℝ)≤h := Nat.cast_nonneg h
  have hq : 1≤(χ.modulus:ℝ) := by exact_mod_cast χ.positive
  have hqQ : (χ.modulus:ℝ)≤Q := by exact_mod_cast hχ
  have hQr : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have hlogX : 0≤Real.log X := Real.log_nonneg (by linarith)
  have hlogU : 0≤Real.log ((Q:ℝ)*U) := Real.log_nonneg (by nlinarith)
  obtain ⟨c,hc⟩ := hbound χ
  have huns := V1co χ h X y δ hX2 hy hhX hδ hδX
  have hrem := smoothing_remainder (V7p χ c)
    E χ.modulus Q X y h δ hE.le hq hqQ hQX hX hy hh hhX hδp hδX hc
  have hori := V1wr χ X y h δ hX2 hy hh hhX hδ hδX
  have htail := V1t6 Q hQ χ hχ X y h δ U hX2 hy hh hhX hδp hδX hU
  have hid := V172 χ c y h δ U hδp hyδ hh
  have hn := V1gu (V4q χ h y) _ _ _ _ _ hid
  have hs : ‖V4q χ h y+
      V3q (fun u=>∑ i∈(V1 χ).V14 U,
        Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
      18*(δ*Real.log X)+(208*E)*(Real.sqrt X*Real.log X/δ)+
        V38*((Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
    linarith
  exact hs.trans (Vwl E (δ*Real.log X) (Real.sqrt X*Real.log X/δ)
    ((Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) hE (by positivity) (by positivity) (by positivity))

theorem sharper_tail (Q : ℕ) (hQ : 1≤Q) (χ : PrimitiveComplexCharacter)
    (hχ : χ.modulus≤Q) (X y h δ U : ℝ)
    (hX : 2≤X) (hy : y∈Set.Icc X (2*X)) (hh : 0≤h) (hhX : h≤X)
    (hδ : 0<δ) (hδX : δ≤X/2) (hU : 2≤U) :
    ‖V1c (fun u=>V56 χ u U) y h δ‖≤
      V38*(X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
  have hQr : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have hlog : 0<Real.log (14/13) := Real.log_pos (by norm_num)
  have hL : 0≤Real.log ((Q:ℝ)*U) := Real.log_nonneg (by nlinarith)
  have hC : 2*(36864/Real.log (14/13))≤V38 := by
    unfold V38
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by norm_num) hlog.le
  calc
    _ ≤ (36864/Real.log (14/13))*X^2*Real.log ((Q:ℝ)*(U+2))/(δ*U) :=
      Vny Q hQ X y h δ U hX hy.1 hy.2 hh hhX hδ hδX hU χ hχ
    _ ≤ (2*(36864/Real.log (14/13)))*(X^2*Real.log ((Q:ℝ)*U)/(δ*U)) :=
      by
        have hcoef : 0 ≤ (36864/Real.log (14/13))*X^2/(δ*U) := by positivity
        have hmono := mul_le_mul_of_nonneg_left (V14r (Q:ℝ) U hQr hU) hcoef
        convert hmono using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

theorem polynomial_formula_sharp_tail :
    ∃ D:ℝ,0<D ∧ ∀ Q:ℕ,1≤Q → ∀ (X y δ U:ℝ) (h:ℕ),
      4≤X → y∈Set.Icc X (2*X) → (h:ℝ)≤X → 1≤δ → δ≤X/2 → 2≤U →
      (Q:ℝ)≤X →
      ∀ χ:PrimitiveComplexCharacter,χ.modulus≤Q →
      ‖V4q χ h y+
        V3q (fun u=>∑ i∈(V1 χ).V14 U,
          Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
        D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
          X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
  obtain ⟨E,hE,hbound⟩ := Vt5
  have hT := Vj5
  refine ⟨20+208*E+V38,by positivity,?_⟩
  intro Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ hχ
  have hX2 : 2≤X := by linarith
  have hδp : 0<δ := by linarith
  have hyδ : δ<y := by linarith [hy.1]
  have hh : (0:ℝ)≤h := Nat.cast_nonneg h
  have hq : 1≤(χ.modulus:ℝ) := by exact_mod_cast χ.positive
  have hqQ : (χ.modulus:ℝ)≤Q := by exact_mod_cast hχ
  have hQr : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have hlogX : 0≤Real.log X := Real.log_nonneg (by linarith)
  have hlogU : 0≤Real.log ((Q:ℝ)*U) := Real.log_nonneg (by nlinarith)
  obtain ⟨c,hc⟩ := hbound χ
  have huns := V1co χ h X y δ hX2 hy hhX hδ hδX
  have hrem := smoothing_remainder (V7p χ c)
    E χ.modulus Q X y h δ hE.le hq hqQ hQX hX hy hh hhX hδp hδX hc
  have hori := V1wr χ X y h δ hX2 hy hh hhX hδ hδX
  have htail := sharper_tail Q hQ χ hχ X y h δ U hX2 hy hh hhX hδp hδX hU
  have hid := V172 χ c y h δ U hδp hyδ hh
  have hn := V1gu (V4q χ h y) _ _ _ _ _ hid
  have hs : ‖V4q χ h y+
      V3q (fun u=>∑ i∈(V1 χ).V14 U,
        Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
      18*(δ*Real.log X)+(208*E)*(Real.sqrt X*Real.log X/δ)+
        V38*(X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
    linarith
  exact hs.trans (Vwl E (δ*Real.log X) (Real.sqrt X*Real.log X/δ)
    (X^2*Real.log ((Q:ℝ)*U)/(δ*U)) hE (by positivity) (by positivity) (by positivity))

end TH8000PolynomialFormula

end


-- TH8000KernelTransfer
section

namespace GoldbachCentralSeven.Kernel
open Complex Finset MeasureTheory OAI.Ostmann V1e V6i
open scoped BigOperators Interval

theorem increment_height {X u H T : ℝ} {ρ : ℂ} (hX : 2 ≤ X)
    (hu : X/2 ≤ u) (hu' : u ≤ 2*X) (hH : 0 ≤ H) (hH' : H ≤ X)
    (hT : 0 < T) (hγ : T/2 ≤ |ρ.im|) (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖Ve u H ρ‖ ≤ 12 * X^ρ.re/T := by
  have hx : 0 < X := by linarith
  have hup : 0 < u := by linarith
  have hnorm : T/2 ≤ ‖ρ‖ := hγ.trans (Complex.abs_im_le_norm _)
  have hr : 0 < ‖ρ‖ := by linarith
  have hP (v : ℝ) (hv : 0 < v) (h3 : v ≤ 3*X) : ‖(v:ℂ)^ρ‖ ≤ 3*X^ρ.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    apply (Real.rpow_le_rpow hv.le h3 hβ).trans
    rw [Real.mul_rpow (by norm_num) hx.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 3) hβ'
  rw [Ve, norm_div]
  calc
    _ ≤ (6*X^ρ.re)/‖ρ‖ := by
      apply div_le_div_of_nonneg_right _ hr.le
      have h1 := hP (u+H) (by linarith) (by linarith)
      have h2 := hP u hup (by linarith)
      exact (norm_sub_le _ _).trans (by linarith only [h1,h2])
    _ ≤ (6*X^ρ.re)/(T/2) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hnorm
    _ = _ := by ring

theorem increment_min {X u H T : ℝ} {ρ : ℂ} (hX : 2 ≤ X)
    (hu : X/2 ≤ u) (hu' : u ≤ 2*X) (hH : 0 ≤ H) (hH' : H ≤ X)
    (hHscale : X^(2/3:ℝ) ≤ 2*H) (hT : 2 ≤ T)
    (hγ : T=2 ∨ T/2 ≤ |ρ.im|) (hβ : 0 < ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖Ve u H ρ‖ ≤ 24*H*(min 1 (X^(1/3:ℝ)/T)*X^(ρ.re-1)) := by
  have hx : 0 < X := by linarith
  have ht : 0 < T := by linarith
  have hw := Real.rpow_nonneg hx.le (ρ.re-1)
  have hlow := GoldbachOC103.fixed_increment_weight_bound X u H ρ hX hu hH hβ hβ'
  by_cases h : 1 ≤ X^(1/3:ℝ)/T
  · rw [min_eq_left h, one_mul]
    exact hlow.trans (by nlinarith only [mul_nonneg hH hw])
  rw [min_eq_right (le_of_not_ge h)]
  rcases hγ with rfl|hγ
  · have hg := Real.one_le_rpow (show 1 ≤ X by linarith) (by norm_num : 0 ≤ (1/3:ℝ))
    have hsmall : (1/2:ℝ)*(H*X^(ρ.re-1)) ≤ (X^(1/3:ℝ)/2)*(H*X^(ρ.re-1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hH hw)
    exact hlow.trans (by nlinarith only [hsmall, mul_nonneg hH hw])
  · have hi := increment_height hX hu hu' hH hH' ht hγ hβ.le hβ'
    apply hi.trans
    have hid : X^ρ.re = X^(2/3:ℝ)*X^(1/3:ℝ)*X^(ρ.re-1) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]; congr 1; ring
    rw [hid]
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHscale
      (Real.rpow_nonneg hx.le (1/3:ℝ))) hw
    apply (div_le_iff₀ ht).mpr
    calc
      _ ≤ 12*(2*H*X^(1/3:ℝ)*X^(ρ.re-1)) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by field_simp
                  ring

theorem smoothed_min {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) {X y H T δ : ℝ}
    (hX : 2 ≤ X) (hy : y ∈ Set.Icc X (2*X)) (hH : 0 ≤ H) (hH' : H ≤ X)
    (hscale : X^(2/3:ℝ) ≤ 2*H) (hT : 2 ≤ T) (hδ : 0 < δ) (hδX : δ ≤ X/2)
    (hγ : ∀ i ∈ S, T=2 ∨ T/2 ≤ |(ρ i).im|)
    (hβ : ∀ i ∈ S, 0 < (ρ i).re) (hβ' : ∀ i ∈ S, (ρ i).re ≤ 1) :
    ‖V3q (fun u => ∑ i ∈ S, Ve u H (ρ i)) δ y‖ ≤
      24*H*∑ i ∈ S, min 1 (X^(1/3:ℝ)/T)*X^((ρ i).re-1) := by
  let B := 24*H*∑ i ∈ S, min 1 (X^(1/3:ℝ)/T)*X^((ρ i).re-1)
  have hbd : ∀ u ∈ Set.uIoc (y-δ) y, ‖∑ i ∈ S, Ve u H (ρ i)‖ ≤ B := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : y-δ ≤ y)] at hu
    apply (norm_sum_le _ _).trans
    dsimp only [B];rw [mul_sum]
    exact sum_le_sum fun i hi => increment_min hX (by linarith [hu.1,hy.1])
      (hu.2.trans hy.2) hH hH' hscale hT (hγ i hi) (hβ i hi) (hβ' i hi)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have hi' : ‖∫ u in y-δ..y, ∑ i ∈ S, Ve u H (ρ i)‖ ≤ B*δ := by
    simpa only [sub_sub_cancel, abs_of_nonneg hδ.le, mul_comm] using hi
  rw [V3q,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hδ.le]
  exact (mul_le_mul_of_nonneg_left hi' (by positivity)).trans_eq (by dsimp [B];field_simp)

theorem conductor_weighted_smoothed (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X y H T δ : ℝ}
    (hX : 2 ≤ X) (hy : y ∈ Set.Icc X (2*X)) (hH : 0 ≤ H) (hH' : H ≤ X)
    (hscale : X^(2/3:ℝ) ≤ 2*H) (hT : 2 ≤ T) (hδ : 0 < δ) (hδX : δ ≤ X/2)
    (hγ : ∀ χ ∈ F, ∀ i ∈ S χ, T=2 ∨ T/2 ≤ |((V1 χ).zeros i).im|) :
    (∑ χ ∈ F, ‖V3q (fun u => ∑ i ∈ S χ, Ve u H ((V1 χ).zeros i)) δ y‖/(χ.modulus:ℝ)) ≤
      24*H*∑ χ ∈ F, ∑ i ∈ S χ, min 1 (X^(1/3:ℝ)/T)*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ) := by
  rw [mul_sum]
  refine sum_le_sum fun χ hχ => ?_
  have h := smoothed_min (S χ) (V1 χ).zeros hX hy hH hH' hscale hT hδ hδX
    (hγ χ hχ) (fun i _ => ((V1 χ).in_strip i).1) (fun i _ => ((V1 χ).in_strip i).2.le)
  rw [←sum_div, ←mul_div_assoc]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

theorem left_zero_sum (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {Q : ℕ} {X T : ℝ} (hQ : 1 ≤ Q)
    (hX : 1 ≤ X) (hT : 2 ≤ T) (hF : ∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus)
    (hS : ∀ χ ∈ F, S χ ⊆ (V1 χ).V14 T)
    (hβ : ∀ χ ∈ F, ∀ i ∈ S χ, ((V1 χ).zeros i).re ≤ 1/2) :
    (∑ χ ∈ F, ∑ i ∈ S χ, min 1 (X^(1/3:ℝ)/T)*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
      (256/Real.log (14/13))*(Q:ℝ)*X^(-(1/6:ℝ))*Real.log ((Q:ℝ)*T) := by
  have hQr : 1 ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQp : 0 < (Q:ℝ) := by linarith
  have hx := zero_lt_one.trans_le hX
  have ht : 0 < T := by linarith
  let A : ℝ := 2*X^(-(1/6:ℝ))/((Q:ℝ)*T)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 14/13)
  have hcount := V9h.Vt1 Q hQ T ht.le F (fun χ hχ => (hF χ hχ).1) S hS
  have hheight := V9h.V117 Q hQ T hT
  have hcount' :
      (∑ χ ∈ F, ((S χ).card:ℝ)) ≤ (32/Real.log (14/13))*(Q:ℝ)^2*(4*T*Real.log ((Q:ℝ)*T)) :=
    hcount.trans (by
      rw [mul_assoc ((32:ℝ)/Real.log (14/13)*(Q:ℝ)^2)]
      exact mul_le_mul_of_nonneg_left hheight (by positivity))
  have hwt (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (i : ℕ) (hi : i ∈ S χ) :
      min 1 (X^(1/3:ℝ)/T)*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ) ≤ A := by
    have hd : (Q:ℝ) ≤ 2*(χ.modulus:ℝ) := by exact_mod_cast (hF χ hχ).2
    have hdpos : 0 < (χ.modulus:ℝ) := by exact_mod_cast χ.positive
    have hb := Real.rpow_le_rpow_of_exponent_le hX
      (show ((V1 χ).zeros i).re-1 ≤ -(1/2:ℝ) by linarith [hβ χ hχ i hi])
    calc
      _ ≤ ((X^(1/3:ℝ)/T)*X^(-(1/2:ℝ)))/(χ.modulus:ℝ) := by
        apply div_le_div_of_nonneg_right _ hdpos.le
        exact mul_le_mul (min_le_right _ _) hb (by positivity) (by positivity)
      _ = X^(-(1/6:ℝ))/(T*(χ.modulus:ℝ)) := by
        rw [show -(1/6:ℝ) = 1/3+ -(1/2) by norm_num, Real.rpow_add hx]; ring
      _ ≤ A := by
        dsimp [A];apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hd ht.le) (Real.rpow_nonneg hx.le (-(1/6:ℝ)))]
  calc
    _ ≤ ∑ χ ∈ F, ∑ _i ∈ S χ, A := sum_le_sum fun χ hχ => sum_le_sum (hwt χ hχ)
    _ = (∑ χ ∈ F, ((S χ).card:ℝ))*A := by simp [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount' hA
    _ = _ := by dsimp [A];field_simp;ring

theorem left_zero_sum_at_level (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {Q : ℕ} {X T : ℝ} (hQ : 1 ≤ Q)
    (hX : 1 ≤ X) (hT : 2 ≤ T) (hT' : T ≤ X^2) (hlevel : (Q:ℝ) ≤ X^(5/32:ℝ))
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus)
    (hS : ∀ χ ∈ F, S χ ⊆ (V1 χ).V14 T)
    (hβ : ∀ χ ∈ F, ∀ i ∈ S χ, ((V1 χ).zeros i).re ≤ 1/2) :
    (∑ χ ∈ F, ∑ i ∈ S χ, min 1 (X^(1/3:ℝ)/T)*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
      (768/Real.log (14/13))*X^(-(1/96:ℝ))*Real.log X := by
  have hqp : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hx := zero_lt_one.trans_le hX
  have ht : 0 < T := by linarith
  have hQX : (Q:ℝ) ≤ X := hlevel.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (show (5/32:ℝ) ≤ 1 by norm_num))
  have hlog : Real.log ((Q:ℝ)*T) ≤ 3*Real.log X := by
    have h' : (Q:ℝ)*T ≤ X^3 := by calc
      _ ≤ X*X^2 := mul_le_mul hQX hT' ht.le hx.le
      _ = _ := by ring
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) h'
  have hlogpos : 0 ≤ Real.log ((Q:ℝ)*T) := by
    have hQr : 1 ≤ (Q:ℝ) := by exact_mod_cast hQ
    exact Real.log_nonneg (by nlinarith)
  have hc := Real.log_pos (by norm_num : (1:ℝ) < 14/13)
  apply (left_zero_sum F S hQ hX hT hF hS hβ).trans
  calc
    _ ≤ (256/Real.log (14/13))*X^(5/32:ℝ)*X^(-(1/6:ℝ))*(3*Real.log X) := by
      gcongr
    _ = _ := by
      have hpow : X^(5/32:ℝ)*X^(-(1/6:ℝ))=X^(-(1/96:ℝ)) := by rw [←Real.rpow_add hx];norm_num
      rw [← hpow];ring

end GoldbachCentralSeven.Kernel

namespace GoldbachCentralSeven.Kernel
open Complex Finset MeasureTheory OAI.Ostmann V1e V6i V7e
open scoped BigOperators Interval

theorem actual_short_character_error :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ (X y δ U : ℝ) (h : ℕ),
      4 ≤ X → y ∈ Set.Icc X (2*X) → (h:ℝ) ≤ X → X^(2/3:ℝ) ≤ 2*h →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ (F : Finset PrimitiveComplexCharacter) (height : PrimitiveComplexCharacter → ℕ → ℝ),
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∀ χ ∈ F, ∀ i ∈ (V1 χ).V14 U, 2 ≤ height χ i ∧
        (height χ i = 2 ∨ height χ i / 2 ≤ |((V1 χ).zeros i).im|)) →
      (∑ χ ∈ F, ‖V4q χ h y‖/(χ.modulus:ℝ)) ≤
        D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
           X^2*Real.log ((Q:ℝ)*U)/(δ*U))*(∑ χ ∈ F, 1/(χ.modulus:ℝ)) +
        24*(h:ℝ)*∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 U,
          min 1 (X^(1/3:ℝ)/height χ i)*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ) := by
  obtain ⟨D,hD,hformula⟩ := TH8000PolynomialFormula.polynomial_formula_sharp_tail
  refine ⟨D,hD,?_⟩
  intro Q hQ X y δ U h hX hy hh hscale hδ hδX hU hQX F height hF hheight
  let A := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+X^2*Real.log ((Q:ℝ)*U)/(δ*U))
  let z := fun (χ : PrimitiveComplexCharacter) i => (V1 χ).zeros i
  let w := fun χ i => min 1 (X^(1/3:ℝ)/height χ i)*X^((z χ i).re-1)
  have hδp : 0 < δ := by linarith
  have hsm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      ‖V3q (fun u => ∑ i ∈ (V1 χ).V14 U, Ve u h (z χ i)) δ y‖ ≤
        24*(h:ℝ)*(∑ i ∈ (V1 χ).V14 U, w χ i) := by
    let B := 24*(h:ℝ)*(∑ i ∈ (V1 χ).V14 U, w χ i)
    have hbd : ∀ u ∈ Set.uIoc (y-δ) y, ‖∑ i ∈ (V1 χ).V14 U, Ve u h (z χ i)‖ ≤ B := by
      intro u hu
      rw [Set.uIoc_of_le (by linarith : y-δ ≤ y)] at hu
      apply (norm_sum_le _ _).trans
      dsimp only [B];rw [mul_sum]
      apply sum_le_sum
      intro i hi
      exact increment_min (by linarith) (by linarith [hu.1,hy.1]) (hu.2.trans hy.2)
        (Nat.cast_nonneg h) hh hscale (hheight χ hχ i hi).1 (hheight χ hχ i hi).2
        ((V1 χ).in_strip i).1 ((V1 χ).in_strip i).2.le
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hi' : ‖∫ u in y-δ..y, ∑ i ∈ (V1 χ).V14 U, Ve u h (z χ i)‖ ≤ B*δ := by
      simpa only [sub_sub_cancel, abs_of_nonneg hδp.le, mul_comm] using hi
    rw [V3q,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hδp.le]
    exact (mul_le_mul_of_nonneg_left hi' (by positivity)).trans_eq (by dsimp [B];field_simp)
  change _ ≤ A*(∑ χ ∈ F, 1/(χ.modulus:ℝ)) + 24*(h:ℝ)*(∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 U, w χ i/(χ.modulus:ℝ))
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro χ hχ
  have he := hformula Q hQ X y δ U h hX hy hh hδ hδX hU hQX χ (hF χ hχ)
  have hb := hsm χ hχ
  let S := V3q (fun u => ∑ i ∈ (V1 χ).V14 U, Ve u h (z χ i)) δ y
  change ‖V4q χ h y + S‖ ≤ A at he
  change ‖S‖ ≤ _ at hb
  have hsum : ‖V4q χ h y‖ ≤ A + 24*(h:ℝ)*(∑ i ∈ (V1 χ).V14 U, w χ i) := by
    have ht := norm_sub_le (V4q χ h y + S) S
    rw [add_sub_cancel_right] at ht
    exact ht.trans (add_le_add he hb)
  have ht := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg χ.modulus)
  rw [← sum_div]
  exact ht.trans_eq (by ring)

end GoldbachCentralSeven.Kernel

end


-- TH8000HeightBudget
section

namespace GoldbachCentralSeven.Kernel
open OAI.Ostmann V7e Filter Finset
open scoped Classical
noncomputable section

def index (v : ℝ) : ℕ := Nat.log 2 (max 1 ⌊v⌋₊)
def top (j : ℕ) : ℝ := 2^(j+1)
def damp (X T : ℝ) := min 1 (X^(1/3:ℝ)/T)

def HeightBudgetAt (X : ℝ) (B : ℕ) (F : Finset PrimitiveComplexCharacter) : Prop :=
  ∀ T : ℝ, 2 ≤ T → T ≤ X^2 →
    (∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 T, damp X T*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
      ((Real.log X)^B)⁻¹

private theorem top_ge (j : ℕ) : 2 ≤ top j := by
  rw [top,pow_succ]
  linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j)]

theorem height_assignment {U v : ℝ} (_hU : 2 ≤ U) (hv : 0 ≤ v) (hvU : v ≤ U) :
    index v ∈ range (index U+1) ∧ v ≤ top (index v) ∧
      (top (index v)=2 ∨ top (index v)/2 ≤ v) := by
  let n := max 1 ⌊v⌋₊
  have hn : 0 < n := by dsimp [n];omega
  have hm : n ≤ max 1 ⌊U⌋₊ := max_le_max_left 1 (Nat.floor_mono hvU)
  have hJ := Nat.log_mono_right (b:=2) hm
  refine ⟨mem_range.mpr (Nat.lt_succ_of_le hJ), ?_, ?_⟩
  · have hn' := Nat.lt_pow_succ_log_self (by decide : 1<2) n
    have hv' := Nat.lt_floor_add_one v
    have hc : (⌊v⌋₊:ℝ)+1 ≤ ((2:ℕ)^(Nat.log 2 n+1):ℕ) := by exact_mod_cast
      (show ⌊v⌋₊+1 ≤ (2:ℕ)^(Nat.log 2 n+1) by dsimp [n] at *;omega)
    exact hv'.le.trans (by simpa [top,index,n] using hc)
  · by_cases hj : index v=0
    · left;simp [hj,top]
    · right
      have hn1 : 1 < n := by
        by_contra! h
        have he : n=1 := by omega
        apply hj
        change Nat.log 2 n=0;rw [he];decide
      have hfloor : n=⌊v⌋₊ := by dsimp [n] at *;omega
      have hp : (2:ℝ)^(index v) ≤ (⌊v⌋₊:ℝ) := by
        exact_mod_cast (show (2:ℕ)^(index v) ≤ ⌊v⌋₊ by
          exact (Nat.pow_log_le_self 2 hn.ne').trans_eq hfloor)
      rw [top,pow_succ]
      have hle := hp.trans (Nat.floor_le hv)
      linarith

private theorem grid_max {X U : ℝ} (hU : 2 ≤ U) (hX : 2*U ≤ X^2) :
    ∀ j ∈ range (index U+1), top j ≤ X^2 := by
  intro j hj
  have hJ : j ≤ index U := by have := mem_range.mp hj; omega
  have hfloor : 1 ≤ ⌊U⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by norm_num;linarith)
  have hh : (2:ℕ)^(index U) ≤ ⌊U⌋₊ := by
    simpa [index,max_eq_right hfloor] using Nat.pow_log_le_self 2 (by omega : ⌊U⌋₊ ≠ 0)
  have hp : (2:ℝ)^j ≤ (⌊U⌋₊:ℝ) := by exact_mod_cast
    ((Nat.pow_le_pow_right (by decide : 0<2) hJ).trans hh)
  rw [top,pow_succ]
  linarith [hp.trans (Nat.floor_le (by linarith : 0 ≤ U))]

private theorem grid_card {X U : ℝ} (_hX : 1 < X) (hL : 1 ≤ Real.log X)
    (hU : 2 ≤ U) (hUX : 2*U ≤ X^2) : ((index U+1:ℕ):ℝ) ≤ 5*Real.log X := by
  have htop := grid_max hU hUX (index U) (by simp)
  have hl := Real.log_le_log (by positivity : 0 < (2:ℝ)^(index U+1)) htop
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num at hl
  have h2 := Real.log_two_gt_d9
  have hmul := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ Real.log 2 by linarith) (Nat.cast_nonneg (index U+1))
  push_cast at *
  linarith

theorem height_sum {X U : ℝ} (hx : 1 < X) (hl : 1 ≤ Real.log X) (hU : 2 ≤ U)
    (hUX : 2*U ≤ X^2) (F : Finset PrimitiveComplexCharacter) (B : ℕ) (hbudget : HeightBudgetAt X B F) :
    (∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 U, damp X (top (index |((V1 χ).zeros i).im|)) *
        X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)) ≤
          (5*Real.log X)*((Real.log X)^B)⁻¹ := by
  let G := range (index U+1)
  let c := fun (χ : PrimitiveComplexCharacter) i => index |((V1 χ).zeros i).im|
  let w := fun (χ : PrimitiveComplexCharacter) i j =>
    damp X (top j)*X^(((V1 χ).zeros i).re-1)/(χ.modulus:ℝ)
  have wpos (χ : PrimitiveComplexCharacter) (i j : ℕ) : 0 ≤ w χ i j := by
    have hd : 0 ≤ damp X (top j) := le_min zero_le_one (by dsimp [top];positivity)
    dsimp [w];positivity
  have hw (χ : PrimitiveComplexCharacter) :
      (∑ i ∈ (V1 χ).V14 U, w χ i (c χ i)) ≤ ∑ j ∈ G, ∑ i ∈ (V1 χ).V14 (top j), w χ i j := by
    calc
      _ = ∑ j ∈ G, ∑ i ∈ ((V1 χ).V14 U).filter (fun i => c χ i=j), w χ i (c χ i) :=
        (sum_fiberwise_of_maps_to (fun i hi => (height_assignment hU (abs_nonneg _)
          (((V1 χ).V2r U i).mp hi)).1) _).symm
      _ ≤ _ := by
        refine sum_le_sum fun j hj => ?_
        calc
          _ = ∑ i ∈ ((V1 χ).V14 U).filter (fun i => c χ i=j), w χ i j :=
            sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
          _ ≤ _ := by
            apply sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => wpos χ i j)
            intro i hi
            obtain ⟨hi, h⟩ := mem_filter.mp hi
            rw [←h]
            exact ((V1 χ).V2r _ i).mpr ((height_assignment hU (abs_nonneg _) (((V1 χ).V2r U i).mp hi)).2.1)
  calc
    _ ≤ ∑ χ ∈ F, ∑ j ∈ G, ∑ i ∈ (V1 χ).V14 (top j), w χ i j :=
      sum_le_sum (fun χ _ => hw χ)
    _ = ∑ j ∈ G, ∑ χ ∈ F, ∑ i ∈ (V1 χ).V14 (top j), w χ i j := sum_comm
    _ ≤ ∑ _j ∈ G, ((Real.log X)^B)⁻¹ := sum_le_sum (fun j hj => hbudget (top j) (top_ge _) (grid_max hU hUX j hj))
    _ = ((index U+1:ℕ):ℝ)*((Real.log X)^B)⁻¹ := by simp [G]
    _ ≤ _ := mul_le_mul_of_nonneg_right (grid_card hx hl hU hUX) (by positivity)

private theorem sum_inv_conductor (F : Finset PrimitiveComplexCharacter) {Q : ℕ} (hQ : 1 ≤ Q)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) :
    (∑ χ ∈ F, 1/(χ.modulus:ℝ)) ≤ 2*(Q:ℝ) := by
  have hc : (F.card:ℝ) ≤ (Q:ℝ)^2 := by exact_mod_cast V14i F Q (fun χ hχ => (hF χ hχ).1)
  have hqp : (0:ℝ)<Q := by exact_mod_cast hQ
  calc
    _ ≤ ∑ _χ ∈ F, 2/(Q:ℝ) := by
      apply sum_le_sum;intro χ hχ
      apply (div_le_div_iff₀ (by exact_mod_cast χ.positive) hqp).mpr
      simpa only [one_mul] using (show (Q:ℝ) ≤ 2*(χ.modulus:ℝ) by exact_mod_cast (hF χ hχ).2)
    _ ≤ (Q:ℝ)^2*(2/(Q:ℝ)) := by simp only [sum_const,nsmul_eq_mul];gcongr
    _ = _ := by field_simp

theorem character_sum_of_height_budget (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (Q : ℕ) (F : Finset PrimitiveComplexCharacter) (h : ℕ) (y : ℝ),
      1 ≤ Q → (Q:ℝ) ≤ X^(5/32:ℝ) → (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      y ∈ Set.Icc X (2*X) → (h:ℝ) ≤ X → X^(2/3:ℝ) ≤ 2*h →
      HeightBudgetAt X (A+2) F → (∑ χ ∈ F, ‖V4q χ h y‖/(χ.modulus:ℝ)) ≤ h/(Real.log X)^A := by
  obtain ⟨D,hD,he⟩ := actual_short_character_error
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((A+1:ℕ):ℝ)
    (show 0 < (1/6:ℝ) by norm_num)).bound (show 0 < 1/(112*D) by positivity)
  filter_upwards [hsmall,Real.tendsto_log_atTop.eventually_ge_atTop 240,
    eventually_ge_atTop (8:ℝ)] with X hsm hL hX
  intro Q F h y hQ hcut hF hy hh hscale hbudget
  have hx : 1 < X := by linarith
  have hxp := zero_lt_one.trans hx
  let ℓ := Real.log X
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ];linarith
  have hℓp : 0 < ℓ := by linarith
  let s := X^(1/3:ℝ)
  let U := X^2/4
  have hs : 1 ≤ s := Real.one_le_rpow hx.le (by norm_num)
  have hsp : 0 < s := by linarith
  have hU : 2 ≤ U := by dsimp [U];nlinarith
  have hUX : 2*U ≤ X^2 := by dsimp [U];nlinarith
  have hqpos : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hq1 : 1 ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hqX : (Q:ℝ) ≤ X := hcut.trans (by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hx.le
      (show (5/32:ℝ) ≤ 1 by norm_num)))
  have hsHalf : s ≤ X/2 := by
    have hpow : X^(2/3:ℝ) ≥ 2 := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤8) hX (by norm_num : 0≤(2/3:ℝ))
      have h8 : (8:ℝ)^(2/3:ℝ) = 4 := by
        rw [show (8:ℝ)=2^3 by norm_num, ← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
        norm_num
      linarith
    have hxsum : s*X^(2/3:ℝ)=X := by dsimp [s];rw [← Real.rpow_add hxp];norm_num
    linarith [mul_le_mul_of_nonneg_left hpow hsp.le]
  have hmod : s*(Q:ℝ) ≤ X^(1/2:ℝ) := by
    calc
      _ ≤ s*X^(5/32:ℝ) := mul_le_mul_of_nonneg_left hcut hsp.le
      _ = X^(1/3+5/32:ℝ) := (Real.rpow_add hxp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hδ : Real.sqrt X/s ≤ s := by
    dsimp [s];rw [Real.sqrt_eq_rpow,←Real.rpow_sub hxp]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hlog : Real.log ((Q:ℝ)*U) ≤ 3*ℓ := by
    have h' : (Q:ℝ)*U ≤ X^3 := by
      calc
        _ ≤ X*X^2 := mul_le_mul hqX (by linarith) (by linarith) hxp.le
        _ = _ := by ring
    simpa only [ℓ,Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (mul_pos hqpos (by linarith)) h'
  have htail : X^2*Real.log ((Q:ℝ)*U)/(s*U) ≤ 12*s*ℓ := by
    calc
      _ = 4*(Real.log ((Q:ℝ)*U)/s) := by dsimp [U];field_simp
      _ ≤ 4*((3*ℓ)/s) := by gcongr
      _ ≤ 12*s*ℓ := by
        have h := div_le_self (by positivity : 0 ≤ 3*ℓ) hs
        nlinarith [mul_le_mul_of_nonneg_right hs hℓp.le]
  have hrem : D*(s*ℓ+Real.sqrt X*ℓ/s+X^2*Real.log ((Q:ℝ)*U)/(s*U))*
        (∑ χ ∈ F, 1/(χ.modulus:ℝ)) ≤ 28*D*X^(1/2:ℝ)*ℓ := by
    have hmid := mul_le_mul_of_nonneg_right hδ hℓp.le
    have hrem0 : s*ℓ+Real.sqrt X*ℓ/s+X^2*Real.log ((Q:ℝ)*U)/(s*U) ≤ 14*s*ℓ := by
      rw [mul_div_right_comm];linarith
    calc
      _ ≤ (D*(14*s*ℓ))*(2*(Q:ℝ)) := mul_le_mul
        (mul_le_mul_of_nonneg_left hrem0 hD.le) (sum_inv_conductor F hQ hF)
        (sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = 28*D*ℓ*(s*Q) := by ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hmod (by positivity : 0 ≤ 28*D*ℓ)]
  have hLpow : 0 < ℓ^A := pow_pos hℓp A
  have hmain : 28*D*X^(1/2:ℝ)*ℓ ≤ (h:ℝ)/(2*ℓ^A) := by
    change ‖Real.log X ^ ((A+1:ℕ):ℝ)‖ ≤ 1/(112*D)*‖X^(1/6:ℝ)‖ at hsm
    rw [Real.rpow_natCast,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hℓp.le _),
      abs_of_pos (Real.rpow_pos_of_pos hxp _)] at hsm
    have hb : 112*D*ℓ^(A+1) ≤ X^(1/6:ℝ) := by
      have hbound := mul_le_mul_of_nonneg_left hsm (by positivity : 0 ≤ 112*D)
      convert hbound using 1
      field_simp
    have hprod := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hxp.le (1/2:ℝ))
    rw [←Real.rpow_add hxp, show (1/2:ℝ)+1/6=2/3 by norm_num, pow_succ] at hprod
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hprod,hscale]
  let height := fun (χ : PrimitiveComplexCharacter) i => top (index |((V1 χ).zeros i).im|)
  have hb := he Q hQ X y s U h (by linarith) hy hh hscale hs hsHalf hU hqX F height
    (fun χ hχ => (hF χ hχ).1) (by
      intro χ hχ i hi
      have hz := height_assignment hU (abs_nonneg _) (((V1 χ).V2r U i).mp hi)
      exact ⟨top_ge _,hz.2.2⟩)
  have hsums := height_sum hx hℓ hU hUX F (A+2) hbudget
  apply hb.trans
  change _ ≤ h/ℓ^A
  have hzero := mul_le_mul_of_nonneg_left hsums (by positivity : 0 ≤ 24*(h:ℝ))
  have hcheap : 24*(h:ℝ)*((5*ℓ)*(ℓ^(A+2))⁻¹) ≤ h/(2*ℓ^A) := by
    change 240 ≤ ℓ at hL
    rw [pow_add, ←div_eq_mul_inv, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hL
      (by positivity : 0 ≤ (h:ℝ)*ℓ^A*ℓ)]
  refine (add_le_add (hrem.trans hmain) (hzero.trans hcheap)).trans_eq ?_
  ring

end
end GoldbachCentralSeven.Kernel

end


-- TH8000LowConductors
section

open Complex Filter OAI.Ostmann
open scoped Topology Classical

namespace TH8000LowConductors
open OAI.LargePrimeGaps

theorem primitive_weak_gap {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ z : ℂ, z.re < 1 → χ.LFunction z = 0 →
        d / ((((q:ℝ)+2)*(|z.im|+2))^e)^2 ≤ 1-z.re := by
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower he he1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < e/2) (by linarith : e/2 ≤ 1/2)
  let K := K₀*(3:ℝ)^e
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (e/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hde : d ≤ e/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have hh := mul_le_mul_of_nonneg_left (show d ≤ c/(2*K) from min_le_right ..) hK.le
    have heq : K*(c/(2*K))=c/2 := by field_simp
    rwa [heq] at hh
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ z hβ hz
  let t := z.im
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  let P := X^e
  have hP : 1 ≤ P := Real.one_le_rpow hX he.le
  have hP0 : 0 < P := by linarith
  let s₀ := (1:ℂ)+I*(t:ℂ)
  have hbase : c/P ≤ ‖χ.LFunction s₀‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-e) ≤ _ at hh
    simpa only [P,s₀,Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hder : ∀ w ∈ Metric.closedBall s₀ (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*P := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (((1:ℝ):ℂ)+I*t) (d/P^2) := by simpa only [s₀,Complex.ofReal_one] using hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry (σ:=1) (by norm_num) (by norm_num) hP hd.le hd1 hde hw'
    have hh := hb q χ hχ w (by linarith)
    rw [show 2*(e/2)=e by ring] at hh
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ _ := hh
      _ ≤ K₀*(3*X)^e := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn he.le) hK₀.le
      _ = K*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp only [K,P]; ring
  have hr : 0 < d/P^2 := by positivity
  have hr1 := (div_le_self hd.le (one_le_pow₀ hP (n:=2))).trans hd1
  have hMr : (K*P)*(d/P^2) ≤ (c/P)/2 := by
    calc
      _ = (K*d)/P := by field_simp
      _ ≤ (c/2)/P := div_le_div_of_nonneg_right hKd hP0.le
      _ = _ := by ring
  have hne := (logRiesz_local hr hr1 (div_pos hc hP0) (mul_nonneg hK.le hP0.le)
    (show 1 ≤ s₀.re by simp [s₀]) (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w)
    hder hbase hMr).1
  by_contra! hsmall
  apply hne z _ hz
  rw [Metric.mem_closedBall,dist_eq_norm]
  have heq : z-s₀ = ((z.re-1 : ℝ):ℂ) := by
    apply Complex.ext <;> simp [s₀,t]
  rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-1 ≤0)]
  change 1-z.re < d/P^2 at hsmall
  linarith only [hsmall]

open V1l OAI.V2 OAI.Vg

private theorem high_height_window (A B : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ (Real.log X)^B → ∀ (χ : DirichletCharacter ℂ q) (z : ℂ),
      T ≤ |z.im| → |z.im| ≤ X^2 → z.re < 1 → χ.LFunction z = 0 →
        V2j A X ≤ 1-z.re := by
  obtain ⟨c,_,T,hc,_,hT,hstrip⟩ := V1bc
  let b := (B:ℝ)+2
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨P,hcut⟩ := Vjs.V1vq A (c/b) (div_pos hc hb)
  refine ⟨T,hT,?_⟩
  filter_upwards [eventually_ge_atTop P, eventually_ge_atTop (2:ℝ), Vgn A] with X hP hX hgn q _ hq χ z ht htX hβ hz
  let L := Real.log X
  let H := OAI.V2.V96 (2*z.im)
  have hL : 1 ≤ L := hgn.2.1
  have hL0 : 0 < L := by linarith
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  obtain ⟨hH,hHX⟩ := Vjs.V1w7 X z.im hX htX
  change 1 ≤ H at hH
  change H ≤ 4*L at hHX
  have hpad : L ≤ 2*(Real.log X)^24 := by
    have hh : L ≤ L^24 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ 24 by decide)
    dsimp only [L] at hh ⊢
    linarith
  have h := hcut X hP L H hL hpad hH hHX
  have hpos : 0 < 1+Real.log L+Real.log H := by linarith [Real.log_nonneg hL,Real.log_nonneg hH]
  have hden : 0 < 1+Real.log (q:ℝ)+Real.log H := by linarith [Real.log_nonneg hq1,Real.log_nonneg hH]
  have hlog : Real.log (q:ℝ) ≤ (B:ℝ)*Real.log L := by
    simpa only [Real.log_pow] using Real.log_le_log (zero_lt_one.trans_le hq1) hq
  have hcomp : 1+Real.log (q:ℝ)+Real.log H ≤ b*(1+Real.log L+Real.log H) := by
    dsimp only [b]
    nlinarith only [hlog,Nat.cast_nonneg (α:=ℝ) B,Real.log_nonneg hL,Real.log_nonneg hH,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) B) (Real.log_nonneg hH)]
  have hcut' : V2j A X ≤ c*OAI.Vg.V36 (2*z.im)/Vcw q (2*z.im) := by
    change V2j A X ≤ c*H^(-(2/3:ℝ))/(1+Real.log (q:ℝ)+Real.log H)
    apply (le_div_iff₀ hden).mpr
    have hmul := (le_div_iff₀ hpos).mp h
    calc
      _ ≤ V2j A X * (b*(1+Real.log L+Real.log H)) :=
        mul_le_mul_of_nonneg_left hcomp hgn.2.2.1
      _ = b*(V2j A X*(1+Real.log L+Real.log H)) := by ring
      _ ≤ b*(c/b*H^(-(2/3:ℝ))) := mul_le_mul_of_nonneg_left hmul hb.le
      _ = _ := by field_simp
  by_contra! hsmall
  have hup : z.re ≤ 1+OAI.Vg.V36 (2*z.im)/16 := by
    have hp : 0 ≤ OAI.Vg.V36 (2*z.im) := Real.rpow_nonneg (zero_le_one.trans hH) _
    linarith
  have hn := (hstrip q χ z.im z.re ht (by linarith) hup).1
  have he : (z.re : ℂ)+I*(z.im : ℂ)=z := by apply Complex.ext <;> simp
  rw [he] at hn
  exact hn hz

private theorem low_height_window (A B : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ (Real.log X)^B →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ z : ℂ, |z.im| ≤ T → z.re < 1 → χ.LFunction z = 0 → V2j A X ≤ 1-z.re := by
  let e : ℝ := 1/(4*((B:ℝ)+1))
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp [e]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) B]
  obtain ⟨d,hd,hzero⟩ := primitive_weak_gap he he1
  let F := 3*(T+2)
  have hF : 0 < F := by dsimp only [F]; linarith
  let C := 3*((A+14:ℕ):ℝ)*F^(2*e)
  have hlim : Tendsto (fun X : ℝ => C*(Real.log (Real.log X)/(Real.log X)^(1/2:ℝ))) atTop (𝓝 0) := by
    have ht := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero).comp Real.tendsto_log_atTop
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using ht.const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds hd), Vgn A] with X hsmall hgn q _ hq χ hχp hχ z ht hβ hz
  let L := Real.log X
  have hL : 1 ≤ L := hgn.2.1
  have hL0 := zero_lt_one.trans_le hL
  have hLP : 1 ≤ L^B := one_le_pow₀ hL
  let W := ((q:ℝ)+2)*(|z.im|+2)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hWup : W ≤ F*L^(B+1) := by
    have hq' : (q:ℝ)+2 ≤ 3*L^B := by change (q:ℝ) ≤ L^B at hq; linarith
    have hh := mul_le_mul hq' (show |z.im|+2 ≤ T+2 by linarith) (by positivity : 0 ≤ |z.im|+2)
      (by positivity : 0 ≤ 3*L^B)
    have hmono := pow_le_pow_right₀ hL (Nat.le_succ B)
    calc
      W ≤ (3*L^B)*(T+2) := hh
      _ = F*L^B := by dsimp only [F]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hF.le
  have hpow : (W^e)^2 ≤ F^(2*e)*L^(1/2:ℝ) := by
    rw [← Real.rpow_natCast (W^e) 2, ← Real.rpow_mul hW.le]
    norm_num only [Nat.cast_ofNat, mul_comm e 2]
    calc
      _ ≤ (F*L^(B+1))^(2*e) := Real.rpow_le_rpow hW.le hWup (by positivity)
      _ = _ := by
        rw [Real.mul_rpow hF.le (pow_nonneg hL0.le _),
          ← Real.rpow_natCast L (B+1), ← Real.rpow_mul hL0.le]
        congr 2
        dsimp only [e]
        push_cast
        field_simp
        norm_num
  have hsqrt : (L^(1/2:ℝ))^2 = L := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0.le]; norm_num
  have hcut : V2j A X ≤ d/(W^e)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (Real.rpow_pos_of_pos hW e))).mpr
    calc
      _ ≤ V2j A X*(F^(2*e)*L^(1/2:ℝ)) := mul_le_mul_of_nonneg_left hpow hgn.2.2.1
      _ = C*(Real.log L/L^(1/2:ℝ)) := by
        change (3*((A+14:ℕ):ℝ)*Real.log L/L)*(F^(2*e)*L^(1/2:ℝ)) = _
        dsimp only [C]
        field_simp [hL0.ne', (Real.rpow_pos_of_pos hL0 (1/2:ℝ)).ne']
        rw [hsqrt]
      _ ≤ _ := hsmall.le
  exact hcut.trans (hzero q χ hχp hχ z hβ hz)

theorem primitive_all_heights (A B : ℕ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ χ : PrimitiveComplexCharacter,
      (χ.modulus:ℝ) ≤ (Real.log X)^B → ∀ i : ℕ,
      |((V1 χ).zeros i).im| ≤ X^2 → V2j A X ≤ 1-((V1 χ).zeros i).re := by
  obtain ⟨T,hT,hhigh⟩ := high_height_window A B
  apply eventually_atTop.mp
  filter_upwards [hhigh,low_height_window A B hT.le] with X hi lo χ hq i hheight
  let _ : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let z := (V1 χ).zeros i
  have hz : χ.character.LFunction z = 0 := (V1 χ).actual_zero i
  have hβ : z.re < 1 := ((V1 χ).in_strip i).2
  rcases le_or_gt T |z.im| with ht | ht
  · exact hi χ.modulus hq χ.character z ht hheight hβ hz
  · exact lo χ.modulus hq χ.character χ.primitive χ.nontrivial z ht.le hβ hz

theorem arbitrary_log_saving (A B : ℕ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ χ : PrimitiveComplexCharacter,
      (χ.modulus:ℝ) ≤ (Real.log X)^B → ∀ i : ℕ,
      |((V1 χ).zeros i).im| ≤ X^2 →
      X^(-(1-((V1 χ).zeros i).re)/2048:ℝ) ≤ ((Real.log X)^A)⁻¹ := by
  obtain ⟨P,hP⟩ := primitive_all_heights (2048*A) B
  refine ⟨max P (Real.exp 1),?_⟩
  intro X hX χ hq i hi
  have hX₁ := (le_max_right _ _).trans hX
  have hX0 := (Real.exp_pos 1).trans_le hX₁
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).mpr hX₁
  have hL0 := zero_lt_one.trans_le hL
  let β := ((V1 χ).zeros i).re
  have hg := hP X ((le_max_left _ _).trans hX) χ hq i hi
  change 3*((2048*A+14:ℕ):ℝ)*Real.log (Real.log X)/Real.log X ≤ 1-β at hg
  have hbase := (div_le_iff₀ hL0).mp hg
  have hc : 2048*(A:ℝ) ≤ 3*((2048*A+14:ℕ):ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) A]
  have hs := mul_le_mul_of_nonneg_right hc (Real.log_nonneg hL)
  rw [Real.rpow_def_of_pos hX0, ← Real.exp_log (pow_pos hL0 A), ← Real.exp_neg, Real.log_pow]
  apply Real.exp_le_exp.mpr
  change Real.log X * (-(1-β)/2048) ≤ _
  linarith only [hs,hbase]

end TH8000LowConductors

end


-- THConductorWeights
section

/- The divisor regrouping proof is from OpenAI maths, PrimeGaps/OrthantIntegrals,
revision f5702854040e97fa7675c21ba37a9608f5f92dd3, Apache-2.0. -/
namespace GoldbachCentralSeven.Conductors
open Finset

theorem reciprocal_divisor_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 Q, f d / (d : ℝ)) * (harmonic Q : ℝ) := by
  classical
  let s := (Finset.Icc 1 Q).sigma fun q => q.divisors
  let t := (Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)
  let e : (a : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1/x.2)
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q,d⟩ hx
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdq,hq0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq1
    have hdle : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hdivpos : 0 < q/d := Nat.div_pos hdle hd0
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, hdle.trans hqQ⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, (Nat.div_le_self q d).trans hqQ⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
    obtain ⟨hq,hd⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq',hd'⟩ := Finset.mem_sigma.mp hy
    have hed : d = d' := congrArg Prod.fst he
    have heq : q/d = q'/d' := congrArg Prod.snd he
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdq' : d' ∣ q' := (Nat.mem_divisors.mp hd').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst d'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (∑ d ∈ q.divisors, f d) / (q : ℝ)) =
      ∑ x ∈ s, f (e x).1 / (e x).1 / (e x).2 := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    dsimp only [e]
    rw [div_div, ← Nat.cast_mul, Nat.mul_div_cancel' hdq]
  rw [hsum]
  calc
    _ = ∑ x ∈ s.image e, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, f x.1 / (x.1 : ℝ) / (x.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [t, Finset.sum_product, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
        harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.sum_comm]

private lemma finite_ratio (P : Finset ℕ) :
    (∀ p ∈ P, 2 ≤ p) → (∏ p ∈ P, (p:ℝ)/((p-1:ℕ):ℝ)) ≤ (P.card:ℝ)+1 := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert p s hl ih =>
    intro h
    have hp : 2 ≤ p := h _ (mem_insert_self _ _)
    have hs (a) (ha : a ∈ s) : 2 ≤ a := h _ (mem_insert_of_mem ha)
    have hnot : p ∉ s := fun hp => (lt_irrefl p) (hl p hp)
    have sub : s ⊆ Ico 2 p := fun a ha => mem_Ico.mpr ⟨hs a ha, hl a ha⟩
    have hcard : s.card ≤ p-2 := by simpa using card_le_card sub
    have hgap : s.card+2 ≤ p := by omega
    have hgapR : (s.card:ℝ)+2 ≤ p := by exact_mod_cast hgap
    have hpos : 0 < (p:ℝ)-1 := by
      apply sub_pos.mpr
      exact_mod_cast (show 1 < p by omega)
    rw [prod_insert hnot,card_insert_of_notMem hnot,Nat.cast_add_one,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
    calc
      _ ≤ (p:ℝ)/((p:ℝ)-1)*((s.card:ℝ)+1) := mul_le_mul_of_nonneg_left (ih hs) (by positivity)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div,div_le_iff₀ hpos]
        nlinarith

theorem conductor_ratio {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/(n.totient:ℝ) ≤ 1+Real.log n/Real.log 2 := by
  have ht : 0 < (n.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hsub (p) (hp : p ∈ n.primeFactors) : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hden : 0 < ∏ p ∈ n.primeFactors, ((p-1:ℕ):ℝ) := by
    apply prod_pos
    intro p hp
    exact_mod_cast (show 0 < p-1 by have := hsub p hp; omega)
  have hprod : (n:ℝ)/(n.totient:ℝ) = ∏ p ∈ n.primeFactors, (p:ℝ)/((p-1:ℕ):ℝ) := by
    rw [prod_div_distrib,div_eq_div_iff ht.ne' hden.ne']
    have hid := congrArg (fun a : ℕ => (a:ℝ))
      ((Nat.totient_mul_prod_primeFactors n).symm.trans (mul_comm _ _))
    simpa only [Nat.cast_mul,Nat.cast_prod] using hid
  have htwo : (2:ℕ)^n.primeFactors.card ≤ n := by
    calc
      _ = ∏ _p ∈ n.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ n.primeFactors, p := prod_le_prod' hsub
      _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hm := Real.log_le_log (by positivity : 0 < (2:ℝ)^n.primeFactors.card)
    (by exact_mod_cast htwo : (2:ℝ)^n.primeFactors.card ≤ n)
  rw [Real.log_pow] at hm
  have hh := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hm
  rw [hprod]
  exact (finite_ratio _ hsub).trans (by linarith)

theorem totient_divisor_transport (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, (∑ d ∈ q.divisors, f d)/(q.totient:ℝ)) ≤
      (1+Real.log Q/Real.log 2)*(harmonic Q:ℝ)*(∑ d ∈ Icc 1 Q, f d/(d:ℝ)) := by
  let K := 1+Real.log Q/Real.log 2
  have hL := Real.log_natCast_nonneg Q
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, K*((∑ d ∈ q.divisors, f d)/(q:ℝ)) := by
      apply sum_le_sum
      intro q hq
      have hh := mem_Icc.mp hq
      have hqr : 0 < (q:ℝ) := by exact_mod_cast hh.1
      have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hh.1
      have hr : (q:ℝ)/(q.totient:ℝ) ≤ K := (conductor_ratio hh.1).trans (by
        dsimp [K]; gcongr; exact_mod_cast hh.2)
      have hmass : 0 ≤ (∑ d ∈ q.divisors, f d)/(q:ℝ) :=
        div_nonneg (sum_nonneg fun d _ => hf d) hqr.le
      calc
        _ = ((q:ℝ)/(q.totient:ℝ))*((∑ d ∈ q.divisors,f d)/(q:ℝ)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hr hmass
    _ = _ := (mul_sum _ _ _).symm
    _ ≤ K*((∑ d ∈ Icc 1 Q, f d/(d:ℝ))*(harmonic Q:ℝ)) :=
      mul_le_mul_of_nonneg_left (reciprocal_divisor_sum_le f hf Q) hK
    _ = _ := by dsimp [K]; ring

end GoldbachCentralSeven.Conductors

end


-- THPrimitiveTransport
section

noncomputable section
open scoped BigOperators Classical
namespace GoldbachCentralSeven.PrimitiveTransfer
open Finset ArithmeticFunction OAI.Ostmann
open V7e Vel V2h

noncomputable def primitiveAt (d : ℕ) : Finset PrimitiveComplexCharacter := by
  classical
  by_cases hd : 0 < d
  · letI : NeZero d := ⟨hd.ne'⟩
    exact (univ : Finset {χ : DirichletCharacter ℂ d // χ.IsPrimitive ∧ χ ≠ 1}).image
      (fun s => ⟨d,hd,s.1,s.2.1,s.2.2⟩)
  · exact ∅

lemma mem_primitiveAt {d : ℕ} {χ : PrimitiveComplexCharacter} :
    χ ∈ primitiveAt d ↔ χ.modulus = d := by
  classical
  by_cases hd : 0 < d
  · letI : NeZero d := ⟨hd.ne'⟩
    simp only [primitiveAt,dif_pos hd,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨s,hs⟩
      exact (congrArg PrimitiveComplexCharacter.modulus hs).symm
    · cases χ with
      | mk m hp ξ hξ hn =>
        intro he
        change m=d at he
        subst m
        exact ⟨⟨ξ,hξ,hn⟩,rfl⟩
  · have hz : d = 0 := by omega
    subst d
    simp [primitiveAt,χ.positive.ne']

lemma conductor_inj {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (h : Vni χ hχ = Vni ψ hψ) : χ = ψ := by
  let lift (ω : PrimitiveComplexCharacter) : DirichletCharacter ℂ q :=
    if hh : ω.modulus ∣ q then ω.character.changeLevel hh else 1
  have hl (c : DirichletCharacter ℂ q) (hc : c ≠ 1) : lift (Vni c hc) = c := by
    dsimp only [lift,Vni]
    rw [dif_pos c.conductor_dvd_level,c.changeLevel_primitiveCharacter]
  simpa only [hl] using congrArg lift h

lemma primitive_row {q : ℕ} [NeZero q] (h : ℕ) (y : ℝ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖Vco (V9a h y) (fun k => (vonMangoldt k:ℂ)) χ.primitiveCharacter‖) ≤
      ∑ d ∈ q.divisors, ∑ ξ ∈ primitiveAt d, ‖V4q ξ h y‖ := by
  classical
  let S := (univ : Finset (DirichletCharacter ℂ q)).erase 1
  let m (c : {χ // χ ∈ S}) : PrimitiveComplexCharacter := Vni c.1 (ne_of_mem_erase c.2)
  have hinj : Function.Injective m := by
    intro x y he
    apply Subtype.ext
    exact conductor_inj x.1 y.1 (ne_of_mem_erase x.2) (ne_of_mem_erase y.2) he
  have hdis : ∀ᵉ (i ∈ q.divisors) (j ∈ q.divisors), i ≠ j → Disjoint (primitiveAt i) (primitiveAt j) := by
    intro i hi j hj hn
    apply disjoint_left.mpr
    intro c hci hcj
    exact hn ((mem_primitiveAt.mp hci).symm.trans (mem_primitiveAt.mp hcj))
  have hsub : S.attach.image m ⊆ q.divisors.biUnion primitiveAt := by
    intro c hc
    obtain ⟨s,_,rfl⟩ := mem_image.mp hc
    exact mem_biUnion.mpr ⟨s.val.conductor,Nat.mem_divisors.mpr
      ⟨s.val.conductor_dvd_level,(NeZero.ne q)⟩,mem_primitiveAt.mpr rfl⟩
  calc
    _ = ∑ c ∈ S.attach, ‖V4q (m c) h y‖ := by
      conv_lhs => rw [← sum_attach S]
      apply sum_congr rfl
      intro c _
      congr 1
      simp only [Vco,V4q,Vl,m,Vni]
      apply sum_congr rfl
      intro k hk
      exact mul_comm _ _
    _ = ∑ ξ ∈ S.attach.image m, ‖V4q ξ h y‖ := by rw [sum_image fun a _ b _ hh => hinj hh]
    _ ≤ ∑ ξ ∈ q.divisors.biUnion primitiveAt, ‖V4q ξ h y‖ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = _ := sum_biUnion hdis

theorem actual_principal_ap {q : ℕ} [NeZero q] (I : Finset ℕ) (a : ZMod q) (ha : IsUnit a) :
    ‖(∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=a), (vonMangoldt k:ℂ)) -
      (∑ k ∈ I, (vonMangoldt k:ℂ))/(q.totient:ℂ)‖ ≤
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖Vco I (fun k => (vonMangoldt k:ℂ)) χ.primitiveCharacter‖)/(q.totient:ℝ) +
      ∑ k ∈ I.filter (fun k => ¬k.Coprime q), vonMangoldt k := by
  classical
  let Φ := (q.totient:ℝ)
  have hφ : 0 < Φ := by dsimp [Φ]; exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  let w := fun k : ℕ => (vonMangoldt k:ℂ)
  let sumχ := fun χ : DirichletCharacter ℂ q => Vco I w χ
  let primχ := fun χ : DirichletCharacter ℂ q => Vco I w χ.primitiveCharacter
  let aχ := fun χ : DirichletCharacter ℂ q => χ a⁻¹
  have haInv : IsUnit a⁻¹ := by
    obtain ⟨u,rfl⟩ := ha
    rw [ZMod.inv_coe_unit]
    exact Units.isUnit _
  have princ : aχ 1 * primχ 1 = ∑ k ∈ I, w k := by
    dsimp [aχ,primχ,Vco]
    rw [MulChar.one_apply haInv,one_mul,DirichletCharacter.primitiveCharacter_one]
    apply sum_congr rfl
    intro k hk
    rw [MulChar.one_apply,mul_one]
    apply (ZMod.isUnit_iff_coprime _ _).2
    simp [DirichletCharacter.conductor_one]
  have H : (∑ χ : DirichletCharacter ℂ q, aχ χ*sumχ χ) =
      (q.totient:ℂ)* ∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=a), w k := by
    simp only [sumχ,aχ,Vco,mul_sum]
    rw [sum_comm,sum_filter]
    apply sum_congr rfl
    intro k _
    calc
      _ = w k * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (k:ZMod q) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ = _ := by
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
        by_cases hk : (k:ZMod q) = a
        · simp [hk]; ring
        · simp [hk,Ne.symm hk]
  let bad := ∑ k ∈ I.filter (fun k => ¬k.Coprime q), vonMangoldt k
  have herr (χ : DirichletCharacter ℂ q) : ‖aχ χ*(sumχ χ-primχ χ)‖ ≤ bad := by
    have hh := Vue χ.conductor_dvd_level χ.primitiveCharacter I vonMangoldt
      (fun n => vonMangoldt_nonneg)
    rw [χ.changeLevel_primitiveCharacter] at hh
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans hh
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  let primSum := ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, aχ χ*primχ χ
  have heq : (∑ χ : DirichletCharacter ℂ q, aχ χ*sumχ χ) - ∑ k ∈ I, w k =
      (∑ χ : DirichletCharacter ℂ q, aχ χ*(sumχ χ-primχ χ)) + primSum := by
    have hsum := sum_erase_add (s:= (univ : Finset (DirichletCharacter ℂ q)))
      (f:=fun χ => aχ χ*primχ χ) (mem_univ (1:DirichletCharacter ℂ q))
    rw [princ] at hsum
    simp_rw [mul_sub]; rw [sum_sub_distrib]
    dsimp [primSum]; linear_combination -hsum
  have hnorm := norm_add_le (∑ χ : DirichletCharacter ℂ q, aχ χ*(sumχ χ-primχ χ)) primSum
  have hb : ‖∑ χ : DirichletCharacter ℂ q, aχ χ*(sumχ χ-primχ χ)‖ ≤ Φ*bad := by
    refine (norm_sum_le _ _).trans ?_
    simpa [Φ,hcard] using sum_le_sum (s := (univ : Finset (DirichletCharacter ℂ q))) (fun χ _ => herr χ)
  have hpri : ‖primSum‖ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖primχ χ‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have main := hnorm.trans (add_le_add hb hpri)
  rw [← heq,H] at main
  have hne : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hid : (q.totient:ℂ) * ((∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=a), w k) -
      (∑ k ∈ I, w k)/(q.totient:ℂ)) =
      (q.totient:ℂ)*(∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=a), w k) - ∑ k ∈ I,w k := by field_simp
  rw [← hid,norm_mul,Complex.norm_natCast] at main
  let S := ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖primχ χ‖
  let E := ‖(∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=a), w k) -
      (∑ k ∈ I, w k)/(q.totient:ℂ)‖
  change Φ*E ≤ Φ*bad + S at main
  change E ≤ S/Φ + bad
  calc
    _ ≤ (Φ*bad+S)/Φ := (le_div_iff₀ hφ).mpr (by simpa [mul_comm] using main)
    _ = _ := by field_simp <;> ring

def pool (D : ℕ) : Finset PrimitiveComplexCharacter :=
  (Icc 1 D).biUnion primitiveAt

lemma mem_pool {D : ℕ} {χ : PrimitiveComplexCharacter} :
    χ ∈ pool D ↔ χ.modulus ≤ D := by
  classical
  simp only [pool,mem_biUnion,mem_primitiveAt,mem_Icc]
  constructor
  · rintro ⟨d,⟨_,hD⟩,hd⟩; simpa [hd] using hD
  · intro h; exact ⟨χ.modulus,⟨χ.positive,h⟩,rfl⟩

lemma conductor_sum_as_pool (D : ℕ) (g : PrimitiveComplexCharacter → ℝ) :
    (∑ d ∈ Icc 1 D, (∑ χ ∈ primitiveAt d, g χ)/(d:ℝ)) =
      ∑ χ ∈ pool D, g χ/(χ.modulus:ℝ) := by
  classical
  unfold pool
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro d hd
    rw [sum_div]
    exact sum_congr rfl (fun χ hχ => by rw [mem_primitiveAt.mp hχ])
  · intro a ha b hb hab
    exact disjoint_left.mpr fun χ hc hd => hab ((mem_primitiveAt.mp hc).symm.trans (mem_primitiveAt.mp hd))

theorem sum_conductor_bands (D : ℕ) {X W : ℝ} (hX : 1 < X) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ X^(5/32:ℝ)) (g : PrimitiveComplexCharacter → ℝ)
    (hg : ∀ χ, 0 ≤ g χ)
    (hbound : ∀ (Q : ℕ) (r : ℝ) (F : Finset PrimitiveComplexCharacter),
      1 ≤ Q → 0 ≤ r → r ≤ 5/32 → (Q:ℝ) ≤ X^r → X^r ≤ 2*(Q:ℝ) →
      (∀ χ ∈ F, χ.modulus ≤ Q ∧ Q ≤ 2*χ.modulus) →
      (∑ χ ∈ F, g χ/(χ.modulus:ℝ)) ≤ W) :
    (∑ d ∈ Icc 1 D, (∑ χ ∈ primitiveAt d, g χ)/(d:ℝ)) ≤
      ((Nat.log 2 D:ℝ)+1)*W := by
  classical
  let J := range (Nat.log 2 D+1)
  let P (j : ℕ) := (pool D).filter (fun χ => Nat.log 2 χ.modulus = j)
  have eq : (∑ χ ∈ pool D, g χ/(χ.modulus:ℝ)) =
      ∑ j ∈ J, ∑ χ ∈ P j, g χ/(χ.modulus:ℝ) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro χ hχ
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_pool.mp hχ)))
  rw [conductor_sum_as_pool,eq]
  calc
    _ ≤ ∑ _j ∈ J, W := by
      apply sum_le_sum
      intro j hj
      let Q := min D (2^(j+1))
      have hQ : 1 ≤ Q := le_min hD (Nat.one_le_pow _ _ (by norm_num))
      have hqr : 1 ≤ (Q:ℝ) := by exact_mod_cast hQ
      have hq0 : 0 < (Q:ℝ) := by linarith
      have hl := Real.log_pos hX
      let r := Real.log Q/Real.log X
      have hr : 0 ≤ r := div_nonneg (Real.log_nonneg hqr) hl.le
      have he : X^r = (Q:ℝ) := by
        rw [Real.rpow_def_of_pos (zero_lt_one.trans hX)]
        dsimp [r]
        rw [show Real.log X * (Real.log Q / Real.log X) = Real.log Q by field_simp,
          Real.exp_log hq0]
      have hQX : (Q:ℝ) ≤ X^(5/32:ℝ) := (by exact_mod_cast min_le_left D (2^(j+1)) : (Q:ℝ) ≤ D).trans hlevel
      have hr' : r ≤ 5/32 := (Real.rpow_le_rpow_left_iff hX).mp (he ▸ hQX)
      apply hbound Q r _ hQ hr hr' he.ge (by rw [he]; linarith)
      intro χ hχ
      obtain ⟨hχD,hj'⟩ := mem_filter.mp hχ
      have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) χ.modulus
      have hs := Nat.pow_log_le_self 2 χ.positive.ne'
      rw [hj'] at hh hs
      refine ⟨le_min (mem_pool.mp hχD) hh.le,?_⟩
      exact (min_le_right _ _).trans (by rw [pow_succ]; omega)
    _ = _ := by simp [J]

end GoldbachCentralSeven.PrimitiveTransfer

end
end


-- THShortBV
section

noncomputable section
namespace GoldbachCentralSeven
open Finset ArithmeticFunction Filter OAI.Ostmann V7e
open PrimitiveTransfer
open scoped Classical

private theorem natlog_two_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n:ℝ) ≤ Real.log n/Real.log 2 := by
  have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^(Nat.log 2 n)) (by
    exact_mod_cast h : (2:ℝ)^(Nat.log 2 n) ≤ n)
  rw [Real.log_pow] at hh
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hh

def characterMass (X H d : ℕ) : ℝ := ∑ χ ∈ primitiveAt d, ‖V4q χ H X‖

private lemma char_nonneg (X H d : ℕ) : 0 ≤ characterMass X H d := sum_nonneg fun _ _ => norm_nonneg _

theorem psiWorst_primitive_bound {q : ℕ} (hq : 1 ≤ q) (X H : ℕ) :
    (psiWorst X H q (fullPsiMass X H):ℝ) ≤
      (∑ d ∈ q.divisors, characterMass X H d)/(q.totient:ℝ) +
      (Nat.log 2 (X+H):ℝ)*Real.log q := by
  letI : NeZero q := ⟨by omega⟩
  let I := Ioc X (X+H)
  let M := fullPsiMass X H
  let B := (∑ d ∈ q.divisors, characterMass X H d)/(q.totient:ℝ) +
    (Nat.log 2 (X+H):ℝ)*Real.log q
  have hB : 0 ≤ B := add_nonneg (div_nonneg (sum_nonneg fun _ _ => char_nonneg ..)
    (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  have hnn : psiWorst X H q M ≤ (⟨B,hB⟩:NNReal) := by
    apply Finset.sup_le
    intro a ha
    change (if a.Coprime q then (⟨|psiWindow X H q a-M/q.totient|,abs_nonneg _⟩:NNReal) else 0) ≤ _
    by_cases hc : a.Coprime q
    · rw [ite_eq_left hc]
      change |psiWindow X H q a - M/q.totient| ≤ B
      have hI : V2h.V9a H (X:ℝ) = I := by simp [V2h.V9a,I]
      have hset : I.filter (fun k : ℕ => (k:ZMod q)=(a:ZMod q)) = classWindow X H q a := by
        ext n
        simp only [I,classWindow,mem_filter,ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt (mem_range.mp ha)]
      have hraw := actual_principal_ap I (a:ZMod q) ((ZMod.isUnit_iff_coprime a q).mpr hc)
      rw [hset] at hraw
      have hh : ((∑ k ∈ classWindow X H q a,(vonMangoldt k:ℂ))-
          (∑ k ∈ I,(vonMangoldt k:ℂ))/(q.totient:ℂ)) =
          ((psiWindow X H q a - M/(q.totient:ℝ):ℝ):ℂ) := by
        dsimp [psiWindow,M,fullPsiMass,I]
        push_cast; rfl
      rw [hh,Complex.norm_real,Real.norm_eq_abs] at hraw
      have row := primitive_row (q:=q) H X
      rw [hI] at row
      apply hraw.trans
      refine add_le_add (div_le_div_of_nonneg_right row (Nat.cast_nonneg _)) ?_
      refine le_trans (sum_le_sum_of_subset_of_nonneg (s := I.filter (fun k => ¬ k.Coprime q))
        (t := (Ioc 0 (X+H)).filter (fun k => ¬ k.Coprime q)) ?_ (fun _ _ _ => vonMangoldt_nonneg)) ?_
      · intro k hk
        obtain ⟨hmem,hcop⟩ := mem_filter.mp hk
        have h := mem_Ioc.mp hmem
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,h.2⟩,hcop⟩
      · exact OAI.LargePrimeGaps.vonMangoldt_noncoprime_sum_le _ hq
    · rw [ite_eq_right hc]; exact bot_le
  exact_mod_cast hnn

theorem uniform_characterTransport (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ H D : ℕ, 1 ≤ D → (D:ℝ) ≤ (X:ℝ)^(5/32:ℝ) →
      H ≤ X → (X:ℝ)^(2/3:ℝ) ≤ 2*H →
      (∑ d ∈ Icc 1 D, characterMass X H d/(d:ℝ)) ≤
        ((Nat.log 2 D:ℝ)+1)*(H/(Real.log X)^A) := by
  have hbase := Density.uniform_band_log_budget TH8000LowConductors.arbitrary_log_saving (A+2)
  have hw := Kernel.character_sum_of_height_budget A
  filter_upwards [eventually_ge_atTop (2:ℕ), tendsto_natCast_atTop_atTop.eventually hbase,
    tendsto_natCast_atTop_atTop.eventually hw] with X hx hzero hwin
  intro H D hD hl hd hh
  have hx' : (1:ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  apply sum_conductor_bands D hx' hD hl _ (fun _ => norm_nonneg _)
  intro Q r F hQ hr hr' hQu hQl hF
  have hlevel := hQu.trans (Real.rpow_le_rpow_of_exponent_le hx'.le hr')
  apply hwin Q F H (X:ℝ) hQ hlevel hF
    ⟨le_rfl,by linarith⟩ (by exact_mod_cast hd) hh
  intro T ht ht'
  simpa only [Kernel.damp,Density.damping,one_div] using
    hzero r T Q F hr hr' ht ht' hQ hQu hQl hF

private theorem exceptional_cost (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ D H : ℕ, 1 ≤ D → (D:ℝ) ≤ (X:ℝ)^(5/32:ℝ) →
      H ≤ X → (X:ℝ)^(2/3:ℝ) ≤ 2*H →
      (D:ℝ)*(Nat.log 2 (X+H):ℝ)*Real.log D ≤ (H:ℝ)/(2*(Real.log X)^A) := by
  have hsave := (isLittleO_log_rpow_rpow_atTop ((A+2:ℕ):ℝ)
    (by norm_num : 0 < (1/2:ℝ))).bound (by norm_num : (0:ℝ) < 1/16)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    tendsto_natCast_atTop_atTop.eventually hsave] with X hx hpow
  intro D H hD hl hHX hH
  have hx2 : (2:ℝ) ≤ X := by exact_mod_cast hx
  have hx' : (1:ℝ) < X := by linarith
  have hL := Real.log_pos hx'
  have hDpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have hDX := hl.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx'.le (by norm_num : (5/32:ℝ) ≤ 1))
  have hLD := Real.log_le_log hDpos hDX
  have hL0 := Real.log_natCast_nonneg D
  have hT : (Nat.log 2 (X+H):ℝ) ≤ 4*Real.log X := by
    apply (natlog_two_le (by omega : 1≤X+H)).trans
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    have hxy : (0:ℝ) < (X+H:ℕ) := by exact_mod_cast (show 0 < X+H by omega)
    have hu : ((X+H:ℕ):ℝ) ≤ (X:ℝ)^2 := by
      push_cast
      have hHx : (H:ℝ) ≤ X := by exact_mod_cast hHX
      nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) X) (sub_nonneg.mpr hx2)]
    have hh := Real.log_le_log hxy hu
    rw [Real.log_pow] at hh
    have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    calc
      _ ≤ 2*Real.log X := by simpa only [Nat.cast_ofNat] using hh
      _ = 4*Real.log X*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl2 (by positivity)
  change ‖Real.log (X:ℝ)^((A+2:ℕ):ℝ)‖ ≤ 1/16*‖(X:ℝ)^(1/2:ℝ)‖ at hpow
  rw [Real.rpow_natCast,Real.norm_eq_abs,abs_of_pos (pow_pos hL _),
    Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hx') _)] at hpow
  have hd' := hl.trans (Real.rpow_le_rpow_of_exponent_le hx'.le (by norm_num : (5/32:ℝ) ≤ 1/6))
  have htarget : 8*(D:ℝ)*(Real.log X)^(A+2) ≤ H := by
    have hh := mul_le_mul hd' hpow (pow_nonneg hL.le _) (by positivity)
    have hid : (X:ℝ)^(1/6:ℝ)*(X:ℝ)^(1/2:ℝ) = (X:ℝ)^(2/3:ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans hx')]; norm_num
    rw [show (X:ℝ)^(1/6:ℝ)*(1/16*(X:ℝ)^(1/2:ℝ)) =
      (1/16)*((X:ℝ)^(1/6:ℝ)*(X:ℝ)^(1/2:ℝ)) by ring,hid] at hh
    linarith
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hT hDpos.le) hLD hL0 (by positivity)) ?_
  apply (le_div_iff₀ (by positivity : 0 < 2*(Real.log X)^A)).mpr
  convert htarget using 1
  rw [pow_add];ring

theorem short_bv_nonprincipal (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ D H : ℕ, (D:ℝ) ≤ (X:ℝ)^(5/32:ℝ) → H ≤ X →
      (X:ℝ)^(2/3:ℝ) ≤ 2*H →
      (∑ q ∈ Icc 1 D, (psiWorst X H q (fullPsiMass X H):ℝ)) ≤ H/(Real.log X)^A := by
  filter_upwards [uniform_characterTransport (A+5),exceptional_cost A,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (8:ℝ),
    eventually_ge_atTop (2:ℕ)] with X hc hbad hXL hx
  intro D H hlevel hh hH
  change 8 ≤ Real.log (X:ℝ) at hXL
  have hlog : 0 < Real.log X := by linarith
  by_cases hD : D = 0
  · subst D; simp; positivity
  have hD1 : 1 ≤ D := by omega
  have hx' : (1:ℝ) < X := by exact_mod_cast (show 1<X by omega)
  have hDX := hlevel.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx'.le (by norm_num : (5/32:ℝ) ≤ 1))
  have hDpos : 0 < (D:ℝ) := by exact_mod_cast hD1
  have hLD := Real.log_le_log hDpos hDX
  have hld := Real.log_natCast_nonneg D
  have hrow := hc H D hD1 hlevel hh hH
  have hsum := GoldbachCentralSeven.Conductors.totient_divisor_transport
    (characterMass X H) (char_nonneg X H) D hD1
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh1 : 1 + Real.log D/Real.log 2 ≤ 3*Real.log X := by
    have hL : Real.log D/Real.log 2 ≤ 2*Real.log X := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith [mul_nonneg hlog.le (sub_nonneg.mpr hl2)]
    linarith
  have hh2 : (harmonic D:ℝ) ≤ 2*Real.log X := by linarith [harmonic_le_one_add_log D]
  have hh3 : (Nat.log 2 D:ℝ)+1 ≤ 3*Real.log X := by linarith [natlog_two_le hD1]
  have khpos : 0 ≤ 1+Real.log D/Real.log 2 := by positivity
  have hhp : 0 ≤ (harmonic D:ℝ) := by unfold harmonic; positivity
  have hmid : (∑ q ∈ Icc 1 D, (∑ d ∈ q.divisors, characterMass X H d)/(q.totient:ℝ)) ≤
      (H:ℝ)/(2*(Real.log X)^A) := by
    apply hsum.trans
    calc
      _ ≤ ((3*Real.log X)*(2*Real.log X))*((3*Real.log X)*(H/(Real.log X)^(A+5))) := by
        apply mul_le_mul (mul_le_mul hh1 hh2 hhp (by positivity))
          (hrow.trans (mul_le_mul_of_nonneg_right hh3 (by positivity)))
          (sum_nonneg fun d _ => div_nonneg (char_nonneg ..) (Nat.cast_nonneg _)) (by positivity)
      _ ≤ _ := by
        have hp : (36:ℝ) ≤ (Real.log X)^2 := by nlinarith [sq_nonneg (Real.log X-8)]
        field_simp
        rw [pow_add]
        nlinarith only [mul_le_mul_of_nonneg_right hp
          (by positivity : 0 ≤ (H:ℝ)*(Real.log X)^3*(Real.log X)^A)]
  calc
    _ ≤ ∑ q ∈ Icc 1 D, ((∑ d ∈ q.divisors, characterMass X H d)/(q.totient:ℝ) +
        (Nat.log 2 (X+H):ℝ)*Real.log q) := sum_le_sum fun q hq => psiWorst_primitive_bound (mem_Icc.mp hq).1 X H
    _ ≤ (H:ℝ)/(2*(Real.log X)^A) + (D:ℝ)*(Nat.log 2 (X+H):ℝ)*Real.log D := by
      rw [sum_add_distrib]
      apply add_le_add hmid
      calc
        _ ≤ ∑ _q ∈ Icc 1 D, (Nat.log 2 (X+H):ℝ)*Real.log D := by
          apply sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hq).1) (by exact_mod_cast (mem_Icc.mp hq).2)
        _ = _ := by simp; ring
    _ ≤ _ := by
      have h := hbad D H hD1 hlevel hh hH
      calc
        _ ≤ (H:ℝ)/(2*(Real.log X)^A) + H/(2*(Real.log X)^A) := add_le_add le_rfl h
        _ = _ := by ring

end GoldbachCentralSeven

end
end


-- TH8000PaidRemainders
section

namespace GoldbachCentralSeven.Model
open Finset Filter CentralUpperGeometry GoldbachSevenWeight

theorem paid_remainders_from_uniform_AP (d A : ℕ) (hd : 0 < d)
    (hAP : ∀ᶠ X : ℕ in atTop, ∀ H D : ℕ, 1 ≤ D → (D:ℝ) ≤ (X:ℝ)^(5/32:ℝ) →
      H ≤ X → (X:ℝ)^(2/3:ℝ) ≤ 2*H →
      (∑ q ∈ Icc 1 D, (psiWorst X H q (fullPsiMass X H):ℝ)) ≤ H/(Real.log X)^A) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime → ∀ (H b : ℕ) (Q : Finset ℕ),
      H^3 ≤ p^4 → p^4 < (H+1)^3 → b.Coprime d →
      let z := sieveCut p
      let X := p^2
      let J := fullPsiMass X H/Real.log X
      (∀ q ∈ Q, q.Prime ∧ z ≤ q ∧ ¬q ∣ 2*d) →
      (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤ H/(Real.log X)^A ∧
      (∑ q ∈ Q, ∑ k ∈ moduli d (radius z q) ((radius z q)^2),
        |rhoRemainder p H d b J (q*k)|) ≤ H/(Real.log X)^A := by
  obtain ⟨K,hK⟩ := rosser_remainder_pair d A hd
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 2,
    aligned_level_eventually d, tendsto_cut.eventually_ge_atTop 1,
    (tendsto_pow_atTop (α:=ℕ) (by decide : 2≠0)).eventually hAP] with p hpK hp2 hlev hz hpsi
  intro hp H b Q hH hh hb
  dsimp only
  intro hQ
  apply hK p hpK hp H b Q hH hh hb hQ
  exact hpsi H _ (Nat.mul_pos hd (Nat.pow_pos hz)) ((Nat.le_floor_iff (by positivity)).mp hlev.1)
    (floor_window_le_center hp.pos hH) (floor_window_real_bounds hp2 hH hh).2

end GoldbachCentralSeven.Model

namespace GoldbachCentralSeven.Model
open Finset Filter CentralUpperGeometry GoldbachSevenWeight

theorem paid_rosser_remainders (d A : ℕ) (hd : 0 < d) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime → ∀ (H b : ℕ) (Q : Finset ℕ),
      H^3 ≤ p^4 → p^4 < (H+1)^3 → b.Coprime d →
      let z := sieveCut p
      let X := p^2
      let J := fullPsiMass X H/Real.log X
      (∀ q ∈ Q, q.Prime ∧ z ≤ q ∧ ¬q ∣ 2*d) →
      (∑ k ∈ moduli d z (z^4), |rhoRemainder p H d b J k|) ≤ H/(Real.log X)^A ∧
      (∑ q ∈ Q, ∑ k ∈ moduli d (radius z q) ((radius z q)^2),
        |rhoRemainder p H d b J (q*k)|) ≤ H/(Real.log X)^A := by
  apply paid_remainders_from_uniform_AP d A hd
  filter_upwards [short_bv_nonprincipal A] with X hX
  exact fun H D _ hlev hH hl => hX D H hlev hH hl

end GoldbachCentralSeven.Model

end


-- TH8000WeightedUnconditional
section

namespace GoldbachCentralSeven.Model
open Finset Filter Real GoldbachSevenWeight CentralUpperGeometry

theorem actual_weighted_comparison (d A : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime → ∀ H b : ℕ, b < d → b.Coprime d →
      (2*p^2-b).Coprime d → H^3 ≤ p^4 → p^4 < (H+1)^3 →
      let X := p^2
      let z := sieveCut p
      let Q := penaltyBand X z
      let J := fullPsiMass X H / Real.log X
      let E := (H:ℝ)/(Real.log X)^A
      (J/d.totient)*V d z*(Real.exp Real.eulerMascheroniConstant/2*Real.log 3-ε) - E -
        ((J/d.totient)*(Real.exp Real.eulerMascheroniConstant+ε) *
          (∑ q ∈ Q, discount z q*V d (radius z q)/((q:ℝ)-1))+E)/(3/2) ≤
        ∑ h ∈ roughOffsets p H d b, weight X (X-h) := by
  obtain ⟨K,hK,hlocal,_⟩ := local_product_control
  obtain ⟨Zl,hl⟩ := lower_bound hK hε
  obtain ⟨Zu,hu⟩ := upper_bound hK hε
  obtain ⟨P,hpa⟩ := paid_rosser_remainders d A hd
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (max (max P d) 4),
    tendsto_cut.eventually_ge_atTop (max Zl (2*d+1)),tendsto_cut.eventually (radius_uniform Zu)]
    with p hpstart hz hradius
  intro hp H b hbd hb hadm hH hh X z Q J E
  have hp4 : 4 ≤ p := by omega
  have hzel : 2*d < z := by change 2*d < sieveCut p;omega
  have hpX : 2 < p^2 := by nlinarith
  have hble : b ≤ 2*p^2 := by nlinarith [show d ≤ p by omega]
  have hhalf := half_window p H hp4 hH
  have hpos : 1 < p^2-H := by omega
  have hle : H ≤ p^2 := by omega
  have hJ : 0 ≤ J := div_nonneg (sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    (Real.log_natCast_nonneg X)
  have hpq := penaltyBand_conditions hd hzel
  obtain ⟨hEL,hEU⟩ := hpa p (by omega) hp H b Q hH hh hb hpq
  apply weighted_combine_at_cut hp4 hbd hH J ε E hJ hε
  · exact hl z (by change Zl ≤ sieveCut p;omega) p H d b J hJ hle hble hadm hpX hpos
      (hlocal p H d b 1 z J)
  · intro q hq
    obtain ⟨hi,hpr,hqy⟩ := mem_filter.mp hq
    have hwz : radius z q ≤ z := min_le_left _ _
    have hqend : (q:ℝ) ≤ penaltyEnd z := hqy.le.trans (level_alignment (p:=p) hp.pos).2
    have hw : Zu ≤ radius z q := hradius q hpr.pos hqend
    exact hu _ hw p H d b q J hJ hle hble hadm hpX hpos hpr
      (hwz.trans (mem_Icc.mp hi).1) (hlocal p H d b q (radius z q) J)
  · exact hEL
  · exact hEU

end GoldbachCentralSeven.Model

end


-- Sidon.NumberTheory.ZetaZeroCount
section

noncomputable section

open Filter
open scoped Topology

namespace Sidon

def criticalZetaZeros (T : ℝ) : Finset ℂ :=
  ((isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_riemannZetaZeros_finite.toFinset).filter
    fun ρ => 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T

theorem mem_criticalZetaZeros {T : ℝ} {ρ : ℂ} :
    ρ ∈ criticalZetaZeros T ↔
      riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  classical
  simp only [criticalZetaZeros, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, mem_riemannZetaZeros]
  constructor
  · rintro ⟨⟨_, hz⟩, hρ⟩
    exact ⟨hz, hρ⟩
  · rintro ⟨hz, hρ⟩
    refine ⟨⟨?_, hz⟩, hρ⟩
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ |T| + 2 := by
        rw [abs_of_nonneg hρ.1, abs_of_nonneg hρ.2.2.1.le]
        linarith [le_abs_self T]

theorem analyticOrderAt_riemannZeta_ne_top (ρ : ℂ) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  intro htop
  have hzero : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z = 0 :=
    (analyticOrderAt_eq_top.mp htop).filter_mono nhdsWithin_le_nhds
  have hdisj := isClosed_and_discrete_iff.mp
    ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩ ρ
  have hnot : ∀ᶠ z in 𝓝[≠] ρ, z ∉ riemannZetaZeros :=
    Filter.disjoint_principal_right.mp hdisj
  obtain ⟨z, hnot, hz⟩ := (hnot.and hzero).exists
  exact hnot hz

theorem zeta_zero_multiplicity_pos {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    0 < analyticOrderNatAt riemannZeta ρ := by
  have hne : ρ ≠ 1 := by
    intro h
    subst ρ
    exact riemannZeta_one_ne_zero hρ
  apply ENat.toNat_pos _ (analyticOrderAt_riemannZeta_ne_top ρ)
  exact analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hne, hρ⟩

def zetaZeroOccurrences (T : ℝ) : Finset (ℂ × ℕ) :=
  (criticalZetaZeros T).biUnion fun ρ =>
    (Finset.range (analyticOrderNatAt riemannZeta ρ)).image fun k => (ρ, k)

theorem mem_zetaZeroOccurrences {T : ℝ} {ρ : ℂ} {k : ℕ} :
    (ρ, k) ∈ zetaZeroOccurrences T ↔
      ρ ∈ criticalZetaZeros T ∧ k < analyticOrderNatAt riemannZeta ρ := by
  classical
  simp only [zetaZeroOccurrences, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, j, hj, hρ, hk⟩
    subst z
    subst j
    exact ⟨hz, hj⟩
  · rintro ⟨hρ, hk⟩
    exact ⟨ρ, hρ, k, hk, rfl, rfl⟩

theorem sum_zetaZeroOccurrences (T : ℝ) (w : ℂ → ℝ) :
    (∑ z ∈ zetaZeroOccurrences T, w z.1) =
      ∑ ρ ∈ criticalZetaZeros T, (analyticOrderNatAt riemannZeta ρ : ℝ) * w ρ := by
  classical
  unfold zetaZeroOccurrences
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.sum_image]
    · simp
    · intro k _ l _ h
      exact (Prod.mk.inj h).2
  · intro ρ _ τ _ hne
    apply Finset.disjoint_left.mpr
    intro z hzρ hzτ
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hzρ
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hzτ
    exact hne (congrArg Prod.fst he).symm

theorem zetaZeroOccurrences_re_bounds {T : ℝ} {z : ℂ × ℕ}
    (hz : z ∈ zetaZeroOccurrences T) : 0 ≤ z.1.re ∧ z.1.re ≤ 1 := by
  have h := mem_criticalZetaZeros.mp (mem_zetaZeroOccurrences.mp hz).1
  exact ⟨h.2.1, h.2.2.1⟩

theorem zetaZeroOccurrences_height_bounds {T : ℝ} {z : ℂ × ℕ}
    (hz : z ∈ zetaZeroOccurrences T) : 0 < z.1.im ∧ z.1.im ≤ T := by
  have h := mem_criticalZetaZeros.mp (mem_zetaZeroOccurrences.mp hz).1
  exact h.2.2.2

def zetaZeroCount (σ T : ℝ) : ℕ :=
  ((zetaZeroOccurrences T).filter fun z => σ ≤ z.1.re).card

theorem zetaZeroCount_antitone (T : ℝ) : Antitone (fun σ => zetaZeroCount σ T) := by
  intro a b hab
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz, hb⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz, hab.trans hb⟩

theorem zetaZeroCount_mono_height (σ : ℝ) : Monotone (zetaZeroCount σ) := by
  intro T U hTU
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz, hσ⟩ := Finset.mem_filter.mp hz
  obtain ⟨hρ, hk⟩ := mem_zetaZeroOccurrences.mp hz
  obtain ⟨hzero, hre0, hre1, him0, himT⟩ := mem_criticalZetaZeros.mp hρ
  exact Finset.mem_filter.mpr ⟨mem_zetaZeroOccurrences.mpr
    ⟨mem_criticalZetaZeros.mpr ⟨hzero, hre0, hre1, him0, himT.trans hTU⟩, hk⟩, hσ⟩

theorem zetaZeroCount_le_low_add_high (σ T : ℝ) :
    zetaZeroCount σ T ≤ zetaZeroCount 0 4 +
      ((zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re ∧ 4 ≤ z.1.im)).card := by
  classical
  have hzero : (zetaZeroOccurrences 4).filter (fun z => 0 ≤ z.1.re) =
      zetaZeroOccurrences 4 := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    exact (zetaZeroOccurrences_re_bounds hz).1
  have hsub : (zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re) ⊆
      zetaZeroOccurrences 4 ∪
        (zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re ∧ 4 ≤ z.1.im) := by
    intro z hz
    obtain ⟨hz, hσ⟩ := Finset.mem_filter.mp hz
    by_cases hhigh : 4 ≤ z.1.im
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hσ, hhigh⟩)
    · apply Finset.mem_union_left
      obtain ⟨hρ, hk⟩ := mem_zetaZeroOccurrences.mp hz
      obtain ⟨hζ, hβ0, hβ1, hγ0, _⟩ := mem_criticalZetaZeros.mp hρ
      exact mem_zetaZeroOccurrences.mpr
        ⟨mem_criticalZetaZeros.mpr ⟨hζ, hβ0, hβ1, hγ0, (lt_of_not_ge hhigh).le⟩, hk⟩
  unfold zetaZeroCount
  rw [hzero]
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

def UniformZetaZeroDensity (A : ℝ) (B : ℕ) (K T₀ : ℝ) : Prop :=
  ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
    (zetaZeroCount σ T : ℝ) ≤ K * T ^ (A * (1 - σ)) * (Real.log T) ^ B

def ZetaZeroFreeWidth (η : ℝ → ℝ) (T₀ : ℝ) : Prop :=
  ∀ T : ℝ, T₀ ≤ T → ∀ z ∈ zetaZeroOccurrences T, z.1.re ≤ 1 - η T

end Sidon

end
end


-- Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian

noncomputable section

lemma iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n
        ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => simp [iteratedDeriv_eq_iterate]
  | succ n ih =>
      rw [show n + 1 = n.succ by omega, iteratedDeriv_succ,
        iteratedDeriv_succ, ih, deriv_conj_conj]

lemma riemannZeta_eq_conj_comp_conj :
    riemannZeta = (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) := by
  funext s
  simp [Function.comp_apply]

theorem iteratedDeriv_riemannZeta_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (iteratedDeriv n riemannZeta s) := by
  have hiter := iteratedDeriv_conj_conj riemannZeta n
  rw [← riemannZeta_eq_conj_comp_conj] at hiter
  have h := congrFun hiter (starRingEnd ℂ s)
  simpa [Function.comp_apply] using h

def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

def nontrivialZetaZeroSet : Set ℂ :=
  {s | IsNontrivialZetaZero s}

theorem nontrivialZetaZeroSet_subset_riemannZetaZeros :
    nontrivialZetaZeroSet ⊆ riemannZetaZeros := by
  intro s hs
  exact hs.1

theorem IsCompact.inter_nontrivialZetaZeroSet_finite
    {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ nontrivialZetaZeroSet).Finite := by
  exact hS.inter_riemannZetaZeros_finite.subset
    (Set.inter_subset_inter_right S
      nontrivialZetaZeroSet_subset_riemannZetaZeros)

abbrev NontrivialZetaZero := {s : ℂ // IsNontrivialZetaZero s}

namespace NontrivialZetaZero

def conjugate (ρ : NontrivialZetaZero) : NontrivialZetaZero := by
  refine ⟨starRingEnd ℂ ρ.1, ?_⟩
  refine ⟨by simp [ρ.2.1], ?_, ?_⟩
  · rintro ⟨n, hn⟩
    apply ρ.2.2.1
    refine ⟨n, ?_⟩
    have h := congrArg (starRingEnd ℂ) hn
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    rw [map_mul, map_neg, htwo] at h
    simpa using h
  · intro hone
    apply ρ.2.2.2
    have h := congrArg (starRingEnd ℂ) hone
    simpa using h

@[simp]
theorem conjugate_coe (ρ : NontrivialZetaZero) :
    (conjugate ρ : ℂ) = starRingEnd ℂ ρ.1 := rfl

@[simp]
theorem conjugate_conjugate (ρ : NontrivialZetaZero) :
    conjugate (conjugate ρ) = ρ := by
  apply Subtype.ext
  simp

theorem coe_ne_zero (ρ : NontrivialZetaZero) : (ρ.1 : ℂ) ≠ 0 := by
  intro hzero
  have hzeta := ρ.2.1
  rw [hzero, riemannZeta_zero] at hzeta
  norm_num at hzeta

theorem GammaR_ne_zero (ρ : NontrivialZetaZero) :
    Complex.Gammaℝ ρ.1 ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  cases n with
  | zero =>
      apply coe_ne_zero ρ
      simpa using hn
  | succ n =>
      apply ρ.2.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ] using hn

theorem completedRiemannZeta_eq_zero (ρ : NontrivialZetaZero) :
    completedRiemannZeta ρ.1 = 0 := by
  have hzeta := ρ.2.1
  rw [riemannZeta_def_of_ne_zero (coe_ne_zero ρ)] at hzeta
  exact (div_eq_zero_iff.mp hzeta).resolve_right (GammaR_ne_zero ρ)

def functionalPartner (ρ : NontrivialZetaZero) : NontrivialZetaZero := by
  refine ⟨1 - ρ.1, ?_⟩
  have hcompleted : completedRiemannZeta (1 - ρ.1) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact completedRiemannZeta_eq_zero ρ
  have hzero : riemannZeta (1 - ρ.1) = 0 := by
    rw [riemannZeta_def_of_ne_zero]
    · rw [hcompleted, zero_div]
    · exact sub_ne_zero.mpr ρ.2.2.2.symm
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hRe : 1 ≤ ρ.1.re := by
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hRe ρ.2.1
  · intro hone
    apply coe_ne_zero ρ
    exact sub_eq_self.mp hone

@[simp]
theorem functionalPartner_coe (ρ : NontrivialZetaZero) :
    (functionalPartner ρ : ℂ) = 1 - ρ.1 := rfl

def conjugatePartner (ρ : NontrivialZetaZero) : NontrivialZetaZero :=
  functionalPartner (conjugate ρ)

@[simp]
theorem conjugatePartner_coe (ρ : NontrivialZetaZero) :
    (conjugatePartner ρ : ℂ) = 1 - starRingEnd ℂ ρ.1 := rfl

@[simp]
theorem conjugatePartner_conjugatePartner (ρ : NontrivialZetaZero) :
    conjugatePartner (conjugatePartner ρ) = ρ := by
  apply Subtype.ext
  simp

end NontrivialZetaZero

abbrev ZetaZeroMultiplicity := NontrivialZetaZero → ℕ

noncomputable def analyticZetaZeroMultiplicity : ZetaZeroMultiplicity :=
  fun ρ => analyticOrderNatAt riemannZeta ρ.1

lemma analyticAt_riemannZeta_nontrivialZero (ρ : NontrivialZetaZero) :
    AnalyticAt ℂ riemannZeta ρ.1 := by
  exact analyticOn_riemannZeta ρ.1 (by simpa using ρ.2.2.2)

lemma analyticAt_completedRiemannZeta_nontrivialZero
    (ρ : NontrivialZetaZero) :
    AnalyticAt ℂ completedRiemannZeta ρ.1 := by
  let U : Set ℂ := {0}ᶜ ∩ {1}ᶜ
  have hUopen : IsOpen U := isOpen_compl_singleton.inter isOpen_compl_singleton
  have hρU : ρ.1 ∈ U := by
    exact ⟨by simpa using NontrivialZetaZero.coe_ne_zero ρ,
      by simpa using ρ.2.2.2⟩
  apply DifferentiableOn.analyticAt (s := U) _ (hUopen.mem_nhds hρU)
  intro z hz
  exact (differentiableAt_completedZeta
    (by simpa [U] using hz.1) (by simpa [U] using hz.2)).differentiableWithinAt

theorem analyticOrderAt_riemannZeta_eq_completedRiemannZeta
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta ρ.1 =
      analyticOrderAt completedRiemannZeta ρ.1 := by
  let inverseGamma : ℂ → ℂ := fun z => (Complex.Gammaℝ z)⁻¹
  have hinverseAnalytic : AnalyticAt ℂ inverseGamma ρ.1 := by
    exact Complex.differentiable_Gammaℝ_inv.analyticAt ρ.1
  have hinverseOrder : analyticOrderAt inverseGamma ρ.1 = 0 := by
    exact hinverseAnalytic.analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (NontrivialZetaZero.GammaR_ne_zero ρ))
  have heq :
      riemannZeta =ᶠ[nhds ρ.1]
        fun z => completedRiemannZeta z * inverseGamma z := by
    filter_upwards [eventually_ne_nhds (NontrivialZetaZero.coe_ne_zero ρ)] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  calc
    analyticOrderAt riemannZeta ρ.1 =
        analyticOrderAt
          (fun z => completedRiemannZeta z * inverseGamma z) ρ.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt completedRiemannZeta ρ.1 +
        analyticOrderAt inverseGamma ρ.1 :=
      analyticOrderAt_mul
        (analyticAt_completedRiemannZeta_nontrivialZero ρ) hinverseAnalytic
    _ = analyticOrderAt completedRiemannZeta ρ.1 := by
      rw [hinverseOrder, add_zero]

theorem analyticOrderAt_riemannZeta_conjugate
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta (NontrivialZetaZero.conjugate ρ).1 =
      analyticOrderAt riemannZeta ρ.1 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannZeta_nontrivialZero
        (NontrivialZetaZero.conjugate ρ)),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannZeta_nontrivialZero ρ)]
  simp [iteratedDeriv_riemannZeta_conj]

theorem analyticOrderAt_riemannZeta_nontrivialZero_ne_top
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta ρ.1 ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[nhds ρ.1] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hpreconnected : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hglobal : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hpreconnected
        (by simpa using ρ.2.2.2) hlocal
  have hzetaTwo : riemannZeta (2 : ℂ) = 0 := by
    simpa using hglobal (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hzetaTwo

def IsPositiveZetaZeroMultiplicity
    (multiplicity : ZetaZeroMultiplicity) : Prop :=
  ∀ ρ, 0 < multiplicity ρ

theorem analyticZetaZeroMultiplicity_positive :
    IsPositiveZetaZeroMultiplicity analyticZetaZeroMultiplicity := by
  intro ρ
  change 0 < analyticOrderNatAt riemannZeta ρ.1
  have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
  have horder : analyticOrderAt riemannZeta ρ.1 ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨analyticAt_riemannZeta_nontrivialZero ρ, ρ.2.1⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  rw [hzero, Nat.cast_zero] at hcast
  exact horder hcast.symm

@[simp]
theorem analyticZetaZeroMultiplicity_conjugate
    (ρ : NontrivialZetaZero) :
    analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugate ρ) =
      analyticZetaZeroMultiplicity ρ := by
  unfold analyticZetaZeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_conjugate]

end

end RiemannGaussian

end


-- TH8000ZetaOccurrences
section

open Finset Complex Vx
open scoped ComplexConjugate Classical

namespace TH8000Zeta

private noncomputable def rgZero (c : V1o) : RiemannGaussian.NontrivialZetaZero := by
  refine ⟨c.val.1, c.property.1.2.2, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hnR := congrArg Complex.re hn
    simp [Complex.mul_re] at hnR
    linarith [Nat.cast_nonneg (α:=ℝ) n,c.property.1.1]
  · intro hone
    have h := c.property.1.2.1
    rw [hone] at h
    simp at h

private lemma same_multiplicity (c : V1o) :
    analyticOrderNatAt riemannZeta (conj c.val.1) = analyticOrderNatAt riemannZeta c.val.1 :=
  RiemannGaussian.analyticZetaZeroMultiplicity_conjugate (rgZero c)

theorem two_sided_count (T σ : ℝ) :
    ((V3b T).filter (fun c => σ ≤ c.val.1.re)).card ≤
      2*Sidon.zetaZeroCount σ T+(V3b 1).card := by
  let S := (V3b T).filter (fun c => σ ≤ c.val.1.re)
  let P := S.filter (fun c => 0 < c.val.1.im)
  let M := S.filter (fun c => c.val.1.im < 0)
  let Z := (Sidon.zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re)
  have hp : P.card ≤ Z.card := by
    apply card_le_card_of_injOn (fun (c : V1o) => c.val)
    · intro c hc
      obtain ⟨hcS,hpos⟩ := mem_filter.mp hc
      obtain ⟨ht,hre⟩ := mem_filter.mp hcS
      refine mem_filter.mpr ⟨Sidon.mem_zetaZeroOccurrences.mpr ⟨?_,c.property.2⟩,hre⟩
      have height := (V5l T c).mp ht
      rw [abs_of_pos hpos] at height
      exact Sidon.mem_criticalZetaZeros.mpr ⟨c.property.1.2.2, c.property.1.1.le,
        c.property.1.2.1.le,hpos,height⟩
    · intro a _ b _ h
      exact Subtype.ext h
  have hm : M.card ≤ Z.card := by
    apply card_le_card_of_injOn (fun (c : V1o) => (conj c.val.1,c.val.2))
    · intro c hc
      obtain ⟨hcS,hneg⟩ := mem_filter.mp hc
      obtain ⟨ht,hre⟩ := mem_filter.mp hcS
      refine mem_filter.mpr ⟨Sidon.mem_zetaZeroOccurrences.mpr ⟨?_,?_⟩,?_⟩
      · have height := (V5l T c).mp ht
        rw [abs_of_neg hneg] at height
        apply Sidon.mem_criticalZetaZeros.mpr
        simpa only [riemannZeta_conj,Complex.conj_im,Complex.conj_re,
          c.property.1.2.2,map_zero] using
          (show (0:ℂ)=0 ∧ 0 ≤ c.val.1.re ∧ c.val.1.re ≤ 1 ∧
            0 < -c.val.1.im ∧ -c.val.1.im ≤ T from
            ⟨rfl,c.property.1.1.le,c.property.1.2.1.le,neg_pos.mpr hneg,height⟩)
      · rw [same_multiplicity]
        exact c.property.2
      · simpa only [Complex.conj_re] using hre
    · intro a _ b _ he
      apply Subtype.ext
      apply Prod.ext
      · exact (starRingEnd ℂ).injective (congrArg Prod.fst he)
      · exact (Prod.mk.inj he).2
  have hcover : S ⊆ P ∪ M ∪ V3b 1 := by
    intro c hc
    rcases lt_trichotomy c.val.1.im 0 with hn | he | hp
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hc,hn⟩))
    · exact mem_union_right _ ((V5l 1 c).mpr (by rw [he]; norm_num))
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hc,hp⟩))
  change S.card ≤ 2*Z.card+(V3b 1).card
  have hh := (card_le_card hcover).trans (card_union_le ..)
  have hpm := card_union_le P M
  omega

theorem all_heights_zero_free (A : ℕ) :
    ∃ P : ℝ, ∀ X ≥ P, ∀ U : ℝ, U ≤ X^2 → ∀ c ∈ V3b U,
      c.val.1.re ≤ 1 - V1l.V2j A X := by
  obtain ⟨P,h⟩ := Vqx.Vwg A
  exact ⟨P,fun X hX U hU c hc => h X hX c (((V5l U c).mp hc).trans hU)⟩

end TH8000Zeta

end


-- Sidon.NumberTheory.JensenZeroOccurrences
section

noncomputable section

open Set MeasureTheory MeromorphicOn Metric Real

namespace Sidon

theorem jensen_detector_summand_nonneg (N : ℕ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall c |R|, z ≠ (1 : ℂ)) (z : ℂ) :
    0 ≤ (divisor (mollifierDetector N) (closedBall c |R|) z : ℝ) *
      Real.log (R * ‖c - z‖⁻¹) := by
  have hd : AnalyticOnNhd ℂ (mollifierDetector N) (closedBall c |R|) :=
    fun w hw => analyticAt_mollifierDetector N (hdisc w hw)
  by_cases hz : z ∈ closedBall c |R|
  · have hdiv : (0 : ℝ) ≤ divisor (mollifierDetector N) (closedBall c |R|) z := by
      exact_mod_cast hd.divisor_nonneg z
    by_cases hzero : ‖c - z‖ = 0
    · simp [hzero]
    · have hnorm : 0 < ‖c - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      have hbound : ‖c - z‖ ≤ R := by
        simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hz
      apply mul_nonneg hdiv
      rw [← div_eq_mul_inv]
      exact Real.log_nonneg ((one_le_div hnorm).mpr hbound)
  · simp [hz]

theorem zeta_jensen_weight_le_detector_summand (N : ℕ) {R y : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N (jensenCenter y) ≠ 0) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    (analyticOrderNatAt riemannZeta ρ : ℝ) * jensenVerticalWeight R ρ y ≤
      (divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|) ρ : ℝ) *
        Real.log (R * ‖jensenCenter y - ρ‖⁻¹) := by
  have hd : 0 < ‖jensenCenter y - ρ‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_jensenCenter_sub hρ y)
  by_cases hnorm : ‖jensenCenter y - ρ‖ ≤ R
  · have hmem : ρ ∈ closedBall (jensenCenter y) |R| := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hnorm
    have hζ : AnalyticOnNhd ℂ riemannZeta (closedBall (jensenCenter y) |R|) :=
      fun z hz => analyticOn_riemannZeta z (hdisc z hz)
    have horder : divisor riemannZeta (closedBall (jensenCenter y) |R|) ρ =
        (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      rw [hζ.divisor_apply hmem, ← Nat.cast_analyticOrderNatAt
        (analyticOrderAt_riemannZeta_ne_top ρ)]
      simp
    have hdom := zeta_divisor_le_mollifierDetector N hdisc hc ρ
    rw [horder] at hdom
    have hdomR : (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        (divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|) ρ : ℝ) := by
      exact_mod_cast hdom
    have hlog : 0 ≤ Real.log (R / ‖jensenCenter y - ρ‖) :=
      Real.log_nonneg ((one_le_div hd).mpr hnorm)
    have hw : jensenVerticalWeight R ρ y = Real.log (R / ‖jensenCenter y - ρ‖) := by
      rw [jensenVerticalWeight, ← Real.log_div hR.ne' hd.ne', max_eq_right hlog]
    rw [hw, ← div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hdomR hlog
  · have hnot : ρ ∉ closedBall (jensenCenter y) |R| := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hnorm
    have hlog : Real.log R - Real.log ‖jensenCenter y - ρ‖ ≤ 0 := by
      have hh := Real.log_le_log hR (le_of_lt (lt_of_not_ge hnorm))
      linarith
    simp [jensenVerticalWeight, max_eq_left hlog, hnot]

theorem sum_zeta_jensen_weight_le_detector (N : ℕ) (T : ℝ) {R y : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N (jensenCenter y) ≠ 0) :
    (∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y) ≤
      ∑ᶠ ρ, (divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|) ρ : ℝ) *
        Real.log (R * ‖jensenCenter y - ρ‖⁻¹) := by
  classical
  let D := divisor (mollifierDetector N) (closedBall (jensenCenter y) |R|)
  let q : ℂ → ℝ := fun ρ => (D ρ : ℝ) * Real.log (R * ‖jensenCenter y - ρ‖⁻¹)
  let U := criticalZetaZeros T ∪ (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hsupport : Function.support q ⊆ (U : Set ℂ) := by
    intro ρ hρ
    apply Finset.mem_union_right
    have hdρ : ρ ∈ D.support := by
      change D ρ ≠ 0
      intro hzero
      exact hρ (by simp [q, hzero])
    simpa only [Set.Finite.mem_toFinset] using hdρ
  change (∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y) ≤ ∑ᶠ ρ, q ρ
  rw [sum_zetaZeroOccurrences T (fun ρ => jensenVerticalWeight R ρ y),
    finsum_eq_finsetSum_of_support_subset q hsupport]
  calc
    _ ≤ ∑ ρ ∈ criticalZetaZeros T, q ρ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact zeta_jensen_weight_le_detector_summand N hR hdisc hc
        (mem_criticalZetaZeros.mp hρ).2.2.1
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro ρ _ _
      exact jensen_detector_summand_nonneg N hR hdisc ρ

theorem sum_zeta_jensen_weight_le_error (N : ℕ) (T : ℝ) {R y : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ))
    (hc : mollifierDetector N (jensenCenter y) ≠ 0) :
    (∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y) ≤
      circleAverage (fun z => ‖mollifierError N z‖ ^ 2) (jensenCenter y) R -
        Real.log ‖mollifierDetector N (jensenCenter y)‖ :=
  (sum_zeta_jensen_weight_le_detector N T hR hdisc hc).trans
    (jensen_mollifier_detector_le N hR.ne' hdisc hc)

end Sidon

end
end


-- Sidon.NumberTheory.MollifierCenter
section

noncomputable section

namespace Sidon

theorem norm_mollifierError_re_two_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : s.re = 2) :
    ‖mollifierError N s‖ ≤ 256 / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hf := LSeriesHasSum_balancedMollifierCoefficient (s := s) (by rw [hs]; norm_num) N
  have hterm (n : ℕ) : ‖LSeries.term (balancedMollifierCoefficient N) s n‖ ≤
      (1 / Real.sqrt N) * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    by_cases hnN : n ≤ N
    · have hz := balancedMollifierCoefficient_eq_zero hnN
      simp only [LSeries.term, hz, zero_div, ite_self, norm_zero]
      positivity
    · have hn : 0 < n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hrootle : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ n))
      have hd : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
        simpa only [pow_two] using
          (show (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) * n.divisors.card by
            exact_mod_cast Nat.le_mul_self n.divisors.card)
      have heq : (n : ℝ) ^ 2 = (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
        norm_num
      rw [LSeries.term, if_neg (by omega : n ≠ 0), norm_div,
        Complex.norm_natCast_cpow_of_pos hn, hs, Real.rpow_two]
      calc
        _ ≤ (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact (norm_balancedMollifierCoefficient_le hN n).trans hd
        _ ≤ (n.divisors.card : ℝ) ^ 2 /
            ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt N) := by
          rw [heq]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hrootle (Real.rpow_nonneg hn0.le _)
        _ = _ := by ring
  have hmajor := (summable_divisor_sq_div_rpow (σ := (3 / 2 : ℝ)) (by norm_num)).mul_left
    (1 / Real.sqrt N)
  calc
    _ = ‖∑' n : ℕ, LSeries.term (balancedMollifierCoefficient N) s n‖ := by rw [hf.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (balancedMollifierCoefficient N) s n‖ :=
      norm_tsum_le_tsum_norm hf.summable.norm
    _ ≤ ∑' n : ℕ, (1 / Real.sqrt N) *
        ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Summable.tsum_le_tsum hterm hf.summable.norm hmajor
    _ = (1 / Real.sqrt N) *
        ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ (1 / Real.sqrt N) * 256 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := tsum_divisor_sq_div_rpow_le_pole (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at hh
      exact hh
    _ = _ := by ring

theorem neg_log_norm_one_sub_sq_le {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 2) :
    1 - z ^ 2 ≠ 0 ∧ -Real.log ‖1 - z ^ 2‖ ≤ 2 * ‖z‖ ^ 2 := by
  let u := ‖z‖ ^ 2
  let a := ‖1 - z ^ 2‖
  have hu0 : 0 ≤ u := sq_nonneg _
  have ha : 1 - u ≤ a := by
    have hh := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    simpa only [norm_one, norm_pow] using hh
  have ha0 : 0 < a := by dsimp [u] at *; linarith
  have hlog := Real.one_sub_inv_le_log_of_pos ha0
  have hprod : 1 ≤ (1 + 2 * u) * a := by
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1 + 2 * u by positivity)
    have hh' := mul_nonneg hu0 (show 0 ≤ 1 - 2 * u by dsimp [u]; linarith)
    nlinarith
  have hinv : a⁻¹ ≤ 1 + 2 * u := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ ha0).mpr (by nlinarith)
  exact ⟨norm_pos_iff.mp ha0, by change -Real.log a ≤ 2 * u; linarith⟩

theorem mollifierDetector_center_bound {N : ℕ} (hN : 131072 ≤ N) {s : ℂ}
    (hs : s.re = 2) :
    mollifierDetector N s ≠ 0 ∧
      -Real.log ‖mollifierDetector N s‖ ≤ 131072 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlarge : (131072 : ℝ) ≤ N := by exact_mod_cast hN
  have herr := norm_mollifierError_re_two_le (by omega : 1 ≤ N) hs
  have hsq : ‖mollifierError N s‖ ^ 2 ≤ 65536 / (N : ℝ) := by
    have hh := sq_le_sq₀ (norm_nonneg (mollifierError N s))
      (show 0 ≤ 256 / Real.sqrt N by positivity) |>.mpr herr
    rw [div_pow, Real.sq_sqrt hNpos.le] at hh
    norm_num at hh ⊢
    exact hh
  have hhalf : ‖mollifierError N s‖ ^ 2 ≤ 1 / 2 := by
    apply hsq.trans
    exact (div_le_iff₀ hNpos).mpr (by linarith)
  obtain ⟨hne, hlog⟩ := neg_log_norm_one_sub_sq_le hhalf
  refine ⟨hne, hlog.trans ?_⟩
  calc
    2 * ‖mollifierError N s‖ ^ 2 ≤ 2 * (65536 / (N : ℝ)) := by gcongr
    _ = _ := by ring

end Sidon

end
end


-- Sidon.NumberTheory.JensenZeroDensity
section

noncomputable section

open Set MeasureTheory Metric Real

namespace Sidon

theorem jensen_disc_avoids_pole {R y : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 3 / 2)
    (hy : 3 ≤ y) : ∀ z ∈ closedBall (jensenCenter y) |R|, z ≠ (1 : ℂ) := by
  intro z hz he
  subst z
  have hh : ‖jensenCenter y - 1‖ ≤ R := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_nonneg hR] using hz
  have him := Complex.abs_im_le_norm (jensenCenter y - 1)
  have hi : (jensenCenter y - 1).im = y := by simp [jensenCenter]
  rw [hi] at him
  have hh' := (le_abs_self y).trans him
  linarith

theorem continuousOn_mollifierError_sq_rectangle (N : ℕ) (R T : ℝ) :
    ContinuousOn (fun z => ‖mollifierError N z‖ ^ 2) (verticalCircleRectangle R T) := by
  intro z hz
  have hz1 : z ≠ (1 : ℂ) := by
    intro he
    subst z
    have hh := hz.2.1
    norm_num at hh
  exact ((analyticAt_mollifierError N hz1).continuousAt.norm.pow 2).continuousWithinAt

theorem jensen_zero_occurrences_bound {N : ℕ} (hN : 131072 ≤ N)
    {σ δ T L : ℝ} (hσ0 : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hT : 3 ≤ T)
    (S : Finset (ℂ × ℕ)) (hS : S ⊆ zetaZeroOccurrences T)
    (hβ : ∀ z ∈ S, σ + δ ≤ z.1.re) (hγ : ∀ z ∈ S, 4 ≤ z.1.im)
    (hslice : ∀ u ∈ Icc σ (4 - σ),
      (∫ t in Icc 1 (T + 3), ‖mollifierError N ((u : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤ L) :
    (S.card : ℝ) * (2 * δ ^ 2 / 3) ≤ L + (T - 2) * (131072 / (N : ℝ)) := by
  let R : ℝ := 2 - σ
  let C : ℝ := 131072 / (N : ℝ)
  let F : ℂ → ℝ := fun z => ‖mollifierError N z‖ ^ 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R ≤ 3 / 2 := by dsimp [R]; linarith
  have hY : (3 : ℝ) ≤ T + 1 := by linarith
  have hF : ContinuousOn F (verticalCircleRectangle R T) :=
    continuousOn_mollifierError_sq_rectangle N R T
  have hiF := integrableOn_circleAverage_vertical hR.le hR1 hF
  have hiC : IntegrableOn (fun _ : ℝ => C) (Icc 3 (T + 1)) := integrable_const _
  have hws : Continuous (fun y : ℝ => ∑ z ∈ S, jensenVerticalWeight R z.1 y) := by
    apply continuous_finsetSum
    intro z hz
    exact continuous_jensenVerticalWeight R (zetaZeroOccurrences_re_bounds (hS hz)).2
  have hcount := card_mul_jensen_mass_le_integral S Prod.fst hσ0 hσ1 hδ0 hδ1 hβ
    (fun z hz => (zetaZeroOccurrences_re_bounds (hS hz)).2) hγ
    (fun z hz => (zetaZeroOccurrences_height_bounds (hS hz)).2)
  rw [intervalIntegral.integral_of_le hY, ← integral_Icc_eq_integral_Ioc] at hcount
  have hpoint (y : ℝ) (hy : y ∈ Icc 3 (T + 1)) :
      (∑ z ∈ S, jensenVerticalWeight R z.1 y) ≤
        circleAverage F (2 + (y : ℂ) * Complex.I) R + C := by
    have hc := mollifierDetector_center_bound hN (s := jensenCenter y)
      (by simp [jensenCenter])
    have hh := sum_zeta_jensen_weight_le_error N T hR
      (jensen_disc_avoids_pole hR.le hR1 hy.1) hc.1
    have hsubsum : (∑ z ∈ S, jensenVerticalWeight R z.1 y) ≤
        ∑ z ∈ zetaZeroOccurrences T, jensenVerticalWeight R z.1 y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun z _ _ => le_max_left 0 _)
    have hc' : -Real.log ‖mollifierDetector N (jensenCenter y)‖ ≤ C := hc.2
    change (∑ z ∈ S, jensenVerticalWeight R z.1 y) ≤
      circleAverage F (jensenCenter y) R + C
    exact hsubsum.trans (hh.trans (by dsimp [F]; linarith))
  have hcircle : (∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * Complex.I) R) ≤ L := by
    apply integral_circleAverage_vertical_le hR.le hR1 hT hF
      (fun z _ => sq_nonneg _)
    intro u hu
    apply hslice u
    simpa only [R, sub_sub_cancel, show (2 : ℝ) + (2 - σ) = 4 - σ by ring] using hu
  have hconst : (∫ _ in Icc (3 : ℝ) (T + 1), C) = (T - 2) * C := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  calc
    _ ≤ ∫ y in Icc 3 (T + 1), ∑ z ∈ S, jensenVerticalWeight R z.1 y := hcount
    _ ≤ ∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * Complex.I) R + C :=
      setIntegral_mono_on (hws.continuousOn.integrableOn_compact isCompact_Icc)
        (hiF.add hiC) measurableSet_Icc hpoint
    _ = (∫ y in Icc 3 (T + 1), circleAverage F (2 + (y : ℂ) * Complex.I) R) +
        (T - 2) * C := by rw [integral_add hiF hiC, hconst]
    _ ≤ _ := by dsimp [C]; linarith

end Sidon

end
end


-- Sidon.NumberTheory.RiemannGaussian.GaussianXiGrowth
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology
def riemannThetaTail (x : ℝ) : ℂ :=
  (HurwitzZeta.evenKernel 0 x : ℂ) - 1

theorem continuousOn_riemannThetaTail :
    ContinuousOn riemannThetaTail (Ioi 0) := by
  unfold riemannThetaTail
  exact (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_evenKernel 0)).sub continuousOn_const

theorem exists_riemannThetaTail_exp_bound :
    ∃ (C p : ℝ), 1 ≤ C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x) := by
  obtain ⟨p, hp, hbigO⟩ :=
    HurwitzZeta.isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  have hbigO' :
      riemannThetaTail =O[atTop] fun x : ℝ => Real.exp (-p * x) := by
    change (fun x : ℝ =>
      (HurwitzZeta.evenKernel 0 x : ℂ) - 1) =O[atTop]
        fun x : ℝ => Real.exp (-p * x)
    simpa using Complex.isBigO_ofReal_left.mpr hbigO
  obtain ⟨Ctop, hCtop⟩ := hbigO'.bound
  rw [eventually_atTop] at hCtop
  obtain ⟨a, ha⟩ := hCtop
  let M : ℝ := max 1 a
  have hM1 : 1 ≤ M := le_max_left _ _
  have haM : a ≤ M := le_max_right _ _
  have hcontinuous : ContinuousOn (fun x => ‖riemannThetaTail x‖)
      (Icc 1 M) := by
    exact (continuousOn_riemannThetaTail.mono
      (fun x hx => by exact hx.1.trans_lt' zero_lt_one)).norm
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc.bddAbove_image hcontinuous)
  let C : ℝ := max 1 (max Ctop (C₀ * Real.exp (p * M)))
  refine ⟨C, p, le_max_left _ _, hp, ?_⟩
  intro x hx
  by_cases hMx : M ≤ x
  · have hbound := ha x (haM.trans hMx)
    have hbound' :
        ‖riemannThetaTail x‖ ≤ Ctop * Real.exp (-p * x) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        using hbound
    have hCtopC : Ctop ≤ C :=
      (le_max_left Ctop (C₀ * Real.exp (p * M))).trans
        (le_max_right 1 _)
    exact hbound'.trans
      (mul_le_mul_of_nonneg_right hCtopC (Real.exp_nonneg _))
  · have hxM : x ≤ M := le_of_not_ge hMx
    have hnormC₀ : ‖riemannThetaTail x‖ ≤ C₀ := by
      apply hC₀
      exact ⟨x, ⟨hx, hxM⟩, rfl⟩
    have hC₀nonneg : 0 ≤ C₀ :=
      (norm_nonneg (riemannThetaTail x)).trans hnormC₀
    have hratio :
        C₀ ≤ (C₀ * Real.exp (p * M)) * Real.exp (-p * x) := by
      rw [mul_assoc, ← Real.exp_add]
      have hexp : 1 ≤ Real.exp (p * M + -p * x) := by
        rw [Real.one_le_exp_iff]
        nlinarith
      simpa using mul_le_mul_of_nonneg_left hexp hC₀nonneg
    have hcompactC : C₀ * Real.exp (p * M) ≤ C :=
      (le_max_right Ctop (C₀ * Real.exp (p * M))).trans
        (le_max_right 1 _)
    exact hnormC₀.trans <| hratio.trans <|
      mul_le_mul_of_nonneg_right hcompactC (Real.exp_nonneg _)

def riemannThetaUpper : ℝ → ℂ :=
  (Ioi 1).indicator riemannThetaTail

theorem riemannThetaUpper_eq_tail {x : ℝ} (hx : 1 < x) :
    riemannThetaUpper x = riemannThetaTail x := by
  simp [riemannThetaUpper, hx]

theorem riemannThetaUpper_eq_zero {x : ℝ} (hx : x ≤ 1) :
    riemannThetaUpper x = 0 := by
  simp [riemannThetaUpper, hx]

theorem riemann_f_modif_eq_upper_add_reflection (x : ℝ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
      riemannThetaUpper x +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) • riemannThetaUpper (1 / x) := by
  by_cases hx : 0 < x
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have hinv : 1 < 1 / x := by
        exact (one_lt_div hx).mpr hx1
      rw [riemannThetaUpper_eq_zero hx1.le,
        riemannThetaUpper_eq_tail hinv, zero_add]
      rw [WeakFEPair.f_modif, Pi.add_apply,
        Set.indicator_of_notMem (notMem_Ioi.mpr hx1.le), zero_add,
        Set.indicator_of_mem (mem_Ioo.mpr ⟨hx, hx1⟩)]
      simp only [HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply,
        ite_eq_left, one_mul]
      rw [HurwitzZeta.evenKernel_functional_equation]
      push_cast
      rw [Complex.ofReal_cpow hx.le, Complex.ofReal_div,
        Complex.ofReal_one]
      field_simp [hx.ne']
      rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
      unfold riemannThetaTail
      simp only [smul_eq_mul, mul_one]
      have hreal :
          x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hx]
        norm_num
      have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        norm_num
      have hcomplex :
          (x : ℂ) ^ (1 / 2 : ℂ) *
              ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
        rw [hhalf, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul,
          hreal, Complex.ofReal_one]
      have hcpow :
          (x : ℂ) ^ (1 / 2 : ℂ) *
              (x : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
        rw [← Complex.cpow_add _ _
          (Complex.ofReal_ne_zero.mpr hx.ne')]
        norm_num
      change (HurwitzZeta.evenKernel 0 (1 / x) : ℂ) -
          (x : ℂ) ^ (1 / 2 : ℂ) *
            ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (x : ℂ) ^ (1 / 2 : ℂ) *
          ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((HurwitzZeta.evenKernel 0 (1 / x) : ℂ) - 1))
      rw [hcomplex, ← mul_assoc, hcpow, one_mul]
    · simp [WeakFEPair.f_modif, riemannThetaUpper]
    · have hinv : 1 / x ≤ 1 := by
        exact (div_le_one hx).mpr hx1.le
      rw [riemannThetaUpper_eq_tail hx1,
        riemannThetaUpper_eq_zero hinv, smul_zero, add_zero]
      simp [WeakFEPair.f_modif, hx1,
        notMem_Ioo_of_ge hx1.le, riemannThetaTail,
        HurwitzZeta.hurwitzEvenFEPair]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hinv : 1 / x ≤ 1 := by
      by_cases hxzero : x = 0
      · simp [hxzero]
      · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
        exact (div_nonpos_of_nonneg_of_nonpos zero_le_one hxle).trans
          zero_le_one
    rw [riemannThetaUpper_eq_zero (hxle.trans zero_le_one),
      riemannThetaUpper_eq_zero hinv, smul_zero, add_zero]
    rw [WeakFEPair.f_modif, Pi.add_apply,
      Set.indicator_of_notMem
        (notMem_Ioi.mpr (hxle.trans zero_le_one)),
      Set.indicator_of_notMem (notMem_Ioo_of_le hxle)]
    simp

theorem locallyIntegrableOn_riemannThetaUpper :
    LocallyIntegrableOn riemannThetaUpper (Ioi 0) := by
  have htail : LocallyIntegrableOn riemannThetaTail (Ioi 0) :=
    continuousOn_riemannThetaTail.locallyIntegrableOn measurableSet_Ioi
  intro x hx
  obtain ⟨U, hU, hInt⟩ := htail x hx
  refine ⟨U, hU, ?_⟩
  simpa [riemannThetaUpper] using hInt.indicator measurableSet_Ioi

theorem exists_isBigO_riemannThetaUpper_exp :
    ∃ p : ℝ, 0 < p ∧
      riemannThetaUpper =O[atTop]
        fun x : ℝ => Real.exp (-p * x) := by
  obtain ⟨C, p, hC, hp, hbound⟩ :=
    exists_riemannThetaTail_exp_bound
  refine ⟨p, hp, IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [riemannThetaUpper_eq_tail hx]
  have h := hbound x hx.le
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h

theorem isBigO_riemannThetaUpper_nhdsGT_zero (b : ℝ) :
    riemannThetaUpper =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  apply IsBigO.of_bound 0
  filter_upwards [(eventually_le_nhds zero_lt_one).filter_mono
    nhdsWithin_le_nhds] with x hx
  rw [riemannThetaUpper_eq_zero hx]
  simp

theorem mellinConvergent_riemannThetaUpper (s : ℂ) :
    MellinConvergent riemannThetaUpper s := by
  obtain ⟨p, hp, htop⟩ := exists_isBigO_riemannThetaUpper_exp
  apply mellinConvergent_of_isBigO_rpow_exp hp
    locallyIntegrableOn_riemannThetaUpper htop
    (isBigO_riemannThetaUpper_nhdsGT_zero (s.re - 1))
  linarith

def riemannThetaReflection (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(1 / 2 : ℂ)) • riemannThetaUpper (1 / x)

theorem riemann_f_modif_eq_upper_add_reflection_fun :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif =
      riemannThetaUpper + riemannThetaReflection := by
  funext x
  exact riemann_f_modif_eq_upper_add_reflection x

theorem mellinConvergent_riemannThetaReflection (s : ℂ) :
    MellinConvergent riemannThetaReflection s := by
  let P := HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)
  have hfmodif : MellinConvergent P.f_modif s := by
    exact (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hupper := mellinConvergent_riemannThetaUpper s
  have hdifference :
      MellinConvergent (fun x => P.f_modif x - riemannThetaUpper x) s :=
    (hasMellin_sub hfmodif hupper).1
  have hreflection :
      riemannThetaReflection =
        fun x => P.f_modif x - riemannThetaUpper x := by
    funext x
    have hdecomp := riemann_f_modif_eq_upper_add_reflection x
    dsimp [P] at hdecomp ⊢
    rw [hdecomp]
    abel
  rw [hreflection]
  exact hdifference

theorem mellin_riemannThetaReflection (s : ℂ) :
    mellin riemannThetaReflection s =
      mellin riemannThetaUpper (1 / 2 - s) := by
  unfold riemannThetaReflection
  calc
    mellin
        (fun x : ℝ =>
          (x : ℂ) ^ (-(1 / 2 : ℂ)) •
            riemannThetaUpper (1 / x)) s =
        mellin (fun x : ℝ => riemannThetaUpper (1 / x))
          (s + -(1 / 2 : ℂ)) :=
      mellin_cpow_smul
        (fun x : ℝ => riemannThetaUpper (1 / x)) s
          (-(1 / 2 : ℂ))
    _ = mellin riemannThetaUpper (-(s + -(1 / 2 : ℂ))) := by
      simpa [one_div] using
        mellin_comp_inv riemannThetaUpper (s + -(1 / 2 : ℂ))
    _ = mellin riemannThetaUpper (1 / 2 - s) := by
      congr 2
      ring

theorem mellin_riemann_f_modif_eq_upper_add_reflected (s : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s =
      mellin riemannThetaUpper s +
        mellin riemannThetaUpper (1 / 2 - s) := by
  rw [riemann_f_modif_eq_upper_add_reflection_fun]
  change mellin
      (fun x => riemannThetaUpper x + riemannThetaReflection x) s = _
  rw [(hasMellin_add
    (mellinConvergent_riemannThetaUpper s)
    (mellinConvergent_riemannThetaReflection s)).2]
  rw [mellin_riemannThetaReflection]

set_option maxHeartbeats 2000000 in
theorem completedRiemannZeta₀_eq_upperMellin (s : ℂ) :
    completedRiemannZeta₀ s =
      (mellin riemannThetaUpper (s / 2) +
        mellin riemannThetaUpper ((1 - s) / 2)) / 2 := by
  change mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) / 2 = _
  rw [mellin_riemann_f_modif_eq_upper_add_reflected,
    show (1/2:ℂ) - s/2 = (1-s)/2 by ring]

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.GaussianXiMellinSubquadratic
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def mellinFourThirdsCost (p u : ℝ) : ℝ :=
  (4 * u / (2 * p) ^ (1 / 4 : ℝ)) ^ (4 / 3 : ℝ) / (4 / 3)

theorem holderConjugate_four_thirds_four :
    Real.HolderConjugate (4 / 3 : ℝ) 4 := by
  rw [Real.holderConjugate_iff]
  norm_num

theorem scaled_fourth_rpow_div_four
    {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    (((2 * p) ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) ^ (4 : ℝ)) / 4 =
      p * x / 2 := by
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg hx _)]
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul hx]
  norm_num
  ring

theorem four_mul_mul_rpow_quarter_le_mellinFourThirdsCost_add_half
    {p u x : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    4 * u * x ^ (1 / 4 : ℝ) ≤
      mellinFourThirdsCost p u + p * x / 2 := by
  let a : ℝ := 4 * u / (2 * p) ^ (1 / 4 : ℝ)
  let b : ℝ := (2 * p) ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hyoung :=
    Real.young_inequality_of_nonneg ha hb
      holderConjugate_four_thirds_four
  have hab : a * b = 4 * u * x ^ (1 / 4 : ℝ) := by
    dsimp [a, b]
    field_simp [ne_of_gt
      (Real.rpow_pos_of_pos (by positivity : 0 < 2 * p) _)]
  rw [hab] at hyoung
  dsimp [a, b] at hyoung
  rw [scaled_fourth_rpow_div_four hp hx] at hyoung
  simpa [mellinFourThirdsCost] using hyoung

theorem rpow_mul_exp_neg_le_exp_fourThirdsCost_mul_exp_neg_half_of_nonneg
    {p x u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (hx : 1 ≤ x) :
    x ^ u * Real.exp (-p * x) ≤
      Real.exp (mellinFourThirdsCost p u) *
        Real.exp (-(p / 2) * x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h :=
      Real.log_le_rpow_div hxpos.le
        (by norm_num : (0 : ℝ) < 1 / 4)
    calc
      Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4) := h
      _ = 4 * x ^ (1 / 4 : ℝ) := by ring
  have hulog : u * Real.log x ≤ 4 * u * x ^ (1 / 4 : ℝ) := by
    nlinarith
  have hyoung :=
    four_mul_mul_rpow_quarter_le_mellinFourThirdsCost_add_half
      hp hu hxpos.le
  have hexponent :
      u * Real.log x + (-p * x) ≤
        mellinFourThirdsCost p u + (-(p / 2) * x) := by
    nlinarith
  rw [Real.rpow_def_of_pos hxpos]
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hexponent)

theorem rpow_mul_exp_neg_le_exp_fourThirdsCost_posPart_mul_exp_neg_half
    {p x u : ℝ} (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ u * Real.exp (-p * x) ≤
      Real.exp (mellinFourThirdsCost p (max 0 u)) *
        Real.exp (-(p / 2) * x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have huMax : u ≤ max 0 u := le_max_right _ _
  have hpow : x ^ u ≤ x ^ max 0 u :=
    Real.rpow_le_rpow_of_exponent_le hx huMax
  calc
    x ^ u * Real.exp (-p * x) ≤
        x ^ max 0 u * Real.exp (-p * x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ ≤ Real.exp (mellinFourThirdsCost p (max 0 u)) *
        Real.exp (-(p / 2) * x) :=
      rpow_mul_exp_neg_le_exp_fourThirdsCost_mul_exp_neg_half_of_nonneg
        hp (le_max_left _ _) hx

theorem norm_mellin_riemannThetaUpper_le_fourThirds
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖mellin riemannThetaUpper s‖ ≤
      (2 * C / p) *
        Real.exp
          (mellinFourThirdsCost p (max 0 (s.re - 1))) := by
  let Q : ℝ := mellinFourThirdsCost p (max 0 (s.re - 1))
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hhalf : 0 < p / 2 := by positivity
  have hmajorant : IntegrableOn
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (Ioi 0) := by
    change Integrable
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (volume.restrict (Ioi 0))
    exact (exp_neg_integrableOn_Ioi 0 hhalf).const_mul
      (C * Real.exp Q)
  rw [mellin]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) • riemannThetaUpper x‖ ≤
        ∫ x : ℝ in Ioi 0,
          (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx0
      by_cases hx1 : x ≤ 1
      · rw [riemannThetaUpper_eq_zero hx1, smul_zero, norm_zero]
        positivity
      · have hx1' : 1 < x := lt_of_not_ge hx1
        rw [riemannThetaUpper_eq_tail hx1', norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re,
          Complex.one_re]
        calc
          x ^ (s.re - 1) * ‖riemannThetaTail x‖ ≤
              x ^ (s.re - 1) * (C * Real.exp (-p * x)) :=
            mul_le_mul_of_nonneg_left (hbound x hx1'.le)
              (Real.rpow_nonneg hx0.le _)
          _ = C * (x ^ (s.re - 1) * Real.exp (-p * x)) := by ring
          _ ≤ C *
              (Real.exp (mellinFourThirdsCost p (max 0 (s.re - 1))) *
                Real.exp (-(p / 2) * x)) :=
            mul_le_mul_of_nonneg_left
              (rpow_mul_exp_neg_le_exp_fourThirdsCost_posPart_mul_exp_neg_half
                hp hx1'.le) hC0
          _ = (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
            simp only [Q]
            ring
    _ = (C * Real.exp Q) * (2 / p) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(p / 2)) (by linarith) 0]
      simp
    _ = (2 * C / p) *
        Real.exp (mellinFourThirdsCost p (max 0 (s.re - 1))) := by
      simp only [Q]
      field_simp [hp.ne']

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian

noncomputable section

open Filter MeromorphicOn Metric Set Topology
def riemannXi (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1

@[simp]
theorem riemannXi_zero : riemannXi 0 = -1 := by
  simp [riemannXi]

@[simp]
theorem riemannXi_one : riemannXi 1 = -1 := by
  simp [riemannXi]

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  apply Differentiable.sub
  · apply Differentiable.mul
    · apply Differentiable.mul
      · exact differentiable_id
      · exact (differentiable_const (c := (1 : ℂ))).sub differentiable_id
    · exact differentiable_completedZeta₀
  · exact differentiable_const (c := (1 : ℂ))

theorem analyticOnNhd_riemannXi :
    AnalyticOnNhd ℂ riemannXi Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_riemannXi

theorem analyticAt_riemannXi (s : ℂ) :
    AnalyticAt ℂ riemannXi s :=
  differentiable_riemannXi.analyticAt s

theorem riemannXi_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (1 - s) * completedRiemannZeta s := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

theorem isNontrivialZetaZero_of_riemannXi_eq_zero
    {s : ℂ} (hxi : riemannXi s = 0) :
    IsNontrivialZetaZero s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hxi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hxi
  have hcompleted : completedRiemannZeta s = 0 := by
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
      mul_eq_zero] at hxi
    rcases hxi with hfactor | hcompleted
    · rcases mul_eq_zero.mp hfactor with hs | hs
      · exact (hs0 hs).elim
      · exact (hs1 (sub_eq_zero.mp hs).symm).elim
    · exact hcompleted
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]
  refine ⟨hzeta, ?_, hs1⟩
  rintro ⟨n, rfl⟩
  let w : ℂ := 1 - (-2 * ((n : ℂ) + 1))
  have hw0 : w ≠ 0 := by
    dsimp [w]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hpos : (0 : ℝ) < 1 + 2 * ((n : ℝ) + 1) := by positivity
    linarith
  have hwre : 1 ≤ w.re := by
    dsimp [w]
    norm_num
    positivity
  have hwcompleted : completedRiemannZeta w = 0 := by
    dsimp [w]
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have hwzeta : riemannZeta w = 0 := by
    rw [riemannZeta_def_of_ne_zero hw0, hwcompleted, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re hwre hwzeta

theorem riemannXi_eq_zero_of_isNontrivialZetaZero
    {s : ℂ} (hs : IsNontrivialZetaZero s) :
    riemannXi s = 0 := by
  let ρ : NontrivialZetaZero := ⟨s, hs⟩
  rw [riemannXi_eq_mul_completedRiemannZeta
    (NontrivialZetaZero.coe_ne_zero ρ) hs.2.2,
    NontrivialZetaZero.completedRiemannZeta_eq_zero, mul_zero]

theorem riemannXi_eq_zero_iff_isNontrivialZetaZero (s : ℂ) :
    riemannXi s = 0 ↔ IsNontrivialZetaZero s :=
  ⟨isNontrivialZetaZero_of_riemannXi_eq_zero,
    riemannXi_eq_zero_of_isNontrivialZetaZero⟩

theorem analyticOrderAt_riemannXi_eq_riemannZeta
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannXi ρ.1 =
      analyticOrderAt riemannZeta ρ.1 := by
  let factor : ℂ → ℂ := fun z => z * (1 - z)
  have hfactorAnalytic : AnalyticAt ℂ factor ρ.1 := by
    dsimp [factor]
    fun_prop
  have hfactorNe : factor ρ.1 ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero (NontrivialZetaZero.coe_ne_zero ρ)
      (sub_ne_zero.mpr ρ.2.2.2.symm)
  have hfactorOrder : analyticOrderAt factor ρ.1 = 0 :=
    hfactorAnalytic.analyticOrderAt_eq_zero.mpr hfactorNe
  have heq :
      riemannXi =ᶠ[nhds ρ.1]
        fun z => factor z * completedRiemannZeta z := by
    filter_upwards
      [eventually_ne_nhds (NontrivialZetaZero.coe_ne_zero ρ),
        eventually_ne_nhds ρ.2.2.2] with z hz0 hz1
    exact riemannXi_eq_mul_completedRiemannZeta hz0 hz1
  calc
    analyticOrderAt riemannXi ρ.1 =
        analyticOrderAt
          (fun z => factor z * completedRiemannZeta z) ρ.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt factor ρ.1 +
        analyticOrderAt completedRiemannZeta ρ.1 :=
      analyticOrderAt_mul hfactorAnalytic
        (analyticAt_completedRiemannZeta_nontrivialZero ρ)
    _ = analyticOrderAt completedRiemannZeta ρ.1 := by
      rw [hfactorOrder, zero_add]
    _ = analyticOrderAt riemannZeta ρ.1 :=
      (analyticOrderAt_riemannZeta_eq_completedRiemannZeta ρ).symm

theorem sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor
    {R : ℝ} (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ R) :
    ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) ≤
      ((∑ᶠ u, divisor riemannXi (closedBall 0 R) u : ℤ) : ℝ) := by
  classical
  let D := divisor riemannXi (closedBall (0 : ℂ) R)
  have hxiAnalytic :
      AnalyticOnNhd ℂ riemannXi (closedBall (0 : ℂ) R) :=
    analyticOnNhd_riemannXi.mono (subset_univ _)
  have hD (ρ : NontrivialZetaZero) (hρ : ρ ∈ S) :
      D ρ.1 = (analyticZetaZeroMultiplicity ρ : ℤ) := by
    have hmem : (ρ.1 : ℂ) ∈ closedBall (0 : ℂ) R := by
      simpa [mem_closedBall] using hS ρ hρ
    rw [show D ρ.1 = divisor riemannXi (closedBall (0 : ℂ) R) ρ.1 by rfl,
      hxiAnalytic.divisor_apply hmem,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
    rw [← Nat.cast_analyticOrderNatAt hfinite]
    simp [analyticZetaZeroMultiplicity]
  let T : Finset ℂ :=
    (D.finiteSupport (isCompact_closedBall (0 : ℂ) R)).toFinset
  have himage : S.image (fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)) ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρS, rfl⟩
    rw [Set.Finite.mem_toFinset]
    change D ρ.1 ≠ 0
    rw [hD ρ hρS]
    exact Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive ρ))
  calc
    ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) =
        ∑ z ∈ S.image (fun ρ : NontrivialZetaZero => (ρ.1 : ℂ)),
          (D z : ℝ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro ρ hρ
        rw [hD ρ hρ]
        norm_cast
      · intro ρ _ σ _ hρσ
        exact Subtype.ext hρσ
    _ ≤ ∑ z ∈ T, (D z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z _ _
      exact_mod_cast hxiAnalytic.divisor_nonneg z
    _ = ∑ᶠ z, (D z : ℝ) := by
      rw [finsum_eq_sum_of_support_subset]
      intro z hz
      change z ∈
        (D.finiteSupport (isCompact_closedBall (0 : ℂ) R)).toFinset
      apply (D.finiteSupport
        (isCompact_closedBall (0 : ℂ) R)).mem_toFinset.mpr
      change D z ≠ 0
      intro hDz
      apply hz
      simp [hDz]
    _ = ((∑ᶠ z, D z : ℤ) : ℝ) := by
      exact (map_finsum (Int.castRingHom ℝ)
        (D.finiteSupport (isCompact_closedBall (0 : ℂ) R))).symm

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticGrowth
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def mellinFourThirdsCoefficient (p : ℝ) : ℝ :=
  (4 / (2 * p) ^ (1 / 4 : ℝ)) ^ (4 / 3 : ℝ) / (4 / 3)

theorem mellinFourThirdsCost_eq_coefficient_mul_rpow
    {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) :
    mellinFourThirdsCost p u =
      mellinFourThirdsCoefficient p * u ^ (4 / 3 : ℝ) := by
  unfold mellinFourThirdsCost mellinFourThirdsCoefficient
  rw [show 4 * u / (2 * p) ^ (1 / 4 : ℝ) =
      (4 / (2 * p) ^ (1 / 4 : ℝ)) * u by ring]
  rw [Real.mul_rpow (by positivity) hu]
  ring

theorem mellinFourThirdsCoefficient_nonneg
    {p : ℝ} (hp : 0 < p) :
    0 ≤ mellinFourThirdsCoefficient p := by
  unfold mellinFourThirdsCoefficient
  positivity

theorem mellinFourThirdsCost_mono_of_nonneg
    {p u v : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (huv : u ≤ v) :
    mellinFourThirdsCost p u ≤ mellinFourThirdsCost p v := by
  have hv : 0 ≤ v := hu.trans huv
  rw [mellinFourThirdsCost_eq_coefficient_mul_rpow hp hu,
    mellinFourThirdsCost_eq_coefficient_mul_rpow hp hv]
  apply mul_le_mul_of_nonneg_left _
    (mellinFourThirdsCoefficient_nonneg hp)
  exact Real.rpow_le_rpow hu huv (by norm_num)

theorem norm_completedRiemannZeta₀_le_fourThirds
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤
      (2 * C / p) *
        Real.exp
          (mellinFourThirdsCoefficient p *
            (‖s‖ + 1) ^ (4 / 3 : ℝ)) := by
  let R : ℝ := ‖s‖ + 1
  let K : ℝ := 2 * C / p
  let B : ℝ := mellinFourThirdsCoefficient p
  let Q : ℝ := B * R ^ (4 / 3 : ℝ)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hfirstU : max 0 ((s / 2).re - 1) ≤ R := by
    apply max_le
    · exact hR0
    · have hre := Complex.abs_re_le_norm s
      norm_num
      dsimp [R]
      nlinarith [le_abs_self s.re]
  have hsecondU : max 0 (((1 - s) / 2).re - 1) ≤ R := by
    apply max_le
    · exact hR0
    · have hre := Complex.abs_re_le_norm s
      norm_num
      dsimp [R]
      nlinarith [neg_le_abs s.re]
  have hfirstCost :
      mellinFourThirdsCost p (max 0 ((s / 2).re - 1)) ≤ Q := by
    calc
      mellinFourThirdsCost p (max 0 ((s / 2).re - 1)) ≤
          mellinFourThirdsCost p R :=
        mellinFourThirdsCost_mono_of_nonneg hp (le_max_left _ _) hfirstU
      _ = Q := by
        rw [mellinFourThirdsCost_eq_coefficient_mul_rpow hp hR0]
  have hsecondCost :
      mellinFourThirdsCost p (max 0 (((1 - s) / 2).re - 1)) ≤ Q := by
    calc
      mellinFourThirdsCost p (max 0 (((1 - s) / 2).re - 1)) ≤
          mellinFourThirdsCost p R :=
        mellinFourThirdsCost_mono_of_nonneg hp (le_max_left _ _) hsecondU
      _ = Q := by
        rw [mellinFourThirdsCost_eq_coefficient_mul_rpow hp hR0]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hfirst :
      ‖mellin riemannThetaUpper (s / 2)‖ ≤ K * Real.exp Q := by
    calc
      ‖mellin riemannThetaUpper (s / 2)‖ ≤
          K * Real.exp
            (mellinFourThirdsCost p (max 0 ((s / 2).re - 1))) :=
        norm_mellin_riemannThetaUpper_le_fourThirds hC hp hbound (s / 2)
      _ ≤ K * Real.exp Q :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hfirstCost) hK0
  have hsecond :
      ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤ K * Real.exp Q := by
    calc
      ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤
          K * Real.exp
            (mellinFourThirdsCost p
              (max 0 (((1 - s) / 2).re - 1))) :=
        norm_mellin_riemannThetaUpper_le_fourThirds
          hC hp hbound ((1 - s) / 2)
      _ ≤ K * Real.exp Q :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hsecondCost) hK0
  rw [completedRiemannZeta₀_eq_upperMellin, norm_div]
  norm_num
  calc
    ‖mellin riemannThetaUpper (s / 2) +
        mellin riemannThetaUpper ((1 - s) / 2)‖ / 2 ≤
        (‖mellin riemannThetaUpper (s / 2)‖ +
          ‖mellin riemannThetaUpper ((1 - s) / 2)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (K * Real.exp Q + K * Real.exp Q) / 2 := by gcongr
    _ = (2 * C / p) *
        Real.exp
          (mellinFourThirdsCoefficient p *
            (‖s‖ + 1) ^ (4 / 3 : ℝ)) := by
      simp only [K, Q, B, R]
      ring

def RiemannXiThreeHalvesGrowth : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
    ‖riemannXi z‖ ≤
      Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))

theorem riemannXi_threeHalvesGrowth : RiemannXiThreeHalvesGrowth := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  let K : ℝ := max 1 (2 * C / p)
  let B : ℝ := mellinFourThirdsCoefficient p
  let A : ℝ := K + B + 4
  have hrawK0 : 0 ≤ 2 * C / p := by positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hrawK_le : 2 * C / p ≤ K := le_max_right _ _
  have hB0 : 0 ≤ B := mellinFourThirdsCoefficient_nonneg hp
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA1, ?_⟩
  intro z
  let R : ℝ := ‖z‖ + 1
  let U : ℝ := R ^ (4 / 3 : ℝ)
  let T : ℝ := R ^ (3 / 2 : ℝ)
  let E : ℝ := Real.exp (B * U)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hT1 : 1 ≤ T := by
    dsimp [T]
    calc
      (1 : ℝ) = 1 ^ (3 / 2 : ℝ) := by norm_num
      _ ≤ R ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hR1 (by norm_num)
  have hRleT : R ≤ T := by
    dsimp [T]
    calc
      R = R ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ R ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hUleT : U ≤ T := by
    dsimp [U, T]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hcompleted : ‖completedRiemannZeta₀ z‖ ≤ K * E := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * C / p) *
            Real.exp
              (mellinFourThirdsCoefficient p *
                (‖z‖ + 1) ^ (4 / 3 : ℝ)) :=
        norm_completedRiemannZeta₀_le_fourThirds hC hp htail z
      _ = (2 * C / p) * E := by simp only [B, E, U, R]
      _ ≤ K * E :=
        mul_le_mul_of_nonneg_right hrawK_le (Real.exp_nonneg _)
  have honeSub : ‖1 - z‖ ≤ R := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = R := by simp [R, add_comm]
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    linarith
  have hpoly : ‖z‖ * ‖1 - z‖ ≤ R ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hzR honeSub (norm_nonneg _) hR0
  have hmain :
      ‖z * (1 - z) * completedRiemannZeta₀ z‖ ≤ K * R ^ 2 * E := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖1 - z‖ * ‖completedRiemannZeta₀ z‖ ≤
          R ^ 2 * (K * E) :=
        mul_le_mul hpoly hcompleted (norm_nonneg _) (sq_nonneg R)
      _ = K * R ^ 2 * E := by ring
  have hRexp : R ≤ Real.exp R := by
    linarith [Real.add_one_le_exp R]
  have hRsqExp : R ^ 2 ≤ Real.exp (2 * R) := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ Real.exp R * Real.exp R :=
        mul_le_mul hRexp hRexp hR0 (Real.exp_nonneg _)
      _ = Real.exp (2 * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have hKExp : K ≤ Real.exp K := by
    linarith [Real.add_one_le_exp K]
  have hexponent : 1 + K + 2 * R + B * U ≤ A * T := by
    have hnonneg : 0 ≤ (K + B + 3) * (T - 1) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [A]
    nlinarith
  have habsorb : 2 * (K * R ^ 2 * E) ≤ Real.exp (A * T) := by
    calc
      2 * (K * R ^ 2 * E) = 2 * K * R ^ 2 * E := by ring
      _ ≤ Real.exp 1 * Real.exp K * Real.exp (2 * R) * E := by
        gcongr
      _ = Real.exp (1 + K + 2 * R + B * U) := by
        simp only [E, ← Real.exp_add]
      _ ≤ Real.exp (A * T) := Real.exp_le_exp.mpr hexponent
  unfold riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ K * R ^ 2 * E + 1 := by
      simpa using add_le_add_right hmain 1
    _ ≤ 2 * (K * R ^ 2 * E) := by
      have hKRE1 : 1 ≤ K * R ^ 2 * E := by
        have hRtwo : 1 ≤ R ^ 2 := by nlinarith
        have hE1 : 1 ≤ E := by
          dsimp [E]
          rw [Real.one_le_exp_iff]
          exact mul_nonneg hB0 (Real.rpow_nonneg hR0 _)
        exact one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hK1 hRtwo) hE1
      linarith
    _ ≤ Real.exp (A * T) := habsorb
    _ = Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)) := by rfl

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticCounting
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian

noncomputable section

open MeromorphicOn Metric Set
theorem jensen_riemannXi_divisor_le_threeHalves
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * (2 * r + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hM :
      1 ≤ Real.exp (A * (2 * r + 1) ^ (3 / 2 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (le_trans (by norm_num) hA)
      (Real.rpow_nonneg (by positivity) _)
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * (2 * r + 1) ^ (3 / 2 : ℝ)))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

end

end RiemannGaussian

end


-- Sidon.NumberTheory.ZetaCrudeCount
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/

noncomputable section

open RiemannGaussian MeromorphicOn Metric Set

namespace Sidon

def RiemannXiFourThirdsGrowth : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
    ‖riemannXi z‖ ≤
      Real.exp (A * (‖z‖ + 1) ^ (4 / 3 : ℝ))

theorem riemannXi_fourThirdsGrowth : RiemannXiFourThirdsGrowth := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  let K : ℝ := max 1 (2 * C / p)
  let B : ℝ := mellinFourThirdsCoefficient p
  let A : ℝ := K + B + 4
  have hrawK0 : 0 ≤ 2 * C / p := by positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hrawK_le : 2 * C / p ≤ K := le_max_right _ _
  have hB0 : 0 ≤ B := mellinFourThirdsCoefficient_nonneg hp
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA1, ?_⟩
  intro z
  let R : ℝ := ‖z‖ + 1
  let U : ℝ := R ^ (4 / 3 : ℝ)
  let T : ℝ := R ^ (4 / 3 : ℝ)
  let E : ℝ := Real.exp (B * U)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hT1 : 1 ≤ T := by
    dsimp [T]
    calc
      (1 : ℝ) = 1 ^ (4 / 3 : ℝ) := by norm_num
      _ ≤ R ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hR1 (by norm_num)
  have hRleT : R ≤ T := by
    dsimp [T]
    calc
      R = R ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ R ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hUleT : U ≤ T := by
    dsimp [U, T]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hcompleted : ‖completedRiemannZeta₀ z‖ ≤ K * E := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * C / p) *
            Real.exp
              (mellinFourThirdsCoefficient p *
                (‖z‖ + 1) ^ (4 / 3 : ℝ)) :=
        norm_completedRiemannZeta₀_le_fourThirds hC hp htail z
      _ = (2 * C / p) * E := by simp only [B, E, U, R]
      _ ≤ K * E :=
        mul_le_mul_of_nonneg_right hrawK_le (Real.exp_nonneg _)
  have honeSub : ‖1 - z‖ ≤ R := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = R := by simp [R, add_comm]
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    linarith
  have hpoly : ‖z‖ * ‖1 - z‖ ≤ R ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hzR honeSub (norm_nonneg _) hR0
  have hmain :
      ‖z * (1 - z) * completedRiemannZeta₀ z‖ ≤ K * R ^ 2 * E := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖1 - z‖ * ‖completedRiemannZeta₀ z‖ ≤
          R ^ 2 * (K * E) :=
        mul_le_mul hpoly hcompleted (norm_nonneg _) (sq_nonneg R)
      _ = K * R ^ 2 * E := by ring
  have hRexp : R ≤ Real.exp R := by
    linarith [Real.add_one_le_exp R]
  have hRsqExp : R ^ 2 ≤ Real.exp (2 * R) := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ Real.exp R * Real.exp R :=
        mul_le_mul hRexp hRexp hR0 (Real.exp_nonneg _)
      _ = Real.exp (2 * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have hKExp : K ≤ Real.exp K := by
    linarith [Real.add_one_le_exp K]
  have hexponent : 1 + K + 2 * R + B * U ≤ A * T := by
    have hnonneg : 0 ≤ (K + B + 3) * (T - 1) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [A]
    nlinarith
  have habsorb : 2 * (K * R ^ 2 * E) ≤ Real.exp (A * T) := by
    calc
      2 * (K * R ^ 2 * E) = 2 * K * R ^ 2 * E := by ring
      _ ≤ Real.exp 1 * Real.exp K * Real.exp (2 * R) * E := by
        gcongr
      _ = Real.exp (1 + K + 2 * R + B * U) := by
        simp only [E, ← Real.exp_add]
      _ ≤ Real.exp (A * T) := Real.exp_le_exp.mpr hexponent
  unfold riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ K * R ^ 2 * E + 1 := by
      simpa using add_le_add_right hmain 1
    _ ≤ 2 * (K * R ^ 2 * E) := by
      have hKRE1 : 1 ≤ K * R ^ 2 * E := by
        have hRtwo : 1 ≤ R ^ 2 := by nlinarith
        have hE1 : 1 ≤ E := by
          dsimp [E]
          rw [Real.one_le_exp_iff]
          exact mul_nonneg hB0 (Real.rpow_nonneg hR0 _)
        exact one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hK1 hRtwo) hE1
      linarith
    _ ≤ Real.exp (A * T) := habsorb
    _ = Real.exp (A * (‖z‖ + 1) ^ (4 / 3 : ℝ)) := by rfl

theorem jensen_riemannXi_divisor_le_fourThirds
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (4 / 3 : ℝ))) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * (2 * r + 1) ^ (4 / 3 : ℝ) / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hM :
      1 ≤ Real.exp (A * (2 * r + 1) ^ (4 / 3 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (le_trans (by norm_num) hA)
      (Real.rpow_nonneg (by positivity) _)
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * (2 * r + 1) ^ (4 / 3 : ℝ)))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

theorem isNontrivialZetaZero_of_mem_criticalZetaZeros {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ criticalZetaZeros T) : IsNontrivialZetaZero ρ := by
  obtain ⟨hzero, _, _, him, _⟩ := mem_criticalZetaZeros.mp hρ
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hh := congrArg Complex.im hn
    norm_num at hh
    linarith
  · intro hn
    have hh := congrArg Complex.im hn
    norm_num at hh
    linarith

theorem card_zetaZeroOccurrences (T : ℝ) :
    (zetaZeroOccurrences T).card =
      ∑ ρ ∈ criticalZetaZeros T, analyticOrderNatAt riemannZeta ρ := by
  classical
  unfold zetaZeroOccurrences
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro j k h
      exact (Prod.mk.inj h).2
  · intro ρ _ τ _ hne
    apply Finset.disjoint_left.mpr
    intro z hzρ hzτ
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzρ
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hzτ
    exact hne (congrArg Prod.fst (hj.trans hk.symm))

theorem zetaZeroCount_zero (T : ℝ) :
    zetaZeroCount 0 T = (zetaZeroOccurrences T).card := by
  unfold zetaZeroCount
  congr 1
  exact Finset.filter_true_of_mem fun z hz => (zetaZeroOccurrences_re_bounds hz).1

theorem zetaZeroCount_zero_le_riemannXi_divisor (T : ℝ) :
    (zetaZeroCount 0 T : ℝ) ≤
      ((∑ᶠ u, divisor riemannXi (closedBall 0 (T + 2)) u : ℤ) : ℝ) := by
  classical
  let S := (criticalZetaZeros T).subtype IsNontrivialZetaZero
  have hS : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ T + 2 := by
    intro ρ hρ
    have hmem : ρ.1 ∈ criticalZetaZeros T := (Finset.mem_subtype.mp hρ)
    obtain ⟨_, hre0, hre1, him0, himT⟩ := mem_criticalZetaZeros.mp hmem
    calc
      ‖(ρ.1 : ℂ)‖ ≤ |ρ.1.re| + |ρ.1.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ T + 2 := by
        rw [abs_of_nonneg hre0, abs_of_nonneg him0.le]
        linarith
  have hsum :
      ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) =
        (zetaZeroCount 0 T : ℝ) := by
    rw [zetaZeroCount_zero, card_zetaZeroOccurrences, Nat.cast_sum]
    exact Finset.sum_subtype_of_mem
      (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
      (fun _ hρ => isNontrivialZetaZero_of_mem_criticalZetaZeros hρ)
  rw [← hsum]
  exact sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor S hS

theorem zetaZeroCount_zero_le_fourThirds :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (zetaZeroCount 0 T : ℝ) ≤ C * T ^ (4 / 3 : ℝ) := by
  obtain ⟨A, hA, hgrowth⟩ := riemannXi_fourThirdsGrowth
  refine ⟨A * 7 ^ (4 / 3 : ℝ) / Real.log 2, by positivity, ?_⟩
  intro T hT
  have hcount := (zetaZeroCount_zero_le_riemannXi_divisor T).trans
    (jensen_riemannXi_divisor_le_fourThirds hA (by linarith : 0 < T + 2) hgrowth)
  calc
    (zetaZeroCount 0 T : ℝ) ≤
        A * (2 * (T + 2) + 1) ^ (4 / 3 : ℝ) / Real.log 2 := hcount
    _ ≤ A * (7 * T) ^ (4 / 3 : ℝ) / Real.log 2 := by
      gcongr
      linarith
    _ = (A * 7 ^ (4 / 3 : ℝ) / Real.log 2) * T ^ (4 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ T)]
      ring

theorem zetaZeroCount_le_fourThirds :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ σ : ℝ, 0 ≤ σ →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (4 / 3 : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := zetaZeroCount_zero_le_fourThirds
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  exact (Nat.cast_le.mpr (zetaZeroCount_antitone T hσ)).trans (hcount T hT)

theorem zetaZeroCount_le_fourThirds_add_one :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ σ : ℝ, 0 ≤ σ →
      (zetaZeroCount σ T : ℝ) ≤ C * (T + 1) ^ (4 / 3 : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := zetaZeroCount_le_fourThirds
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  exact (Nat.cast_le.mpr (zetaZeroCount_mono_height σ (by linarith : T ≤ T + 1))).trans
    (hcount (T + 1) (by linarith) σ hσ)

end Sidon

end
end


-- Sidon.NumberTheory.InghamDensity
section

noncomputable section

open Set MeasureTheory Real

namespace Sidon

theorem rpow_logarithmic_shift {T : ℝ} (hT : 1 < T) (a σ : ℝ) :
    T ^ (a * (1 - (σ - 1 / Real.log T))) =
      Real.exp a * T ^ (a * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem crude_rpow_le_density_scale {T σ A : ℝ} (hT : 1 < T)
    (hA : (8 / 3 : ℝ) ≤ A) (hσ : σ ≤ 1 / 2 + 1 / Real.log T) :
    T ^ (4 / 3 : ℝ) ≤ Real.exp A * T ^ (A * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hσ' := mul_le_mul_of_nonneg_right hσ hlog.le
  rw [add_mul, div_mul_cancel₀ _ hlog.ne'] at hσ'
  have hA0 : 0 ≤ A := by linarith
  have hh := mul_le_mul_of_nonneg_left hσ' hA0
  have hhalf := mul_le_mul_of_nonneg_right hA hlog.le
  rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem jensen_center_loss_le {N : ℕ} {T : ℝ} (hT : 0 < T) (hN : T ≤ N) :
    (T - 2) * (131072 / (N : ℝ)) ≤ 131072 := by
  have hN0 : (0 : ℝ) < N := hT.trans_le hN
  calc
    _ ≤ (N : ℝ) * (131072 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

theorem exists_uniformZeroDensity_of_mollifier_slices {K T₀ : ℝ} (hK : 0 < K)
    (hslices : ∀ T : ℝ, T₀ ≤ T → ∀ σ₀ : ℝ, (1 / 2 : ℝ) ≤ σ₀ → σ₀ ≤ 1 →
      ∃ N : ℕ, 131072 ≤ N ∧ T ≤ (N : ℝ) ∧
        ∀ u ∈ Icc σ₀ (4 - σ₀),
          (∫ t in Icc 1 (T + 3), ‖mollifierError N ((u : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
            K * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) * (Real.log T) ^ 9) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : ℝ, UniformZetaZeroDensity (23 / 8) 11 C U := by
  obtain ⟨D, hD, hcrude⟩ := zetaZeroCount_zero_le_fourThirds
  let Z : ℝ := zetaZeroCount 0 4
  let H : ℝ := Z + 2 * (K * Real.exp (11 / 4) + 131072)
  let C : ℝ := D * Real.exp (23 / 8) + H
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max T₀ (Real.exp 4), ?_⟩
  intro T hT σ hσ0 hσ1
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hexp : Real.exp 4 ≤ T := (le_max_right _ _).trans hT
  have hexp5 : (5 : ℝ) ≤ Real.exp 4 := by
    have hh := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hT1 : 1 < T := by linarith
  have hTpos : 0 < T := by linarith
  have hT3 : 3 ≤ T := by linarith
  have hlog : 4 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 4) hexp
    simpa only [Real.log_exp] using hh
  let ℓ := Real.log T
  let ε : ℝ := 1 / ℓ
  let X : ℝ := T ^ ((23 / 8 : ℝ) * (1 - σ))
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith
  have hℓpos : 0 < ℓ := by linarith
  have hε : 0 < ε := one_div_pos.mpr hℓpos
  have hεquarter : ε ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) hlog
  have hX : 1 ≤ X := Real.one_le_rpow hT1.le (by nlinarith)
  have hℓ9 : 1 ≤ ℓ ^ 9 := one_le_pow₀ hℓ
  have hℓ11 : 1 ≤ ℓ ^ 11 := one_le_pow₀ hℓ
  have hscale : 1 ≤ X * ℓ ^ 11 := one_le_mul_of_one_le_of_one_le hX hℓ11
  by_cases hlow : σ ≤ 1 / 2 + ε
  · have hc0 : (zetaZeroCount σ T : ℝ) ≤ D * T ^ (4 / 3 : ℝ) := by
      exact (Nat.cast_le.mpr (zetaZeroCount_antitone T hσ0)).trans (hcrude T hT1.le)
    have hp := crude_rpow_le_density_scale hT1 (A := 23 / 8) (by norm_num) hlow
    calc
      _ ≤ D * T ^ (4 / 3 : ℝ) := hc0
      _ ≤ D * (Real.exp (23 / 8) * X) := mul_le_mul_of_nonneg_left hp hD.le
      _ ≤ C * X * ℓ ^ 11 := by
        have hDC : D * Real.exp (23 / 8) ≤ C := by dsimp [C]; linarith
        calc
          _ = (D * Real.exp (23 / 8)) * X := by ring
          _ ≤ C * X := mul_le_mul_of_nonneg_right hDC (by positivity)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hℓ11
  · let σ₀ : ℝ := σ - ε
    have hσ₀ : (1 / 2 : ℝ) ≤ σ₀ := by dsimp [σ₀]; linarith
    have hσ₀1 : σ₀ ≤ 1 := by dsimp [σ₀]; linarith
    obtain ⟨N, hN, hNT, hslice⟩ := hslices T hT₀ σ₀ hσ₀ hσ₀1
    let S := (zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re ∧ 4 ≤ z.1.im)
    have hmass := jensen_zero_occurrences_bound hN hσ₀ hσ₀1 hε.le hεquarter hT3 S
      (Finset.filter_subset _ _) (fun z hz => by
        have hh := (Finset.mem_filter.mp hz).2.1
        simpa only [σ₀, sub_add_cancel] using hh)
      (fun z hz => (Finset.mem_filter.mp hz).2.2) hslice
    have hpower : T ^ ((11 / 4 : ℝ) * (1 - σ₀)) ≤ Real.exp (11 / 4) * X := by
      rw [rpow_logarithmic_shift hT1]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      nlinarith
    have hmajor : (S.card : ℝ) * (2 * ε ^ 2 / 3) ≤
        K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072 := by
      apply hmass.trans
      apply add_le_add
      · have hh := mul_le_mul_of_nonneg_left hpower hK.le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (pow_nonneg hℓpos.le 9)
      · exact jensen_center_loss_le hTpos hNT
    have hidentity : (S.card : ℝ) = (3 / 2 : ℝ) * ℓ ^ 2 *
        ((S.card : ℝ) * (2 * ε ^ 2 / 3)) := by
      dsimp [ε]
      field_simp
    have hcard : (S.card : ℝ) ≤ 2 * ℓ ^ 2 *
        (K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072) := by
      calc
        _ = _ := hidentity
        _ ≤ (3 / 2 : ℝ) * ℓ ^ 2 *
            (K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072) :=
          mul_le_mul_of_nonneg_left hmajor (by positivity)
        _ ≤ _ := by gcongr; norm_num
    have hcount : (zetaZeroCount σ T : ℝ) ≤ Z + (S.card : ℝ) := by
      dsimp [Z, S]
      exact_mod_cast zetaZeroCount_le_low_add_high σ T
    have hℓ2 : ℓ ^ 2 ≤ X * ℓ ^ 11 := by
      have hp : ℓ ^ 11 = ℓ ^ 2 * ℓ ^ 9 := by ring
      rw [hp]
      have hh := mul_le_mul_of_nonneg_left hℓ9 (sq_nonneg ℓ)
      nlinarith
    have hZscale : Z ≤ Z * X * ℓ ^ 11 := by nlinarith
    have hHle : H ≤ C := by
      dsimp [C]
      have hh : 0 ≤ D * Real.exp (23 / 8) := by positivity
      linarith
    calc
      _ ≤ Z + (S.card : ℝ) := hcount
      _ ≤ Z + 2 * ℓ ^ 2 * (K * Real.exp (11 / 4) * X * ℓ ^ 9 + 131072) := by
        linarith
      _ = Z + 2 * (K * Real.exp (11 / 4)) * X * ℓ ^ 11 + 262144 * ℓ ^ 2 := by ring
      _ ≤ Z * X * ℓ ^ 11 + 2 * (K * Real.exp (11 / 4)) * X * ℓ ^ 11 +
          262144 * (X * ℓ ^ 11) := by linarith
      _ = H * X * ℓ ^ 11 := by dsimp [H]; ring
      _ ≤ C * X * ℓ ^ 11 := by gcongr

end Sidon

end
end


-- Sidon.NumberTheory.MollifierSymmetry
section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

theorem dirichletMollifier_conj (N : ℕ) (s : ℂ) :
    dirichletMollifier N (conj s) = conj (dirichletMollifier N s) := by
  simp only [dirichletMollifier, map_sum, map_mul, map_intCast,
    ← Complex.exp_conj, map_neg, Complex.conj_ofReal]

theorem mollifierError_conj (N : ℕ) (s : ℂ) :
    mollifierError N (conj s) = conj (mollifierError N s) := by
  simp only [mollifierError, riemannZeta_conj, dirichletMollifier_conj,
    map_sub, map_mul, map_one]

theorem norm_mollifierError_vertical_neg (N : ℕ) (σ t : ℝ) :
    ‖mollifierError N ((σ : ℂ) + (-t : ℝ) * Complex.I)‖ =
      ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ := by
  have heq : (σ : ℂ) + (-t : ℝ) * Complex.I =
      conj ((σ : ℂ) + t * Complex.I) := by simp
  rw [heq, mollifierError_conj, Complex.norm_conj]

theorem continuous_mollifierError_vertical (N : ℕ) {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun t : ℝ => mollifierError N ((σ : ℂ) + t * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (analyticAt_mollifierError N ?_).continuousAt.comp (by fun_prop)
  intro heq
  have hh := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.one_re] at hh
  exact hσ hh

theorem integral_neg_pos_eq_two_of_even {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ t, f (-t) = f t) (T : ℝ) :
    (∫ t in -T..T, f t) = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have hneg : (∫ t in -T..(0 : ℝ), f t) = ∫ t in (0 : ℝ)..T, f t := by
    have hh := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := T)
    simpa only [heven, neg_zero] using hh.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-T) 0)
    (hf.intervalIntegrable 0 T), hneg]
  ring

theorem integral_mollifierError_right_symmetric_le {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in Set.Icc (-T) T,
      ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
      4096 * (T / (N : ℝ) + 1) / δ ^ 8 := by
  have hc := (continuous_mollifierError_vertical N (σ := 1 + δ) (by linarith)).norm.pow 2
  have heven : ∀ t : ℝ,
      ‖mollifierError N ((1 + δ : ℝ) + (-t : ℝ) * Complex.I)‖ ^ 2 =
        ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2 := by
    intro t
    rw [norm_mollifierError_vertical_neg]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    integral_neg_pos_eq_two_of_even (f := fun t =>
      ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) hc heven]
  have hh := integral_mollifierError_right_norm_sq_le_simple hN hδ hδ1 hT
  calc
    _ ≤ 2 * (2048 * (T / (N : ℝ) + 1) / δ ^ 8) := by gcongr
    _ = _ := by ring

end Sidon

end
end


-- Sidon.NumberTheory.RiemannGaussian.EtaZetaMultiplicitySchwarz
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem riemannZeta₁_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp [sub_ne_zero.mpr hs]

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEta
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

lemma pairedEtaCoreSummand_conj (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand ((starRingEnd ℂ) s) n =
      (starRingEnd ℂ) (pairedEtaCoreSummand s n) := by
  unfold pairedEtaCoreSummand
  rw [map_sub]
  congr 1
  · simpa only [map_neg, Complex.conj_ofReal] using
      (Complex.cpow_conj
        ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) (-s)
        (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]
          exact Real.pi_ne_zero.symm))
  · simpa only [map_neg, Complex.conj_ofReal] using
      (Complex.cpow_conj
        ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) (-s)
        (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]
          exact Real.pi_ne_zero.symm))

lemma pairedEtaCore_conj (s : ℂ) :
    pairedEtaCore ((starRingEnd ℂ) s) = (starRingEnd ℂ) (pairedEtaCore s) := by
  unfold pairedEtaCore
  calc
    ∑' n : ℕ, pairedEtaCoreSummand ((starRingEnd ℂ) s) n =
        ∑' n : ℕ, (starRingEnd ℂ) (pairedEtaCoreSummand s n) := by
      apply tsum_congr
      exact pairedEtaCoreSummand_conj s
    _ = (starRingEnd ℂ) (∑' n : ℕ, pairedEtaCoreSummand s n) :=
      (Complex.conj_tsum _).symm

lemma two_cpow_neg_conj (s : ℂ) :
    (2 : ℂ) ^ (-((starRingEnd ℂ) s)) =
      (starRingEnd ℂ) ((2 : ℂ) ^ (-s)) := by
  simpa only [map_neg, map_ofNat] using
    (Complex.cpow_conj (2 : ℂ) (-s)
      (by
        change (((2 : ℕ) : ℂ)).arg ≠ Real.pi
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm))

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_neg
    {s : ℂ} (hsre : 0 < s.re) (hsim : s.im < 0) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  have h := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := (starRingEnd ℂ) s) (by simpa using hsre) (by simpa using hsim)
  have hc := congrArg (starRingEnd ℂ) h
  simpa [pairedEtaCore_conj, two_cpow_neg_conj,
    starRingEnd_self_apply, map_ofNat] using hc

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_eq_zero
    {s : ℂ} (hsre : 0 < s.re) (hsim : s.im = 0) (hsone : s ≠ 1) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let rhs : ℂ → ℂ := fun w =>
    (1 - 2 * (2 : ℂ) ^ (-w)) * riemannZeta w
  let t : Set ℂ := pairedEtaUpperRightDomain ∪ {s}
  have heq : Set.EqOn pairedEtaCore rhs pairedEtaUpperRightDomain := by
    intro w hw
    exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos hw.1 hw.2
  have htpos : t ⊆ {w : ℂ | 0 < w.re} := by
    intro w hw
    rcases hw with hw | hw
    · exact hw.1
    · simpa only [mem_singleton_iff] using hw ▸ hsre
  have hlhs : ContinuousOn pairedEtaCore t :=
    (analyticOnNhd_pairedEtaCore.mono htpos).continuousOn
  have hrhs : ContinuousOn rhs t := by
    intro w hw
    have hwone : w ≠ 1 := by
      rcases hw with hw | hw
      · intro h
        subst w
        simpa [pairedEtaUpperRightDomain] using hw.2
      · simpa only [mem_singleton_iff] using hw ▸ hsone
    have hfactor : DifferentiableAt ℂ
        (fun u : ℂ => 1 - 2 * (2 : ℂ) ^ (-u)) w := by
      fun_prop (disch := norm_num)
    exact
      (hfactor.mul
        (differentiableAt_riemannZeta hwone)).continuousAt.continuousWithinAt
  have hsclosure : s ∈ closure pairedEtaUpperRightDomain := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨s + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · constructor
      · simpa [pairedEtaUpperRightDomain] using hsre
      · simp [hsim]
        positivity
    · rw [dist_eq_norm]
      simp [Real.norm_eq_abs, abs_of_pos hε]
      linarith
  have htclosure : t ⊆ closure pairedEtaUpperRightDomain := by
    intro w hw
    rcases hw with hw | hw
    · exact subset_closure hw
    · simpa only [mem_singleton_iff] using hw ▸ hsclosure
  have hall := heq.of_subset_closure hlhs hrhs subset_union_left htclosure
  exact hall (by simp [t])

lemma pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    {s : ℂ} (hsre : 0 < s.re) (hsone : s ≠ 1) :
    pairedEtaCore s =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  rcases lt_trichotomy s.im 0 with hsim | hsim | hsim
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_neg hsre hsim
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_eq_zero
      hsre hsim hsone
  · exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos hsre hsim

end
end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaFiniteLaplacePartition (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp (-s * t)

theorem pairedEtaCoreSummand_eq_mul_logLaplaceInterval
    (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      s * ∫ t : ℝ in
        Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp (-s * t) := by
  by_cases hs : s = 0
  · subst s
    simp [pairedEtaCoreSummand]
  · have hoddNonneg : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      positivity
    have hevenNonneg : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
      positivity
    have hodd : ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
    have heven : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)
    have hoddPow :
        Complex.exp (-s * Real.log (2 * n + 1)) =
          ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero hodd,
        ← Complex.ofReal_log hoddNonneg]
      congr 1
      push_cast
      ring
    have hevenPow :
        Complex.exp (-s * Real.log (2 * n + 2)) =
          ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero heven,
        ← Complex.ofReal_log hevenNonneg]
      congr 1
      push_cast
      ring
    rw [integral_exp_mul_complex (c := -s) (neg_ne_zero.mpr hs)]
    rw [hoddPow, hevenPow]
    unfold pairedEtaCoreSummand
    field_simp [hs]
    simp only [Nat.mul_comm]
    abel

theorem pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition
    (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N s =
      s * pairedEtaFiniteLaplacePartition N s := by
  unfold pairedEtaCorePartialSum pairedEtaFiniteLaplacePartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact pairedEtaCoreSummand_eq_mul_logLaplaceInterval s n

theorem pairedEtaFiniteLaplaceKernel_re (sigma y t : ℝ) :
    (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re =
      Real.exp (-sigma * t) * Real.cos (y * t) := by
  rw [Complex.exp_re]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem pairedEtaFiniteLaplaceKernel_im (sigma y t : ℝ) :
    (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im =
      -(Real.exp (-sigma * t) * Real.sin (y * t)) := by
  rw [Complex.exp_im]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem pairedEtaFiniteLaplaceInterval_re
    (sigma y : ℝ) (n : ℕ) :
    (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re =
      ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t) * Real.cos (y * t) := by
  have hcont : Continuous
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
      MeasureSpace.volume
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2)) :=
    hcont.intervalIntegrable
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2))
  have hre :
      (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re) =
        (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re := by
    simpa using intervalIntegral.intervalIntegral_re hint
  rw [← hre]
  apply intervalIntegral.integral_congr
  intro t _
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

theorem pairedEtaFiniteLogInterval_pos (n : ℕ) :
    Real.log (2 * n + 1) < Real.log (2 * n + 2) := by
  apply Real.log_lt_log
  · positivity
  · exact_mod_cast (show 2 * n + 1 < 2 * n + 2 by omega)

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.GaussianZetaGeometry
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian

noncomputable section

open Filter Topology
theorem nontrivialZetaZeroSet_countable :
    nontrivialZetaZeroSet.Countable := by
  exact (HereditarilyLindelofSpace.isLindelof
    nontrivialZetaZeroSet).countable_of_isDiscrete
      (isDiscrete_riemannZetaZeros.mono
        nontrivialZetaZeroSet_subset_riemannZetaZeros)

noncomputable instance : Countable NontrivialZetaZero :=
  nontrivialZetaZeroSet_countable.to_subtype

namespace NontrivialZetaZero

theorem re_lt_one (ρ : NontrivialZetaZero) : ρ.1.re < 1 := by
  exact lt_of_not_ge fun h =>
    riemannZeta_ne_zero_of_one_le_re h ρ.2.1

theorem zero_lt_re (ρ : NontrivialZetaZero) : 0 < ρ.1.re := by
  have hpartner := re_lt_one (functionalPartner ρ)
  simpa using hpartner

end NontrivialZetaZero

def SameZetaConjugatePacket
    (ρ σ : NontrivialZetaZero) : Prop :=
  σ = ρ ∨ σ = NontrivialZetaZero.conjugatePartner ρ

theorem SameZetaConjugatePacket.refl (ρ : NontrivialZetaZero) :
    SameZetaConjugatePacket ρ ρ :=
  Or.inl rfl

theorem SameZetaConjugatePacket.symm
    {ρ σ : NontrivialZetaZero}
    (h : SameZetaConjugatePacket ρ σ) :
    SameZetaConjugatePacket σ ρ := by
  rcases h with rfl | rfl
  · exact .refl _
  · exact Or.inr (NontrivialZetaZero.conjugatePartner_conjugatePartner ρ).symm

namespace NontrivialZetaZero

end NontrivialZetaZero

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaLogInterval (n : ℕ) : Set ℝ :=
  Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2))

def pairedEtaLogSupport : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogInterval n

def pairedEtaLogMeasure : Measure ℝ :=
  volume.restrict pairedEtaLogSupport

theorem pairwise_disjoint_pairedEtaLogInterval :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogInterval n) (pairedEtaLogInterval m)) := by
  suffices hordered : ∀ {n m : ℕ}, n < m →
      Disjoint (pairedEtaLogInterval n) (pairedEtaLogInterval m) by
    intro n m hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact hordered hnm
    · exact (hordered hmn).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro t htn htm
  have harg : (2 : ℝ) * n + 2 < 2 * m + 1 := by
    exact_mod_cast (show 2 * n + 2 < 2 * m + 1 by omega)
  have hlog : Real.log (2 * n + 2) < Real.log (2 * m + 1) :=
    Real.log_lt_log (by positivity) harg
  exact (not_lt_of_ge htn.2) (hlog.trans htm.1)

theorem pairedEtaLogMeasure_eq_sum_restrict :
    pairedEtaLogMeasure =
      Measure.sum fun n : ℕ ↦ volume.restrict (pairedEtaLogInterval n) := by
  unfold pairedEtaLogMeasure pairedEtaLogSupport
  exact Measure.restrict_iUnion
    pairwise_disjoint_pairedEtaLogInterval
    (fun _ ↦ by
      unfold pairedEtaLogInterval
      exact measurableSet_Ioc)

def pairedEtaLaplaceInterval (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
    Complex.exp (-s * t)

def pairedEtaLaplacePartition (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaLaplaceInterval s n

theorem summable_pairedEtaLaplaceInterval
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaLaplaceInterval s) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hsum := (summable_pairedEtaCoreSummand hs).div_const s
  apply hsum.congr
  intro n
  rw [pairedEtaCoreSummand_eq_mul_logLaplaceInterval]
  simp [pairedEtaLaplaceInterval, hs0]

theorem summable_pairedEtaTiltedMassInterval
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : ℕ ↦
      ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t)) := by
  have hcomplex : Summable (pairedEtaLaplaceInterval (sigma : ℂ)) :=
    summable_pairedEtaLaplaceInterval (by simpa using hsigma)
  have hre := Complex.reCLM.summable hcomplex
  apply hre.congr
  intro n
  simpa [pairedEtaLaplaceInterval] using
    (pairedEtaFiniteLaplaceInterval_re sigma 0 n)

theorem integrable_exp_neg_mul_pairedEtaLogMeasure
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      pairedEtaLogMeasure := by
  rw [pairedEtaLogMeasure_eq_sum_restrict]
  apply integrable_sum_measure
  · intro n
    have hcont : Continuous (fun t : ℝ ↦ Complex.exp (-s * t)) := by
      fun_prop
    have hab : Real.log (2 * n + 1) ≤ Real.log (2 * n + 2) :=
      (pairedEtaFiniteLogInterval_pos n).le
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        (hcont.intervalIntegrable _ _)
  · have hnorm := summable_pairedEtaTiltedMassInterval hs
    apply hnorm.congr
    intro n
    have hab : Real.log (2 * n + 1) ≤ Real.log (2 * n + 2) :=
      (pairedEtaFiniteLogInterval_pos n).le
    unfold pairedEtaLogInterval
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re]

theorem integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) =
      pairedEtaLaplacePartition s := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure hs
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogMeasure_eq_sum_restrict,
    integral_sum_measure hint]
  unfold pairedEtaLaplacePartition pairedEtaLaplaceInterval
    pairedEtaLogInterval
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos n).le).symm

theorem pairedEtaCore_eq_mul_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s = s * pairedEtaLaplacePartition s := by
  unfold pairedEtaCore pairedEtaLaplacePartition
  calc
    ∑' n : ℕ, pairedEtaCoreSummand s n =
        ∑' n : ℕ, s * pairedEtaLaplaceInterval s n := by
      apply tsum_congr
      intro n
      exact pairedEtaCoreSummand_eq_mul_logLaplaceInterval s n
    _ = s * ∑' n : ℕ, pairedEtaLaplaceInterval s n :=
      (summable_pairedEtaLaplaceInterval hs).tsum_mul_left s

def pairedEtaTiltedCosineMoment (sigma y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-sigma * t) * Real.cos (y * t)
    ∂pairedEtaLogMeasure

def pairedEtaTiltedSineMoment (sigma y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-sigma * t) * Real.sin (y * t)
    ∂pairedEtaLogMeasure

theorem integrable_pairedEtaTiltedCosineKernel
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ ↦
      Real.exp (-sigma * t) * Real.cos (y * t))
      pairedEtaLogMeasure := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  apply hint.re.congr
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

theorem pairedEtaTiltedCosineMoment_zero_pos
    (sigma : ℝ) (hsigma : 0 < sigma) :
    0 < pairedEtaTiltedCosineMoment sigma 0 := by
  have hint := integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  simp only [zero_mul, Real.cos_zero, mul_one] at hint
  unfold pairedEtaTiltedCosineMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [pairedEtaLogMeasure_eq_sum_restrict, integral_sum_measure hint]
  have hsum := summable_pairedEtaTiltedMassInterval hsigma
  calc
    0 < ∑' n : ℕ,
        ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Real.exp (-sigma * t) := by
      apply hsum.tsum_pos
      · intro n
        exact (intervalIntegral.intervalIntegral_pos_of_pos
          (by
            apply Continuous.intervalIntegrable
            fun_prop)
          (fun _ ↦ Real.exp_pos _)
          (pairedEtaFiniteLogInterval_pos n)).le
      · exact intervalIntegral.intervalIntegral_pos_of_pos
          (by
            apply Continuous.intervalIntegrable
            fun_prop)
          (fun _ ↦ Real.exp_pos _)
          (pairedEtaFiniteLogInterval_pos 0)
    _ = ∑' n : ℕ,
        ∫ t : ℝ, Real.exp (-sigma * t)
          ∂volume.restrict (pairedEtaLogInterval n) := by
      apply tsum_congr
      intro n
      unfold pairedEtaLogInterval
      exact (intervalIntegral.integral_of_le
        (pairedEtaFiniteLogInterval_pos n).le)

theorem integral_exp_neg_mul_pairedEtaLogMeasure_re
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    (∫ t : ℝ,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
        ∂pairedEtaLogMeasure).re =
      pairedEtaTiltedCosineMoment sigma y := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have hre :
      (∫ t : ℝ,
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re
          ∂pairedEtaLogMeasure) =
        (∫ t : ℝ,
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
            ∂pairedEtaLogMeasure).re := by
    simpa using integral_re hint
  rw [← hre]
  unfold pairedEtaTiltedCosineMoment
  apply integral_congr_ae
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

theorem integral_exp_neg_mul_pairedEtaLogMeasure_im
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    (∫ t : ℝ,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
        ∂pairedEtaLogMeasure).im =
      -pairedEtaTiltedSineMoment sigma y := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have him :
      (∫ t : ℝ,
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im
          ∂pairedEtaLogMeasure) =
        (∫ t : ℝ,
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
            ∂pairedEtaLogMeasure).im := by
    simpa using integral_im hint
  rw [← him]
  unfold pairedEtaTiltedSineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_im sigma y t

theorem pairedEtaLaplacePartition_eq_cosine_sub_I_sine
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    pairedEtaLaplacePartition
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
      (pairedEtaTiltedCosineMoment sigma y : ℂ) -
        (pairedEtaTiltedSineMoment sigma y : ℂ) * Complex.I := by
  rw [← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)]
  apply Complex.ext
  · rw [integral_exp_neg_mul_pairedEtaLogMeasure_re sigma y hsigma]
    norm_num [Complex.mul_re]
  · rw [integral_exp_neg_mul_pairedEtaLogMeasure_im sigma y hsigma]
    norm_num [Complex.mul_im]

theorem pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaLaplacePartition rho.1 = 0 := by
  have hre : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      hre rho.2.2.2, rho.2.1, mul_zero]
  have hmul : rho.1 * pairedEtaLaplacePartition rho.1 = 0 := by
    rw [← pairedEtaCore_eq_mul_laplacePartition hre, hcore]
  exact (mul_eq_zero.mp hmul).resolve_left (by
    intro hrho
    have := congrArg Complex.re hrho
    norm_num at this
    linarith)

theorem pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaTiltedCosineMoment rho.1.re rho.1.im = 0 ∧
      pairedEtaTiltedSineMoment rho.1.re rho.1.im = 0 := by
  have hre : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hzeroCoordinates :
      pairedEtaLaplacePartition
        (((rho.1.re : ℝ) : ℂ) + ((rho.1.im : ℝ) : ℂ) * Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using
      pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho
  have hsplit :=
    pairedEtaLaplacePartition_eq_cosine_sub_I_sine
      rho.1.re rho.1.im hre
  rw [hzeroCoordinates] at hsplit
  constructor
  · have hreal := congrArg Complex.re hsplit
    norm_num [Complex.mul_re] at hreal
    exact hreal.symm
  · have himag := congrArg Complex.im hsplit
    norm_num [Complex.mul_im] at himag
    exact himag

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapFinite
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def pairedEtaLogTailSupport (N : ℕ) : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogInterval (n + N)

def pairedEtaLogTailMeasure (N : ℕ) : Measure ℝ :=
  volume.restrict (pairedEtaLogTailSupport N)

theorem pairwise_disjoint_pairedEtaLogInterval_natAdd (N : ℕ) :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogInterval (n + N))
        (pairedEtaLogInterval (m + N))) := by
  intro n m hne
  apply pairwise_disjoint_pairedEtaLogInterval
  omega

theorem pairedEtaLogTailMeasure_eq_sum_restrict (N : ℕ) :
    pairedEtaLogTailMeasure N =
      Measure.sum fun n : ℕ ↦
        volume.restrict (pairedEtaLogInterval (n + N)) := by
  unfold pairedEtaLogTailMeasure pairedEtaLogTailSupport
  exact Measure.restrict_iUnion
    (pairwise_disjoint_pairedEtaLogInterval_natAdd N)
    (fun _ ↦ by
      unfold pairedEtaLogInterval
      exact measurableSet_Ioc)

theorem pairedEtaLogTailSupport_subset_Ioi_log_odd (N : ℕ) :
    pairedEtaLogTailSupport N ⊆ Ioi (Real.log (2 * N + 1)) := by
  intro t ht
  rw [pairedEtaLogTailSupport, mem_iUnion] at ht
  obtain ⟨n, hn⟩ := ht
  have harg : (2 : ℝ) * N + 1 ≤ 2 * (n + N) + 1 := by
    exact_mod_cast (show 2 * N + 1 ≤ 2 * (n + N) + 1 by omega)
  have hlog : Real.log (2 * N + 1) ≤
      Real.log (2 * (n + N) + 1) :=
    Real.log_le_log (by positivity) harg
  exact hlog.trans_lt (by simpa [Nat.cast_add] using hn.1)

theorem pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd (N : ℕ) :
    pairedEtaLogTailMeasure N ≤
      volume.restrict (Ioi (Real.log (2 * N + 1))) := by
  unfold pairedEtaLogTailMeasure
  exact Measure.restrict_mono
    (pairedEtaLogTailSupport_subset_Ioi_log_odd N) le_rfl

theorem integrable_exp_neg_mul_pairedEtaLogTailMeasure
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      (pairedEtaLogTailMeasure N) := by
  have hfull := integrableOn_exp_mul_complex_Ioi (a := -s) (by
    norm_num
    linarith) (Real.log (2 * N + 1))
  have hfull' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      (volume.restrict (Ioi (Real.log (2 * N + 1)))) := by
    apply hfull.congr
    filter_upwards with t
    congr 1
  exact hfull'.mono_measure
    (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N)

theorem integral_exp_neg_mul_pairedEtaLogTailMeasure_eq_tsum_natAdd
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N) =
      ∑' n : ℕ, pairedEtaLaplaceInterval s (n + N) := by
  have hint := integrable_exp_neg_mul_pairedEtaLogTailMeasure hs N
  rw [pairedEtaLogTailMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogTailMeasure_eq_sum_restrict, integral_sum_measure hint]
  apply tsum_congr
  intro n
  unfold pairedEtaLaplaceInterval pairedEtaLogInterval
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos (n + N)).le).symm

theorem pairedEtaCore_sub_partialSum_eq_mul_tailIntegral
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      s * ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N := by
  have hsplit :=
    (summable_pairedEtaLaplaceInterval hs).sum_add_tsum_nat_add N
  change pairedEtaFiniteLaplacePartition N s +
      (∑' n : ℕ, pairedEtaLaplaceInterval s (n + N)) =
    pairedEtaLaplacePartition s at hsplit
  rw [pairedEtaCore_eq_mul_laplacePartition hs,
    pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition,
    integral_exp_neg_mul_pairedEtaLogTailMeasure_eq_tsum_natAdd hs]
  rw [← hsplit]
  ring

theorem norm_cexp_neg_mul_eq_exp_neg_re_mul (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * t)‖ = Real.exp (-s.re * t) := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re]

theorem integral_exp_neg_mul_Ioi_log_odd
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    (∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
      Real.exp (-sigma * t)) =
      ((2 * N + 1 : ℕ) : ℝ) ^ (-sigma) / sigma := by
  rw [integral_exp_mul_Ioi (a := -sigma) (by linarith)]
  rw [neg_div_neg_eq]
  have hbase : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [Real.rpow_def_of_pos hbase, hcast]
  apply congrArg (fun x : ℝ ↦ x / sigma)
  apply congrArg Real.exp
  ring

theorem norm_pairedEtaCore_sub_partialSum_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      ‖s‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) / s.re) := by
  rw [pairedEtaCore_sub_partialSum_eq_mul_tailIntegral hs, norm_mul]
  have hrealIntegrable : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-s.re * t))
      (Ioi (Real.log (2 * N + 1))) := by
    have h := integrableOn_exp_mul_Ioi (a := -s.re) (by linarith)
      (Real.log (2 * N + 1))
    simpa only [neg_mul] using h
  have hnormIntegral :
      ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, Real.exp (-s.re * t) ∂pairedEtaLogTailMeasure N := by
    calc
      ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
          ∫ t : ℝ, ‖Complex.exp (-s * t)‖
            ∂pairedEtaLogTailMeasure N :=
        norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, Real.exp (-s.re * t)
            ∂pairedEtaLogTailMeasure N := by
        apply integral_congr_ae
        filter_upwards with t
        exact norm_cexp_neg_mul_eq_exp_neg_re_mul s t
  have hmeasureIntegral :
      (∫ t : ℝ, Real.exp (-s.re * t) ∂pairedEtaLogTailMeasure N) ≤
        ∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
          Real.exp (-s.re * t) := by
    exact integral_mono_measure
      (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N)
      (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
      hrealIntegrable
  calc
    ‖s‖ *
        ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
        ‖s‖ *
          (∫ t : ℝ, Real.exp (-s.re * t)
            ∂pairedEtaLogTailMeasure N) :=
      mul_le_mul_of_nonneg_left hnormIntegral (norm_nonneg s)
    _ ≤ ‖s‖ *
        (∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
          Real.exp (-s.re * t)) :=
      mul_le_mul_of_nonneg_left hmeasureIntegral (norm_nonneg s)
    _ = ‖s‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) / s.re) := by
      rw [integral_exp_neg_mul_Ioi_log_odd hs]

theorem tendsto_pairedEtaOddEndpoint_rpow_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) atTop (nhds 0) := by
  have hbase : Tendsto (fun N : ℕ ↦ (2 : ℝ) * N + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
  convert (tendsto_rpow_neg_atTop hs).comp hbase using 1
  funext N
  norm_num

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.EtaZetaPoleBounds
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem norm_pairedEtaCore_le_div_re {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaCore s‖ ≤ ‖s‖ / s.re := by
  simpa [pairedEtaCorePartialSum, div_eq_mul_inv] using
    norm_pairedEtaCore_sub_partialSum_le hs 0

theorem pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁ {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s * (s - 1) =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta₁ s := by
  by_cases hs1 : s = 1
  · subst s
    norm_num [Complex.cpow_neg_one]
  · rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1,
      riemannZeta_eq_inv_sub_mul hs1]
    field_simp

theorem norm_riemannZeta₁_le_of_etaFactor_lower {s : ℂ} (hs : 0 < s.re)
    (hfactor : (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖) :
    ‖riemannZeta₁ s‖ ≤ 4 * ‖s - 1‖ * ‖s‖ / s.re := by
  have he := congrArg norm (pairedEtaCore_mul_sub_one_eq_factor_riemannZeta₁ hs)
  simp only [norm_mul] at he
  have hm := mul_le_mul_of_nonneg_right (norm_pairedEtaCore_le_div_re hs) (norm_nonneg (s - 1))
  have hf := mul_le_mul_of_nonneg_right hfactor (norm_nonneg (riemannZeta₁ s))
  calc
    ‖riemannZeta₁ s‖ ≤ 4 * (‖s‖ / s.re * ‖s - 1‖) := by nlinarith
    _ = _ := by ring

theorem norm_two_mul_two_cpow_neg (s : ℂ) :
    ‖2 * (2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (1 - s.re) := by
  have hp := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-s)
  norm_num only [Complex.ofReal_ofNat, Complex.neg_re] at hp
  rw [norm_mul, Complex.norm_ofNat, hp]
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]

theorem quarter_le_norm_etaFactor_of_re_boundary {s : ℂ}
    (hs : s.re = 1 / 2 ∨ s.re = 3 / 2) :
    (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rcases hs with hs | hs
  · have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
    rw [norm_two_mul_two_cpow_neg, hs, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, norm_one, norm_sub_rev] at h
    nlinarith
  · have h := norm_sub_norm_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
    rw [norm_one, norm_two_mul_two_cpow_neg, hs,
      show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow] at h
    have hi : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
      rw [inv_eq_one_div, div_le_iff₀ hsqrt]
      nlinarith
    linarith

theorem one_le_norm_etaFactor_of_cos_eq_neg_one {s : ℂ}
    (hcos : Real.cos (Real.log 2 * s.im) = -1) :
    (1 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have hre : (1 - 2 * (2 : ℂ) ^ (-s)).re =
      1 + 2 * Real.exp (-(Real.log 2 * s.re)) := by
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    simp only [hlog, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Complex.exp_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_im, mul_neg, Real.cos_neg]
    ring_nf
    rw [hcos]
    ring
  have h := Complex.re_le_norm (1 - 2 * (2 : ℂ) ^ (-s))
  rw [hre] at h
  linarith [Real.exp_pos (-(Real.log 2 * s.re))]

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.EtaThinStripFactor
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem quarter_width_le_norm_etaFactor_of_re_boundary {s : ℂ} {epsilon : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2)
    (hs : s.re = 1 - epsilon ∨ s.re = 1 + epsilon) :
    epsilon / 4 ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have hp : 0 < (2 : ℝ) ^ epsilon := Real.rpow_pos_of_pos (by norm_num) _
  have hlo : 1 + epsilon / 2 ≤ (2 : ℝ) ^ epsilon := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h := Real.add_one_le_exp (Real.log 2 * epsilon)
    nlinarith [Real.log_two_gt_d9]
  have hhi : (2 : ℝ) ^ epsilon ≤ 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : epsilon ≤ 1)).trans_eq (Real.rpow_one 2)
  rcases hs with hs | hs
  · have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
    rw [norm_two_mul_two_cpow_neg, hs, show 1 - (1 - epsilon) = epsilon by ring,
      norm_one, norm_sub_rev] at h
    linarith
  · have hi : ((2 : ℝ) ^ epsilon)⁻¹ ≤ 1 - epsilon / 4 := by
      rw [inv_eq_one_div, div_le_iff₀ hp]
      nlinarith [mul_le_mul_of_nonneg_left hhi he.le]
    have h := norm_sub_norm_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
    rw [norm_one, norm_two_mul_two_cpow_neg, hs,
      show 1 - (1 + epsilon) = -epsilon by ring, Real.rpow_neg (by norm_num)] at h
    linarith

theorem norm_pairedEtaCore_ofReal_le_one {x : ℝ} (hx : 0 < x) :
    ‖pairedEtaCore (x : ℂ)‖ ≤ 1 := by
  simpa [abs_of_pos hx, hx.ne'] using
    norm_pairedEtaCore_le_div_re (s := (x : ℂ)) hx

theorem norm_riemannZeta_one_add_le_four_div {x : ℝ} (hx : 0 < x) (hxhi : x ≤ 1 / 2) :
    ‖riemannZeta (1 + (x : ℂ))‖ ≤ 4 / x := by
  have hs : 0 < (1 + (x : ℂ)).re := by simp; linarith
  have hs1 : (1 + (x : ℂ)) ≠ 1 := by simp [hx.ne']
  have hfactor := quarter_width_le_norm_etaFactor_of_re_boundary hx hxhi
    (s := 1 + (x : ℂ)) (Or.inr (by simp))
  have he := congrArg norm (pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1)
  rw [norm_mul] at he
  have heta : ‖pairedEtaCore (1 + (x : ℂ))‖ ≤ 1 := by
    simpa using norm_pairedEtaCore_ofReal_le_one (show 0 < 1 + x by linarith)
  have hm := mul_le_mul_of_nonneg_right hfactor (norm_nonneg (riemannZeta (1 + (x : ℂ))))
  rw [le_div_iff₀ hx]
  nlinarith

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.EtaZetaDyadicRectangle
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

def etaDyadicImaginaryPeriod : ℝ := 2 * Real.pi / Real.log 2

theorem etaDyadicImaginaryPeriod_pos : 0 < etaDyadicImaginaryPeriod :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by norm_num))

theorem etaDyadicImaginaryPeriod_le_sixteen : etaDyadicImaginaryPeriod ≤ 16 := by
  unfold etaDyadicImaginaryPeriod
  rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  linarith [Real.pi_lt_four, Real.log_two_gt_d9]

theorem exists_etaDyadicRectangle_center (y : ℝ) : ∃ n : ℤ,
    y ∈ Icc (etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2)
      (etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2) := by
  refine ⟨round (y / etaDyadicImaginaryPeriod), ?_⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_sub_round (y / etaDyadicImaginaryPeriod))
  have h1 : (round (y / etaDyadicImaginaryPeriod) : ℝ) - 1 / 2 ≤
      y / etaDyadicImaginaryPeriod := by linarith
  have h2 : y / etaDyadicImaginaryPeriod ≤
      (round (y / etaDyadicImaginaryPeriod) : ℝ) + 1 / 2 := by linarith
  have h1' := (le_div_iff₀ etaDyadicImaginaryPeriod_pos).mp h1
  have h2' := (div_le_iff₀ etaDyadicImaginaryPeriod_pos).mp h2
  constructor <;> nlinarith

theorem cos_log_two_mul_etaDyadicRectangle_boundary (n : ℤ) {y : ℝ}
    (hy : y = etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2 ∨
      y = etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2) :
    Real.cos (Real.log 2 * y) = -1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rcases hy with hy | hy
  · have he : Real.log 2 * y = (n : ℝ) * (2 * Real.pi) - Real.pi := by
      rw [hy, etaDyadicImaginaryPeriod]
      field_simp
    rw [he, Real.cos_int_mul_two_pi_sub_pi]
  · have he : Real.log 2 * y = (n : ℝ) * (2 * Real.pi) + Real.pi := by
      rw [hy, etaDyadicImaginaryPeriod]
      field_simp
    rw [he, Real.cos_int_mul_two_pi_add_pi]

theorem norm_riemannZeta₁_le_etaRectangle_envelope {s : ℂ} {y : ℝ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 3 / 2)
    (him : |s.im - y| ≤ etaDyadicImaginaryPeriod)
    (hfactor : (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖) :
    ‖riemannZeta₁ s‖ ≤ 8 * (|y| + 20) ^ 2 := by
  have hspos : 0 < s.re := by linarith
  have himabs : |s.im| ≤ |y| + 16 := by
    have h := abs_add_le (s.im - y) y
    rw [sub_add_cancel] at h
    linarith [etaDyadicImaginaryPeriod_le_sixteen]
  have hreabs : |s.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, hshi⟩
  have hreone : |s.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : ‖s‖ ≤ |y| + 20 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hn1 : ‖s - 1‖ ≤ |y| + 20 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have hprod : ‖s - 1‖ * ‖s‖ ≤ (|y| + 20) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hn1 hn (norm_nonneg s) (by positivity : 0 ≤ |y| + 20)
  refine (norm_riemannZeta₁_le_of_etaFactor_lower hspos hfactor).trans ?_
  rw [div_le_iff₀ hspos]
  nlinarith [sq_nonneg (|y| + 20)]

theorem norm_riemannZeta₁_le_etaStrip {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 3 / 2) :
    ‖riemannZeta₁ s‖ ≤ 8 * (|s.im| + 20) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_etaDyadicRectangle_center s.im
  let a := etaDyadicImaginaryPeriod * n - etaDyadicImaginaryPeriod / 2
  let b := etaDyadicImaginaryPeriod * n + etaDyadicImaginaryPeriod / 2
  have hab : a < b := by dsimp [a, b]; linarith [etaDyadicImaginaryPeriod_pos]
  have hsab : s.im ∈ Icc a b := hn
  have hnear {y : ℝ} (hy : y ∈ Icc a b) : |y - s.im| ≤ etaDyadicImaginaryPeriod := by
    have hlen : b - a = etaDyadicImaginaryPeriod := by dsimp [a, b]; ring
    exact abs_le.mpr ⟨by linarith [hy.1, hsab.2], by linarith [hy.2, hsab.1]⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (1 / 2 : ℝ) (3 / 2)).reProdIm (isBounded_Ioo a b))
    differentiable_riemannZeta₁.diffContOnCl
  · intro z hz
    rw [frontier_reProdIm, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 3 / 2),
      frontier_Ioo (by norm_num : (1 / 2 : ℝ) < 3 / 2),
      closure_Ioo hab.ne, frontier_Ioo hab] at hz
    rcases hz with hz | hz
    · have hzab : z.im = a ∨ z.im = b := by simpa using hz.2
      have hzmem : z.im ∈ Icc a b := by
        rcases hzab with hzab | hzab
        · rw [hzab]; exact ⟨le_rfl, hab.le⟩
        · rw [hzab]; exact ⟨hab.le, le_rfl⟩
      apply norm_riemannZeta₁_le_etaRectangle_envelope hz.1.1 hz.1.2 (hnear hzmem)
      exact (by norm_num : (1 / 4 : ℝ) ≤ 1).trans
        (one_le_norm_etaFactor_of_cos_eq_neg_one (cos_log_two_mul_etaDyadicRectangle_boundary n hzab))
    · have hzre : z.re = 1 / 2 ∨ z.re = 3 / 2 := by simpa using hz.1
      have hzlo : 1 / 2 ≤ z.re := hzre.elim (fun h ↦ by rw [h]) (fun h ↦ by rw [h]; norm_num)
      have hzhi : z.re ≤ 3 / 2 := hzre.elim (fun h ↦ by rw [h]; norm_num) (fun h ↦ by rw [h])
      exact norm_riemannZeta₁_le_etaRectangle_envelope hzlo hzhi (hnear hz.2)
        (quarter_le_norm_etaFactor_of_re_boundary hzre)
  · rw [closure_reProdIm, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 3 / 2), closure_Ioo hab.ne]
    exact ⟨⟨hslo, hshi⟩, hsab⟩

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeZeta
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Metric Set Topology
open scoped ArithmeticFunction.Moebius Classical ComplexConjugate ENNReal
  Interval Topology

namespace RiemannGaussian

noncomputable section

def staticContourSafeZetaDirichletMass : ℝ :=
  ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

theorem summable_staticContourSafeZetaDirichletSeries :
    Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  exact Real.summable_nat_rpow_inv.mpr (by norm_num)

theorem one_le_staticContourSafeZetaDirichletMass :
    1 ≤ staticContourSafeZetaDirichletMass := by
  unfold staticContourSafeZetaDirichletMass
  have hone : (((1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ = 1 := by norm_num
  rw [← hone]
  apply summable_staticContourSafeZetaDirichletSeries.le_tsum 1
  intro n _hn
  positivity

theorem norm_riemannZeta_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖riemannZeta s‖ ≤ staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hsum := summable_riemannZetaSummand hsOne
  rw [← tsum_riemannZetaSummand hsOne]
  calc
    ‖∑' n : ℕ, riemannZetaSummandHom
        (Complex.ne_zero_of_one_lt_re hsOne) n‖ ≤
        ∑' n : ℕ, ‖riemannZetaSummandHom
          (Complex.ne_zero_of_one_lt_re hsOne) n‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = staticContourSafeZetaDirichletMass := by
      unfold staticContourSafeZetaDirichletMass
      apply tsum_congr
      intro n
      simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk,
        ZeroHom.coe_mk]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
          (by rw [neg_re, hs]; norm_num),
        neg_re, hs, Real.rpow_neg (Nat.cast_nonneg n)]

theorem norm_moebius_LSeries_term_safeLine_le
    {s : ℂ} (hs : s.re = 3 / 2) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ ↦
        ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos hnpos, hs]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hmu (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem norm_moebius_LSeries_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖LSeries (fun n : ℕ ↦
        ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
      staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hsum : LSeriesSummable
      (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsOne
  calc
    ‖LSeries (fun n : ℕ ↦
        ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
        ∑' n : ℕ, ‖LSeries.term
          (fun m : ℕ ↦ ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
      hsum.norm.tsum_le_tsum
        (norm_moebius_LSeries_term_safeLine_le hs)
        summable_staticContourSafeZetaDirichletSeries
    _ = staticContourSafeZetaDirichletMass := rfl

theorem norm_inv_riemannZeta_safeLine_le_mass
    {s : ℂ} (hs : s.re = 3 / 2) :
    ‖(riemannZeta s)⁻¹‖ ≤ staticContourSafeZetaDirichletMass := by
  have hsOne : 1 < s.re := by rw [hs]; norm_num
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsOne
  have hmul : riemannZeta s *
      LSeries (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsOne]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hsOne
  have hinv : (riemannZeta s)⁻¹ =
      LSeries (fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
    apply mul_left_cancel₀ hzeta
    rw [mul_inv_cancel₀ hzeta, hmul]
  rw [hinv]
  exact norm_moebius_LSeries_safeLine_le_mass hs

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaLocalDiscBounds
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

theorem staticContourSafeZetaDirichletMass_eq_zeta :
    (staticContourSafeZetaDirichletMass : ℂ) = riemannZeta (3 / 2) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num : 1 < (3 / 2 : ℂ).re)]
  unfold staticContourSafeZetaDirichletMass
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  norm_num [one_div]

theorem staticContourSafeZetaDirichletMass_le_eight : staticContourSafeZetaDirichletMass ≤ 8 := by
  have h := norm_riemannZeta_one_add_le_four_div
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  norm_num at h
  rw [← staticContourSafeZetaDirichletMass_eq_zeta] at h
  simpa [abs_of_nonneg (zero_le_one.trans one_le_staticContourSafeZetaDirichletMass)] using h

theorem quarter_le_norm_etaFactor_of_three_halves_le_re {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    (1 / 4 : ℝ) ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (2 * (2 : ℂ) ^ (-s))
  rw [norm_one, norm_two_mul_two_cpow_neg] at h
  have hp : (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hsqrt]
    nlinarith
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow] at hp
  linarith

def localZetaPoleRemoved (y : ℝ) (z : ℂ) : ℂ := riemannZeta₁ (3 / 2 + I * y + z)

theorem differentiable_localZetaPoleRemoved (y : ℝ) : Differentiable ℂ (localZetaPoleRemoved y) := by
  unfold localZetaPoleRemoved
  exact differentiable_riemannZeta₁.comp (by fun_prop)

theorem norm_localZetaPoleRemoved_le (y : ℝ) {z : ℂ} (hz : z ∈ closedBall 0 (1 : ℝ)) :
    ‖localZetaPoleRemoved y z‖ ≤ 8 * (|y| + 22) ^ 2 := by
  have hzn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hzre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hzn
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hzn
  let s : ℂ := 3 / 2 + I * y + z
  have hsre : s.re = 3 / 2 + z.re := by simp [s]
  have hsim : s.im = y + z.im := by simp [s]
  have hslo : 1 / 2 ≤ s.re := by rw [hsre]; linarith [(abs_le.mp hzre).1]
  have hshi : s.re ≤ 5 / 2 := by rw [hsre]; linarith [(abs_le.mp hzre).2]
  have him : |s.im| ≤ |y| + 1 := by rw [hsim]; exact (abs_add_le _ _).trans (by linarith)
  change ‖riemannZeta₁ s‖ ≤ _
  by_cases hs : s.re ≤ 3 / 2
  · exact (norm_riemannZeta₁_le_etaStrip hslo hs).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |s.im| + 20) (by linarith) 2) (by norm_num))
  · have hspos : 0 < s.re := by linarith
    have hre : |s.re| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, hshi⟩
    have hre1 : |s.re - 1| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hn : ‖s‖ ≤ |y| + 22 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      linarith
    have hn1 : ‖s - 1‖ ≤ |y| + 22 := by
      have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
      linarith
    have hp : ‖s - 1‖ * ‖s‖ ≤ (|y| + 22) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hn1 hn (norm_nonneg s) (by positivity)
    refine (norm_riemannZeta₁_le_of_etaFactor_lower hspos
      (quarter_le_norm_etaFactor_of_three_halves_le_re (by linarith))).trans ?_
    rw [div_le_iff₀ hspos]
    nlinarith [sq_nonneg (|y| + 22)]

theorem sixteenth_le_norm_localZetaPoleRemoved_zero (y : ℝ) :
    (1 / 16 : ℝ) ≤ ‖localZetaPoleRemoved y 0‖ := by
  let s : ℂ := 3 / 2 + I * y
  have hs : s.re = 3 / 2 := by simp [s]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs]; norm_num)
  have hinv : ‖(riemannZeta s)⁻¹‖ ≤ 8 :=
    (norm_inv_riemannZeta_safeLine_le_mass hs).trans staticContourSafeZetaDirichletMass_le_eight
  have hlower : (1 / 8 : ℝ) ≤ ‖riemannZeta s‖ := by
    have hprod := mul_le_mul_of_nonneg_right hinv (norm_nonneg (riemannZeta s))
    rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzne)] at hprod
    linarith
  have hn : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re, hs] at h
    linarith
  change (1 / 16 : ℝ) ≤ ‖riemannZeta₁ (s + 0)‖
  rw [add_zero, riemannZeta₁_eq_sub_one_mul hs1, norm_mul]
  nlinarith [mul_le_mul hn hlower (by norm_num : (0 : ℝ) ≤ 1 / 8) (norm_nonneg (s - 1))]

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaGaussianLocalizer
noncomputable section
open Complex Filter Metric Set
open scoped Topology

def regularized (s : ℂ) : ℂ := riemannZeta₁ s / (s + 1)

def carrier (t : ℝ) (s : ℂ) : ℂ :=
  regularized s * Complex.exp ((s - Complex.I * (t : ℂ)) ^ 2)

theorem regularized_eq {s : ℂ} (hs : s ≠ 1) :
    regularized s = (s - 1) / (s + 1) * riemannZeta s := by
  rw [regularized, riemannZeta₁_eq_sub_one_mul hs]
  ring

theorem add_one_ne_zero {s : ℂ} (hs : 0 ≤ s.re) : s + 1 ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
  linarith

theorem norm_ratio_le_one {s : ℂ} (hs : 0 ≤ s.re) : ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr (add_one_ne_zero hs))).mpr
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, sub_zero, add_zero]
  nlinarith

theorem norm_regularized_le_zeta {s : ℂ} (hs : 0 ≤ s.re) (hs1 : s ≠ 1) :
    ‖regularized s‖ ≤ ‖riemannZeta s‖ := by
  rw [regularized_eq hs1, norm_mul]
  simpa using mul_le_mul_of_nonneg_right (norm_ratio_le_one hs) (norm_nonneg (riemannZeta s))

theorem norm_carrier (t : ℝ) (s : ℂ) :
    ‖carrier t s‖ = ‖regularized s‖ * Real.exp (s.re ^ 2 - (s.im - t) ^ 2) := by
  simp only [carrier, norm_mul, Complex.norm_exp, pow_two, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero,
    sub_zero, zero_add]

theorem differentiableAt_carrier (t : ℝ) {s : ℂ} (hs : s + 1 ≠ 0) :
    DifferentiableAt ℂ (carrier t) s := by
  unfold carrier regularized
  exact ((differentiable_riemannZeta₁ s).div (by fun_prop) hs).mul (by fun_prop)

theorem norm_poleRemoved_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖riemannZeta₁ s‖ ≤ 8 * (|s.im| + 22) ^ 2 := by
  have h := norm_localZetaPoleRemoved_le s.im
    (z := ((s.re - 3 / 2 : ℝ) : ℂ)) (by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have he : (3 / 2 : ℂ) + Complex.I * (s.im : ℂ) +
      ((s.re - 3 / 2 : ℝ) : ℂ) = s := by
    apply Complex.ext <;> simp
  simpa only [localZetaPoleRemoved, he] using h

theorem norm_regularized_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖regularized s‖ ≤ 8 * (|s.im| + 22) ^ 2 := by
  have hden : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  rw [regularized, norm_div]
  exact (div_le_self (norm_nonneg _) hden).trans (norm_poleRemoved_le hs hs')

theorem quadratic_gaussian_bound (t y : ℝ) :
    (|y| + 22) ^ 2 * Real.exp (-(y - t) ^ 2) ≤ 2 * (1 + (|t| + 22) ^ 2) := by
  let d : ℝ := |y - t|
  let T : ℝ := |t| + 22
  have hd : 0 ≤ d := abs_nonneg _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hy : |y| + 22 ≤ d + T := by
    have h := abs_add_le (y - t) t
    rw [sub_add_cancel] at h
    dsimp [d, T]
    linarith
  have hs : (|y| + 22) ^ 2 ≤ 2 * d ^ 2 + 2 * T ^ 2 := by
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ |y| + 22) (add_nonneg hd hT) |>.mpr hy
    nlinarith [sq_nonneg (d - T)]
  have he : Real.exp (-d ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg d))
  have hx : d ^ 2 * Real.exp (-d ^ 2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show d ^ 2 ≤ Real.exp (d ^ 2) by linarith [Real.add_one_le_exp (d ^ 2)])
      (Real.exp_pos (-d ^ 2)).le
    simpa only [← Real.exp_add, add_neg_cancel, Real.exp_zero] using h
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-d ^ 2)).le
  have ht := mul_le_mul_of_nonneg_left he (sq_nonneg T)
  have heq : (y - t) ^ 2 = d ^ 2 := by dsimp [d]; rw [sq_abs]
  rw [heq]
  change _ ≤ 2 * (1 + T ^ 2)
  nlinarith

theorem carrier_bounded (t : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖carrier t s‖ ≤ 16 * Real.exp 3 * (1 + (|t| + 22) ^ 2) := by
  rw [norm_carrier]
  have hr : s.re ^ 2 ≤ 3 := by nlinarith
  have he := Real.exp_le_exp.mpr (sub_le_sub_right hr ((s.im - t) ^ 2))
  have hm := mul_le_mul (norm_regularized_le hs hs') he (Real.exp_pos _).le (by positivity)
  apply hm.trans
  rw [Real.exp_sub]
  have hx := quadratic_gaussian_bound t s.im
  have hm' := mul_le_mul_of_nonneg_left hx (show 0 ≤ 8 * Real.exp 3 by positivity)
  rw [Real.exp_neg] at hm'
  convert hm' using 1 <;> ring

end
end RiemannGaussian.ZetaGaussianLocalizer

end


-- Sidon.NumberTheory.MollifierGaussian
section

noncomputable section

open MeasureTheory
open Complex.HadamardThreeLines

namespace Sidon

def poleRemovedMollifierError (N : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta₁ s * dirichletMollifier N s - (s - 1)) / (s + 1)

def gaussianMollifier (N : ℕ) (R : ℝ) (s : ℂ) : ℂ :=
  poleRemovedMollifierError N s * Complex.exp ((s / (R : ℂ)) ^ 2)

theorem poleRemovedMollifierError_eq {N : ℕ} {s : ℂ} (hs : s ≠ 1) :
    poleRemovedMollifierError N s = (s - 1) / (s + 1) * mollifierError N s := by
  rw [poleRemovedMollifierError, RiemannGaussian.riemannZeta₁_eq_sub_one_mul hs,
    mollifierError]
  ring

theorem norm_poleRemovedMollifierError_le {N : ℕ} {s : ℂ} (hs : 0 ≤ s.re)
    (hs1 : s ≠ 1) : ‖poleRemovedMollifierError N s‖ ≤ ‖mollifierError N s‖ := by
  rw [poleRemovedMollifierError_eq hs1, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (RiemannGaussian.ZetaGaussianLocalizer.norm_ratio_le_one hs)

theorem analyticAt_gaussianMollifier (N : ℕ) (R : ℝ) {s : ℂ} (hs : s + 1 ≠ 0) :
    AnalyticAt ℂ (gaussianMollifier N R) s := by
  have hM : AnalyticAt ℂ (dirichletMollifier N) s := by
    unfold dirichletMollifier
    fun_prop
  unfold gaussianMollifier poleRemovedMollifierError
  exact ((((differentiable_riemannZeta₁.analyticAt s).mul hM).sub
    (analyticAt_id.sub analyticAt_const)).div (analyticAt_id.add analyticAt_const) hs).mul
      (by fun_prop)

theorem norm_gaussianMollifier (N : ℕ) {R : ℝ} (hR : R ≠ 0) (s : ℂ) :
    ‖gaussianMollifier N R s‖ = ‖poleRemovedMollifierError N s‖ *
      Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2) := by
  rw [gaussianMollifier, norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.mul_re, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

theorem norm_dirichletMollifier_le {N : ℕ} {s : ℂ} (hs : 0 ≤ s.re) :
    ‖dirichletMollifier N s‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ‖(ArithmeticFunction.moebius n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [norm_mul]
      apply mul_le_one₀ _ (norm_nonneg _) _
      · rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      · rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hs (Real.log_nonneg hn1))
    _ = _ := by simp

theorem norm_poleRemovedMollifierError_le_polynomial {N : ℕ} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖poleRemovedMollifierError N s‖ ≤ 8 * (N : ℝ) * (|s.im| + 22) ^ 2 + 1 := by
  have heq : poleRemovedMollifierError N s =
      RiemannGaussian.ZetaGaussianLocalizer.regularized s * dirichletMollifier N s -
        (s - 1) / (s + 1) := by
    unfold poleRemovedMollifierError RiemannGaussian.ZetaGaussianLocalizer.regularized
    ring
  rw [heq]
  calc
    _ ≤ ‖RiemannGaussian.ZetaGaussianLocalizer.regularized s * dirichletMollifier N s‖ +
        ‖(s - 1) / (s + 1)‖ := norm_sub_le _ _
    _ ≤ (8 * (|s.im| + 22) ^ 2) * (N : ℝ) + 1 := by
      rw [norm_mul]
      gcongr
      · exact RiemannGaussian.ZetaGaussianLocalizer.norm_regularized_le hs hs'
      · exact norm_dirichletMollifier_le (by linarith)
      · exact RiemannGaussian.ZetaGaussianLocalizer.norm_ratio_le_one (by linarith)
    _ = _ := by ring

theorem norm_poleRemovedMollifierError_le_quadratic {N : ℕ} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖poleRemovedMollifierError N s‖ ≤ (8000 * (N : ℝ) + 1) * (1 + s.im ^ 2) := by
  apply (norm_poleRemovedMollifierError_le_polynomial hs hs').trans
  have hsq : (|s.im| + 22) ^ 2 ≤ 1000 * (1 + s.im ^ 2) := by
    nlinarith [sq_nonneg (|s.im| - 22), sq_abs s.im]
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * (N : ℝ) by positivity)
  nlinarith [sq_nonneg s.im]

theorem quadratic_mul_gaussian_le {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (1 + t ^ 2) * Real.exp (-b * t ^ 2) ≤ 1 + 1 / b := by
  have hx : b * t ^ 2 * Real.exp (-b * t ^ 2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right
      (show b * t ^ 2 ≤ Real.exp (b * t ^ 2) by linarith [Real.add_one_le_exp (b * t ^ 2)])
      (Real.exp_nonneg (-b * t ^ 2))
    simpa only [← Real.exp_add, add_neg_cancel_left, Real.exp_zero, mul_neg,
      neg_mul, add_neg_cancel] using hh
  have hterm : t ^ 2 * Real.exp (-b * t ^ 2) ≤ 1 / b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith
  have he : Real.exp (-b * t ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  nlinarith

def gaussianMollifierEnvelope (N : ℕ) (R : ℝ) : ℝ :=
  (8000 * (N : ℝ) + 1) * Real.exp 3 * (1 + 2 * R ^ 2)

theorem norm_gaussianMollifier_le_decay {N : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖gaussianMollifier N R s‖ ≤
      gaussianMollifierEnvelope N R * Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hu : s.re ^ 2 / R ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  have hquad := quadratic_mul_gaussian_le (b := 1 / (2 * R ^ 2)) (by positivity) s.im
  have hq : (1 + s.im ^ 2) * Real.exp (-s.im ^ 2 / (2 * R ^ 2)) ≤ 1 + 2 * R ^ 2 := by
    have he : -(1 / (2 * R ^ 2)) * s.im ^ 2 = -s.im ^ 2 / (2 * R ^ 2) := by ring
    have he' : 1 / (1 / (2 * R ^ 2)) = 2 * R ^ 2 := by simp
    rw [he, he'] at hquad
    exact hquad
  rw [norm_gaussianMollifier N hR0.ne']
  calc
    _ ≤ ((8000 * (N : ℝ) + 1) * (1 + s.im ^ 2)) *
        Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2) := by
      gcongr
      exact norm_poleRemovedMollifierError_le_quadratic hs hs'
    _ = (8000 * (N : ℝ) + 1) * Real.exp (s.re ^ 2 / R ^ 2) *
        ((1 + s.im ^ 2) * Real.exp (-s.im ^ 2 / (2 * R ^ 2))) *
          Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by
      have he : (s.re ^ 2 - s.im ^ 2) / R ^ 2 = s.re ^ 2 / R ^ 2 +
          (-s.im ^ 2 / (2 * R ^ 2)) + (-s.im ^ 2 / (2 * R ^ 2)) := by ring
      rw [he, Real.exp_add, Real.exp_add]
      ring
    _ ≤ (8000 * (N : ℝ) + 1) * Real.exp 3 * (1 + 2 * R ^ 2) *
        Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by gcongr
    _ = _ := rfl

theorem analyticOnNhd_gaussianMollifier (N : ℕ) (R : ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    AnalyticOnNhd ℂ (gaussianMollifier N R) (verticalClosedStrip a b) := by
  intro s hs
  apply analyticAt_gaussianMollifier N R
  exact RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero (ha.trans hs.1)

theorem bddAbove_gaussianMollifier (N : ℕ) {R : ℝ} (hR : 1 ≤ R)
    {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : b ≤ 3 / 2) :
    BddAbove ((norm ∘ gaussianMollifier N R) '' verticalClosedStrip a b) := by
  refine ⟨gaussianMollifierEnvelope N R, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hh := norm_gaussianMollifier_le_decay (N := N) hR (ha.trans hs.1) (hs.2.trans hb)
  have he : Real.exp (-s.im ^ 2 / (2 * R ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  exact hh.trans (mul_le_of_le_one_right (by unfold gaussianMollifierEnvelope; positivity) he)

theorem integrable_gaussianMollifier_norm_sq (N : ℕ) {R σ : ℝ} (hR : 1 ≤ R)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hc : Continuous (fun t : ℝ => gaussianMollifier N R ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (analyticAt_gaussianMollifier N R ?_).continuousAt.comp (by fun_prop)
    apply RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero
    simpa using (show 0 ≤ σ by linarith)
  have hi := (integrable_exp_neg_mul_sq (b := 1 / R ^ 2) (by positivity)).const_mul
    (gaussianMollifierEnvelope N R ^ 2)
  have hc2 : Continuous (fun t : ℝ => ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
    fun_prop
  apply hi.mono' hc2.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := norm_gaussianMollifier_le_decay (N := N) hR
    (s := (σ : ℂ) + t * Complex.I) (by simpa using hσ) (by simpa using hσ')
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [mul_pow, ← Real.exp_nat_mul, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one,
    zero_mul, add_zero, zero_add] at hsquare
  convert hsquare using 1 <;> congr 1 <;> ring

theorem mollifierError_sq_le_poleRemoved_sq {N : ℕ} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) (ht : 1 ≤ |s.im|) :
    ‖mollifierError N s‖ ^ 2 ≤ 8 * ‖poleRemovedMollifierError N s‖ ^ 2 := by
  have hs1 : s ≠ 1 := by
    intro heq
    have hh := congrArg Complex.im heq
    simp only [Complex.one_im] at hh
    rw [hh] at ht
    norm_num at ht
  have hdenpos : 0 < ‖s + 1‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero (by linarith))
  have hden : ‖s + 1‖ ^ 2 ≤ 8 * ‖s - 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
    have ht2 : 1 ≤ s.im ^ 2 := by nlinarith [sq_abs s.im]
    nlinarith [sq_nonneg (s.re - 1)]
  rw [poleRemovedMollifierError_eq hs1, norm_mul, norm_div, mul_pow, div_pow]
  calc
    _ ≤ 8 * (‖s - 1‖ ^ 2 * ‖mollifierError N s‖ ^ 2) / ‖s + 1‖ ^ 2 := by
      apply (le_div_iff₀ hdenpos).mpr
      nlinarith [mul_le_mul_of_nonneg_right hden (sq_nonneg ‖mollifierError N s‖)]
    _ = _ := by ring

theorem mollifierError_sq_le_gaussianMollifier_sq {N : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (ht : 1 ≤ |s.im|) (htR : |s.im| ≤ R) :
    ‖mollifierError N s‖ ^ 2 ≤ 8 * Real.exp 2 * ‖gaussianMollifier N R s‖ ^ 2 := by
  have hR0 : 0 < R := by linarith
  have ht2 : s.im ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs s.im]
  have hexp : 1 ≤ Real.exp (2 + 2 * ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) := by
    apply Real.one_le_exp_iff.mpr
    have hh : -1 ≤ (s.re ^ 2 - s.im ^ 2) / R ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hR0)).mpr
      nlinarith [sq_nonneg s.re]
    linarith
  have hpole : ‖poleRemovedMollifierError N s‖ ^ 2 ≤
      Real.exp 2 * ‖gaussianMollifier N R s‖ ^ 2 := by
    rw [norm_gaussianMollifier N hR0.ne', mul_pow]
    have heq : (Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) ^ 2 =
        Real.exp (2 * ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) := by
      simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul ((s.re ^ 2 - s.im ^ 2) / R ^ 2) 2).symm
    rw [heq]
    calc
      _ ≤ ‖poleRemovedMollifierError N s‖ ^ 2 *
          Real.exp (2 + 2 * ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) :=
        le_mul_of_one_le_right (sq_nonneg _) hexp
      _ = _ := by rw [Real.exp_add]; ring
  calc
    _ ≤ 8 * ‖poleRemovedMollifierError N s‖ ^ 2 :=
      mollifierError_sq_le_poleRemoved_sq hs hs' ht
    _ ≤ 8 * (Real.exp 2 * ‖gaussianMollifier N R s‖ ^ 2) := by gcongr
    _ = _ := by ring

end Sidon

end
end


-- Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DerivativeOrderComparison
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters
def delta (k : ℕ) : ℝ := ((k : ℝ) + 2) * alpha k

theorem delta_eq_one_sub_line (k : ℕ) : delta k = 1 - line k := by
  unfold delta line
  ring

theorem delta_pos (k : ℕ) : 0 < delta k :=
  mul_pos (by positivity) (alpha_pos k)

theorem alpha_succ_le_half (k : ℕ) : alpha (k + 1) ≤ alpha k / 2 := by
  rw [alpha_succ]
  exact div_le_div_of_nonneg_left (alpha_pos k).le (by norm_num)
    (by linarith [alpha_pos k])

theorem delta_succ_le (k : ℕ) : delta (k + 1) ≤ delta k := by
  have h := mul_le_mul_of_nonneg_left (alpha_succ_le_half k)
    (show 0 ≤ (k : ℝ) + 3 by positivity)
  have hp : 0 ≤ ((k : ℝ) + 1) * alpha k := mul_nonneg (by positivity) (alpha_pos k).le
  unfold delta
  push_cast
  nlinarith

theorem delta_antitone : Antitone delta := antitone_nat_of_succ_le delta_succ_le

theorem transition_succ_le (k : ℕ) : transition (k + 1) ≤ transition k := by
  unfold transition
  rw [amp_succ]
  push_cast
  apply one_div_le_one_div_of_le
    (show 0 < (k : ℝ) + amp k by have h := amp_pos k; positivity)
  linarith [amp_le_one k]

theorem transition_antitone : Antitone transition :=
  antitone_nat_of_succ_le transition_succ_le

theorem transition_zero : transition 0 = 1 := by norm_num [transition, amp]

theorem adjacent_identity (k : ℕ) : alpha k - alpha (k + 1) =
    transition (k + 1) * (delta k - delta (k + 1)) := by
  have ha := alpha_pos k
  have hrec : alpha (k + 1) * (2 + 2 * alpha k) = alpha k := by
    rw [alpha_succ]
    field_simp
  have hp := amp_alpha_identity k
  have hd : (((k + 1 : ℕ) : ℝ) + amp (k + 1)) ≠ 0 := by
    have h := amp_pos (k + 1)
    positivity
  rw [show transition (k + 1) * (delta k - delta (k + 1)) =
    (delta k - delta (k + 1)) / (((k + 1 : ℕ) : ℝ) + amp (k + 1)) by
      unfold transition; ring]
  apply (eq_div_iff hd).mpr
  unfold delta
  rw [amp_succ]
  push_cast
  linear_combination (1 - amp k / 2) * hrec + (alpha (k + 1) / 2) * hp

theorem order_comparison (j k : ℕ) (hjk : j ≤ k) :
    alpha j + transition (j + 1) * (delta k - delta j) ≤ alpha k := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have ht := transition_antitone (Nat.succ_le_succ hjk)
    have hd : 0 ≤ delta k - delta (k + 1) := sub_nonneg.mpr (delta_succ_le k)
    have hm := mul_le_mul_of_nonneg_right ht hd
    have hi := adjacent_identity k
    nlinarith

theorem amp_le_delta (k : ℕ) : amp k ≤ delta k := by
  by_cases hk : 2 ≤ k
  · have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 0 ≤ ((k : ℝ) - 2) * alpha k := mul_nonneg (by linarith) (alpha_pos k).le
    have h2 : 0 ≤ amp k * alpha k := mul_nonneg (amp_pos k).le (alpha_pos k).le
    have h := amp_alpha_identity k
    unfold delta
    nlinarith
  · have hklt : k < 2 := Nat.lt_of_not_ge hk
    interval_cases k <;> norm_num [delta, alpha, amp]

theorem half_le_line (k : ℕ) (hk : 1 ≤ k) : 1 / 2 ≤ line k := by
  cases k with
  | zero => omega
  | succ k => exact half_le_line_succ k

end
end RiemannGaussian.DerivativeOrderComparison

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletPowerCoefficients
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletPowerCoefficients
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.LogarithmicDerivativeFamily
def factor (k : ℕ) : ℝ := ((k + 1).factorial : ℝ) / (2 : ℝ) ^ (k + 2)

theorem factor_pos (k : ℕ) : 0 < factor k := by
  unfold factor
  positivity

theorem factorial_le_double_power (k : ℕ) : (k + 1).factorial ≤ (2 : ℕ) ^ (2 ^ k) := by
  have hlin : ∀ j : ℕ, j + 1 ≤ (2 : ℕ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; omega
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : k + 2 ≤ (2 : ℕ) ^ (2 ^ k) :=
      (hlin (k + 1)).trans (pow_le_pow_right₀ (by norm_num) (hlin k))
    rw [Nat.factorial_succ]
    calc
      _ ≤ ((2 : ℕ) ^ (2 ^ k)) * ((2 : ℕ) ^ (2 ^ k)) := Nat.mul_le_mul hk ih
      _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

theorem double_power_exponent_le_one (k : ℕ) : (2 : ℝ) ^ k * alpha k ≤ 1 := by
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hd := denominator_ge_two k
  unfold alpha
  rw [mul_one_div]
  apply (div_le_one (by linarith)).mpr
  rw [pow_add]
  norm_num
  nlinarith

theorem factor_positive_power_le_two (k : ℕ) : factor k ^ alpha k ≤ 2 := by
  have hf : ((k + 1).factorial : ℝ) ≤ (2 : ℝ) ^ (2 ^ k) := by
    exact_mod_cast factorial_le_double_power k
  have hfac : factor k ≤ (2 : ℝ) ^ (2 ^ k) := by
    apply (div_le_self (by positivity : (0 : ℝ) ≤ (k + 1).factorial)
      (one_le_pow₀ (by norm_num))).trans hf
  have he : (((2 : ℕ) ^ k : ℕ) : ℝ) * alpha k ≤ 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using double_power_exponent_le_one k
  calc
    _ ≤ ((2 : ℝ) ^ (2 ^ k)) ^ alpha k :=
      Real.rpow_le_rpow (factor_pos k).le hfac (alpha_pos k).le
    _ = (2 : ℝ) ^ ((((2 : ℕ) ^ k : ℕ) : ℝ) * alpha k) :=
      (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one _

theorem factor_negative_power_le_two (k : ℕ) : factor k ^ (-alpha k) ≤ 2 := by
  have hf : (1 : ℝ) ≤ (k + 1).factorial := by
    exact_mod_cast (Nat.factorial_pos (k + 1))
  have hi : 1 / factor k ≤ (2 : ℝ) ^ (k + 2) := by
    unfold factor
    rw [one_div_div]
    exact div_le_self (by positivity) hf
  have he : ((k + 2 : ℕ) : ℝ) * alpha k ≤ 1 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using order_mul_alpha_le_one k
  calc
    _ = (1 / factor k) ^ alpha k := by
      rw [Real.div_rpow (by norm_num) (factor_pos k).le, Real.one_rpow,
        Real.rpow_neg (factor_pos k).le, one_div]
    _ ≤ ((2 : ℝ) ^ (k + 2)) ^ alpha k :=
      Real.rpow_le_rpow (one_div_pos.mpr (factor_pos k)).le hi (alpha_pos k).le
    _ = (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) * alpha k) :=
      (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one _

theorem lowerScale_eq_factor (t X : ℝ) (k : ℕ) :
    lowerScale t X k = factor k * t / X ^ (k + 2) := by
  unfold lowerScale factor
  rw [mul_pow]
  ring

theorem scale_power (k : ℕ) {t X : ℝ} (ht : 0 < t) (hX : 0 < X) (q : ℝ) :
    lowerScale t X k ^ q = factor k ^ q * t ^ q * X ^ (-((k : ℝ) + 2) * q) := by
  rw [lowerScale_eq_factor,
    Real.div_rpow (mul_nonneg (factor_pos k).le ht.le) (by positivity),
    Real.mul_rpow (factor_pos k).le ht.le,
    ← Real.rpow_natCast_mul hX.le, div_eq_mul_inv, ← Real.rpow_neg hX.le]
  congr 2
  push_cast
  ring

end
end RiemannGaussian.DirichletPowerCoefficients

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletBlockPowerProfile
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerCoefficients RiemannGaussian.DirichletDyadicBlocks
open RiemannGaussian.LogarithmicDerivativeFamily
def exactProfile (k : ℕ) (σ t X : ℝ) : ℝ :=
  128 * factor k ^ alpha k * t ^ alpha k * X ^ (1 - σ - ((k : ℝ) + 2) * alpha k) +
    32 * factor k ^ (-alpha k) * t ^ (-alpha k) *
      X ^ (beta k - σ + ((k : ℝ) + 2) * alpha k)

def profile (k : ℕ) (σ t X : ℝ) : ℝ :=
  256 * t ^ alpha k * X ^ (1 - σ - ((k : ℝ) + 2) * alpha k) +
    64 * t ^ (-alpha k) * X ^ (beta k - σ + ((k : ℝ) + 2) * alpha k)

theorem profile_nonneg (k : ℕ) (σ : ℝ) {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) :
    0 ≤ profile k σ t X := by
  unfold profile
  positivity

theorem exactProfile_le (k : ℕ) (σ : ℝ) {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) :
    exactProfile k σ t X ≤ profile k σ t X := by
  have h1 := mul_le_mul_of_nonneg_right (factor_positive_power_le_two k)
    (show 0 ≤ t ^ alpha k * X ^ (1 - σ - ((k : ℝ) + 2) * alpha k) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (factor_negative_power_le_two k)
    (show 0 ≤ t ^ (-alpha k) * X ^ (beta k - σ + ((k : ℝ) + 2) * alpha k) by positivity)
  unfold exactProfile profile
  nlinarith

theorem exact_bound (k j : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im) :
    ‖block s j‖ ≤ exactProfile k s.re s.im ((2 ^ j : ℕ) : ℝ) := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have h := UniformDirichletPowerBound.uniform_bound k hσ ht hX (2 ^ j) (2 ^ j)
    le_rfl (by dsimp [X]; ring_nf; exact le_rfl)
  rw [weight_eq_rpow s.re (by positivity)] at h
  change ‖block s j‖ ≤ 32 * (4 * X * lowerScale s.im X k ^ alpha k +
    X ^ beta k * lowerScale s.im X k ^ (-alpha k)) * X ^ (-s.re) at h
  have hlead : X ^ (1 - s.re - ((k : ℝ) + 2) * alpha k) =
      X * X ^ (-((k : ℝ) + 2) * alpha k) * X ^ (-s.re) := by
    rw [show 1 - s.re - ((k : ℝ) + 2) * alpha k =
      1 + (-((k : ℝ) + 2) * alpha k) + (-s.re) by ring,
      Real.rpow_add hX, Real.rpow_add hX, Real.rpow_one]
  have herr : X ^ (beta k - s.re + ((k : ℝ) + 2) * alpha k) =
      X ^ beta k * X ^ (-((k : ℝ) + 2) * (-alpha k)) * X ^ (-s.re) := by
    rw [show beta k - s.re + ((k : ℝ) + 2) * alpha k =
      beta k + (-((k : ℝ) + 2) * (-alpha k)) + (-s.re) by ring,
      Real.rpow_add hX, Real.rpow_add hX]
  apply h.trans_eq
  rw [scale_power k ht hX (alpha k), scale_power k ht hX (-alpha k)]
  change _ = exactProfile k s.re s.im X
  unfold exactProfile
  rw [hlead, herr]
  ring

theorem bound (k j : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im) :
    ‖block s j‖ ≤ profile k s.re s.im ((2 ^ j : ℕ) : ℝ) :=
  (exact_bound k j hσ ht).trans (exactProfile_le k s.re ht.le (by positivity))

end
end RiemannGaussian.DirichletBlockPowerProfile

end


-- Sidon.NumberTheory.RiemannGaussian.EtaAdjacentRatio
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian
noncomputable section
open Complex Set
open scoped Classical

def pairedEtaStepLog (x : ℝ) : ℝ := Real.log ((x + 1) / x)

def pairedEtaAdjacentRatio (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-s * (pairedEtaStepLog x : ℂ))

def pairedEtaAdjacentInverse (s : ℂ) (x : ℝ) : ℂ :=
  (1 + pairedEtaAdjacentRatio s x)⁻¹

theorem pairedEtaStepLog_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ pairedEtaStepLog x ∧ pairedEtaStepLog x ≤ 1 / x := by
  have hr : 1 ≤ (x + 1) / x := (le_div_iff₀ hx).mpr (by linarith)
  constructor
  · exact Real.log_nonneg hr
  · have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hr)
    apply h.trans_eq
    field_simp
    ring

theorem pairedEtaStepLog_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    pairedEtaStepLog y ≤ pairedEtaStepLog x := by
  have hy : 0 < y := hx.trans_le hxy
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (hx.trans_le hxy) hx]
  nlinarith

theorem norm_exp_sub_exp_le_of_re_nonpos {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp w - Complex.exp z‖ ≤ ‖w - z‖ := by
  have h := (convex_halfSpace_re_le 0).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Complex.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => show ‖Complex.exp u‖ ≤ (1 : ℝ) by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hu) hz hw
  simpa using h

theorem re_pairedEtaAdjacentRatio_nonneg {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : 0 ≤ (pairedEtaAdjacentRatio s x).re := by
  have hlog := pairedEtaStepLog_bounds hx
  have hangle : |s.im * pairedEtaStepLog x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlog.1]
    calc
      |s.im| * pairedEtaStepLog x ≤ ‖s‖ * pairedEtaStepLog x :=
        mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) hlog.1
      _ ≤ x * (1 / x) := mul_le_mul hscale hlog.2 hlog.1 (by positivity)
      _ = 1 := by field_simp
  have hcos : 0 ≤ Real.cos (s.im * pairedEtaStepLog x) := by
    apply Real.cos_nonneg_of_mem_Icc
    have hpi := Real.pi_gt_three
    constructor <;> linarith [(abs_le.mp hangle).1, (abs_le.mp hangle).2]
  rw [pairedEtaAdjacentRatio, Complex.exp_re]
  simp only [neg_mul, neg_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, Real.cos_neg]
  exact mul_nonneg (Real.exp_pos _).le hcos

theorem one_le_norm_one_add_pairedEtaAdjacentRatio {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : 1 ≤ ‖1 + pairedEtaAdjacentRatio s x‖ := by
  have h := re_pairedEtaAdjacentRatio_nonneg hx hscale
  have hn := Complex.re_le_norm (1 + pairedEtaAdjacentRatio s x)
  simp only [Complex.add_re, Complex.one_re] at hn
  linarith

theorem norm_pairedEtaAdjacentInverse_le_one {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) : ‖pairedEtaAdjacentInverse s x‖ ≤ 1 := by
  rw [pairedEtaAdjacentInverse, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale)

theorem norm_pairedEtaAdjacentRatio_sub_le {s : ℂ} (hs : 0 ≤ s.re)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖pairedEtaAdjacentRatio s y - pairedEtaAdjacentRatio s x‖ ≤
      ‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog y) := by
  have hleft (u : ℝ) (hu : 0 < u) : (-s * (pairedEtaStepLog u : ℂ)).re ≤ 0 := by
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg hs (pairedEtaStepLog_bounds hu).1)
  have h := norm_exp_sub_exp_le_of_re_nonpos (hleft x hx) (hleft y (hx.trans_le hxy))
  unfold pairedEtaAdjacentRatio
  apply h.trans_eq
  rw [show -s * (pairedEtaStepLog y : ℂ) - -s * (pairedEtaStepLog x : ℂ) =
    s * ((pairedEtaStepLog x - pairedEtaStepLog y : ℝ) : ℂ) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (pairedEtaStepLog_antitone hx hxy))]

theorem norm_pairedEtaAdjacentInverse_sub_le {s : ℂ} (hs : 0 ≤ s.re)
    {x y : ℝ} (hx : 0 < x) (hscale : ‖s‖ ≤ x) (hxy : x ≤ y) :
    ‖pairedEtaAdjacentInverse s y - pairedEtaAdjacentInverse s x‖ ≤
      ‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog y) := by
  have hx1 := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hy1 := one_le_norm_one_add_pairedEtaAdjacentRatio (hx.trans_le hxy) (hscale.trans hxy)
  have hx0 : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx1; linarith
  have hy0 : 1 + pairedEtaAdjacentRatio s y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy1; linarith
  have he : pairedEtaAdjacentInverse s y - pairedEtaAdjacentInverse s x =
      (pairedEtaAdjacentRatio s x - pairedEtaAdjacentRatio s y) /
        ((1 + pairedEtaAdjacentRatio s y) * (1 + pairedEtaAdjacentRatio s x)) := by
    unfold pairedEtaAdjacentInverse
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_sub_rev]
  calc
    _ ≤ ‖pairedEtaAdjacentRatio s y - pairedEtaAdjacentRatio s x‖ :=
      div_le_self (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hy1 hx1)
    _ ≤ _ := norm_pairedEtaAdjacentRatio_sub_le hs hx hxy

theorem cpow_add_one_eq_pairedEtaAdjacentRatio_mul (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x + 1 : ℝ) : ℂ) ^ (-s) = pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log (by linarith : 0 ≤ x + 1), ← Complex.ofReal_log hx.le,
    pairedEtaAdjacentRatio, ← Complex.exp_add]
  congr 1
  unfold pairedEtaStepLog
  rw [Real.log_div (by linarith : x + 1 ≠ 0) hx.ne']
  push_cast
  ring

theorem pairedEtaAdjacentInverse_mul_add (s : ℂ) {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    pairedEtaAdjacentInverse s x *
        ((x : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) = (x : ℂ) ^ (-s) := by
  rw [cpow_add_one_eq_pairedEtaAdjacentRatio_mul s hx]
  have hn := one_le_norm_one_add_pairedEtaAdjacentRatio hx hscale
  have hz : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; linarith
  unfold pairedEtaAdjacentInverse
  rw [show (x : ℂ) ^ (-s) + pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) =
    (1 + pairedEtaAdjacentRatio s x) * (x : ℂ) ^ (-s) by ring,
    ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

end
end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.EtaUniformTailBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian
noncomputable section
open Complex Filter Set Topology
open scoped Classical

def pairedEtaAdjacentBoundary (s : ℂ) (x : ℝ) : ℂ :=
  pairedEtaAdjacentInverse s x * (x : ℂ) ^ (-s)

def pairedEtaAdjacentDefect (s : ℂ) (x : ℝ) : ℂ :=
  (pairedEtaAdjacentInverse s x - pairedEtaAdjacentInverse s (x + 1)) *
      ((x + 1 : ℝ) : ℂ) ^ (-s) +
  (pairedEtaAdjacentInverse s (x + 2) - pairedEtaAdjacentInverse s (x + 1)) *
      ((x + 2 : ℝ) : ℂ) ^ (-s)

theorem cpow_pair_eq_adjacent_boundary_add_defect (s : ℂ) {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) =
      pairedEtaAdjacentBoundary s x - pairedEtaAdjacentBoundary s (x + 2) +
        pairedEtaAdjacentDefect s x := by
  have h1 := pairedEtaAdjacentInverse_mul_add s hx hscale
  have h2 := pairedEtaAdjacentInverse_mul_add s
    (show 0 < x + 1 by linarith) (show ‖s‖ ≤ x + 1 by linarith)
  rw [show x + 1 + 1 = x + 2 by ring] at h2
  unfold pairedEtaAdjacentBoundary pairedEtaAdjacentDefect
  linear_combination -h1 + h2

theorem norm_pairedEtaAdjacentBoundary_le {s : ℂ} {x : ℝ}
    (hx : 0 < x) (hscale : ‖s‖ ≤ x) :
    ‖pairedEtaAdjacentBoundary s x‖ ≤ x ^ (-s.re) := by
  rw [pairedEtaAdjacentBoundary, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  simpa using mul_le_mul_of_nonneg_right
    (norm_pairedEtaAdjacentInverse_le_one hx hscale) (Real.rpow_nonneg hx.le _)

theorem norm_pairedEtaAdjacentDefect_le {s : ℂ} (hs : 0 ≤ s.re)
    {X x : ℝ} (hX : 0 < X) (hscale : ‖s‖ ≤ X) (hx : X ≤ x) :
    ‖pairedEtaAdjacentDefect s x‖ ≤
      ‖s‖ * X ^ (-s.re) * (pairedEtaStepLog x - pairedEtaStepLog (x + 2)) := by
  have hx0 := hX.trans_le hx
  have h1 := norm_pairedEtaAdjacentInverse_sub_le hs hx0 (hscale.trans hx)
    (show x ≤ x + 1 by linarith)
  have h2 := norm_pairedEtaAdjacentInverse_sub_le hs
    (show 0 < x + 1 by linarith) (show ‖s‖ ≤ x + 1 by linarith)
    (show x + 1 ≤ x + 2 by linarith)
  rw [norm_sub_rev] at h1
  have hp (u : ℝ) (hu : X ≤ u) : ‖(u : ℂ) ^ (-s)‖ ≤ X ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hX.trans_le hu), Complex.neg_re]
    exact Real.rpow_le_rpow_of_nonpos hX hu (neg_nonpos.mpr hs)
  unfold pairedEtaAdjacentDefect
  calc
    _ ≤ _ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ (‖s‖ * (pairedEtaStepLog x - pairedEtaStepLog (x + 1))) * X ^ (-s.re) +
        (‖s‖ * (pairedEtaStepLog (x + 1) - pairedEtaStepLog (x + 2))) * X ^ (-s.re) := by
      exact add_le_add
        (mul_le_mul h1 (hp (x + 1) (by linarith)) (norm_nonneg _) ((norm_nonneg _).trans h1))
        (mul_le_mul h2 (hp (x + 2) (by linarith)) (norm_nonneg _) ((norm_nonneg _).trans h2))
    _ = _ := by ring

theorem pairedEtaCorePartialSum_sub_eq_adjacent (s : ℂ) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) -
        pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ) +
      ∑ n ∈ Finset.range M, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hx : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * (M + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
    have h := cpow_pair_eq_adjacent_boundary_add_defect s
      (x := ((2 * (M + N) + 1 : ℕ) : ℝ)) (by positivity) (hscale.trans hx)
    have hη : pairedEtaCorePartialSum (M + 1 + N) s =
        pairedEtaCorePartialSum (M + N) s + pairedEtaCoreSummand s (M + N) := by
      rw [show M + 1 + N = (M + N) + 1 by omega]
      exact Finset.sum_range_succ _ _
    rw [hη, Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    simp only [pairedEtaCoreSummand] at h ⊢
    push_cast at h ih ⊢
    rw [show (2 * ((M : ℂ) + N) + 1 + 1 : ℂ) = 2 * ((M : ℂ) + N) + 2 by ring] at h
    linear_combination ih + h

private theorem sum_norm_adjacent_defect_le {s : ℂ} (hs : 0 ≤ s.re) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.range M,
      ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        (pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) -
          pairedEtaStepLog ((2 * (M + N) + 1 : ℕ) : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hx : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * (M + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
    have h := norm_pairedEtaAdjacentDefect_le hs (by positivity) hscale hx
    rw [Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    push_cast at h ih ⊢
    calc
      _ ≤ _ := add_le_add ih h
      _ = _ := by ring

private theorem sum_norm_adjacent_defect_le_const {s : ℂ} (hs : 0 ≤ s.re) (N M : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑ n ∈ Finset.range M,
      ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) := by
  apply (sum_norm_adjacent_defect_le hs N M hscale).trans
  apply mul_le_mul_of_nonneg_left
    (sub_le_self _ (pairedEtaStepLog_bounds (by positivity)).1)
  positivity

theorem summable_pairedEtaAdjacentDefect_tail {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    Summable (fun n : ℕ => pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)) := by
  apply Summable.of_norm
  exact summable_of_sum_range_le (fun _ => norm_nonneg _)
    (fun M => sum_norm_adjacent_defect_le_const hs N M hscale)

theorem tsum_norm_pairedEtaAdjacentDefect_tail_le {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    (∑' n : ℕ, ‖pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      ‖s‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) *
        pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    (fun M => sum_norm_adjacent_defect_le_const hs N M hscale)

private theorem tendsto_adjacent_boundary_zero {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    Tendsto (fun M : ℕ => pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun M : ℕ => ((2 * (M + N) + 1 : ℕ) : ℝ) ^ (-s.re))
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · apply Filter.Eventually.of_forall
    intro M
    apply norm_pairedEtaAdjacentBoundary_le (by positivity)
    apply hscale.trans
    exact_mod_cast (show 2 * N + 1 ≤ 2 * (M + N) + 1 by omega)
  · exact (tendsto_pairedEtaOddEndpoint_rpow_zero hs).comp (tendsto_add_atTop_nat N)

theorem pairedEtaCore_tail_eq_adjacent {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) +
        ∑' n : ℕ, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  have he := ((summable_pairedEtaCoreSummand hs).tendsto_sum_tsum_nat.comp
    (tendsto_add_atTop_nat N)).sub_const (pairedEtaCorePartialSum N s)
  change Tendsto (fun M => pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s)
    atTop (nhds (pairedEtaCore s - pairedEtaCorePartialSum N s)) at he
  simp_rw [pairedEtaCorePartialSum_sub_eq_adjacent s N _ hscale] at he
  have hb := tendsto_adjacent_boundary_zero hs N hscale
  have hr := (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).tendsto_sum_tsum_nat
  have ht := ((tendsto_const_nhds
    (x := pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ))).sub hb).add hr
  simpa using tendsto_nhds_unique he ht

theorem norm_pairedEtaCore_tail_le_two {s : ℂ} (hs : 0 < s.re) (N : ℕ)
    (hscale : ‖s‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      2 * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  let X : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hX : 0 < X := by dsimp [X]; positivity
  have hl := pairedEtaStepLog_bounds hX
  have hbudget : ‖s‖ * pairedEtaStepLog X ≤ 1 := by
    calc
      _ ≤ X * (1 / X) := mul_le_mul hscale hl.2 hl.1 hX.le
      _ = 1 := by field_simp
  rw [pairedEtaCore_tail_eq_adjacent hs N hscale]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ X ^ (-s.re) + ‖s‖ * X ^ (-s.re) * pairedEtaStepLog X := by
      exact add_le_add (norm_pairedEtaAdjacentBoundary_le hX hscale)
        ((norm_tsum_le_tsum_norm (summable_pairedEtaAdjacentDefect_tail hs.le N hscale).norm).trans
          (tsum_norm_pairedEtaAdjacentDefect_tail_le hs.le N hscale))
    _ ≤ 2 * X ^ (-s.re) := by
      have h := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hX.le (-s.re))
      nlinarith only [h]

end
end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaDyadicTruncation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaDyadicTruncation
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks
def etaFactor (s : ℂ) : ℂ := 1 - 2 * zetaPrimeFeature s 2

def remainder (s : ℂ) (J : ℕ) : ℂ := pairedEtaCore s - pairedEtaCorePartialSum (2 ^ J) s

def depth (s : ℂ) : ℕ := Nat.log 2 (⌈‖s‖⌉₊ + 1)

theorem factor_eq (s : ℂ) : etaFactor s = 1 - 2 * (2 : ℂ) ^ (-s) := by
  rw [etaFactor, feature_eq_cpow s (by norm_num)]
  norm_num only [Nat.cast_ofNat]

theorem reconstruction {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (J : ℕ) :
    etaFactor s * riemannZeta s =
      (∑ j ∈ Finset.range (J + 1), block s j) -
        2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
          zetaPrimeFeature s (2 ^ (J + 1)) + remainder s J := by
  rw [factor_eq, ← pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1,
    ← eta_pow_two_eq_blocks, remainder]
  ring

theorem remainder_bound {s : ℂ} (hs : 0 < s.re) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖remainder s J‖ ≤ 2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re)) :=
  norm_pairedEtaCore_tail_le_two hs (2 ^ J) hscale

theorem factor_lower (s : ℂ) : (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖etaFactor s‖ := by
  have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
  rw [norm_two_mul_two_cpow_neg, norm_one, norm_sub_rev, ← factor_eq] at h
  exact h

theorem factor_lower_pos {s : ℂ} (hs : s.re < 1) : 0 < (2 : ℝ) ^ (1 - s.re) - 1 := by
  have h : 1 < (2 : ℝ) ^ (1 - s.re) := Real.one_lt_rpow (by norm_num) (by linarith)
  linarith

theorem zeta_norm_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤
      (‖(∑ j ∈ Finset.range (J + 1), block s j) -
          2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
            zetaPrimeFeature s (2 ^ (J + 1))‖ +
        2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re))) /
          ((2 : ℝ) ^ (1 - s.re) - 1) := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  have he := congrArg norm (reconstruction hs hne J)
  rw [norm_mul] at he
  have hu := (norm_add_le
    ((∑ j ∈ Finset.range (J + 1), block s j) -
      2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
        zetaPrimeFeature s (2 ^ (J + 1))) (remainder s J)).trans
    (add_le_add le_rfl (remainder_bound hs J hscale))
  rw [← he] at hu
  have hl := mul_le_mul_of_nonneg_right (factor_lower s) (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (factor_lower_pos hs1)).mpr
  nlinarith

theorem depth_scale (s : ℂ) : ‖s‖ ≤ ((2 * 2 ^ depth s + 1 : ℕ) : ℝ) := by
  have hc := Nat.le_ceil ‖s‖
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (⌈‖s‖⌉₊ + 1)
  rw [Nat.succ_eq_add_one, pow_succ] at hp
  have hr : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) < ((2 : ℕ) ^ depth s * 2 : ℕ) := by
    exact_mod_cast hp
  push_cast at hr ⊢
  nlinarith

theorem depth_length_lt (s : ℂ) : ((2 ^ depth s : ℕ) : ℝ) < ‖s‖ + 2 := by
  have hp := Nat.pow_log_le_self 2 (show ⌈‖s‖⌉₊ + 1 ≠ 0 by omega)
  have hr : ((2 ^ depth s : ℕ) : ℝ) ≤ ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (norm_nonneg s)
  push_cast at hr ⊢
  linarith

theorem depth_le_log (s : ℂ) : (depth s : ℝ) ≤ Real.log (‖s‖ + 2) / Real.log 2 := by
  have hp : (2 : ℝ) ^ depth s ≤ ‖s‖ + 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (depth_length_lt s).le
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ depth s) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

end
end RiemannGaussian.ZetaDyadicTruncation

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaDyadicPowerBound
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.DirichletBlockPowerProfile RiemannGaussian.ZetaDyadicTruncation
open scoped Classical

def blockBudget (s : ℂ) (orders : ℕ → ℕ) (j : ℕ) : ℝ :=
  min (((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re))
    (profile (orders j) s.re s.im ((2 ^ j : ℕ) : ℝ))

def prefixBudget (s : ℂ) (orders : ℕ → ℕ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, blockBudget s orders j

theorem trivial_block_bound {s : ℂ} (hσ : 0 ≤ s.re) (j : ℕ) :
    ‖block s j‖ ≤ ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) := by
  unfold block
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range (2 ^ j), (((2 ^ j : ℕ) : ℝ) ^ (-s.re)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_zetaPrimeFeature, weight_eq_rpow s.re (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast Nat.le_add_right (2 ^ j) n) (neg_nonpos.mpr hσ)
    _ = _ := by simp

theorem block_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (j : ℕ) : ‖block s j‖ ≤ blockBudget s orders j :=
  le_min (trivial_block_bound hσ j) (DirichletBlockPowerProfile.bound (orders j) j hσ ht)

theorem blockBudget_nonneg {s : ℂ} (ht : 0 < s.im) (orders : ℕ → ℕ) (j : ℕ) :
    0 ≤ blockBudget s orders j :=
  le_min (by positivity) (profile_nonneg _ _ ht.le (by positivity))

theorem prefixBudget_nonneg {s : ℂ} (ht : 0 < s.im) (orders : ℕ → ℕ) (J : ℕ) :
    0 ≤ prefixBudget s orders J :=
  Finset.sum_nonneg fun j _ ↦ blockBudget_nonneg ht orders j

theorem prefixBudget_le_succ {s : ℂ} (ht : 0 < s.im) (orders : ℕ → ℕ) (J : ℕ) :
    prefixBudget s orders J ≤ prefixBudget s orders (J + 1) := by
  unfold prefixBudget
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (blockBudget_nonneg ht orders J)

theorem prefix_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (J : ℕ) :
    ‖positivePrefix s (2 ^ J)‖ ≤ prefixBudget s orders J := by
  rw [prefix_pow_two]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ block_bound hσ ht orders j)

theorem eta_prefix_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (J : ℕ) :
    ‖pairedEtaCorePartialSum (2 ^ J) s‖ ≤
      prefixBudget s orders (J + 1) + (2 : ℝ) ^ (1 - s.re) * prefixBudget s orders J +
        ((2 ^ (J + 1) : ℕ) : ℝ) ^ (-s.re) := by
  rw [eta_pow_two_eq_blocks, ← prefix_pow_two, ← prefix_pow_two]
  apply (norm_sub_le _ _).trans
  apply add_le_add _ (by rw [norm_zetaPrimeFeature, weight_eq_rpow _ (by positivity)])
  apply (norm_sub_le _ _).trans
  apply add_le_add (prefix_bound hσ ht orders (J + 1))
  rw [norm_mul, feature_eq_cpow s (by norm_num), Nat.cast_ofNat, norm_two_mul_two_cpow_neg]
  exact mul_le_mul_of_nonneg_left (prefix_bound hσ ht orders J) (by positivity)

theorem zeta_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im)
    (orders : ℕ → ℕ) (J : ℕ) (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤
      (prefixBudget s orders (J + 1) + (2 : ℝ) ^ (1 - s.re) * prefixBudget s orders J +
        ((2 ^ (J + 1) : ℕ) : ℝ) ^ (-s.re) +
          2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re))) /
            ((2 : ℝ) ^ (1 - s.re) - 1) := by
  apply (ZetaDyadicTruncation.zeta_norm_le hσ hσ1 J hscale).trans
  apply div_le_div_of_nonneg_right _ (factor_lower_pos hσ1).le
  apply add_le_add _ le_rfl
  rw [← eta_pow_two_eq_blocks]
  exact eta_prefix_bound hσ.le ht orders J

theorem canonical_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im)
    (orders : ℕ → ℕ) :
    ‖riemannZeta s‖ ≤
      (prefixBudget s orders (depth s + 1) +
        (2 : ℝ) ^ (1 - s.re) * prefixBudget s orders (depth s) +
          ((2 ^ (depth s + 1) : ℕ) : ℝ) ^ (-s.re) +
            2 * (((2 * 2 ^ depth s + 1 : ℕ) : ℝ) ^ (-s.re))) /
              ((2 : ℝ) ^ (1 - s.re) - 1) :=
  zeta_bound hσ hσ1 ht orders (depth s) (depth_scale s)

theorem simple_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im)
    (orders : ℕ → ℕ) :
    ‖riemannZeta s‖ ≤ 6 * (prefixBudget s orders (depth s + 1) + 1) / (1 - s.re) := by
  have h := (le_div_iff₀ (factor_lower_pos hσ1)).mp (canonical_bound hσ hσ1 ht orders)
  have hb0 := prefixBudget_nonneg ht orders (depth s)
  have hb1 := prefixBudget_nonneg ht orders (depth s + 1)
  have hb := prefixBudget_le_succ ht orders (depth s)
  have htwo : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - s.re ≤ 1)).trans_eq
    exact Real.rpow_one _
  have hm := mul_le_mul_of_nonneg_right htwo hb0
  have he : ((2 ^ (depth s + 1) : ℕ) : ℝ) ^ (-s.re) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
      (by linarith)
  have he' : (((2 * 2 ^ depth s + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  have hgap : (1 - s.re) / 2 ≤ (2 : ℝ) ^ (1 - s.re) - 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hg := Real.add_one_le_exp (Real.log 2 * (1 - s.re))
    nlinarith [Real.log_two_gt_d9]
  have hg := mul_le_mul_of_nonneg_right hgap (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (by linarith : 0 < 1 - s.re)).mpr
  nlinarith

end
end RiemannGaussian.ZetaDyadicPowerBound

end


-- Sidon.NumberTheory.RiemannGaussian.EtaOddPowerQuadrature
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

theorem norm_cpow_sub_cpow_le_above (r : ℂ) {a x y : ℝ} (ha : 0 < a)
    (hr : r.re ≤ 1) (hx : a ≤ x) (hy : a ≤ y) :
    ‖(y : ℂ) ^ r - (x : ℂ) ^ r‖ ≤ ‖r‖ * a ^ (r.re - 1) * |y - x| := by
  have hderiv (z : ℝ) (hz : z ∈ Ici a) :
      HasDerivWithinAt (fun t : ℝ ↦ (t : ℂ) ^ r)
        (r * (z : ℂ) ^ (r - 1)) (Ici a) z := by
    by_cases hr0 : r = 0
    · subst r
      simpa using (hasDerivAt_const (x := z) (c := (1 : ℂ))).hasDerivWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (ha.trans_le hz)) hr0).hasDerivWithinAt
  have hbound (z : ℝ) (hz : z ∈ Ici a) :
      ‖r * (z : ℂ) ^ (r - 1)‖ ≤ ‖r‖ * a ^ (r.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hz)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hz (by linarith))
      (norm_nonneg _)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ici a) hx hy

end

end RiemannGaussian

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerCell
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerCell
noncomputable section
open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval

def partialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

def cell (s : ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (-s) - ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), (x : ℂ) ^ (-s)

def regularizedCell (s : ℂ) (n : ℕ) : ℂ :=
  (1 - s) * (n + 1 : ℂ) ^ (-s) -
    (n + 2 : ℂ) ^ (1 - s) + (n + 1 : ℂ) ^ (1 - s)

theorem intervalIntegrable_power (s : ℂ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ (-s)) volume (n + 1 : ℝ) (n + 2 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
  exact Complex.ofReal_mem_slitPlane.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n, hx.1])

theorem integral_power {s : ℂ} (hs : s ≠ 1) (n : ℕ) :
    (∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), (x : ℂ) ^ (-s)) =
      ((n + 2 : ℂ) ^ (1 - s) - (n + 1 : ℂ) ^ (1 - s)) / (1 - s) := by
  have h := integral_cpow (a := (n + 1 : ℝ)) (b := (n + 2 : ℝ)) (r := -s)
    (Or.inr ⟨by simpa using hs, by
      rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)]
      simp only [mem_Icc, not_and]
      intro h
      linarith [Nat.cast_nonneg (α := ℝ) n]⟩)
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat, show -s + 1 = 1 - s by ring] using h

theorem regularizedCell_eq (s : ℂ) (n : ℕ) :
    regularizedCell s n = (1 - s) * cell s n := by
  by_cases hs : s = 1
  · subst s
    simp [regularizedCell]
  · unfold regularizedCell cell
    rw [integral_power hs]
    field_simp
    ring

theorem differentiable_regularizedCell (n : ℕ) :
    Differentiable ℂ (fun s ↦ regularizedCell s n) := by
  unfold regularizedCell
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hlin : Differentiable ℂ (fun s : ℂ ↦ 1 - s) := by fun_prop
  exact ((hlin.mul (differentiable_neg.const_cpow (Or.inl h1))).sub
    (hlin.const_cpow (Or.inl h2))).add (hlin.const_cpow (Or.inl h1))

theorem norm_cell_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖cell s n‖ ≤ ‖s‖ * (n + 1 : ℝ) ^ (-s.re - 1) := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have he : cell s n = ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ),
      ((n + 1 : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegrable_power s n),
      intervalIntegral.integral_const]
    simp only [show (n + 2 : ℝ) - (n + 1) = 1 by ring, one_smul]
    rfl
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n + 1 : ℝ)) (b := (n + 2 : ℝ))
    (f := fun x ↦ (n + 1 : ℂ) ^ (-s) - (x : ℂ) ^ (-s))
    (C := ‖s‖ * (n + 1 : ℝ) ^ (-s.re - 1)) (by
      intro x hx
      rw [uIoc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
      have h := norm_cpow_sub_cpow_le_above (-s) hn
        (by simp only [neg_re]; linarith) hx.1.le (le_refl _)
      have hd : |(n + 1 : ℝ) - x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
      simp only [norm_neg, neg_re, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one] at h
      exact h.trans (by nlinarith [mul_nonneg (norm_nonneg s) (Real.rpow_nonneg hn.le (-s.re - 1))]))
  simpa only [show (n + 2 : ℝ) - (n + 1) = 1 by ring, abs_one, mul_one] using hb

theorem summable_envelope {p : ℝ} (hp : 0 < p) :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-p - 1)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (p + 1)).mpr (by linarith)
  apply h.congr
  intro n
  rw [abs_of_nonneg (by positivity), one_div, ← Real.rpow_neg (by positivity)]
  congr 1
  ring

theorem summable_cell {s : ℂ} (hs : 0 < s.re) : Summable (cell s) :=
  ((summable_envelope hs).mul_left ‖s‖).of_norm_bounded (norm_cell_le hs)

theorem summable_regularizedCell {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n ↦ regularizedCell s n) := by
  simpa only [regularizedCell_eq] using (summable_cell hs).mul_left (1 - s)

theorem sum_regularizedCell (N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.range N, regularizedCell s n) =
      (1 - s) * partialSum N s - (N + 1 : ℂ) ^ (1 - s) + 1 := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [partialSum, Finset.sum_range_succ, regularizedCell, Nat.cast_add, Nat.cast_one]
      have he : (N : ℂ) + 1 + 1 = N + 2 := by ring
      rw [he]
      ring

end
end RiemannGaussian.ZetaEulerCell

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerContinuation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerContinuation
noncomputable section
open Complex Filter MeasureTheory Metric Set Topology RiemannGaussian.ZetaEulerCell
def regularizedSum (s : ℂ) : ℂ := ∑' n, regularizedCell s n

theorem differentiableOn_regularizedSum :
    DifferentiableOn ℂ regularizedSum {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let d := z.re / 2
  let K := ‖z‖ + d
  have hd : 0 < d := by dsimp [d]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm := (summable_envelope hd).mul_left ((1 + K) * K)
  have hb (n : ℕ) (w : ℂ) (hw : w ∈ ball z d) :
      ‖regularizedCell w n‖ ≤ (1 + K) * K * (n + 1 : ℝ) ^ (-d - 1) := by
    have hn : ‖w - z‖ < d := by simpa only [mem_ball, dist_eq_norm] using hw
    have hre : d < w.re := by
      have h := Complex.abs_re_le_norm (w - z)
      simp only [sub_re] at h
      dsimp only [d] at hn ⊢
      linarith [neg_le_abs (w.re - z.re)]
    have hnw : ‖w‖ ≤ K := by
      have h := norm_add_le (w - z) z
      simp only [sub_add_cancel] at h
      dsimp only [K]
      linarith
    have hn1 : ‖1 - w‖ ≤ 1 + K := by
      have h := norm_sub_le (1 : ℂ) w
      simp only [norm_one] at h
      linarith
    have hp : (n + 1 : ℝ) ^ (-w.re - 1) ≤ (n + 1 : ℝ) ^ (-d - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    rw [regularizedCell_eq, norm_mul]
    calc
      _ ≤ ‖1 - w‖ * (‖w‖ * (n + 1 : ℝ) ^ (-w.re - 1)) :=
        mul_le_mul_of_nonneg_left (norm_cell_le (hd.trans hre) n) (norm_nonneg _)
      _ ≤ (1 + K) * (K * (n + 1 : ℝ) ^ (-d - 1)) :=
        mul_le_mul hn1 (mul_le_mul hnw hp (by positivity) hK) (by positivity) (by positivity)
      _ = _ := by ring
  have hl : DifferentiableOn ℂ regularizedSum (ball z d) := by
    unfold regularizedSum
    exact Complex.differentiableOn_tsum_of_summable_norm hm
      (fun n ↦ (differentiable_regularizedCell n).differentiableOn) isOpen_ball hb
  exact (hl.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hd))).differentiableWithinAt

theorem analyticOnNhd_regularizedSum :
    AnalyticOnNhd ℂ regularizedSum {s : ℂ | 0 < s.re} :=
  differentiableOn_regularizedSum.analyticOnNhd (Complex.isOpen_re_gt 0)

theorem endpoint_tendsto_zero {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ (N + 1 : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).comp ht
  apply h.congr
  intro N
  rw [show (N + 1 : ℂ) = ((N + 1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Function.comp_apply, sub_re, one_re, neg_sub]

theorem regularizedSum_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    regularizedSum s = 1 - riemannZeta₁ s := by
  have hp : Tendsto (fun N : ℕ ↦ partialSum N s) atTop (𝓝 (riemannZeta s)) := by
    simpa only [partialSum, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one,
      Complex.ofReal_add, Complex.ofReal_one] using
      (hasSum_nat_add_one_cpow_neg_riemannZeta hs).tendsto_sum_nat
  have he := endpoint_tendsto_zero hs
  have hlim := ((hp.const_mul (1 - s)).sub he).add_const 1
  have hreg := (summable_regularizedCell (by linarith : 0 < s.re)).hasSum.tendsto_sum_nat
  simp only [sum_regularizedCell] at hreg
  simp only [sub_zero] at hlim
  have hu := tendsto_nhds_unique hreg hlim
  have hsne : s ≠ 1 := by intro h; simp [h] at hs
  have hmul : (s - 1) * riemannZeta s = riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
  change regularizedSum s = (1 - s) * riemannZeta s + 1 at hu
  linear_combination hu - hmul

theorem regularizedSum_eq {s : ℂ} (hs : 0 < s.re) :
    regularizedSum s = 1 - riemannZeta₁ s := by
  have hr : AnalyticOnNhd ℂ (fun s : ℂ ↦ 1 - riemannZeta₁ s) {s : ℂ | 0 < s.re} :=
    ((differentiable_const (1 : ℂ)).sub differentiable_riemannZeta₁).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt 0)
  have he : regularizedSum =ᶠ[𝓝 (2 : ℂ)] (fun s ↦ 1 - riemannZeta₁ s) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s h
    exact regularizedSum_eq_of_one_lt_re h
  exact analyticOnNhd_regularizedSum.eqOn_of_preconnected_of_eventuallyEq hr
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by norm_num : (2 : ℂ).re > 0) he hs

theorem tsum_cell_eq {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) :
    (∑' n, cell s n) = riemannZeta s - 1 / (s - 1) := by
  have h := regularizedSum_eq hs
  have hm : (s - 1) * riemannZeta s = riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
  simp only [regularizedSum, regularizedCell_eq, tsum_mul_left, ← hm] at h
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hsne) : 1 - s ≠ 0)
  rw [h]
  field_simp
  ring

end
end RiemannGaussian.ZetaEulerContinuation

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerTruncation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerTruncation
noncomputable section
open Complex Filter MeasureTheory Set Topology RiemannGaussian.ZetaEulerCell RiemannGaussian.ZetaEulerContinuation
def remainder (N : ℕ) (s : ℂ) : ℂ := ∑' n, cell s (n + N)

theorem sum_cell {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, cell s n) =
      partialSum N s + ((N + 1 : ℂ) ^ (1 - s) - 1) / (s - 1) := by
  have h := sum_regularizedCell N s
  simp only [regularizedCell_eq, ← Finset.mul_sum] at h
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hs) : 1 - s ≠ 0)
  rw [h]
  field_simp
  ring

theorem summable_remainder {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n ↦ cell s (n + N)) :=
  (summable_cell hs).comp_injective (by intro a b h; exact Nat.add_right_cancel h)

theorem zeta_eq_partialSum_add_endpoint_add_remainder {s : ℂ}
    (hs : 0 < s.re) (hsne : s ≠ 1) (N : ℕ) :
    riemannZeta s = partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s := by
  have h := (summable_cell hs).sum_add_tsum_nat_add N
  rw [sum_cell hsne, tsum_cell_eq hs hsne] at h
  change partialSum N s + ((N + 1 : ℂ) ^ (1 - s) - 1) / (s - 1) + remainder N s =
    riemannZeta s - 1 / (s - 1) at h
  linear_combination -h

theorem tsum_envelope_tail_le {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, (n + N + 1 : ℝ) ^ (-p - 1)) ≤ (N : ℝ) ^ (-p) / p := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have he : -p - 1 < -1 := by linarith
  have ha : AntitoneOn (fun x : ℝ ↦ x ^ (-p - 1)) (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNp.trans_le hx) hxy (by linarith)
  have h := ha.tsum_comp_add_le_integral N (integrableOn_Ioi_rpow_of_lt he hNp)
    (fun x hx ↦ Real.rpow_nonneg (hNp.trans hx).le _)
  simp only [Nat.cast_add, Nat.cast_one] at h
  apply h.trans_eq
  rw [integral_Ioi_rpow_of_lt he hNp]
  rw [show -p - 1 + 1 = -p by ring]
  ring

theorem norm_remainder_le {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖remainder N s‖ ≤ ‖s‖ / s.re * (N : ℝ) ^ (-s.re) := by
  have hm := ((summable_envelope hs).comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + N) by intro a b h; exact Nat.add_right_cancel h)).mul_left ‖s‖
  have hn := (summable_remainder hs N).norm
  have hb := hn.tsum_le_tsum (fun n ↦ norm_cell_le hs (n + N)) hm
  unfold remainder
  apply (norm_tsum_le_tsum_norm hn).trans (hb.trans _)
  simp only [Nat.cast_add, tsum_mul_left]
  have h := mul_le_mul_of_nonneg_left (tsum_envelope_tail_le hs hN) (norm_nonneg s)
  convert h using 1
  ring

theorem norm_zeta_sub_partialSum_le {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - partialSum N s‖ ≤
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ + ‖s‖ / s.re * (N : ℝ) ^ (-s.re) := by
  rw [zeta_eq_partialSum_add_endpoint_add_remainder hs hsne N]
  have he : partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s - partialSum N s =
      (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hp : ‖(N + 1 : ℂ) ^ (1 - s) / (s - 1)‖ =
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
    rw [norm_div]
    congr 1
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < N + 1) (1 - s)
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      sub_re, one_re] using h
  rw [hp]
  exact add_le_add_right (norm_remainder_le hs hN) _

end
end RiemannGaussian.ZetaEulerTruncation

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerBernoulli
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerBernoulli
noncomputable section
open Complex Filter MeasureTheory Set Topology RiemannGaussian.ZetaEulerCell RiemannGaussian.ZetaEulerTruncation
open scoped Interval

def kernel (a x : ℝ) : ℝ := (x - a) ^ 2 - (x - a) + 1 / 6

def block (s : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ),
    (kernel (n + 1) x : ℂ) * (x : ℂ) ^ (-s - 2)

def tail (N : ℕ) (s : ℂ) : ℂ := ∑' n, block s (n + N)

private theorem power_deriv (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

private theorem power_integrable (r : ℂ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ r) volume (n + 1 : ℝ) (n + 2 : ℝ) := by
  simpa only [neg_neg] using intervalIntegrable_power (-r) n

private theorem linear_deriv (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ((y - a - 1 / 2 : ℝ) : ℂ)) 1 x := by
  simpa using (((hasDerivAt_id x).sub_const a).sub_const (1 / 2)).ofReal_comp

private theorem kernel_deriv (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (kernel a y : ℂ))
      (2 * ((x - a - 1 / 2 : ℝ) : ℂ)) x := by
  have h := (((((hasDerivAt_id x).sub_const a).pow 2).sub
    ((hasDerivAt_id x).sub_const a)).add_const (1 / 6)).ofReal_comp
  convert h using 1
  · rfl
  dsimp
  push_cast
  ring

theorem cell_eq (s : ℂ) (n : ℕ) :
    cell s n = ((n + 1 : ℂ) ^ (-s) - (n + 2 : ℂ) ^ (-s)) / 2 +
      s / 12 * ((n + 1 : ℂ) ^ (-s - 1) - (n + 2 : ℂ) ^ (-s - 1)) -
      s * (s + 1) / 2 * block s n := by
  have hpos {x : ℝ} (hx : x ∈ [[(n + 1 : ℝ), (n + 2 : ℝ)]]) : 0 < x := by
    rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ linear_deriv (n + 1) x)
    (fun x hx ↦ power_deriv (-s) (hpos hx))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℂ))
      volume (n + 1 : ℝ) (n + 2 : ℝ))
    ((power_integrable (-s - 1) n).const_mul (-s))
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ kernel_deriv (n + 1) x)
    (fun x hx ↦ power_deriv (-s - 1) (hpos hx))
    (show IntervalIntegrable (fun x : ℝ ↦ 2 * ((x - (n + 1) - 1 / 2 : ℝ) : ℂ))
      volume (n + 1 : ℝ) (n + 2 : ℝ) from (by fun_prop : Continuous _).intervalIntegrable _ _)
    ((power_integrable (-s - 1 - 1) n).const_mul (-s - 1))
  simp only [one_mul] at h1
  simp only [show -s - 1 - 1 = -s - 2 by ring] at h2
  simp_rw [show ∀ x : ℝ,
    ((x - (n + 1) - 1 / 2 : ℝ) : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) =
      -s * (((x - (n + 1) - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) by intro x; ring] at h1
  simp_rw [show ∀ x : ℝ,
    (kernel (n + 1) x : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 2)) =
      (-s - 1) * ((kernel (n + 1) x : ℂ) * (x : ℂ) ^ (-s - 2)) by intro x; ring,
    mul_assoc] at h2
  rw [intervalIntegral.integral_const_mul] at h1
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h2
  simp only [kernel, show (n + 2 : ℝ) - (n + 1) = 1 by ring,
    show (n + 1 : ℝ) - (n + 1) = 0 by ring] at h1 h2
  unfold cell block kernel
  push_cast at h1 h2 ⊢
  linear_combination -h1 - s / 2 * h2

theorem abs_kernel_le {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    |kernel a x| ≤ 1 / 6 := by
  unfold kernel
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x - a - 1 / 2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]

theorem norm_block_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖block s n‖ ≤
      ((n + 1 : ℝ) ^ (-s.re - 1) - (n + 2 : ℝ) ^ (-s.re - 1)) /
        (6 * (s.re + 1)) := by
  have hpos {x : ℝ} (hx : x ∈ [[(n + 1 : ℝ), (n + 2 : ℝ)]]) : 0 < x := by
    rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
  have hi : IntervalIntegrable (fun x : ℝ ↦ x ^ (-s.re - 2))
      volume (n + 1 : ℝ) (n + 2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    exact fun x hx ↦ Or.inl (hpos hx).ne'
  have hb : ‖block s n‖ ≤ (1 / 6) *
      ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), x ^ (-s.re - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · apply Filter.Eventually.of_forall
      intro x hx
      have hxp : 0 < x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxp.le _)
      exact abs_kernel_le ⟨hx.1.le, by linarith [hx.2]⟩
    · exact hi.const_mul (1 / 6)
  rw [integral_rpow (Or.inr ⟨by linarith,
    fun hx ↦ (hpos hx).ne' rfl⟩)] at hb
  rw [show -s.re - 2 + 1 = -s.re - 1 by ring] at hb
  convert hb using 1
  field_simp [show s.re + 1 ≠ 0 by linarith, show -s.re - 1 ≠ 0 by linarith]
  ring

theorem sum_norm_block_le {s : ℂ} (hs : 0 < s.re) (N M : ℕ) :
    (∑ n ∈ Finset.range M, ‖block s (n + N)‖) ≤
      ((N + 1 : ℝ) ^ (-s.re - 1) - (M + N + 1 : ℝ) ^ (-s.re - 1)) /
        (6 * (s.re + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hb := norm_block_le hs (M + N)
    simp only [Nat.cast_add, Nat.cast_one] at hb ⊢
    apply (add_le_add ih hb).trans_eq
    rw [show (M : ℝ) + 1 + N + 1 = M + N + 2 by ring]
    ring

theorem summable_block {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n ↦ block s (n + N)) := by
  apply Summable.of_norm
  apply summable_of_sum_range_le (fun _ ↦ norm_nonneg _)
  intro M
  exact (sum_norm_block_le hs N M).trans
    (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
      (by positivity))

theorem sum_cell_eq (s : ℂ) (N M : ℕ) :
    (∑ n ∈ Finset.range M, cell s (n + N)) =
      ((N + 1 : ℂ) ^ (-s) - (M + N + 1 : ℂ) ^ (-s)) / 2 +
      s / 12 * ((N + 1 : ℂ) ^ (-s - 1) - (M + N + 1 : ℂ) ^ (-s - 1)) -
      s * (s + 1) / 2 * ∑ n ∈ Finset.range M, block s (n + N) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, cell_eq]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (M : ℂ) + 1 + N + 1 = M + N + 2 by ring]
    ring

private theorem endpoint_zero {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Tendsto (fun M : ℕ ↦ (M + N + 1 : ℂ) ^ (-s)) atTop (𝓝 0) := by
  have h := (ZetaEulerContinuation.endpoint_tendsto_zero (s := s + 1)
    (by simpa using hs)).comp (tendsto_add_atTop_nat N)
  change Tendsto (fun M : ℕ ↦ ((M + N : ℕ) + 1 : ℂ) ^ (1 - (s + 1))) atTop (𝓝 0) at h
  simpa only [Nat.cast_add, show 1 - (s + 1) = -s by ring] using h

theorem remainder_eq {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    remainder N s = (N + 1 : ℂ) ^ (-s) / 2 +
      s / 12 * (N + 1 : ℂ) ^ (-s - 1) - s * (s + 1) / 2 * tail N s := by
  have he := (summable_remainder hs N).tendsto_sum_tsum_nat
  simp_rw [sum_cell_eq] at he
  have h0 := endpoint_zero hs N
  have h1 : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℂ) ^ (-s - 1)) atTop (𝓝 0) := by
    simpa only [neg_add_rev, neg_add, sub_eq_add_neg, add_comm] using
      (endpoint_zero (s := s + 1) (by simpa using hs.trans (lt_add_one s.re)) N)
  have ht := ((((tendsto_const_nhds (x := (N + 1 : ℂ) ^ (-s))).sub h0).div_const 2).add
    (((tendsto_const_nhds (x := (N + 1 : ℂ) ^ (-s - 1))).sub h1).const_mul (s / 12))).sub
      (((summable_block hs N).tendsto_sum_tsum_nat).const_mul (s * (s + 1) / 2))
  simpa only [sub_zero, remainder, tail] using tendsto_nhds_unique he ht

theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖tail N s‖ ≤ (N + 1 : ℝ) ^ (-s.re - 1) / (6 * (s.re + 1)) := by
  apply (norm_tsum_le_tsum_norm (summable_block hs N).norm).trans
  apply Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _)
  intro M
  exact (sum_norm_block_le hs N M).trans
    (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
      (by positivity))

end
end RiemannGaussian.ZetaEulerBernoulli

end


-- Sidon.NumberTheory.RiemannGaussian.OscillatoryPowerPrimitive
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.OscillatoryPowerPrimitive
noncomputable section
open Complex MeasureTheory Set
open scoped Interval

def mode (r : ℂ) (w x : ℝ) : ℂ := exp (I * w * x) * (x : ℂ) ^ r

def denominator (r : ℂ) (w x : ℝ) : ℂ := I * w * x + r

def primitive (r : ℂ) (w x : ℝ) : ℂ :=
  exp (I * w * x) * (x : ℂ) ^ (r + 1) / denominator r w x

private theorem power_deriv (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

theorem hasDerivAt_primitive (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 < x)
    (hd : denominator r w x ≠ 0) :
    HasDerivAt (primitive r w)
      (mode r w x + r * mode r w x / denominator r w x ^ 2) x := by
  have he := (((hasDerivAt_id x).ofReal_comp).const_mul (I * w)).cexp
  have hp := power_deriv (r + 1) hx
  have hl := (((hasDerivAt_id x).ofReal_comp).const_mul (I * w)).add_const r
  apply ((he.mul hp).div hl hd).congr_deriv
  dsimp
  rw [show r + 1 - 1 = r by ring]
  rw [cpow_add r 1 (Complex.ofReal_ne_zero.mpr hx.ne'), cpow_one]
  unfold mode denominator
  unfold denominator at hd
  field_simp [hd]
  ring

theorem norm_mode (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mode r w x‖ = x ^ r.re := by
  unfold mode
  rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem denominator_lower (r : ℂ) (w : ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    |w| * x / 2 ≤ ‖denominator r w x‖ := by
  have hi : (denominator r w x).im = w * x + r.im := by simp [denominator]
  have ht : |w| * x ≤ |w * x + r.im| + |r.im| := by
    have h := abs_add_le (w * x + r.im) (-r.im)
    simpa only [add_neg_cancel_right, abs_neg, abs_mul, abs_of_nonneg hx] using h
  have hn := abs_im_le_norm (denominator r w x)
  rw [hi] at hn
  linarith

theorem denominator_ne_zero (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) : denominator r w x ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by positivity : 0 < |w| * x / 2).trans_le (denominator_lower r w hx.le hsep)

theorem norm_primitive_le (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    ‖primitive r w x‖ ≤ 2 / |w| * x ^ r.re := by
  have hd := denominator_lower r w hx.le hsep
  have hn : ‖exp (I * w * x) * (x : ℂ) ^ (r + 1)‖ = x ^ (r.re + 1) := by
    simpa only [mode, add_re, one_re] using norm_mode (r + 1) w hx
  unfold primitive
  rw [norm_div, hn]
  apply (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) hd).trans_eq
  rw [Real.rpow_add hx, Real.rpow_one]
  field_simp

theorem norm_defect_le (r : ℂ) {w x : ℝ} (hw : w ≠ 0) (hx : 0 < x)
    (hsep : 2 * |r.im| ≤ |w| * x) :
    ‖r * mode r w x / denominator r w x ^ 2‖ ≤
      4 * ‖r‖ / |w| ^ 2 * x ^ (r.re - 2) := by
  have hd := denominator_lower r w hx.le hsep
  rw [norm_div, norm_mul, norm_pow, norm_mode r w hx]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hd 2)).trans_eq
  rw [Real.rpow_sub hx, Real.rpow_two]
  field_simp
  ring

private theorem mode_continuousOn (r : ℂ) (w : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (mode r w) [[a, b]] := by
  unfold mode
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)

theorem intervalIntegrable_mode (r : ℂ) (w : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (mode r w) volume a b :=
  (mode_continuousOn r w ha hab).intervalIntegrable

set_option maxHeartbeats 2000000 in
theorem integral_eq (r : ℂ) {w a b : ℝ} (hw : w ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hsep : 2 * |r.im| ≤ |w| * a) :
    (∫ x : ℝ in a..b, mode r w x) = primitive r w b - primitive r w a -
      ∫ x : ℝ in a..b, r * mode r w x / denominator r w x ^ 2 := by
  have hs {x : ℝ} (hx : x ∈ [[a, b]]) :
      0 < x ∧ 2 * |r.im| ≤ |w| * x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans_le hx.1, hsep.trans (mul_le_mul_of_nonneg_left hx.1 (abs_nonneg w))⟩
  have hm : IntervalIntegrable (mode r w) volume a b :=
    (mode_continuousOn r w ha hab).intervalIntegrable
  have hd : IntervalIntegrable (fun x ↦ r * mode r w x / denominator r w x ^ 2)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuousOn_const.mul (mode_continuousOn r w ha hab))
      (by unfold denominator; fun_prop)
    exact fun x hx ↦ pow_ne_zero 2 (denominator_ne_zero r hw (hs hx).1 (hs hx).2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hasDerivAt_primitive r w (hs hx).1
      (denominator_ne_zero r hw (hs hx).1 (hs hx).2)) (hm.add hd)
  rw [intervalIntegral.integral_add hm hd] at h
  exact eq_sub_of_add_eq h

theorem norm_integral_le (r : ℂ) {w a b : ℝ} (hw : w ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hsep : 2 * |r.im| ≤ |w| * a) :
    ‖∫ x : ℝ in a..b, mode r w x‖ ≤
      2 / |w| * (a ^ r.re + b ^ r.re) +
        (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
  have hs {x : ℝ} (hx : x ∈ [[a, b]]) :
      0 < x ∧ 2 * |r.im| ≤ |w| * x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans_le hx.1, hsep.trans (mul_le_mul_of_nonneg_left hx.1 (abs_nonneg w))⟩
  have hi : IntervalIntegrable (fun x : ℝ ↦ x ^ (r.re - 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    exact fun x hx ↦ Or.inl (hs hx).1.ne'
  have hd : ‖∫ x : ℝ in a..b, r * mode r w x / denominator r w x ^ 2‖ ≤
      (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · apply Filter.Eventually.of_forall
      intro x hx
      exact norm_defect_le r hw (ha.trans hx.1)
        (hsep.trans (mul_le_mul_of_nonneg_left hx.1.le (abs_nonneg w)))
    · exact hi.const_mul _
  rw [integral_eq r hw ha hab hsep]
  have hb := norm_primitive_le r hw (ha.trans_le hab)
    (hsep.trans (mul_le_mul_of_nonneg_left hab (abs_nonneg w)))
  have hna := norm_primitive_le r hw ha hsep
  apply (norm_sub_le _ _).trans
  have he := (norm_sub_le (primitive r w b) (primitive r w a)).trans (add_le_add hb hna)
  exact (add_le_add he hd).trans_eq (by ring)

theorem cosine_eq_modes (r : ℂ) (w x : ℝ) :
    (Real.cos (w * x) : ℂ) * (x : ℂ) ^ r = (mode r w x + mode r (-w) x) / 2 := by
  rw [ofReal_cos, Complex.cos]
  unfold mode
  push_cast
  ring_nf

theorem norm_cosine_integral_le (r : ℂ) {w a b : ℝ} (hw : w ≠ 0)
    (ha : 0 < a) (hab : a ≤ b) (hsep : 2 * |r.im| ≤ |w| * a) :
    ‖∫ x : ℝ in a..b, (Real.cos (w * x) : ℂ) * (x : ℂ) ^ r‖ ≤
      2 / |w| * (a ^ r.re + b ^ r.re) +
        (4 * ‖r‖ / |w| ^ 2) * ∫ x : ℝ in a..b, x ^ (r.re - 2) := by
  have hi := intervalIntegrable_mode r w ha hab
  have hj := intervalIntegrable_mode r (-w) ha hab
  simp_rw [cosine_eq_modes]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi hj, norm_div]
  have hp := norm_integral_le r hw ha hab hsep
  have hn := norm_integral_le r (neg_ne_zero.mpr hw) ha hab
    (show 2 * |r.im| ≤ |-w| * a by simpa only [abs_neg] using hsep)
  simp only [abs_neg] at hn
  norm_num only [norm_ofNat]
  have h := (norm_add_le (∫ x : ℝ in a..b, mode r w x)
    (∫ x : ℝ in a..b, mode r (-w) x)).trans (add_le_add hp hn)
  linarith

end
end RiemannGaussian.OscillatoryPowerPrimitive

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerFourier
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerFourier
noncomputable section
open Complex Filter MeasureTheory Set Topology RiemannGaussian.ZetaEulerBernoulli
open scoped Interval

def weight (n : ℕ) : ℝ := (1 / (n : ℝ) ^ 2) / Real.pi ^ 2

theorem weight_zero : weight 0 = 0 := by simp [weight]

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem hasSum_weight : HasSum weight (1 / 6) := by
  have h := hasSum_zeta_two.div_const (Real.pi ^ 2)
  have he : (Real.pi ^ 2 / 6) / Real.pi ^ 2 = 1 / 6 := by field_simp
  rw [he] at h
  exact h

theorem hasSum_kernel {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    HasSum (fun n : ℕ ↦ weight n * Real.cos (2 * Real.pi * n * (x - a))) (kernel a x) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) (by omega)
    (show x - a ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2])
  change HasSum _ ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / (2 : ℕ).factorial *
    bernoulliFun 2 (x - a)) at h
  rw [bernoulliFun_two] at h
  convert! h.div_const (Real.pi ^ 2) using 1
  · funext n
    unfold weight
    norm_num
    ring
  · unfold kernel
    norm_num
    field_simp

theorem cosine_cell_shift (n j : ℕ) (x : ℝ) :
    Real.cos (2 * Real.pi * n * (x - (j + 1))) = Real.cos (2 * Real.pi * n * x) := by
  have he : 2 * Real.pi * n * (x - (j + 1)) =
      2 * Real.pi * n * x - (n * (j + 1) : ℕ) * (2 * Real.pi) := by push_cast; ring
  rw [he, Real.cos_sub_nat_mul_two_pi]

theorem hasSum_kernel_global (j : ℕ) {x : ℝ} (hx : x ∈ Icc (j + 1 : ℝ) (j + 2 : ℝ)) :
    HasSum (fun n : ℕ ↦ weight n * Real.cos (2 * Real.pi * n * x)) (kernel (j + 1) x) := by
  have h := hasSum_kernel (show x ∈ Icc (j + 1 : ℝ) ((j + 1 : ℝ) + 1) by
    simpa only [show (j + 1 : ℝ) + 1 = j + 2 by ring] using hx)
  simpa only [cosine_cell_shift] using h

def channel (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (weight n * Real.cos (2 * Real.pi * n * x) : ℝ) * (x : ℂ) ^ (-s - 2)

theorem norm_channel_le (s : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖channel s n x‖ ≤ weight n * x ^ (-s.re - 2) := by
  unfold channel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (weight_nonneg n), norm_cpow_eq_rpow_re_of_pos hx]
  change weight n * |Real.cos _| * x ^ (-s.re - 2) ≤ weight n * x ^ (-s.re - 2)
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (weight_nonneg n) (Real.abs_cos_le_one _))
    (Real.rpow_nonneg hx.le _)

theorem hasSum_channel (s : ℂ) (j : ℕ) {x : ℝ}
    (hx : x ∈ Icc (j + 1 : ℝ) (j + 2 : ℝ)) :
    HasSum (fun n ↦ channel s n x) ((kernel (j + 1) x : ℂ) * (x : ℂ) ^ (-s - 2)) :=
  (Complex.hasSum_ofReal.mpr (hasSum_kernel_global j hx)).mul_right _

theorem intervalIntegrable_channel (s : ℂ) (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (channel s n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  unfold channel
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)

theorem hasSum_block (s : ℂ) (j : ℕ) :
    HasSum (fun n ↦ ∫ x : ℝ in (j + 1 : ℝ)..(j + 2 : ℝ), channel s n x) (block s j) := by
  have hj : (j + 1 : ℝ) ≤ j + 2 := by linarith
  have hpos {x : ℝ} (hx : x ∈ Ι (j + 1 : ℝ) (j + 2 : ℝ)) : 0 < x := by
    rw [uIoc_of_le hj] at hx
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) j]
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n x ↦ weight n * x ^ (-s.re - 2))
  · exact fun n ↦ (intervalIntegrable_channel s n (by positivity) hj).aestronglyMeasurable_restrict_uIoc
  · intro n
    exact Filter.Eventually.of_forall fun x hx ↦ norm_channel_le s n (hpos hx)
  · exact Filter.Eventually.of_forall fun x _ ↦ hasSum_weight.summable.mul_right _
  · simp_rw [tsum_mul_right, hasSum_weight.tsum_eq]
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    intro x hx
    rw [uIcc_of_le hj] at hx
    exact Or.inl (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) j] : x ≠ 0)
  · apply Filter.Eventually.of_forall
    intro x hx
    rw [uIoc_of_le hj] at hx
    exact hasSum_channel s j ⟨hx.1.le, hx.2⟩

theorem hasSum_blocks (s : ℂ) (N M : ℕ) :
    HasSum (fun n ↦ ∫ x : ℝ in (N + 1 : ℝ)..(M + N + 1 : ℝ), channel s n x)
      (∑ j ∈ Finset.range M, block s (j + N)) := by
  have h := hasSum_sum (s := Finset.range M) (fun j _ ↦ hasSum_block s (j + N))
  apply h.congr_fun
  intro n
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ ↦ (j + N + 1 : ℝ)) (n := M)
    (fun j _ ↦ intervalIntegrable_channel s n (by positivity) (by push_cast; linarith))
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
    show ∀ j : ℝ, j + 1 + N + 1 = j + N + 2 by intro j; ring] using he.symm

end
end RiemannGaussian.ZetaEulerFourier

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerOscillation
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerOscillation
noncomputable section
open Complex Filter MeasureTheory Set Topology RiemannGaussian.ZetaEulerBernoulli RiemannGaussian.ZetaEulerFourier
open scoped Interval

def envelope (s : ℂ) (a b : ℝ) : ℝ :=
  1 / Real.pi * (a ^ (-s.re - 2) + b ^ (-s.re - 2)) +
    ‖s + 2‖ / Real.pi ^ 2 * ∫ x : ℝ in a..b, x ^ (-s.re - 4)

theorem norm_channel_integral_le (s : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht : |s.im| ≤ a) (n : ℕ) :
    ‖∫ x : ℝ in a..b, channel s n x‖ ≤ weight n * envelope s a b := by
  have hbpos := ha.trans_le hab
  by_cases hn : n = 0
  · subst n
    simp [channel, weight_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : 0 < Real.pi := Real.pi_pos
  have hw : 0 < 2 * Real.pi * n := by positivity
  have hwlo : 2 * Real.pi ≤ 2 * Real.pi * n := by nlinarith
  have hsep : 2 * |(-s - 2).im| ≤ |2 * Real.pi * n| * a := by
    change 2 * |-s.im - 0| ≤ |2 * Real.pi * n| * a
    simp only [sub_zero, abs_neg, abs_of_pos hw]
    have hp1 := Real.pi_gt_three
    nlinarith [mul_le_mul_of_nonneg_right hwlo ha.le]
  have h := OscillatoryPowerPrimitive.norm_cosine_integral_le (-s - 2) hw.ne' ha hab hsep
  have he : ‖-s - 2‖ = ‖s + 2‖ := by rw [show -s - 2 = -(s + 2) by ring, norm_neg]
  change ‖∫ x : ℝ in a..b, (Real.cos (2 * Real.pi * n * x) : ℂ) * (x : ℂ) ^ (-s - 2)‖ ≤
    2 / |2 * Real.pi * n| * (a ^ (-s.re - 2) + b ^ (-s.re - 2)) +
      (4 * ‖-s - 2‖ / |2 * Real.pi * n| ^ 2) * ∫ x : ℝ in a..b, x ^ (-s.re - 2 - 2) at h
  rw [he, abs_of_pos hw, show -s.re - 2 - 2 = -s.re - 4 by ring] at h
  have h1 : 2 / (2 * Real.pi * n) ≤ 1 / Real.pi := by
    calc
      _ ≤ 2 / (2 * Real.pi) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hwlo
      _ = _ := by field_simp
  have h2 : 4 / (2 * Real.pi * n) ^ 2 ≤ 1 / Real.pi ^ 2 := by
    calc
      _ ≤ 4 / (2 * Real.pi) ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) hwlo 2)
      _ = _ := by field_simp; ring
  have hi : 0 ≤ ∫ x : ℝ in a..b, x ^ (-s.re - 4) :=
    intervalIntegral.integral_nonneg hab (fun x hx ↦ Real.rpow_nonneg (ha.trans_le hx.1).le _)
  have hb : ‖∫ x : ℝ in a..b, (Real.cos (2 * Real.pi * n * x) : ℂ) * (x : ℂ) ^ (-s - 2)‖ ≤
      envelope s a b := by
    apply h.trans
    unfold envelope
    have h2' : 4 * ‖s + 2‖ / (2 * Real.pi * n) ^ 2 ≤ ‖s + 2‖ / Real.pi ^ 2 := by
      simpa only [div_eq_mul_inv, mul_one, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_right h2 (norm_nonneg (s + 2))
    exact add_le_add
      (mul_le_mul_of_nonneg_right h1 (by positivity))
      (mul_le_mul_of_nonneg_right h2' hi)
  have hc : (fun x : ℝ ↦ channel s n x) =
      fun x ↦ (weight n : ℂ) * ((Real.cos (2 * Real.pi * n * x) : ℂ) * (x : ℂ) ^ (-s - 2)) := by
    funext x
    simp only [channel, ofReal_mul, mul_assoc]
  rw [hc, intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (weight_nonneg n)]
  exact mul_le_mul_of_nonneg_left hb (weight_nonneg n)

theorem norm_blocks_le (s : ℂ) (N M : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖∑ j ∈ Finset.range M, block s (j + N)‖ ≤ envelope s (N + 1) (M + N + 1) / 6 := by
  have h := (hasSum_blocks s N M).norm_le_of_bounded
    (hasSum_weight.mul_right (envelope s (N + 1) (M + N + 1)))
    (fun n ↦ norm_channel_integral_le s (by positivity)
      (by have hM := Nat.cast_nonneg (α := ℝ) M; linarith) ht n)
  convert h using 1
  ring

private theorem power_integral_le {s : ℂ} (hs : 0 < s.re)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, x ^ (-s.re - 4)) ≤ a ^ (-s.re - 3) / (s.re + 3) := by
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]⟩)]
  rw [show -s.re - 4 + 1 = -s.re - 3 by ring]
  have he : (b ^ (-s.re - 3) - a ^ (-s.re - 3)) / (-s.re - 3) =
      (a ^ (-s.re - 3) - b ^ (-s.re - 3)) / (s.re + 3) := by
    field_simp [show s.re + 3 ≠ 0 by linarith, show -s.re - 3 ≠ 0 by linarith]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (ha.trans_le hab).le _)) (by positivity)

theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖tail N s‖ ≤
      (1 / Real.pi * (N + 1 : ℝ) ^ (-s.re - 2) +
        ‖s + 2‖ / Real.pi ^ 2 * (N + 1 : ℝ) ^ (-s.re - 3) / (s.re + 3)) / 6 := by
  have hbound M : ‖∑ j ∈ Finset.range M, block s (j + N)‖ ≤
      (1 / Real.pi * ((N + 1 : ℝ) ^ (-s.re - 2) + (M + N + 1 : ℝ) ^ (-s.re - 2)) +
        ‖s + 2‖ / Real.pi ^ 2 * (N + 1 : ℝ) ^ (-s.re - 3) / (s.re + 3)) / 6 := by
    apply (norm_blocks_le s N M ht).trans
    unfold envelope
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add_right
    have hi := power_integral_le hs (a := (N + 1 : ℝ)) (b := (M + N + 1 : ℝ))
      (by positivity) (by have hM := Nat.cast_nonneg (α := ℝ) M; linarith)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hi
      (div_nonneg (norm_nonneg (s + 2)) (sq_nonneg Real.pi))
  have htend : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℝ)) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop ((N : ℝ) + 1)
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_assoc] using h
  have hp : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℝ) ^ (-s.re - 2)) atTop (𝓝 0) := by
    have hr := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + 2)).comp htend
    change Tendsto (fun M : ℕ ↦ (M + N + 1 : ℝ) ^ (-(s.re + 2))) atTop (𝓝 0) at hr
    simpa only [show -(s.re + 2) = -s.re - 2 by ring] using hr
  have hc := (((tendsto_const_nhds (x := (N + 1 : ℝ) ^ (-s.re - 2))).add hp).const_mul
    (1 / Real.pi)).add_const
      (‖s + 2‖ / Real.pi ^ 2 * (N + 1 : ℝ) ^ (-s.re - 3) / (s.re + 3))
  have h := le_of_tendsto_of_tendsto (summable_block hs N).tendsto_sum_tsum_nat.norm
    (hc.div_const 6) (Filter.Eventually.of_forall hbound)
  simpa only [add_zero, tail] using h

end
end RiemannGaussian.ZetaEulerOscillation

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerUniformRemainder
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerUniformRemainder
noncomputable section
open Complex Set RiemannGaussian.ZetaEulerCell RiemannGaussian.ZetaEulerTruncation RiemannGaussian.ZetaEulerBernoulli
private theorem norm_bounds {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    {a : ℝ} (ha : 1 ≤ a) (ht : |s.im| ≤ a) :
    ‖s‖ ≤ 2 * a ∧ ‖s + 1‖ ≤ 3 * a ∧ ‖s + 2‖ ≤ 4 * a := by
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hs] at hn
  have hn1 := norm_add_le s 1
  have hn2 := norm_add_le s 2
  norm_num at hn1 hn2
  constructor
  · linarith
  constructor <;> linarith

theorem norm_tail_le_scaled {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖tail N s‖ ≤ (13 / 162 : ℝ) * (N + 1 : ℝ) ^ (-s.re) / (N + 1 : ℝ) ^ 2 := by
  let a : ℝ := N + 1
  have ha1 : 1 ≤ a := by dsimp [a]; have hN := Nat.cast_nonneg (α := ℝ) N; linarith
  have ha : 0 < a := by positivity
  have hn := (norm_bounds hs hs1 ha1 ht).2.2
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpi : 1 / Real.pi ≤ (1 / 3 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hc : ‖s + 2‖ / Real.pi ^ 2 ≤ 4 * a / 9 := by
    calc
      _ ≤ ‖s + 2‖ / 9 := div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by nlinarith)
      _ ≤ _ := div_le_div_of_nonneg_right hn (by norm_num)
  have hfirst := mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg ha.le (-s.re - 2))
  have hsecond : ‖s + 2‖ / Real.pi ^ 2 * a ^ (-s.re - 3) / (s.re + 3) ≤
      (4 * a / 9) * a ^ (-s.re - 3) / 3 := by
    calc
      _ ≤ (‖s + 2‖ / Real.pi ^ 2 * a ^ (-s.re - 3)) / 3 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ha.le _)) (by norm_num)
  have h := (ZetaEulerOscillation.norm_tail_le hs N ht).trans
    (div_le_div_of_nonneg_right (add_le_add hfirst hsecond) (by norm_num))
  change ‖tail N s‖ ≤ (13 / 162 : ℝ) * a ^ (-s.re) / a ^ 2
  apply h.trans_eq
  rw [Real.rpow_sub ha, Real.rpow_sub ha]
  norm_num
  field_simp
  ring

theorem norm_remainder_le_power {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖remainder N s‖ ≤ (N + 1 : ℝ) ^ (-s.re) := by
  let a : ℝ := N + 1
  have ha1 : 1 ≤ a := by dsimp [a]; have hN := Nat.cast_nonneg (α := ℝ) N; linarith
  have ha : 0 < a := by positivity
  obtain ⟨hn, hn1, _⟩ := norm_bounds hs hs1 ha1 ht
  have hp (r : ℂ) : ‖(N + 1 : ℂ) ^ r‖ = a ^ r.re := by
    rw [show (N + 1 : ℂ) = (a : ℂ) by simp [a], norm_cpow_eq_rpow_re_of_pos ha]
  have ht' := norm_tail_le_scaled hs hs1 N ht
  change ‖tail N s‖ ≤ (13 / 162 : ℝ) * a ^ (-s.re) / a ^ 2 at ht'
  have hprod : ‖s‖ * ‖s + 1‖ / 2 ≤ 3 * a ^ 2 := by
    have h := mul_le_mul hn hn1 (norm_nonneg _) (by positivity)
    nlinarith
  have hsecond : ‖s‖ / 12 * a ^ (-s.re - 1) ≤ 2 * a / 12 * a ^ (-s.re - 1) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn (by norm_num)) (by positivity)
  have hthird := mul_le_mul hprod ht' (norm_nonneg _) (by positivity : 0 ≤ 3 * a ^ 2)
  rw [remainder_eq hs]
  have htri := (norm_sub_le
    ((N + 1 : ℂ) ^ (-s) / 2 + s / 12 * (N + 1 : ℂ) ^ (-s - 1))
    (s * (s + 1) / 2 * tail N s)).trans
      (add_le_add_left (norm_add_le _ _) _)
  simp only [norm_div, norm_mul, hp] at htri
  norm_num only [norm_ofNat] at htri
  change _ ≤ a ^ (-s.re) / 2 + ‖s‖ / 12 * a ^ (-s.re - 1) +
    ‖s‖ * ‖s + 1‖ / 2 * ‖tail N s‖ at htri
  apply htri.trans
  apply ((add_le_add (add_le_add_right hsecond _) hthird)).trans
  have he : a ^ (-s.re) / 2 + 2 * a / 12 * a ^ (-s.re - 1) +
      3 * a ^ 2 * ((13 / 162 : ℝ) * a ^ (-s.re) / a ^ 2) =
        (49 / 54 : ℝ) * a ^ (-s.re) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
    field_simp
    ring
  rw [he]
  change (49 / 54 : ℝ) * a ^ (-s.re) ≤ a ^ (-s.re)
  nlinarith [Real.rpow_nonneg ha.le (-s.re)]

theorem norm_zeta_sub_partialSum_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (hsne : s ≠ 1) (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖riemannZeta s - partialSum N s‖ ≤
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ + (N + 1 : ℝ) ^ (-s.re) := by
  rw [zeta_eq_partialSum_add_endpoint_add_remainder hs hsne N]
  rw [show partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s - partialSum N s =
    (N + 1 : ℂ) ^ (1 - s) / (s - 1) + remainder N s by ring]
  apply (norm_add_le _ _).trans
  have hp : ‖(N + 1 : ℂ) ^ (1 - s) / (s - 1)‖ =
      (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
    rw [norm_div]
    congr 1
    have h := norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < N + 1) (1 - s)
    simpa only [ofReal_add, ofReal_natCast, ofReal_one, sub_re, one_re] using h
  rw [hp]
  exact add_le_add_right (norm_remainder_le_power hs hs1 N ht) _

end
end RiemannGaussian.ZetaEulerUniformRemainder

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletCriticalRange
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletCriticalRange
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.DirichletBlockPowerProfile
theorem profile_on_line (k : ℕ) (t X : ℝ) :
    profile k (line k) t X = 256 * t ^ alpha k + 64 * t ^ (-alpha k) * X ^ slope k := by
  unfold profile line
  rw [show 1 - (1 - ((k : ℝ) + 2) * alpha k) - ((k : ℝ) + 2) * alpha k = 0 by ring,
    Real.rpow_zero, mul_one]
  rw [show beta k - (1 - ((k : ℝ) + 2) * alpha k) + ((k : ℝ) + 2) * alpha k =
    slope k by unfold beta DirichletPowerParameters.slope; ring]

theorem profile_le_on_range (k : ℕ) {t X : ℝ} (ht : 0 < t) (hX : 0 < X)
    (hupper : X ≤ t ^ transition k) : profile k (line k) t X ≤ 320 * t ^ alpha k := by
  have hp := Real.rpow_le_rpow hX.le hupper (slope_pos k).le
  rw [← Real.rpow_mul ht.le, transition_balance] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le (-alpha k))
  have he : t ^ (-alpha k) * t ^ (2 * alpha k) = t ^ alpha k := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [he] at hm
  rw [profile_on_line]
  nlinarith

end
end RiemannGaussian.DirichletCriticalRange

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletTransitionWindows
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletTransitionWindows
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open RiemannGaussian.DirichletBlockPowerProfile
set_option maxHeartbeats 2000000 in
theorem profile_on_later_line (r k : ℕ) (t X : ℝ) :
    profile r (line k) t X =
      256 * t ^ alpha r * X ^ (delta k - delta r) +
      64 * t ^ (-alpha r) * X ^ (delta k - amp r + delta r) := by
  unfold profile line delta beta
  congr 2 <;> congr 1 <;> ring

theorem complementary_balance (r k : ℕ) :
    -alpha r + transition r * (delta k - amp r + delta r) =
      alpha r + transition r * (delta k - delta r) := by
  have h := transition_balance r
  have hs : DirichletPowerParameters.slope r = 2 * delta r - amp r := by
    unfold DirichletPowerParameters.slope delta
    ring
  rw [hs] at h
  nlinarith

theorem profile_le_on_window (r k : ℕ) (hrk : r ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hX : 0 < X)
    (hlower : t ^ transition (r + 1) ≤ X) (hupper : X ≤ t ^ transition r) :
    profile r (line k) t X ≤ 320 * t ^ alpha k := by
  have htpos : 0 < t := by linarith
  have ha : delta k - delta r ≤ 0 := sub_nonpos.mpr (delta_antitone hrk)
  have hb : 0 ≤ delta k - amp r + delta r := by
    linarith [amp_le_delta r, delta_pos k]
  have hlead := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos htpos (transition (r + 1))) hlower ha
  rw [← Real.rpow_mul htpos.le] at hlead
  have hlead' := mul_le_mul_of_nonneg_left hlead (Real.rpow_nonneg htpos.le (alpha r))
  rw [← Real.rpow_add htpos] at hlead'
  have hlead'' := Real.rpow_le_rpow_of_exponent_le ht (order_comparison r k hrk)
  have hcomp := Real.rpow_le_rpow hX.le hupper hb
  rw [← Real.rpow_mul htpos.le] at hcomp
  have hcomp' := mul_le_mul_of_nonneg_left hcomp (Real.rpow_nonneg htpos.le (-alpha r))
  rw [← Real.rpow_add htpos, complementary_balance] at hcomp'
  have he : alpha r + transition r * (delta k - delta r) ≤ alpha k := by
    have hm := mul_le_mul_of_nonpos_right (transition_succ_le r) ha
    linarith [order_comparison r k hrk]
  have hcomp'' := Real.rpow_le_rpow_of_exponent_le ht he
  rw [profile_on_later_line]
  nlinarith

theorem window_cover (k : ℕ) {t X : ℝ} (hupper : X ≤ t) :
    X ≤ t ^ transition k ∨
      ∃ r < k, t ^ transition (r + 1) ≤ X ∧ X ≤ t ^ transition r := by
  induction k with
  | zero => left; simpa [transition_zero] using hupper
  | succ k ih =>
    by_cases h : X ≤ t ^ transition (k + 1)
    · exact Or.inl h
    · right
      rcases ih with hi | ⟨r, hr, hlo, hhi⟩
      · exact ⟨k, Nat.lt_succ_self k, (lt_of_not_ge h).le, hi⟩
      · exact ⟨r, Nat.lt_succ_of_lt hr, hlo, hhi⟩

theorem exists_order_bound (k : ℕ) {t X : ℝ} (ht : 1 ≤ t) (hX : 0 < X)
    (hupper : X ≤ t) :
    ∃ r ≤ k, profile r (line k) t X ≤ 320 * t ^ alpha k := by
  rcases window_cover k hupper with h | ⟨r, hr, hlo, hhi⟩
  · exact ⟨k, le_rfl, DirichletCriticalRange.profile_le_on_range k
      (by linarith) hX h⟩
  · exact ⟨r, hr.le, profile_le_on_window r k hr.le ht hX hlo hhi⟩

end
end RiemannGaussian.DirichletTransitionWindows

end


-- Sidon.NumberTheory.RiemannGaussian.DirichletFullRange
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.DirichletFullRange
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open RiemannGaussian.DirichletBlockPowerProfile RiemannGaussian.DirichletTransitionWindows
theorem profile_le_above_height (k : ℕ) (hk : 1 ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hlower : t ≤ X) (hupper : X ≤ 4 * t) :
    profile 0 (line k) t X ≤ 512 * t ^ alpha k := by
  have htpos : 0 < t := by linarith
  have hd : delta k ≤ 1 / 2 := by
    rw [delta_eq_one_sub_line]
    linarith [half_le_line k hk]
  have hdpos := delta_pos k
  have ha : delta k - 1 ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le ht
    (show delta k - 1 / 2 ≤ alpha k by linarith [alpha_pos k])
  have hlead := Real.rpow_le_rpow_of_nonpos htpos hlower ha
  have hlead' := mul_le_mul_of_nonneg_left hlead
    (Real.rpow_nonneg htpos.le (1 / 2))
  rw [← Real.rpow_add htpos,
    show 1 / 2 + (delta k - 1) = delta k - 1 / 2 by ring] at hlead'
  have hfour : (4 : ℝ) ^ delta k ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by linarith : delta k ≤ 1)).trans_eq
    exact Real.rpow_one _
  have hcomp : X ^ delta k ≤ 4 * t ^ delta k := by
    calc
      _ ≤ (4 * t) ^ delta k := Real.rpow_le_rpow
        (by linarith : 0 ≤ X) hupper hdpos.le
      _ = (4 : ℝ) ^ delta k * t ^ delta k := Real.mul_rpow (by norm_num) htpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg htpos.le _)
  have hcomp' := mul_le_mul_of_nonneg_left hcomp
    (Real.rpow_nonneg htpos.le (-(1 / 2)))
  have he : t ^ (-(1 / 2 : ℝ)) * (4 * t ^ delta k) =
      4 * t ^ (delta k - 1 / 2) := by
    rw [show t ^ (-(1 / 2 : ℝ)) * (4 * t ^ delta k) =
      4 * (t ^ (-(1 / 2 : ℝ)) * t ^ delta k) by ring,
      ← Real.rpow_add htpos]
    congr 2
    ring
  rw [he] at hcomp'
  have hd0 : delta 0 = 1 := by norm_num [delta, alpha]
  rw [profile_on_later_line, hd0, amp_zero, alpha_zero,
    show delta k - 1 + 1 = delta k by ring]
  nlinarith

theorem exists_order_bound (k : ℕ) (hk : 1 ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hX : 0 < X) (hupper : X ≤ 4 * t) :
    ∃ r ≤ k, profile r (line k) t X ≤ 512 * t ^ alpha k := by
  by_cases hx : X ≤ t
  · obtain ⟨r, hr, h⟩ := DirichletTransitionWindows.exists_order_bound k ht hX hx
    refine ⟨r, hr, h.trans ?_⟩
    have hp := Real.rpow_nonneg (by linarith : 0 ≤ t) (alpha k)
    nlinarith
  · exact ⟨0, Nat.zero_le k, profile_le_above_height k hk ht
      (lt_of_not_ge hx).le hupper⟩

end
end RiemannGaussian.DirichletFullRange

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLineBudget
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaNearOneLineBudget
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open RiemannGaussian.DirichletBlockPowerProfile RiemannGaussian.ZetaDyadicTruncation RiemannGaussian.ZetaDyadicPowerBound
theorem norm_le_height_add_one {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 0 ≤ s.im) : ‖s‖ ≤ s.im + 1 := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hσ, abs_of_nonneg ht] at h
  linarith

theorem canonical_scale_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) {j : ℕ} (hj : j ≤ depth s) :
    ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im := by
  have hn := norm_le_height_add_one hσ hσ1 (by linarith)
  have hd := depth_length_lt s
  have hp : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ depth s : ℕ) : ℝ) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hj
  linarith

theorem canonical_count_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) : ((depth s + 1 : ℕ) : ℝ) ≤ 8 * Real.log s.im := by
  have htpos : 0 < s.im := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
  have hn := norm_le_height_add_one hσ hσ1 htpos.le
  have hh : ‖s‖ + 2 ≤ 4 * s.im := by linarith
  have hl := Real.log_le_log (by positivity : 0 < ‖s‖ + 2) hh
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat]
      using Real.log_pow (2 : ℝ) 2
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) htpos.ne', hfour] at hl
  have hd := (le_div_iff₀ hl2).mp (depth_le_log s)
  have hc : (((depth s + 1 : ℕ) : ℝ)) * Real.log 2 ≤ 4 * Real.log s.im := by
    push_cast
    nlinarith
  have hb : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ((depth s + 1 : ℕ) : ℝ) by positivity)
  nlinarith

theorem exists_block_order (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hline : s.re = line k) (ht : 2 ≤ s.im) {j : ℕ} (hj : j ≤ depth s) :
    ∃ r ≤ k, profile r s.re s.im ((2 ^ j : ℕ) : ℝ) ≤ 512 * s.im ^ alpha k := by
  have hσ : 0 ≤ s.re := by rw [hline]; exact line_nonneg k
  have hσ1 : s.re ≤ 1 := by rw [hline]; exact (line_lt_one k).le
  have hx := canonical_scale_le hσ hσ1 ht hj
  rw [hline]
  exact DirichletFullRange.exists_order_bound k hk (by linarith) (by positivity) hx

theorem exists_prefix_budget_bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hline : s.re = line k) (ht : 2 ≤ s.im) :
    ∃ orders : ℕ → ℕ, (∀ j, orders j ≤ k) ∧
      prefixBudget s orders (depth s + 1) ≤
        ((depth s + 1 : ℕ) : ℝ) * (512 * s.im ^ alpha k) := by
  classical
  have hex : ∀ j : ℕ, ∃ r : ℕ, r ≤ k ∧ (j ≤ depth s →
      profile r s.re s.im ((2 ^ j : ℕ) : ℝ) ≤ 512 * s.im ^ alpha k) := by
    intro j
    by_cases hj : j ≤ depth s
    · obtain ⟨r, hr, h⟩ := exists_block_order k hk hline ht hj
      exact ⟨r, hr, fun _ => h⟩
    · exact ⟨0, Nat.zero_le k, fun h => (hj h).elim⟩
  choose orders hr hb using hex
  refine ⟨orders, hr, ?_⟩
  unfold prefixBudget
  calc
    _ ≤ ∑ _j ∈ Finset.range (depth s + 1), (512 * s.im ^ alpha k) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (min_le_right _ _).trans (hb j (by have h := Finset.mem_range.mp hj; omega))
    _ = _ := by simp

end
end RiemannGaussian.ZetaNearOneLineBudget

end


-- Sidon.NumberTheory.RiemannGaussian.ZetaEulerLineBound
section

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/

namespace RiemannGaussian.ZetaEulerLineBound
noncomputable section
open Complex RiemannGaussian.ZetaEulerCell RiemannGaussian.ZetaDyadicTruncation RiemannGaussian.ZetaNearOneLineBudget
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open scoped ComplexConjugate

theorem partialSum_eq_positivePrefix (N : ℕ) (s : ℂ) :
    partialSum N s = DirichletDyadicBlocks.positivePrefix s (N + 1) := by
  rw [DirichletDyadicBlocks.positivePrefix, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro n _
  rw [DirichletDyadicBlocks.feature_eq_cpow s (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem norm_lt_endpoint (s : ℂ) : ‖s‖ < ((2 ^ (depth s + 1) : ℕ) : ℝ) := by
  have hc := Nat.le_ceil ‖s‖
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (⌈‖s‖⌉₊ + 1)
  have hr : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) < ((2 ^ (depth s + 1) : ℕ) : ℝ) := by
    exact_mod_cast hp
  push_cast at hr ⊢
  linarith

theorem endpoint_le_five_height {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) : ((2 ^ (depth s + 1) : ℕ) : ℝ) ≤ 5 * s.im := by
  have h := depth_length_lt s
  have hn := norm_le_height_add_one hσ hσ1 (by linarith)
  rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem norm_le_prefix_add_six {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ ‖DirichletDyadicBlocks.positivePrefix s (2 ^ (depth s + 1))‖ + 6 := by
  let M : ℕ := 2 ^ (depth s + 1)
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMN : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsne : s ≠ 1 := by intro h; subst s; norm_num at ht
  have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast hMN
  have hheight : |s.im| ≤ ((M - 1 : ℕ) : ℝ) + 1 := by
    rw [hcast]
    exact (Complex.abs_im_le_norm s).trans (norm_lt_endpoint s).le
  have h := ZetaEulerUniformRemainder.norm_zeta_sub_partialSum_le hσ hσ1 hsne (M - 1) hheight
  rw [partialSum_eq_positivePrefix, hMN] at h
  rw [hcast] at h
  have hp : (M : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM) (by linarith)
  have htpos : 0 < s.im := by linarith
  have hden : s.im ≤ ‖s - 1‖ := by
    simpa only [sub_im, one_im, sub_zero] using Complex.im_le_norm (s - 1)
  have hnum : (M : ℝ) ^ (1 - s.re) ≤ M := by
    calc
      _ ≤ (M : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith)
      _ = _ := Real.rpow_one _
  have hend : (M : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 5 := by
    calc
      _ ≤ (M : ℝ) / s.im :=
        (div_le_div_of_nonneg_left (by positivity) htpos hden).trans
          (div_le_div_of_nonneg_right hnum htpos.le)
      _ ≤ 5 := (div_le_iff₀ htpos).mpr (endpoint_le_five_height hσ.le hσ1 ht)
  have htri := norm_add_le (riemannZeta s - DirichletDyadicBlocks.positivePrefix s M)
    (DirichletDyadicBlocks.positivePrefix s M)
  simp only [sub_add_cancel] at htri
  dsimp [M] at h htri
  linarith

theorem bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k) (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ 8192 * s.im ^ alpha k * Real.log s.im := by
  have hσ : 0 < s.re := by rw [hline]; linarith [half_le_line k hk]
  have hσ1 : s.re ≤ 1 := by rw [hline]; exact (line_lt_one k).le
  obtain ⟨orders, _, hb⟩ := exists_prefix_budget_bound k hk hline ht
  have hprefix := (ZetaDyadicPowerBound.prefix_bound hσ.le (by linarith) orders (depth s + 1)).trans hb
  have hc := canonical_count_le hσ.le hσ1 ht
  have hp : 1 ≤ s.im ^ alpha k := Real.one_le_rpow (by linarith) (alpha_pos k).le
  have hlog : (1 / 2 : ℝ) ≤ Real.log s.im := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
    linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 512 * s.im ^ alpha k)
  have hprod : (1 / 2 : ℝ) ≤ s.im ^ alpha k * Real.log s.im := by nlinarith
  have h := norm_le_prefix_add_six hσ hσ1 ht
  nlinarith

theorem bound_abs (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ alpha k * Real.log |s.im| := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound k hk hline ht
  · have h := bound k hk (s := conj s) (by simpa using hline)
      (by simpa [abs_of_neg (lt_of_not_ge hs)] using ht)
    simpa [abs_of_neg (lt_of_not_ge hs)] using h

end
end RiemannGaussian.ZetaEulerLineBound

end


-- Sidon.NumberTheory.ZetaCriticalLine
section

noncomputable section

namespace Sidon

def zetaCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + t * Complex.I

@[simp] theorem zetaCriticalPoint_re (t : ℝ) : (zetaCriticalPoint t).re = 1 / 2 := by
  simp [zetaCriticalPoint]

@[simp] theorem zetaCriticalPoint_im (t : ℝ) : (zetaCriticalPoint t).im = t := by
  simp [zetaCriticalPoint]

theorem continuous_riemannZeta_criticalPoint :
    Continuous (fun t : ℝ => riemannZeta (zetaCriticalPoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : zetaCriticalPoint t ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hc : Continuous zetaCriticalPoint := by unfold zetaCriticalPoint; fun_prop
  exact (differentiableAt_riemannZeta hs).continuousAt.comp hc.continuousAt

theorem exists_riemannZeta_criticalPoint_bound_on_compact (R : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, |t| ≤ R → ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-R) R)).exists_bound_of_continuousOn
    continuous_riemannZeta_criticalPoint.continuousOn
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC t (abs_le.mp ht)).trans (le_max_left _ _)

theorem rpow_mul_log_le_rpow {x a b : ℝ} (hx : 0 < x) (hab : a < b) :
    x ^ a * Real.log x ≤ (b - a)⁻¹ * x ^ b := by
  have hlog := Real.log_le_rpow_div hx.le (sub_pos.mpr hab)
  calc
    _ ≤ x ^ a * (x ^ (b - a) / (b - a)) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx.le _)
    _ = (b - a)⁻¹ * (x ^ a * x ^ (b - a)) := by ring
    _ = _ := by rw [← Real.rpow_add hx, add_sub_cancel]

theorem sixth_rpow_mul_log_le_three_sixteenths {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 6) * Real.log x ≤ 48 * x ^ ((3 : ℝ) / 16) := by
  have h := rpow_mul_log_le_rpow (a := (1 : ℝ) / 6) (b := (3 : ℝ) / 16)
    hx (by norm_num)
  norm_num only [show ((3 : ℝ) / 16 - 1 / 6)⁻¹ = 48 by norm_num] at h
  exact h

theorem exists_riemannZeta_criticalPoint_growth_of_tail {c C : ℝ}
    (hc : 0 ≤ c)
    (htail : ∀ t : ℝ, 2 ≤ |t| →
      ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C * |t| ^ c) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      ‖riemannZeta (zetaCriticalPoint t)‖ ≤ D * (1 + |t|) ^ c := by
  obtain ⟨B, hB, hcompact⟩ := exists_riemannZeta_criticalPoint_bound_on_compact 2
  let D := max B C
  have hBD : B ≤ D := le_max_left _ _
  have hCD : C ≤ D := le_max_right _ _
  have hD : 0 < D := by linarith
  refine ⟨D, hD, ?_⟩
  intro t
  by_cases ht : |t| ≤ 2
  · have hpow : 1 ≤ (1 + |t|) ^ c :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) hc
    exact (hcompact t ht).trans (hBD.trans (by nlinarith))
  · have hp : |t| ^ c ≤ (1 + |t|) ^ c :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) hc
    exact (htail t (le_of_lt (lt_of_not_ge ht))).trans
      (mul_le_mul hCD hp (Real.rpow_nonneg (abs_nonneg t) _) hD.le)

end Sidon

end
end


-- Sidon.NumberTheory.WeylZeta
section

noncomputable section

namespace Sidon

theorem riemannZeta_critical_line_weyl {s : ℂ} (hσ : s.re = 1 / 2)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ ((1 : ℝ) / 6) * Real.log |s.im| := by
  have hline : s.re = RiemannGaussian.DirichletPowerParameters.line 1 := by
    norm_num [RiemannGaussian.DirichletPowerParameters.line,
      RiemannGaussian.DerivativePowerExponents.alpha]
    exact hσ
  have h := RiemannGaussian.ZetaEulerLineBound.bound_abs 1 (by omega) hline ht
  have hα : RiemannGaussian.DerivativePowerExponents.alpha 1 = (1 : ℝ) / 6 := by
    norm_num [RiemannGaussian.DerivativePowerExponents.alpha]
  simpa only [hα] using h

theorem riemannZeta_critical_line_power {s : ℂ} (hσ : s.re = 1 / 2)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 393216 * |s.im| ^ ((3 : ℝ) / 16) := by
  have hW := riemannZeta_critical_line_weyl hσ ht
  have hlog := sixth_rpow_mul_log_le_three_sixteenths
    (by linarith : (0 : ℝ) < |s.im|)
  nlinarith

theorem exists_riemannZeta_critical_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C * (1 + |t|) ^ ((3 : ℝ) / 16) := by
  apply exists_riemannZeta_criticalPoint_growth_of_tail
    (C := 393216) (by norm_num : (0 : ℝ) ≤ 3 / 16)
  intro t ht
  simpa only [zetaCriticalPoint_im] using
    riemannZeta_critical_line_power (zetaCriticalPoint_re t) (by simpa using ht)

end Sidon

end
end


-- Sidon.NumberTheory.MollifierLeftEndpoint
section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

theorem exists_mollifierError_critical_cumulative_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, 0 ≤ T →
      (∫ t in Set.Icc (-T) T, ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2) ≤
        K * (1 + Real.log N) * (T + N) * (1 + T) ^ ((3 : ℝ) / 8) := by
  obtain ⟨C, hC, hW⟩ := exists_riemannZeta_critical_growth
  refine ⟨48 * C ^ 2 + 4, by positivity, ?_⟩
  intro N hN T hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hp : 1 ≤ (1 + T) ^ ((3 : ℝ) / 8) := Real.one_le_rpow (by linarith) (by norm_num)
  let B : ℝ := 2 * C ^ 2 * (1 + T) ^ ((3 : ℝ) / 8)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2 ≤
        B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2 := by
    have hz : ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C * (1 + T) ^ ((3 : ℝ) / 16) := by
      apply (hW t).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [abs_of_nonneg ht.1]
      linarith [ht.2]
    have hz2 : ‖riemannZeta (zetaCriticalPoint t)‖ ^ 2 ≤
        C ^ 2 * (1 + T) ^ ((3 : ℝ) / 8) := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have hpow : ((1 + T) ^ ((3 : ℝ) / 16)) ^ 2 = (1 + T) ^ ((3 : ℝ) / 8) := by
        calc
          _ = (1 + T) ^ (((3 : ℝ) / 16) * 2) := by
            rw [Real.rpow_mul (by positivity : 0 ≤ 1 + T), Real.rpow_two]
          _ = _ := by norm_num
      rw [mul_pow, hpow] at hh
      exact hh
    have he : ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2 ≤
        2 * ‖riemannZeta (zetaCriticalPoint t)‖ ^ 2 *
          ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2 := by
      have hh := norm_sub_le
        (riemannZeta (zetaCriticalPoint t) * dirichletMollifier N (zetaCriticalPoint t)) (1 : ℂ)
      rw [norm_mul, norm_one] at hh
      change ‖mollifierError N (zetaCriticalPoint t)‖ ≤ _ at hh
      have hh' := pow_le_pow_left₀ (norm_nonneg _) hh 2
      nlinarith [sq_nonneg (‖riemannZeta (zetaCriticalPoint t)‖ *
        ‖dirichletMollifier N (zetaCriticalPoint t)‖ - 1)]
    exact he.trans (by
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_right hz2
        (sq_nonneg ‖dirichletMollifier N (zetaCriticalPoint t)‖)])
  have hcM : Continuous (fun t : ℝ => dirichletMollifier N (zetaCriticalPoint t)) :=
    (differentiable_dirichletMollifier N).continuous.comp (by unfold zetaCriticalPoint; fun_prop)
  have hce : Continuous (fun t : ℝ => ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2) := by
    have hh : Continuous (fun t : ℝ => mollifierError N (zetaCriticalPoint t)) :=
      (continuous_riemannZeta_criticalPoint.mul hcM).sub continuous_const
    simpa only [Function.comp_def] using (continuous_pow 2).comp hh.norm
  have hci : Continuous (fun t : ℝ => B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2) :=
    (hcM.norm.pow 2).const_mul B |>.add continuous_const
  have hint : (∫ t in (0 : ℝ)..T, ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2) ≤
      B * (12 * (T + N) * (1 + Real.log N)) + 2 * T := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..T, (B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2 + 2) :=
        intervalIntegral.integral_mono_on hT (hce.intervalIntegrable _ _)
          (hci.intervalIntegrable _ _) hpoint
      _ = B * (∫ t in (0 : ℝ)..T, ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2) + 2 * T := by
        have hiB : IntervalIntegrable (fun t : ℝ =>
            B * ‖dirichletMollifier N (zetaCriticalPoint t)‖ ^ 2) volume 0 T :=
          ((hcM.norm.pow 2).const_mul B).intervalIntegrable _ _
        rw [intervalIntegral.integral_add hiB intervalIntegrable_const,
          intervalIntegral.integral_const_mul]
        simp [mul_comm]
      _ ≤ _ := by
        gcongr
        exact integral_dirichletMollifier_critical_norm_sq_le hN hT
  have heven (t : ℝ) : ‖mollifierError N (zetaCriticalPoint (-t))‖ ^ 2 =
      ‖mollifierError N (zetaCriticalPoint t)‖ ^ 2 := by
    have heq : zetaCriticalPoint (-t) = conj (zetaCriticalPoint t) := by
      apply Complex.ext <;> norm_num [zetaCriticalPoint]
    rw [heq, mollifierError_conj, Complex.norm_conj]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    integral_neg_pos_eq_two_of_even hce heven]
  have htail : T ≤ (1 + Real.log N) * (T + N) * (1 + T) ^ ((3 : ℝ) / 8) := by
    calc
      T ≤ T + N := le_add_of_nonneg_right (Nat.cast_nonneg N)
      _ ≤ (1 + Real.log N) * (T + N) := le_mul_of_one_le_left (by positivity) hlog
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp
  dsimp [B] at hint
  nlinarith

end Sidon

end
end


-- Sidon.NumberTheory.MollifierInterpolation
section

noncomputable section

open MeasureTheory Set Complex.HadamardThreeLines
open scoped Topology

namespace Sidon

theorem gaussianMollifier_sq_le_weighted_error {N : ℕ} {R σ t : ℝ} (hR : 1 ≤ R)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) (hσ1 : σ ≠ 1) :
    ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp 6 * (Real.exp (-2 * t ^ 2 / R ^ 2) *
        ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro hh
    exact hσ1 (by have he := congrArg Complex.re hh; simpa [hsre] using he)
  have hR0 : 0 < R := by linarith
  have hu : σ ^ 2 / R ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    nlinarith
  have hpole := norm_poleRemovedMollifierError_le (N := N) (s := s)
    (by rw [hsre]; linarith) hs1
  have he : (Real.exp ((σ ^ 2 - t ^ 2) / R ^ 2)) ^ 2 ≤
      Real.exp 6 * Real.exp (-2 * t ^ 2 / R ^ 2) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    have heq : 2 * ((σ ^ 2 - t ^ 2) / R ^ 2) =
        2 * (σ ^ 2 / R ^ 2) + -(2 * t ^ 2) / R ^ 2 := by ring
    linarith
  change ‖gaussianMollifier N R s‖ ^ 2 ≤ _
  rw [norm_gaussianMollifier N hR0.ne', hsre, hsim, mul_pow]
  have hh := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpole 2) he
    (by positivity) (sq_nonneg ‖mollifierError N s‖)
  convert hh using 1 <;> dsimp [s] <;> ring

theorem verticalL2_gaussianMollifier_le_of_cumulative {N : ℕ} {R σ K p : ℝ}
    (hR : 1 ≤ R) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) (hσ1 : σ ≠ 1)
    (hK : 0 ≤ K) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcum : ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc (-U) U, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
        K * (U + N) * (1 + U) ^ p) :
    verticalL2 (gaussianMollifier N R) σ ≤
      Real.exp 6 * gaussianCumulativeConstant * K * (R + N) * R ^ p := by
  have hc : Continuous (fun t : ℝ => ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) :=
    (continuous_pow 2).comp (continuous_mollifierError_vertical N hσ1).norm
  obtain ⟨hi, hbound⟩ := gaussian_integral_of_cumulative hc (fun _ => sq_nonneg _)
    hK hR (Nat.cast_nonneg N) hp hp1 hcum
  unfold verticalL2
  calc
    _ ≤ ∫ t : ℝ, Real.exp 6 * (Real.exp (-2 * t ^ 2 / R ^ 2) *
        ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
      apply integral_mono (integrable_gaussianMollifier_norm_sq N hR hσ hσ') (hi.const_mul _)
      intro t
      exact gaussianMollifier_sq_le_weighted_error hR hσ hσ' hσ1
    _ = Real.exp 6 * ∫ t : ℝ, Real.exp (-2 * t ^ 2 / R ^ 2) *
        ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2 := integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg 6)
      convert hh using 1 <;> ring

theorem exists_verticalL2_gaussianMollifier_left_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ R : ℝ, 1 ≤ R →
      verticalL2 (gaussianMollifier N R) (1 / 2) ≤
        K * (1 + Real.log N) * (R + N) * R ^ ((3 : ℝ) / 8) := by
  obtain ⟨K, hK, hc⟩ := exists_mollifierError_critical_cumulative_bound
  refine ⟨Real.exp 6 * gaussianCumulativeConstant * K, by
    exact mul_pos (mul_pos (Real.exp_pos _) gaussianCumulativeConstant_pos) hK, ?_⟩
  intro N hN R hR
  have hlog : 0 ≤ 1 + Real.log N := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.log_nonneg hn]
  have hh := verticalL2_gaussianMollifier_le_of_cumulative (N := N) (σ := 1 / 2)
    hR (by norm_num) (by norm_num) (by norm_num) (mul_nonneg hK.le hlog)
    (p := 3 / 8) (by norm_num) (by norm_num) (fun U hU => by
      simpa [zetaCriticalPoint, mul_assoc] using hc N hN U hU)
  convert hh using 1 <;> ring

theorem verticalL2_gaussianMollifier_right_bound {N : ℕ} (hN : 1 ≤ N)
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    verticalL2 (gaussianMollifier N R) (1 + δ) ≤
      (4096 * Real.exp 6 * gaussianCumulativeConstant) * (R + N) / ((N : ℝ) * δ ^ 8) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc (U : ℝ) (hU : 0 ≤ U) :
      (∫ t in Icc (-U) U, ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
        (4096 / ((N : ℝ) * δ ^ 8)) * (U + N) * (1 + U) ^ (0 : ℝ) := by
    have hh := integral_mollifierError_right_symmetric_le hN hδ (by linarith) hU
    apply hh.trans_eq
    simp only [Real.rpow_zero, mul_one]
    field_simp <;> ring
  have hh := verticalL2_gaussianMollifier_le_of_cumulative hR (σ := 1 + δ)
    (by linarith) (by linarith) (by linarith) (by positivity)
    (p := 0) (by norm_num) (by norm_num) hc
  simp only [Real.rpow_zero, mul_one] at hh
  convert hh using 1 <;> ring

theorem integral_mollifierError_le_gaussianL2 {N : ℕ} {R σ : ℝ} (hR : 1 ≤ R)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    (∫ t in (1 : ℝ)..R, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      8 * Real.exp 2 * verticalL2 (gaussianMollifier N R) σ := by
  have hce : ContinuousOn
      (fun t : ℝ => ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) (Icc 1 R) := by
    intro t ht
    have hs1 : (σ : ℂ) + t * Complex.I ≠ 1 := by
      intro heq
      have hh := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add,
        Complex.one_im] at hh
      linarith [ht.1]
    have harg : ContinuousAt (fun v : ℝ => (σ : ℂ) + v * Complex.I) t := by fun_prop
    have hcomp : ContinuousAt (fun v : ℝ => mollifierError N ((σ : ℂ) + v * Complex.I)) t :=
      ContinuousAt.comp' (f := fun v : ℝ => (σ : ℂ) + v * Complex.I) (x := t)
        (analyticAt_mollifierError N hs1).continuousAt harg
    exact (hcomp.norm.pow 2).continuousWithinAt
  have hcg : Continuous (fun t : ℝ => gaussianMollifier N R ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (analyticAt_gaussianMollifier N R ?_).continuousAt.comp (by fun_prop)
    apply RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero
    simpa using (show 0 ≤ σ by linarith)
  have hig := integrable_gaussianMollifier_norm_sq N hR hσ hσ'
  calc
    _ ≤ ∫ t in (1 : ℝ)..R, 8 * Real.exp 2 *
        ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hR (hce.intervalIntegrable_of_Icc hR)
        (((hcg.norm.pow 2).const_mul _).intervalIntegrable _ _)
      intro t ht
      exact mollifierError_sq_le_gaussianMollifier_sq hR (by simpa using hσ)
        (by simpa using hσ') (by simpa [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])] using ht.1)
        (by simpa [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])] using ht.2)
    _ = 8 * Real.exp 2 * ∫ t in (1 : ℝ)..R,
        ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [intervalIntegral.integral_of_le hR]
      exact setIntegral_le_integral hig (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

theorem integral_mollifierError_interpolation {N : ℕ} {R δ σ : ℝ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hσ : σ ∈ Icc (1 / 2) (1 + δ)) :
    (∫ t in (1 : ℝ)..R, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      8 * Real.exp 2 *
        (verticalL2 (gaussianMollifier N R) (1 / 2) ^
          (1 - (σ - 1 / 2) / (1 + δ - 1 / 2)) *
        verticalL2 (gaussianMollifier N R) (1 + δ) ^
          ((σ - 1 / 2) / (1 + δ - 1 / 2))) := by
  apply (integral_mollifierError_le_gaussianL2 hR hσ.1 (by linarith [hσ.2])).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply verticalL2_logConvex (by linarith) hσ
    (analyticOnNhd_gaussianMollifier N R (by norm_num))
    (bddAbove_gaussianMollifier N hR (by norm_num) (by linarith))
  intro u hu
  exact integrable_gaussianMollifier_norm_sq N hR hu.1 (by linarith [hu.2])

end Sidon

end
end


-- Sidon.NumberTheory.MollifierRightHalfPlane
section

noncomputable section

open MeasureTheory

namespace Sidon

theorem integral_mollifierError_right_halfPlane_le {N : ℕ} (hN : 1 ≤ N)
    {δ σ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 1 + δ ≤ σ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      T * (16 / ((N : ℝ) * δ ^ 4)) + 1024 / δ ^ 8 + 512 / δ ^ 5 := by
  let a (n : ℕ) := LSeries.term (balancedMollifierCoefficient N) (σ : ℂ) n
  let d (n : ℕ) : ℝ := (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + δ)
  let w (n : ℕ) : ℝ :=
    (n.divisors.card : ℝ) ^ 2 * (1 + Real.log n) / (n : ℝ) ^ (1 + 2 * δ)
  have hcmp (n : ℕ) : ‖a n‖ ≤ ‖rightMollifierCoefficient N δ n‖ :=
    LSeries.norm_term_le_of_re_le_re _ (by simpa using hσ) n
  have ha_le (n : ℕ) : ‖a n‖ ≤ d n :=
    (hcmp n).trans (norm_rightMollifierCoefficient_le_sq hN δ n)
  have ha2_le (n : ℕ) : ‖a n‖ ^ 2 ≤ (1 / (N : ℝ)) * d n :=
    (pow_le_pow_left₀ (norm_nonneg _) (hcmp n) 2).trans
      (norm_rightMollifierCoefficient_sq_le hN hδ n)
  have hlog (n : ℕ) : 0 ≤ 1 + Real.log n := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [Real.log_nonneg hn1]
  have haw_le (n : ℕ) : (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) ≤ w n := by
    apply (show (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n) ≤
        (n : ℝ) * ‖rightMollifierCoefficient N δ n‖ ^ 2 * (1 + Real.log n) from ?_).trans
      (weighted_norm_rightMollifierCoefficient_sq_le hN δ n)
    gcongr
    exact hcmp n
  have hd : Summable d := summable_divisor_sq_div_rpow (by linarith : 1 < 1 + δ)
  have hw : Summable w := summable_divisor_sq_log_div_rpow hδ hδ1
  have ha := Summable.of_nonneg_of_le (fun n => norm_nonneg (a n)) ha_le hd
  have ha2 := Summable.of_nonneg_of_le (fun n => sq_nonneg ‖a n‖) ha2_le (hd.mul_left _)
  have haw := Summable.of_nonneg_of_le
    (fun n : ℕ => mul_nonneg (show 0 ≤ (n : ℝ) * ‖a n‖ ^ 2 by positivity) (hlog n)) haw_le hw
  have ha_bound : (∑' n : ℕ, ‖a n‖) ≤ 16 / δ ^ 4 :=
    (Summable.tsum_le_tsum ha_le ha hd).trans (tsum_divisor_sq_div_rpow_le_pole hδ hδ1)
  have ha2_bound : (∑' n : ℕ, ‖a n‖ ^ 2) ≤ 16 / ((N : ℝ) * δ ^ 4) := by
    calc
      _ ≤ ∑' n : ℕ, (1 / (N : ℝ)) * d n :=
        Summable.tsum_le_tsum ha2_le ha2 (hd.mul_left _)
      _ = (1 / (N : ℝ)) * ∑' n : ℕ, d n := tsum_mul_left
      _ ≤ (1 / (N : ℝ)) * (16 / δ ^ 4) :=
        mul_le_mul_of_nonneg_left (tsum_divisor_sq_div_rpow_le_pole hδ hδ1) (by positivity)
      _ = _ := by ring
  have haw_bound : (∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 * (1 + Real.log n)) ≤ 32 / δ ^ 5 :=
    (Summable.tsum_le_tsum haw_le haw hw).trans (tsum_divisor_sq_log_div_rpow_le hδ hδ1)
  have heq (t : ℝ) : logarithmicSeries a t = mollifierError N ((σ : ℂ) + t * Complex.I) := by
    have hh := LSeriesHasSum_balancedMollifierCoefficient
      (s := (σ : ℂ) + t * Complex.I) (by simp; linarith) N
    rw [← hh.tsum_eq]
    apply tsum_congr
    intro n
    exact (LSeries_term_vertical _ _ _ _).symm
  have hh := integral_logarithmicSeries_norm_sq_le a (by simp [a]) ha ha2 haw hT
  simp_rw [heq] at hh
  calc
    _ ≤ _ := hh
    _ ≤ T * (16 / ((N : ℝ) * δ ^ 4)) + 4 * (16 / δ ^ 4) ^ 2 + 16 * (32 / δ ^ 5) := by
      gcongr
    _ = _ := by ring

end Sidon

end
end


-- Sidon.NumberTheory.MollifierOptimization
section

noncomputable section

open MeasureTheory Set

namespace Sidon

theorem mollifier_interpolation_power_bound {R L B σ₀ σ : ℝ}
    (hR : 1 ≤ R) (hlog : 2 ≤ Real.log R) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ ≤ 1) (hσ : σ₀ ≤ σ)
    (hσ1 : σ ≤ 1 + 1 / Real.log R) :
    (L * Real.log R * R ^ ((11 : ℝ) / 8)) ^
        (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
      (B * Real.log R ^ 8) ^
        ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) ≤
      L * B * Real.exp (11 / 4) * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  have hR0 : 0 < R := by linarith
  have hlog0 : 0 < Real.log R := by linarith
  let θ := (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)
  have hden : 0 < 1 + 1 / Real.log R - 1 / 2 := by
    linarith [one_div_pos.mpr hlog0]
  have hθ : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one hden).mpr (by linarith)
  have hq : 0 ≤ 1 - θ := by linarith
  have hq1 : 1 - θ ≤ 1 := by linarith
  have hqbound : 1 - θ ≤ 2 * (1 - σ₀ + 1 / Real.log R) := by
    have heq : 1 - θ = (1 + 1 / Real.log R - σ) /
        (1 + 1 / Real.log R - 1 / 2) := by
      dsimp [θ]
      rw [one_sub_div hden.ne']
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ (1 + 1 / Real.log R - σ) / (1 / 2) := by
        apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
        linarith [one_div_pos.mpr hlog0]
      _ ≤ _ := by norm_num; linarith
  have hfactor : 1 ≤ L * Real.log R := by nlinarith
  have hleft : (L * Real.log R * R ^ ((11 : ℝ) / 8)) ^ (1 - θ) ≤
      (L * Real.log R) * R ^ (((11 : ℝ) / 8) * (1 - θ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR0.le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hfactor hq1) (by positivity)
  have hright : (B * Real.log R ^ 8) ^ θ ≤ B * Real.log R ^ 8 := by
    apply Real.rpow_le_self_of_one_le _ hθ1
    have hp : 1 ≤ Real.log R ^ 8 := one_le_pow₀ (by linarith : 1 ≤ Real.log R)
    nlinarith
  have hpower : R ^ (((11 : ℝ) / 8) * (1 - θ)) ≤
      R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.exp (11 / 4) := by
    calc
      _ ≤ R ^ ((11 / 4 : ℝ) * (1 - σ₀) + (11 / 4 : ℝ) / Real.log R) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        have hh := mul_le_mul_of_nonneg_left hqbound (by norm_num : (0 : ℝ) ≤ 11 / 8)
        convert hh using 1 <;> ring
      _ = _ := by
        rw [Real.rpow_add hR0]
        congr 1
        rw [Real.rpow_def_of_pos hR0]
        congr 1
        field_simp
  change (_ ^ (1 - θ) * _ ^ θ) ≤ _
  calc
    _ ≤ ((L * Real.log R) * R ^ (((11 : ℝ) / 8) * (1 - θ))) *
        (B * Real.log R ^ 8) := mul_le_mul hleft hright (by positivity) (by positivity)
    _ ≤ ((L * Real.log R) * (R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.exp (11 / 4))) *
        (B * Real.log R ^ 8) := by gcongr
    _ = _ := by ring

theorem ceil_mollifier_parameters {R : ℝ} (hR : 1 ≤ R) (hlog : 2 ≤ Real.log R) :
    1 ≤ ⌈R⌉₊ ∧ R ≤ (⌈R⌉₊ : ℝ) ∧ (⌈R⌉₊ : ℝ) ≤ 2 * R ∧
      1 + Real.log (⌈R⌉₊ : ℝ) ≤ 2 * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hRN : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hN1 : (1 : ℝ) ≤ ⌈R⌉₊ := hR.trans hRN
  have hNR : (⌈R⌉₊ : ℝ) ≤ 2 * R := by
    have hh := Nat.ceil_lt_add_one hR0.le
    linarith
  refine ⟨by exact_mod_cast hN1, hRN, hNR, ?_⟩
  have hlogN := Real.log_le_log (by linarith : (0 : ℝ) < ⌈R⌉₊) hNR
  rw [Real.log_mul (by norm_num) hR0.ne'] at hlogN
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

theorem exists_mollifier_optimized_interior_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → 2 ≤ Real.log R →
      ∀ σ₀ : ℝ, 1 / 2 ≤ σ₀ → σ₀ ≤ 1 → ∀ σ : ℝ, σ₀ ≤ σ →
        σ ≤ 1 + 1 / Real.log R →
      (∫ t in (1 : ℝ)..R,
        ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
        K * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  obtain ⟨K₀, hK₀, hleft⟩ := exists_verticalL2_gaussianMollifier_left_bound
  let L := max (6 * K₀) 1
  let B := max (8192 * Real.exp 6 * gaussianCumulativeConstant) 1
  have hL : 1 ≤ L := le_max_right _ _
  have hB : 1 ≤ B := le_max_right _ _
  refine ⟨8 * Real.exp 2 * (L * B * Real.exp (11 / 4)), by positivity, ?_⟩
  intro R hR hlog σ₀ hσ₀ hσ₀1 σ hσ hσ1
  obtain ⟨hN, hRN, hNR, hlogN⟩ := ceil_mollifier_parameters hR hlog
  have hR0 : 0 < R := by linarith
  have hN0 : (0 : ℝ) < ⌈R⌉₊ := hR0.trans_le hRN
  have hlog0 : 0 < Real.log R := by linarith
  have hδ : 0 < 1 / Real.log R := one_div_pos.mpr hlog0
  have hδhalf : 1 / Real.log R ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hlog
  have hG0 : 0 ≤ gaussianCumulativeConstant := gaussianCumulativeConstant_pos.le
  have hJl : 0 ≤ verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 / 2) := verticalL2_nonneg _ _
  have hJr : 0 ≤ verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 + 1 / Real.log R) := verticalL2_nonneg _ _
  have hleftR : verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 / 2) ≤
      L * Real.log R * R ^ ((11 : ℝ) / 8) := by
    calc
      _ ≤ K₀ * (1 + Real.log (⌈R⌉₊ : ℝ)) * (R + ⌈R⌉₊) * R ^ ((3 : ℝ) / 8) :=
        hleft _ hN R hR
      _ ≤ K₀ * (2 * Real.log R) * (3 * R) * R ^ ((3 : ℝ) / 8) := by gcongr <;> linarith
      _ = (6 * K₀) * Real.log R * R ^ ((11 : ℝ) / 8) := by
        have heq : R * R ^ ((3 : ℝ) / 8) = R ^ ((11 : ℝ) / 8) := by
          conv_lhs => lhs; rw [← Real.rpow_one R]
          rw [← Real.rpow_add hR0]
          norm_num
        calc
          _ = (6 * K₀) * Real.log R * (R * R ^ ((3 : ℝ) / 8)) := by ring
          _ = _ := by rw [heq]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hrightR : verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 + 1 / Real.log R) ≤
      B * Real.log R ^ 8 := by
    calc
      _ ≤ (4096 * Real.exp 6 * gaussianCumulativeConstant) * (R + ⌈R⌉₊) /
          ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 8) :=
        verticalL2_gaussianMollifier_right_bound hN hR hδ hδhalf
      _ ≤ (4096 * Real.exp 6 * gaussianCumulativeConstant) * (2 * (⌈R⌉₊ : ℝ)) /
          ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 8) := by gcongr <;> first | positivity | linarith
      _ = (8192 * Real.exp 6 * gaussianCumulativeConstant) * Real.log R ^ 8 := by
        field_simp
        ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  have hθ : 0 ≤ (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2) := by
    exact div_nonneg (by linarith) (by linarith [hδ])
  have hq : 0 ≤ 1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2) := by
    have hd : 0 < 1 + 1 / Real.log R - 1 / 2 := by linarith [hδ]
    have hh : (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2) ≤ 1 :=
      (div_le_one hd).mpr (by linarith)
    linarith
  calc
    _ ≤ 8 * Real.exp 2 *
        (verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 / 2) ^
          (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
        verticalL2 (gaussianMollifier ⌈R⌉₊ R) (1 + 1 / Real.log R) ^
          ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2))) :=
      integral_mollifierError_interpolation hR hδ hδhalf ⟨by linarith, hσ1⟩
    _ ≤ 8 * Real.exp 2 *
        ((L * Real.log R * R ^ ((11 : ℝ) / 8)) ^
          (1 - (σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2)) *
        (B * Real.log R ^ 8) ^ ((σ - 1 / 2) / (1 + 1 / Real.log R - 1 / 2))) := by
      gcongr <;> positivity
    _ ≤ 8 * Real.exp 2 *
        (L * B * Real.exp (11 / 4) * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mollifier_interpolation_power_bound hR hlog hL hB hσ₀ hσ₀1 hσ hσ1
    _ = _ := by ring

theorem mollifier_optimized_right_bound {R σ : ℝ} (hR : 1 ≤ R)
    (hlog : 2 ≤ Real.log R) (hσ : 1 + 1 / Real.log R ≤ σ) :
    (∫ t in (1 : ℝ)..R,
      ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤ 1552 * Real.log R ^ 9 := by
  obtain ⟨hN, hRN, _, _⟩ := ceil_mollifier_parameters hR hlog
  have hlog0 : 0 < Real.log R := by linarith
  have hN0 : (0 : ℝ) < ⌈R⌉₊ := (show 0 < R by linarith).trans_le hRN
  have hδ : 0 < 1 / Real.log R := by positivity
  have hδ1 : 1 / Real.log R ≤ 1 := by
    apply (div_le_one hlog0).mpr
    linarith
  have hc := (continuous_mollifierError_vertical ⌈R⌉₊ (σ := σ) (by linarith)).norm.pow 2
  have hi0 : IntervalIntegrable
      (fun t : ℝ => ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) volume 0 1 :=
    hc.intervalIntegrable _ _
  have hi1 : IntervalIntegrable
      (fun t : ℝ => ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) volume 1 R :=
    hc.intervalIntegrable _ _
  have hpos : 0 ≤ ∫ t in (0 : ℝ)..1,
      ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have hraw := integral_mollifierError_right_halfPlane_le hN hδ hδ1 hσ (by linarith : 0 ≤ R)
  have hdiag : R * (16 / ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 4)) ≤ 16 * Real.log R ^ 4 := by
    calc
      _ = (16 * Real.log R ^ 4) * (R / (⌈R⌉₊ : ℝ)) := by field_simp <;> ring
      _ ≤ (16 * Real.log R ^ 4) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one hN0).mpr hRN
      _ = _ := mul_one _
  have h4 : Real.log R ^ 4 ≤ Real.log R ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h8 : Real.log R ^ 8 ≤ Real.log R ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h5 : Real.log R ^ 5 ≤ Real.log R ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hraw' : (∫ t in (0 : ℝ)..R,
      ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
      16 * Real.log R ^ 4 + 1024 * Real.log R ^ 8 + 512 * Real.log R ^ 5 := by
    calc
      _ ≤ _ := hraw
      _ = R * (16 / ((⌈R⌉₊ : ℝ) * (1 / Real.log R) ^ 4)) +
          1024 * Real.log R ^ 8 + 512 * Real.log R ^ 5 := by field_simp <;> ring
      _ ≤ _ := by linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  linarith

theorem exists_mollifier_optimized_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → 2 ≤ Real.log R →
      ∀ σ₀ : ℝ, 1 / 2 ≤ σ₀ → σ₀ ≤ 1 → ∀ σ : ℝ, σ₀ ≤ σ →
      (∫ t in (1 : ℝ)..R,
        ‖mollifierError ⌈R⌉₊ ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤
        K * R ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log R ^ 9 := by
  obtain ⟨K, hK, hinner⟩ := exists_mollifier_optimized_interior_bound
  refine ⟨max K 1552, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro R hR hlog σ₀ hσ₀ hσ₀1 σ hσ
  by_cases hcut : σ ≤ 1 + 1 / Real.log R
  · exact (hinner R hR hlog σ₀ hσ₀ hσ₀1 σ hσ hcut).trans
      (by gcongr; exact le_max_left _ _)
  · have hh := mollifier_optimized_right_bound hR hlog (le_of_not_ge hcut)
    have hp : 1 ≤ R ^ ((11 / 4 : ℝ) * (1 - σ₀)) :=
      Real.one_le_rpow hR (by positivity)
    apply hh.trans
    calc
      _ ≤ (max K 1552) * Real.log R ^ 9 := by gcongr; exact le_max_right _ _
      _ ≤ _ := by
        have hconst : 0 ≤ max K 1552 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hp
          (mul_nonneg hconst (show 0 ≤ Real.log R ^ 9 by positivity))]

end Sidon

end
end


-- Sidon.NumberTheory.OptimizedMollifierSlices
section

noncomputable section

open MeasureTheory Set

namespace Sidon

theorem exists_optimizedMollifierSlices :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ σ₀ : ℝ, 1 / 2 ≤ σ₀ → σ₀ ≤ 1 →
        ∃ N : ℕ, 131072 ≤ N ∧ T ≤ (N : ℝ) ∧
          ∀ u ∈ Icc σ₀ (4 - σ₀),
            (∫ t in Icc 1 (T + 3),
              ‖mollifierError N ((u : ℂ) + t * Complex.I)‖ ^ 2) ≤
              K * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log T ^ 9 := by
  obtain ⟨K, hK, hbound⟩ := exists_mollifier_optimized_bound
  refine ⟨2048 * K, by positivity, max 131072 (Real.exp 4), ?_⟩
  intro T hT σ₀ hσ₀ hσ₀1
  have hTlarge : (131072 : ℝ) ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT3 : 3 ≤ T := by linarith
  have hlog : 4 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 4) ((le_max_right _ _).trans hT)
    simpa only [Real.log_exp] using hh
  have hR : 1 ≤ T + 3 := by linarith
  have hR0 : 0 < T + 3 := by linarith
  have hRT : T + 3 ≤ 2 * T := by linarith
  have hlogRlo : 2 ≤ Real.log (T + 3) := by
    have hh := Real.log_le_log hT0 (show T ≤ T + 3 by linarith)
    linarith
  have hlogR : Real.log (T + 3) ≤ 2 * Real.log T := by
    have hh := Real.log_le_log hR0 hRT
    rw [Real.log_mul (by norm_num) hT0.ne'] at hh
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    linarith
  have hRN : T + 3 ≤ (⌈T + 3⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨⌈T + 3⌉₊, ?_, by linarith, ?_⟩
  · exact_mod_cast (show (131072 : ℝ) ≤ ⌈T + 3⌉₊ by linarith)
  intro u hu
  have ha : 0 ≤ (11 / 4 : ℝ) * (1 - σ₀) := by positivity
  have ha2 : (11 / 4 : ℝ) * (1 - σ₀) ≤ 2 := by linarith
  have hpower : (T + 3) ^ ((11 / 4 : ℝ) * (1 - σ₀)) ≤
      4 * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) := by
    calc
      _ ≤ (2 * T) ^ ((11 / 4 : ℝ) * (1 - σ₀)) := Real.rpow_le_rpow hR0.le hRT ha
      _ = (2 : ℝ) ^ ((11 / 4 : ℝ) * (1 - σ₀)) *
          T ^ ((11 / 4 : ℝ) * (1 - σ₀)) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ (2 : ℝ) ^ (2 : ℝ) * T ^ ((11 / 4 : ℝ) * (1 - σ₀)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2) (by positivity)
      _ = _ := by norm_num
  have hlogpow : Real.log (T + 3) ^ 9 ≤ 512 * Real.log T ^ 9 := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (T + 3)) hlogR 9
    rw [mul_pow] at hh
    norm_num at hh
    exact hh
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR]
  calc
    _ ≤ K * (T + 3) ^ ((11 / 4 : ℝ) * (1 - σ₀)) * Real.log (T + 3) ^ 9 :=
      hbound _ hR hlogRlo σ₀ hσ₀ hσ₀1 u hu.1
    _ ≤ K * (4 * T ^ ((11 / 4 : ℝ) * (1 - σ₀))) * (512 * Real.log T ^ 9) := by gcongr
    _ = _ := by ring

end Sidon

end
end


-- Sidon.NumberTheory.ZetaDensity
section

noncomputable section

namespace Sidon

theorem exists_uniformZetaZeroDensity :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, UniformZetaZeroDensity (23 / 8) 11 C T₀ := by
  obtain ⟨K, hK, T₀, hslices⟩ := exists_optimizedMollifierSlices
  exact exists_uniformZeroDensity_of_mollifier_slices hK hslices

end Sidon

end
end


-- Sidon.NumberTheory.ZeroLayers
section

noncomputable section

namespace Sidon

variable {ι : Type*}

theorem geometric_sum_Ico_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r J : ℕ) :
    (∑ j ∈ Finset.Ico r J, q ^ j) ≤ q ^ r / (1 - q) := by
  by_cases hrJ : r ≤ J
  · rw [geom_sum_Ico hq1.ne hrJ]
    have heq : (q ^ J - q ^ r) / (q - 1) = (q ^ r - q ^ J) / (1 - q) := by
      rw [show q - 1 = -(1 - q) by ring, div_neg, ← neg_div, neg_sub]
    rw [heq]
    exact div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hq0 J)) (by linarith)
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    exact div_nonneg (pow_nonneg hq0 r) (by linarith)

theorem sum_layer_weights_le (s : Finset ι) (k : ι → ℕ) (w : ι → ℝ)
    {K a b : ℝ} (hK : 0 ≤ K) (hba : b < a) (r : ℕ)
    (hkr : ∀ i ∈ s, r ≤ k i)
    (hw : ∀ i ∈ s, w i ≤ Real.exp (-a * k i))
    (hcount : ∀ j : ℕ, ((s.filter (fun i => k i = j)).card : ℝ) ≤ K * Real.exp (b * j)) :
    (∑ i ∈ s, w i) ≤ K * Real.exp (-(a - b) * r) / (1 - Real.exp (-(a - b))) := by
  classical
  let J := max r ((s.image k).sup id + 1)
  have hmaps (i : ι) (hi : i ∈ s) : k i ∈ Finset.Ico r J := by
    apply Finset.mem_Ico.mpr
    refine ⟨hkr i hi, ?_⟩
    have hh : k i ≤ (s.image k).sup id := Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    dsimp [J]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  have hq0 : 0 ≤ Real.exp (-(a - b)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(a - b)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc
    _ ≤ ∑ j ∈ Finset.Ico r J, (K * Real.exp (b * j)) * Real.exp (-a * j) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ _i ∈ s.filter (fun i => k i = j), Real.exp (-a * j) := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
          simpa only [hij] using hw i his
        _ = ((s.filter (fun i => k i = j)).card : ℝ) * Real.exp (-a * j) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount j) (Real.exp_pos _).le
    _ = K * ∑ j ∈ Finset.Ico r J, (Real.exp (-(a - b))) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ K * (Real.exp (-(a - b))) ^ r / (1 - Real.exp (-(a - b))) := by
      have hh := mul_le_mul_of_nonneg_left (geometric_sum_Ico_le hq0 hq1 r J) hK
      simpa only [mul_div_assoc] using hh
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

def zeroLayer (s : Finset ι) (β : ι → ℝ) (L : ℝ) (j : ℕ) : Finset ι :=
  s.filter fun i => Nat.floor (L * (1 - β i)) = j

theorem finite_zero_layer_bound (s : Finset ι) (β : ι → ℝ)
    {L η K b : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hK : 0 ≤ K) (hb : b < 1)
    (hβ : ∀ i ∈ s, β i ≤ 1 - η)
    (hcount : ∀ j : ℕ, ((zeroLayer s β L j).card : ℝ) ≤ K * Real.exp (b * (j + 1))) :
    (∑ i ∈ s, Real.exp (-L * (1 - β i))) ≤
      (K * Real.exp b) * Real.exp (-(1 - b) * Nat.floor (L * η)) /
        (1 - Real.exp (-(1 - b))) := by
  classical
  let k := fun i => Nat.floor (L * (1 - β i))
  apply sum_layer_weights_le s k (fun i => Real.exp (-L * (1 - β i)))
    (mul_nonneg hK (Real.exp_pos b).le) hb (Nat.floor (L * η))
  · intro i hi
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith [hβ i hi]) hL.le)
  · intro i hi
    have hdist : 0 ≤ L * (1 - β i) := mul_nonneg hL.le (by linarith [hβ i hi])
    apply Real.exp_le_exp.mpr
    have hfloor := Nat.floor_le hdist
    change -L * (1 - β i) ≤ -(1 : ℝ) * (k i : ℝ)
    dsimp [k]
    linarith
  · intro j
    have h := hcount j
    change ((zeroLayer s β L j).card : ℝ) ≤ _
    convert h using 1
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring

end Sidon

end
end


-- Sidon.NumberTheory.ZeroDensityLayers
section

noncomputable section

namespace Sidon

variable {ι : Type*}

theorem zeroLayer_card_le_of_density (s : Finset ι) (β : ι → ℝ)
    {L K D : ℝ} (hL : 0 < L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hβ : ∀ i ∈ s, 0 ≤ β i ∧ β i ≤ 1)
    (hcount : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      ((s.filter (fun i => σ ≤ β i)).card : ℝ) ≤ K * Real.exp (D * (1 - σ)))
    (j : ℕ) :
    ((zeroLayer s β L j).card : ℝ) ≤ K * Real.exp ((D / L) * (j + 1)) := by
  classical
  let σ : ℝ := max 0 (1 - ((j : ℝ) + 1) / L)
  have hσ0 : 0 ≤ σ := le_max_left _ _
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    apply max_le (by norm_num)
    have := div_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity) hL.le
    linarith
  have hsub : zeroLayer s β L j ⊆ s.filter (fun i => σ ≤ β i) := by
    intro i hi
    obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨his, ?_⟩
    dsimp [σ]
    apply max_le (hβ i his).1
    have hdist : 0 ≤ L * (1 - β i) := mul_nonneg hL.le (by linarith [(hβ i his).2])
    have hf := Nat.lt_floor_add_one (L * (1 - β i))
    rw [hij] at hf
    have hh : 1 - β i < ((j : ℝ) + 1) / L := (lt_div_iff₀ hL).mpr (by nlinarith)
    linarith
  have hDσ : D * (1 - σ) ≤ (D / L) * ((j : ℝ) + 1) := by
    have hmax : 1 - ((j : ℝ) + 1) / L ≤ σ := le_max_right _ _
    have hh : 1 - σ ≤ ((j : ℝ) + 1) / L := by linarith
    have := mul_le_mul_of_nonneg_left hh hD
    convert this using 1; ring
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((hcount σ hσ0 hσ1).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hDσ) hK))

theorem finite_zero_bound_of_density (s : Finset ι) (β : ι → ℝ)
    {L η K D : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hDL : D < L)
    (hβ0 : ∀ i ∈ s, 0 ≤ β i)
    (hβ1 : ∀ i ∈ s, β i ≤ 1 - η)
    (hcount : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      ((s.filter (fun i => σ ≤ β i)).card : ℝ) ≤ K * Real.exp (D * (1 - σ))) :
    (∑ i ∈ s, Real.exp (-L * (1 - β i))) ≤
      (K * Real.exp (D / L)) *
        Real.exp (-(1 - D / L) * Nat.floor (L * η)) /
        (1 - Real.exp (-(1 - D / L))) := by
  apply finite_zero_layer_bound s β hL hη hK ((div_lt_one hL).mpr hDL) hβ1
  intro j
  apply zeroLayer_card_le_of_density s β hL hK hD _ hcount j
  intro i hi
  exact ⟨hβ0 i hi, by linarith [hβ1 i hi]⟩

theorem finite_zero_bound_of_log_reserve (s : Finset ι) (β : ι → ℝ)
    {L η K b : ℝ} {B : ℕ} (hL : 0 < L) (hη : 0 ≤ η) (hK : 0 ≤ K) (hb : b < 1)
    (hβ : ∀ i ∈ s, β i ≤ 1 - η)
    (hcount : ∀ j : ℕ, ((zeroLayer s β L j).card : ℝ) ≤
      (K * L ^ B) * Real.exp (b * (j + 1)))
    (hreserve : ((B : ℝ) + 2) * Real.log L ≤
      (1 - b) * Nat.floor (L * η)) :
    (∑ i ∈ s, Real.exp (-L * (1 - β i))) ≤
      (K * Real.exp b) / (1 - Real.exp (-(1 - b))) / L ^ 2 := by
  have hden : 0 < 1 - Real.exp (-(1 - b)) := by
    have := Real.exp_lt_one_iff.mpr (show -(1 - b) < 0 by linarith)
    linarith
  have hexp : Real.exp (-(1 - b) * Nat.floor (L * η)) ≤ (L ^ (B + 2))⁻¹ := by
    calc
      _ ≤ Real.exp (-(((B : ℝ) + 2) * Real.log L)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, show ((B : ℝ) + 2) = ((B + 2 : ℕ) : ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log hL]
  have hh := finite_zero_layer_bound s β hL hη
    (mul_nonneg hK (pow_nonneg hL.le B)) hb hβ hcount
  apply hh.trans
  calc
    _ ≤ ((K * L ^ B) * Real.exp b) * (L ^ (B + 2))⁻¹ /
        (1 - Real.exp (-(1 - b))) := by gcongr
    _ = _ := by
      rw [pow_add, pow_two]
      field_simp

theorem zeta_zero_weight_bound {A K T₀ T x η : ℝ} {B : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hT : 1 < T) (hx : 1 < x) (hT₀ : T₀ ≤ T)
    (hη : 0 ≤ η) (hscale : A * Real.log T < Real.log x)
    (hdensity : UniformZetaZeroDensity A B K T₀)
    (hfree : ∀ z ∈ zetaZeroOccurrences T, z.1.re ≤ 1 - η) :
    (∑ z ∈ zetaZeroOccurrences T, x ^ (z.1.re - 1)) ≤
      ((K * (Real.log T) ^ B) * Real.exp (A * Real.log T / Real.log x)) *
        Real.exp (-(1 - A * Real.log T / Real.log x) * Nat.floor (Real.log x * η)) /
        (1 - Real.exp (-(1 - A * Real.log T / Real.log x))) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD : 0 ≤ A * Real.log T := mul_nonneg hA (Real.log_pos hT).le
  have hcount (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
      (((zetaZeroOccurrences T).filter (fun z => σ ≤ z.1.re)).card : ℝ) ≤
        (K * (Real.log T) ^ B) * Real.exp ((A * Real.log T) * (1 - σ)) := by
    have hh := hdensity T hT₀ σ hσ0 hσ1
    change (zetaZeroCount σ T : ℝ) ≤ _
    convert hh using 1
    rw [Real.rpow_def_of_pos (by linarith : 0 < T)]
    ring_nf
  have hh := finite_zero_bound_of_density (zetaZeroOccurrences T) (fun z => z.1.re)
    hL hη (mul_nonneg hK (pow_nonneg (Real.log_pos hT).le B)) hD hscale
    (fun z hz => (zetaZeroOccurrences_re_bounds hz).1) hfree hcount
  convert hh using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  congr 1
  ring

end Sidon

end
end


-- TH8000ZetaDensity
section

open Finset Filter Real Vx
open scoped Topology Classical

namespace TH8000Zeta

theorem density_23_8 : ∃ C : ℝ, 0<C ∧ ∀ T σ : ℝ, 2≤T → 0≤σ → σ≤1 →
    (((V3b T).filter (fun c => σ ≤ c.val.1.re)).card:ℝ) ≤
      C*T^((23/8:ℝ)*(1-σ))*(1+log T)^11 := by
  obtain ⟨K,hK,U,h⟩ := Sidon.exists_uniformZetaZeroDensity
  let U' := max 2 U
  let W := 2*K + ((V3b 1).card:ℝ) + ((V3b U').card:ℝ)
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨W,hW,?_⟩
  intro T σ hT hσ hσ1
  let e := (23/8:ℝ)*(1-σ)
  have he : 0 ≤ e := mul_nonneg (by norm_num) (sub_nonneg.mpr hσ1)
  have hT1 : 1 ≤ T := by linarith
  have hTe : 1 ≤ T^e := one_le_rpow hT1 he
  have hL : 0 ≤ log T := log_nonneg hT1
  have hp : 1 ≤ (1+log T)^11 := one_le_pow₀ (by linarith)
  have hbig : 1 ≤ T^e * (1+log T)^11 := one_le_mul_of_one_le_of_one_le hTe hp
  change _ ≤ W*T^e*(1+log T)^11
  by_cases ht : U ≤ T
  · have hcnt := h T ht σ hσ hσ1
    change _ ≤ K*T^e*(log T)^11 at hcnt
    have hmono := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hL (show log T ≤ 1+log T by linarith) 11)
      (mul_nonneg hK.le (zero_le_one.trans hTe))
    have hpair : (((V3b T).filter (fun c => σ ≤ c.val.1.re)).card:ℝ) ≤
      2*(Sidon.zetaZeroCount σ T:ℝ)+(V3b 1).card := by exact_mod_cast two_sided_count T σ
    have hscale := mul_le_mul_of_nonneg_left hbig (Nat.cast_nonneg (α:=ℝ) (V3b 1).card)
    have hextra := mul_nonneg (Nat.cast_nonneg (α:=ℝ) (V3b U').card) (zero_le_one.trans hbig)
    dsimp only [W]
    linarith only [hpair,hcnt,hmono,hscale,hextra]
  · have hsub : ((V3b T).filter (fun c => σ ≤ c.val.1.re)) ⊆ V3b U' := by
      intro c hc
      exact (V5l U' c).mpr (((V5l T c).mp (mem_filter.mp hc).1).trans
        ((lt_of_not_ge ht).le.trans (le_max_right ..)))
    have hWc : ((V3b U').card:ℝ) ≤ W := by dsimp only [W]; linarith [Nat.cast_nonneg (α:=ℝ) (V3b 1).card]
    calc
      _ ≤ ((V3b U').card:ℝ) := by exact_mod_cast card_le_card hsub
      _ ≤ W := hWc
      _ ≤ W*(T^e*(1+log T)^11) := le_mul_of_one_le_right hW.le hbig
      _ = _ := by ring

end TH8000Zeta

end


-- TH8000ZetaDamped
section

open Finset Filter Real Vx
open scoped Classical Topology

namespace TH8000Zeta

noncomputable def damp (X T : ℝ) : ℝ := min 1 (X^(1/3:ℝ)/T)

private lemma damp_count (C : ℝ) (hC : 0<C)
    (hdens : ∀ T σ : ℝ, 2≤T → 0≤σ → σ≤1 →
      (((V3b T).filter (fun c => σ ≤ c.val.1.re)).card:ℝ) ≤
        C*T^((23/8:ℝ)*(1-σ))*(1+log T)^11)
    {X T σ : ℝ} (hX : 1<X) (hT : 2≤T) (hs : 0≤σ) (hs1 : σ≤1) :
    damp X T * (((V3b T).filter (fun c => σ ≤ c.val.1.re)).card:ℝ) ≤
      (C+78/log (14/13))*(1+log T)^11 * exp ((23/24)*(log X)*(1-σ)) := by
  let Y := X^(1/3:ℝ)
  let e := (23/8:ℝ)*(1-σ)
  let S := (V3b T).filter (fun c => σ ≤ c.val.1.re)
  have he : 0 ≤ e := mul_nonneg (by norm_num) (sub_nonneg.mpr hs1)
  have hY : 1 ≤ Y := one_le_rpow hX.le (by norm_num)
  have hY0 := zero_lt_one.trans_le hY
  have hT0 : 0 < T := by linarith
  have htlog := log_nonneg (show 1 ≤ T by linarith)
  have hV : 0 < 78/log (14/13) := div_pos (by norm_num) (log_pos (by norm_num))
  have hc := hdens T σ hT hs hs1
  change (S.card:ℝ) ≤ C*T^e*(1+log T)^11 at hc
  let W := (C+78/log (14/13))*(1+log T)^11
  have hw : 0 ≤ W := by dsimp only [W]; positivity
  have hd : 0 ≤ damp X T := le_min zero_le_one (div_nonneg hY0.le hT0.le)
  have hscale : (S.card:ℝ) ≤ W*T^e := hc.trans (by
    dsimp only [W]
    have hl := mul_nonneg (mul_nonneg hV.le (rpow_nonneg hT0.le e))
      (pow_nonneg (show 0 ≤ 1+log T by linarith) 11)
    nlinarith only [hl])
  have htarget : Y^e = exp ((23/24)*log X*(1-σ)) := by
    dsimp only [Y,e]
    rw [← rpow_mul (zero_lt_one.trans hX).le,rpow_def_of_pos (zero_lt_one.trans hX)]
    congr 1
    ring
  rw [← htarget]
  change damp X T * (S.card:ℝ) ≤ W*Y^e
  by_cases hTY : T ≤ Y
  · calc
      _ ≤ (S.card:ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _) (min_le_left ..)
      _ ≤ W*T^e := hscale
      _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_rpow hT0.le hTY he) hw
  by_cases he1 : e ≤ 1
  · have hratio : 1 ≤ T/Y := (one_le_div hY0).mpr (lt_of_not_ge hTY).le
    have hfactor : T^e = Y^e*(T/Y)^e := by
      rw [← mul_rpow hY0.le (div_nonneg hT0.le hY0.le)]
      field_simp
    calc
      _ ≤ (Y/T)*(W*T^e) := mul_le_mul (min_le_right ..) hscale (Nat.cast_nonneg _) (by positivity)
      _ = W*(Y/T*Y^e)*(T/Y)^e := by rw [hfactor]; ring
      _ ≤ W*(Y/T*Y^e)*(T/Y) := mul_le_mul_of_nonneg_left (rpow_le_self_of_one_le hratio he1) (by positivity)
      _ = _ := by field_simp
  · have hcard := V5s.Vhe T hT S (fun c hc => (V5l T c).mp (mem_filter.mp hc).1)
    have hL1 : 1 ≤ 1+log T := by linarith
    have hLp : log T ≤ (1+log T)^11 := by
      have := pow_le_pow_right₀ hL1 (show 1 ≤ 11 by decide)
      simp only [pow_one] at this
      linarith
    have hcut : Y ≤ Y^e := by
      simpa using rpow_le_rpow_of_exponent_le hY (le_of_not_ge he1)
    calc
      _ ≤ (Y/T)*((78/log (14/13))*T*log T) := mul_le_mul (min_le_right ..) hcard (Nat.cast_nonneg _) (by positivity)
      _ = (78/log (14/13)*log T)*Y := by field_simp
      _ ≤ W*Y^e := mul_le_mul (mul_le_mul (le_add_of_nonneg_left hC.le) hLp htlog (by linarith))
        hcut hY0.le hw

private lemma reserve (A : ℕ) :
    ∃ P : ℝ, ∀ X ≥ P, 1 < X → ∀ T : ℝ, T ≤ X^2 → ∀ c ∈ V3b T,
      exp (-(log X / 48)*(1-c.val.1.re)) ≤ ((log X)^A)⁻¹ := by
  obtain ⟨P,hP⟩ := all_heights_zero_free (48*A)
  refine ⟨max P (exp 1),?_⟩
  intro X hX hx T ht c hc
  have hg := hP X ((le_max_left _ _).trans hX) T ht c hc
  have hL : 1 ≤ log X := (le_log_iff_exp_le (zero_lt_one.trans hx)).mpr ((le_max_right _ _).trans hX)
  have hL0 := zero_lt_one.trans_le hL
  have hwidth : 3*((48*A+14:ℕ):ℝ)*log (log X)/log X ≤ 1-c.val.1.re := by
    change c.val.1.re ≤ 1 - 3*((48*A+14:ℕ):ℝ)*log (log X)/log X at hg
    linarith
  have hmain := (div_le_iff₀ hL0).mp hwidth
  have hc' : 48*(A:ℝ) ≤ 3*((48*A+14:ℕ):ℝ) := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) A]
  have hh := mul_le_mul_of_nonneg_right hc' (log_nonneg hL)
  rw [← exp_log (pow_pos hL0 A), ← exp_neg, log_pow]
  apply exp_le_exp.mpr
  linarith only [hh,hmain]

theorem damped_band (A : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ P : ℝ, ∀ X ≥ P, ∀ T : ℝ, 2 ≤ T → T ≤ X^2 →
      damp X T * (∑ c ∈ V3b T, X^(c.val.1.re-1)) ≤ K/(log X)^A := by
  obtain ⟨C,hC,hdens⟩ := density_23_8
  obtain ⟨P,hP⟩ := reserve (A+11)
  let W := C+78/log (14/13)
  let b := (46/47:ℝ)
  let Z := exp b / (1-exp (-(1-b)))
  have hW : 0 < W := by dsimp only [W]; positivity
  have hZ : 0 < Z := div_pos (exp_pos _) (sub_pos.mpr (exp_lt_one_iff.mpr (by norm_num [b])))
  refine ⟨W*3^11*Z,by positivity,max P (exp 1),?_⟩
  intro X hX T hT hTX
  let L := log X
  let L' := (47/48:ℝ)*L
  let D := (23/24:ℝ)*L
  let S := V3b T
  let β := fun c : V1o => c.val.1.re
  let Q := W*(1+log T)^11 / damp X T
  have hx : 1 < X := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le ((le_max_right _ _).trans hX)
  have hL : 1 ≤ L := (le_log_iff_exp_le (zero_lt_one.trans hx)).mpr ((le_max_right _ _).trans hX)
  have hL0 := zero_lt_one.trans_le hL
  have hT1 : 1 ≤ T := by linarith
  have hd : 0 < damp X T := lt_min zero_lt_one (div_pos (rpow_pos_of_pos (zero_lt_one.trans hx) _) (by linarith))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity [log_nonneg hT1]
  have hL' : 0 < L' := by dsimp only [L']; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hDL : D < L' := by dsimp only [D,L']; linarith
  have hcount (σ : ℝ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) :
      ((S.filter (fun c => σ ≤ β c)).card:ℝ) ≤ Q * exp (D*(1-σ)) := by
    have hh := damp_count C hC hdens hx hT hσ hσ'
    dsimp only [Q,W,D,L,S,β]
    rw [div_mul_eq_mul_div,le_div_iff₀ hd,mul_comm _ (damp X T)]
    exact hh
  have hsum := Sidon.finite_zero_bound_of_density S β (η:=0) hL' (by norm_num) hQ hD hDL
    (fun c _ => c.property.1.1.le) (fun c _ => by simpa [β] using c.property.1.2.1.le) hcount
  have hr : D/L'=b := by dsimp only [D,L',b]; field_simp; ring
  rw [hr] at hsum
  simp only [mul_zero,Nat.floor_zero,Nat.cast_zero,exp_zero,mul_one] at hsum
  have hsum' : (∑ c ∈ S, exp (-L'*(1-β c))) ≤ Q*Z := hsum.trans_eq (by dsimp [Z]; ring)
  have hres : ∀ c ∈ S, X^(β c-1) ≤ ((L^(A+11))⁻¹)*exp (-L'*(1-β c)) := by
    intro c hc
    have hh := hP X ((le_max_left _ _).trans hX) hx T hTX c hc
    rw [rpow_def_of_pos (zero_lt_one.trans hx)]
    have heq : log X*(β c-1) = -(L/48)*(1-β c) + -L'*(1-β c) := by dsimp [L,L'];ring
    rw [heq,exp_add]
    exact mul_le_mul_of_nonneg_right hh (exp_pos _).le
  have hscale : 1+log T ≤ 3*L := by
    have tt := log_le_log (zero_lt_one.trans_le hT1) hTX
    rw [log_pow,Nat.cast_ofNat] at tt
    change log T ≤ 2*L at tt
    linarith
  have hLg := pow_le_pow_left₀ (by linarith [log_nonneg hT1]) hscale 11
  calc
    _ ≤ damp X T * (∑ c ∈ S, (L^(A+11))⁻¹*exp (-L'*(1-β c))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hres) hd.le
    _ = damp X T*(L^(A+11))⁻¹*(∑ c ∈ S, exp (-L'*(1-β c))) := by rw [←mul_sum]; ring
    _ ≤ damp X T*(L^(A+11))⁻¹*(Q*Z) := mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = (W*Z/(L^(A+11)))*(1+log T)^11 := by dsimp only [Q]; field_simp
    _ ≤ (W*Z/(L^(A+11)))*(3*L)^11 := mul_le_mul_of_nonneg_left hLg (by positivity)
    _ = _ := by change _ = W*3^11*Z/L^A; rw [pow_add,mul_pow]; field_simp

end TH8000Zeta

end


-- TH8000ZetaWindow
section

open Finset Filter Real MeasureTheory
open scoped Classical Topology
open Vx V1e V6i V7e

namespace TH8000Zeta

private noncomputable def rank (c : V1o) : ℕ := (⌊|c.val.1.im|⌋₊).log2

private theorem height_band {X : ℝ} (_hx : 4 ≤ X) {c : V1o} (hc : c ∈ V3b X) :
    rank c < (⌊X⌋₊).log2+1 ∧
    |c.val.1.im| ≤ (2:ℝ)^(rank c+1) ∧
    ((2:ℝ)^(rank c+1) = 2 ∨ (2:ℝ)^(rank c+1)/2 ≤ |c.val.1.im|) := by
  let n := ⌊|c.val.1.im|⌋₊
  have hnX : n ≤ ⌊X⌋₊ := Nat.floor_mono ((V5l X c).mp hc)
  have hfloor : (n:ℝ) ≤ |c.val.1.im| := Nat.floor_le (abs_nonneg _)
  have hceil : |c.val.1.im| < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hlow : n < 2^(n.log2+1) := Nat.lt_log2_self
  have hmon : n.log2 ≤ ⌊X⌋₊.log2 := by
    by_cases hn : n=0
    · simp [hn]
    · exact (Nat.le_log2 (by omega : ⌊X⌋₊ ≠ 0)).mpr ((Nat.log2_self_le hn).trans hnX)
  refine ⟨Nat.lt_succ_of_le hmon, ?_, ?_⟩
  · have hs : (n:ℝ)+1 ≤ (2:ℝ)^(rank c+1) := by exact_mod_cast hlow
    exact hceil.le.trans hs
  · by_cases hn : n=0
    · left
      change (2:ℝ)^(n.log2+1)=2
      simp [hn]
    · right
      have hp : (2:ℝ)^(rank c) ≤ (n:ℝ) := by exact_mod_cast (Nat.log2_self_le hn)
      rw [pow_succ]
      linarith

private lemma band_count {X : ℝ} (hx : exp 1 ≤ X) :
    ((⌊X⌋₊.log2+1 : ℕ):ℝ) ≤ 3*log X := by
  have hx1 : 1 < X := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hx0 := zero_lt_one.trans hx1
  have hL : 1 ≤ log X := (le_log_iff_exp_le hx0).mpr hx
  have hn : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by simpa using hx1.le)
  have hpow : (2:ℝ)^(⌊X⌋₊.log2) ≤ X :=
    (show (2:ℝ)^(⌊X⌋₊.log2) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast Nat.log2_self_le (by omega : ⌊X⌋₊ ≠ 0)).trans
      (Nat.floor_le hx0.le)
  have hh := log_le_log (by positivity) hpow
  rw [log_pow] at hh
  have hhalf : (1/2:ℝ) ≤ log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hmul := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α:=ℝ) ⌊X⌋₊.log2)
  push_cast
  linarith

private theorem sum_kernel {X h u : ℝ} (hx : 4 ≤ X) (hxe : exp 1 ≤ X)
    (hu : X/2 ≤ u) (hu' : u ≤ 2*X) (hh : 0 ≤ h) (hh' : h ≤ X)
    (hscale : X^(2/3:ℝ) ≤ 2*h)
    {K : ℝ} (hK : 0 ≤ K)
    (hband : ∀ T : ℝ, 2 ≤ T → T ≤ X^2 →
      damp X T * (∑ c ∈ V3b T, X^(c.val.1.re-1)) ≤ K/(log X)^2) :
    ‖∑ c ∈ V3b X, Ve u h c.val.1‖ ≤ 72*K*h/log X := by
  let J := (⌊X⌋₊).log2+1
  let F := V3b X
  have hx0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have maps : ∀ c ∈ F, rank c ∈ range J := fun c hc => mem_range.mpr (height_band hx hc).1
  have hstr (j) (hj : j ∈ range J) :
      (∑ c ∈ F.filter (fun c => rank c=j), ‖Ve u h c.val.1‖) ≤ 24*h*(K/(log X)^2) := by
    let T := (2:ℝ)^(j+1)
    let S := F.filter (fun c => rank c=j)
    have ht : 2 ≤ T := by
      have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1≤j+1 by omega)
      simpa only [pow_one] using h
    have hn : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by norm_num; linarith)
    have hfloor : (2:ℝ)^⌊X⌋₊.log2 ≤ X :=
      (show (2:ℝ)^⌊X⌋₊.log2 ≤ (⌊X⌋₊:ℝ) by exact_mod_cast Nat.log2_self_le (by omega : ⌊X⌋₊≠0)).trans
        (Nat.floor_le hx0.le)
    have hjle : j ≤ ⌊X⌋₊.log2 := Nat.le_of_lt_succ (mem_range.mp hj)
    have hTmax : T ≤ X^2 := by
      have hk := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjle).trans hfloor
      dsimp only [T]
      rw [pow_succ]
      nlinarith
    have geom (c) (hc : c ∈ S) :
        |c.val.1.im| ≤ T ∧ (T=2 ∨ T/2 ≤ |c.val.1.im|) := by
      obtain ⟨hi,hr⟩ := mem_filter.mp hc
      simpa only [hr] using (height_band hx hi).2
    have hS : S ⊆ V3b T := fun c hc => (V5l T c).mpr (geom c hc).1
    have hd : 0 ≤ damp X T := le_min zero_le_one (by dsimp [T]; positivity)
    have hsub := sum_le_sum_of_subset_of_nonneg (f:=fun c : V1o => X^(c.val.1.re-1)) hS
      (fun c _ _ => rpow_nonneg hx0.le _)
    change (∑ c ∈ S, _) ≤ _
    calc
      _ ≤ ∑ c ∈ S, 24*h*(damp X T*X^(c.val.1.re-1)) := sum_le_sum fun c hc =>
        GoldbachCentralSeven.Kernel.increment_min (by linarith) hu hu' hh hh' hscale ht
          (geom c hc).2 c.property.1.1 c.property.1.2.1.le
      _ = 24*h*(damp X T*∑ c ∈ S, X^(c.val.1.re-1)) := by simp only [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hsub hd).trans (hband T ht hTmax)) (by positivity)
  calc
    _ ≤ ∑ c ∈ F, ‖Ve u h c.val.1‖ := norm_sum_le _ _
    _ = ∑ j ∈ range J, ∑ c ∈ F.filter (fun c => rank c=j), ‖Ve u h c.val.1‖ :=
      (sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑ _j ∈ range J, 24*h*(K/(log X)^2) := sum_le_sum hstr
    _ = (J:ℝ)*(24*h*(K/(log X)^2)) := by simp
    _ ≤ 3*log X*(24*h*(K/(log X)^2)) :=
      mul_le_mul_of_nonneg_right (band_count hxe) (by positivity)
    _ = _ := by field_simp; ring

theorem principal_window_mass :
    ∃ P : ℝ, ∀ X ≥ P, ∀ h : ℕ, (h:ℝ) ≤ X → X^(2/3:ℝ) ≤ 2*h →
      (h:ℝ)/2 ≤ ∑ n ∈ Ioc ⌊X⌋₊ (⌊X⌋₊+h), ArithmeticFunction.vonMangoldt n := by
  obtain ⟨K,hK,P,hband⟩ := damped_band 2
  obtain ⟨D,hD,hfor⟩ := V86.V10s
  have hlogsmall : ∀ᶠ X : ℝ in atTop, log X ≤ (1/(24*D))*X^(1/6:ℝ) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/6)).bound
      (show 0 < 1/(24*D) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with X hh hx
    simpa only [rpow_one,Real.norm_eq_abs,abs_of_nonneg (log_nonneg hx),
      abs_of_nonneg (rpow_nonneg (zero_le_one.trans hx) (1/6:ℝ))] using hh
  apply Filter.eventually_atTop.mp
  filter_upwards [hlogsmall, Filter.eventually_ge_atTop P,Filter.eventually_ge_atTop (exp 1),
    Filter.eventually_ge_atTop (4:ℝ),tendsto_log_atTop.eventually_ge_atTop (288*K)]
      with X hl hP hxe hx hLK h hh hscale
  have hx0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have hr : 0 < sqrt X := sqrt_pos.mpr hx0
  have hs := sq_sqrt hx0.le
  have hr1 : 1 ≤ sqrt X := one_le_sqrt.mpr (by linarith)
  have hr2 : sqrt X ≤ X/2 := by nlinarith [sq_nonneg (sqrt X-2)]
  have hh0 : (0:ℝ) ≤ h := Nat.cast_nonneg _
  let f := fun u : ℝ => ∑ c ∈ V3b X, Ve u (h:ℝ) c.val.1
  have hb : ∀ u ∈ Set.uIoc (X-sqrt X) X, ‖f u‖ ≤ (h:ℝ)/4 := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    apply (sum_kernel hx hxe (by linarith [hu.1]) (by linarith [hu.2]) hh0 hh hscale hK.le (hband X hP)).trans
    apply (div_le_iff₀ hL).mpr
    have := mul_le_mul_of_nonneg_right hLK hh0
    linarith
  have hsm : ‖V3q f (sqrt X) X‖ ≤ (h:ℝ)/4 := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hi' : ‖∫ u in X-sqrt X..X, f u‖ ≤ ((h:ℝ)/4)*sqrt X := by
      simpa only [sub_sub_cancel,abs_of_nonneg hr.le,mul_comm] using hi
    rw [V3q,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left hi' (by positivity)).trans_eq (by field_simp)
  have hformula := hfor X X (sqrt X) X h hx ⟨le_rfl,by linarith⟩ hh hr1 hr2 (by linarith)
  have heq : sqrt X*log X + sqrt X*log X/sqrt X + X^2*log X/(sqrt X*X) =
      (2*sqrt X+1)*log X := by
    field_simp
    nlinarith [hs]
  rw [heq] at hformula
  have hpow : sqrt X * X^(1/6:ℝ) = X^(2/3:ℝ) := by
    rw [sqrt_eq_rpow,←rpow_add hx0]
    norm_num
  have hrem : D*((2*sqrt X+1)*log X) ≤ (h:ℝ)/4 := by
    have hstep := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3*D*sqrt X by positivity)
    calc
      _ ≤ (3*D*sqrt X)*log X := by
        have h := mul_nonneg (mul_nonneg hD.le (sub_nonneg.mpr hr1)) hL.le
        nlinarith only [h]
      _ ≤ _ := hstep
      _ = X^(2/3:ℝ)/8 := by rw [← hpow]; field_simp; norm_num
      _ ≤ _ := by linarith only [hscale]
  have herr : ‖V42 h X‖ ≤ (h:ℝ)/2 := by
    change ‖V42 h X + V3q f (sqrt X) X‖ ≤ _ at hformula
    have h := norm_sub_le (V42 h X + V3q f (sqrt X) X) (V3q f (sqrt X) X)
    rw [add_sub_cancel_right] at h
    linarith only [h,hformula,hsm,hrem]
  have hreal := (Complex.abs_re_le_norm (V42 h X)).trans herr
  simp only [V42,V2h.V9a,OAI.Ostmann.V1n,Complex.sub_re,Complex.re_sum,Complex.ofReal_re,
    Complex.natCast_re] at hreal
  linarith only [(abs_le.mp hreal).1]

theorem principal_square_mass :
    ∃ P : ℕ, ∀ p ≥ P, ∀ h : ℕ, h^3 ≤ p^4 → p^4 < (h+1)^3 →
      (h:ℝ)/2 ≤ ∑ n ∈ Ioc (p^2) (p^2+h), ArithmeticFunction.vonMangoldt n := by
  obtain ⟨P,hP⟩ := principal_window_mass
  refine ⟨max 2 ⌈P⌉₊,?_⟩
  intro p hp h hlo hhi
  have hp2 : 2 ≤ p := (le_max_left _ _).trans hp
  have hp1 : 1 ≤ p := by omega
  have hpow : p ≤ p^2 := by simpa using Nat.pow_le_pow_right hp1 (show 1 ≤ 2 by decide)
  have hlarge : P ≤ ((p^2:ℕ):ℝ) := Nat.ceil_le.mp (((le_max_right _ _).trans hp).trans hpow)
  have hsize : h ≤ p^2 := by
    by_contra! hbad
    have hh := Nat.pow_lt_pow_left hbad (by norm_num : 3 ≠ 0)
    have hcap : p^4 ≤ (p^2)^3 := by rw [←pow_mul]; exact Nat.pow_le_pow_right hp1 (by norm_num)
    omega
  have hn : 1 ≤ h := by
    by_contra! hzero
    have : h=0 := by omega
    subst h
    simp at hhi
    omega
  have h3R : ((p^2:ℕ):ℝ)^2 ≤ ((h:ℝ)+1)^3 := by
    rw [Nat.cast_pow,←pow_mul]
    exact_mod_cast hhi.le
  have hc := Real.rpow_le_rpow (by positivity) h3R (by norm_num : (0:ℝ) ≤ 1/3)
  have hcalc : ∀ x : ℝ, 0 ≤ x → ∀ j : ℕ, (x^j)^(1/3:ℝ)=x^((j:ℝ)/3) := by
    intro x hx j
    rw [← Real.rpow_natCast x j,← Real.rpow_mul hx]
    congr 1
    ring
  rw [hcalc _ (by positivity) 2,hcalc _ (by positivity) 3] at hc
  norm_num at hc
  have hsc : ((p^2:ℕ):ℝ)^(2/3:ℝ) ≤ 2*(h:ℝ) := by
    have h1 : (1:ℝ) ≤ h := by exact_mod_cast hn
    push_cast
    linarith
  simpa only [Nat.floor_natCast] using
    hP ((p^2:ℕ):ℝ) hlarge h (by exact_mod_cast hsize) hsc

end TH8000Zeta

end


-- TH8000UpperPrimeBudget
section

namespace GoldbachCentralSeven.UpperPrimeBudget
open Finset Filter
open GoldbachRoughFifth.AnalyticInput.ErdosStraus.PrimeEstimates.Mertens
noncomputable section

def band (z : ℕ) := (Icc z (z^2)).filter Nat.Prime
def interior (z : ℕ) := (Ioc z (z^2)).filter Nat.Prime

private theorem square_ge {z : ℕ} (hz : 2 ≤ z) : z ≤ z^2 := by nlinarith

private theorem interior_sum (z : ℕ) (hz : 2 ≤ z) (f : ℕ → ℝ) :
    (∑ p ∈ interior z, f p) = (∑ p ∈ primesUpTo (z^2), f p) - ∑ p ∈ primesUpTo z, f p := by
  have hs : primesUpTo z ⊆ primesUpTo (z^2) := fun p hp =>
    mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1,(mem_primesUpTo.mp hp).2.trans (square_ge hz)⟩
  have he : interior z = primesUpTo (z^2) \ primesUpTo z := by
    apply Finset.ext;intro p
    constructor
    · intro hp
      obtain ⟨hi,hp'⟩ := mem_filter.mp hp
      exact mem_sdiff.mpr ⟨mem_primesUpTo.mpr ⟨hp',(mem_Ioc.mp hi).2⟩,
        fun h => (mem_Ioc.mp hi).1.not_ge (mem_primesUpTo.mp h).2⟩
    · intro hp
      obtain ⟨hi,hn⟩ := mem_sdiff.mp hp
      obtain ⟨hp',hup⟩ := mem_primesUpTo.mp hi
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge (fun h => hn (mem_primesUpTo.mpr ⟨hp',h⟩)),hup⟩,hp'⟩
  rw [he,eq_sub_iff_add_eq];exact sum_sdiff hs

private theorem band_sum_endpoint (z : ℕ) (hz : 2 ≤ z) (f : ℕ → ℝ) :
    (∑ p ∈ band z, f p) = (if z.Prime then f z else 0) + ∑ p ∈ interior z, f p := by
  simp only [band,interior,sum_filter]
  rw [Icc_eq_cons_Ioc (square_ge hz),sum_cons]

theorem mertens_band_inputs :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z →
      (∑ p ∈ interior z, 1/(p:ℝ)) ≤ Real.log 2 + C/Real.log z ∧
      Real.log z - C ≤ ∑ p ∈ interior z, Real.log p/(p:ℝ) := by
  obtain ⟨c,hc,hM⟩ := mertensSecond
  obtain ⟨b,hb,hF⟩ := mertensFirst
  refine ⟨2*c+2*b,by positivity,?_⟩
  intro z hz
  have hZ : (2:ℝ) ≤ z := by exact_mod_cast hz
  have hZ2 : (2:ℝ) ≤ (z^2:ℕ) := by exact_mod_cast hz.trans (square_ge hz)
  have hlog := Real.log_pos (by linarith : (1:ℝ) < z)
  have hpow : Real.log ((z^2:ℕ):ℝ) = 2*Real.log z := by rw [Nat.cast_pow,Real.log_pow]; norm_num
  have h1 := abs_le.mp (hM (z:ℝ) hZ)
  have h2 := abs_le.mp (hM ((z^2:ℕ):ℝ) hZ2)
  simp only [Nat.floor_natCast,hpow,Real.log_mul (by norm_num : (2:ℝ)≠0) hlog.ne'] at h1 h2
  have h3 := abs_le.mp (hF (z:ℝ) hZ)
  have h4 := abs_le.mp (hF ((z^2:ℕ):ℝ) hZ2)
  simp only [Nat.floor_natCast,hpow] at h3 h4
  constructor
  · rw [interior_sum z hz]
    change primeReciprocalSum (z^2)-primeReciprocalSum z ≤ _
    have hP := div_le_div_of_nonneg_left hc.le hlog (show Real.log z ≤ 2*Real.log z by linarith)
    have hA : c/Real.log z + c/Real.log z ≤ (2*c+2*b)/Real.log z := by
      rw [← add_div];exact div_le_div_of_nonneg_right (by linarith) hlog.le
    linarith only [h1.1,h2.2,hP,hA]
  · rw [interior_sum z hz]
    linarith only [h3.2,h4.1,hc]

theorem band_bounds (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ z : ℕ in atTop,
      (∑ p ∈ band z, 1/((p:ℝ)-1)) ≤ Real.log 2+5*ε ∧
      1-ε ≤ (∑ p ∈ band z, Real.log p/((p:ℝ)-1))/Real.log z := by
  obtain ⟨C,hC,hM⟩ := mertens_band_inputs
  have hh := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (C/ε)
  have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1/ε+1)
  filter_upwards [hh,hi,eventually_ge_atTop 2] with z hL hZ hz
  have hZ' : (1:ℝ) < z := by exact_mod_cast (by omega : 1<z)
  have hzpos : (0:ℝ) < z := by linarith
  have hlog := Real.log_pos hZ'
  have hc : C ≤ ε*Real.log z := by
    have h := (div_le_iff₀ hε).mp (show C/ε ≤ Real.log z from hL)
    linarith
  have hZr : 1/ε+1 ≤ (z:ℝ) := hZ
  have hOne : 1 ≤ ε*((z:ℝ)-1) := by
    have h := (div_le_iff₀ hε).mp (show 1/ε ≤ (z:ℝ)-1 by linarith)
    linarith
  have hstart : 1/(z:ℝ) ≤ ε := (div_le_iff₀ hzpos).mpr (by nlinarith)
  obtain ⟨hr,hw⟩ := hM z hz
  constructor
  · have hsum : (∑ p ∈ band z, 1/(p:ℝ)) ≤ Real.log 2+2*ε := by
      rw [band_sum_endpoint z hz]
      have hc' := (div_le_iff₀ hlog).mpr hc
      split_ifs <;> linarith
    have hmajor (p : ℕ) (hp : p ∈ band z) : 1/((p:ℝ)-1) ≤ (1+ε)*(1/(p:ℝ)) := by
      have hzp : (z:ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).1
      rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith only [hOne,mul_le_mul_of_nonneg_left hzp hε.le]
    calc
      _ ≤ ∑ p ∈ band z, (1+ε)*(1/(p:ℝ)) := sum_le_sum hmajor
      _ ≤ (1+ε)*(Real.log 2+2*ε) := by rw [← mul_sum];gcongr
      _ ≤ _ := by
        have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
        nlinarith only [mul_le_mul_of_nonneg_left hε1 hε.le,mul_le_mul_of_nonneg_left h2 hε.le]
  · apply (le_div_iff₀ hlog).mpr
    have hsub : interior z ⊆ band z := by
      intro p hp;obtain ⟨hi,hp⟩ := mem_filter.mp hp
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl.le,hu⟩,hp⟩
    have hmono : (∑ p ∈ interior z, Real.log p/(p:ℝ)) ≤
        ∑ p ∈ band z, Real.log p/((p:ℝ)-1) := by
      apply (sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log p/(p:ℝ)) hsub
        (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))).trans
      apply sum_le_sum;intro p hp
      have hp2 := (mem_filter.mp hp).2.two_le
      have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp2
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
        (by linarith : (0:ℝ)<(p:ℝ)-1) (by linarith)
    linarith only [hw,hmono,hc]

theorem limiting_margin : (3/2:ℝ)*Real.log 2 - 1/4 < (3/4:ℝ)*Real.log 3 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<4/3) (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num),
    show (4:ℝ) = 2^2 by norm_num,Real.log_pow] at h
  norm_num at h
  linarith

theorem upper_prime_budget :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ᶠ z : ℕ in atTop,
      (∑ p ∈ band z, (1-Real.log p/(4*Real.log z))/((p:ℝ)-1)) +
      ((1+η)/2)*(∑ p ∈ band (z^2), 1/((p:ℝ)-1)) ≤ (3/4:ℝ)*Real.log 3 - η := by
  let gap := (3/4:ℝ)*Real.log 3 - ((3/2:ℝ)*Real.log 2-1/4)
  have hg : 0 < gap := sub_pos.mpr limiting_margin
  let η := min 1 (gap/32)
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηg : η ≤ gap/32 := min_le_right _ _
  have h := band_bounds η hη hη1
  have hsq := (tendsto_pow_atTop (α := ℕ) (by decide : 2 ≠ 0)).eventually h
  refine ⟨η,hη,hη1,?_⟩
  filter_upwards [h,hsq] with z hlo hhi
  have hid : (∑ p ∈ band z, (1-Real.log p/(4*Real.log z))/((p:ℝ)-1)) =
      (∑ p ∈ band z, 1/((p:ℝ)-1)) - (1/4:ℝ)*((∑ p ∈ band z,Real.log p/((p:ℝ)-1))/Real.log z) := by
    rw [sum_div,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro p _;ring
  rw [hid]
  have hpair := mul_le_mul_of_nonneg_left hhi.1 (by positivity : 0 ≤ (1+η)/2)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  dsimp only [gap] at hηg
  nlinarith only [hlo.1,hlo.2,hpair,mul_le_mul_of_nonneg_left hη1 hη.le,
    mul_le_mul_of_nonneg_left hlog hη.le,hηg,hη]

theorem upper_prime_subsets :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ᶠ z : ℕ in atTop,
      ∀ (S₁ S₂ : Finset ℕ), S₁ ⊆ band z → S₂ ⊆ band (z^2) →
      (∑ p ∈ S₁, (1-Real.log p/(4*Real.log z))/((p:ℝ)-1)) +
      ((1+η)/2)*(∑ p ∈ S₂, 1/((p:ℝ)-1)) ≤ (3/4:ℝ)*Real.log 3 - η := by
  obtain ⟨η,hη,hη1,h⟩ := upper_prime_budget
  refine ⟨η,hη,hη1,?_⟩
  filter_upwards [h,eventually_ge_atTop 2] with z hz h2
  intro S₁ S₂ hS₁ hS₂
  have hlog := Real.log_pos (show (1:ℝ)<z by exact_mod_cast (by omega : 1<z))
  apply le_trans _ hz
  apply add_le_add
  · apply sum_le_sum_of_subset_of_nonneg hS₁
    intro p hp _
    have hpr := (mem_filter.mp hp).2
    have hpp : (2:ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hcmp : (p:ℝ) ≤ (z:ℝ)^2 := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).2
    have hl := Real.log_le_log (by linarith) hcmp
    rw [Real.log_pow] at hl
    norm_num at hl
    apply div_nonneg _ (by linarith)
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).mpr (by linarith)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum_of_subset_of_nonneg hS₂
    intro p hp _
    have hpp : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    exact div_nonneg zero_le_one (by linarith)

end
end GoldbachCentralSeven.UpperPrimeBudget

end


-- TH8000MainBudget
section

namespace GoldbachCentralSeven.Model
open Finset Filter CentralUpperGeometry Real

theorem row_main_budget {K : ℝ} (hK : 2≤K)
    (hcomp : ∀ d w z : ℕ, 2≤w → w≤z →
      V d w ≤ V d z * (log z/log w) * (1+K/log w)) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ ∀ ρ : ℝ, 0<ρ → ∀ᶠ z : ℕ in atTop, ∀ (d : ℕ) (Q : Finset ℕ),
      (∀ q ∈ Q, q.Prime ∧ z≤q ∧ (q:ℝ) ≤ penaltyEnd z) →
      (∑ q ∈ Q, discount z q * V d (radius z q) / ((q:ℝ)-1)) ≤
        (V d z*(1+ρ)) * ((3/4:ℝ)*log 3 - η) := by
  obtain ⟨η,hη,hη1,hsums⟩ := UpperPrimeBudget.upper_prime_subsets
  refine ⟨η,hη,hη1,?_⟩
  intro ρ hρ
  obtain ⟨M,hM⟩ := exists_nat_gt (exp (K/ρ))
  filter_upwards [hsums,upper_band_cost η hη,radius_uniform (max M 2),
    eventually_ge_atTop (2:ℕ)] with z hsum hcost hrad hz
  intro d Q hQ
  let L := Q.filter (fun q => q ≤ z^2)
  let U := Q.filter (fun q => ¬ q ≤ z^2)
  let F := V d z*(1+ρ)
  have hF : 0 ≤ F := mul_nonneg (V_pos ..).le (by linarith)
  have hfge : V d z ≤ F := le_mul_of_one_le_right (V_pos ..).le (by linarith)
  have hsubL : L ⊆ UpperPrimeBudget.band z := by
    intro q hq
    obtain ⟨hmem,hsmall⟩ := mem_filter.mp hq
    obtain ⟨hp,hzq,_⟩ := hQ q hmem
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hzq,hsmall⟩,hp⟩
  have hsubU : U ⊆ UpperPrimeBudget.band (z^2) := by
    intro q hq
    obtain ⟨hmem,hbig⟩ := mem_filter.mp hq
    obtain ⟨hp,_,hy⟩ := hQ q hmem
    have hzR : 1 ≤ (z:ℝ) := by exact_mod_cast (show 1≤z by omega)
    have hle := Real.rpow_le_rpow_of_exponent_le hzR (by norm_num : (320/81:ℝ)≤4)
    have htop : q≤z^4 := by
      have h' := hy.trans hle
      norm_num [penaltyEnd] at h'
      exact_mod_cast h'
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨(lt_of_not_ge hbig).le,?_⟩,hp⟩
    simpa only [← pow_mul] using htop
  let g := fun q : ℕ => discount z q * V d (radius z q) / ((q:ℝ)-1)
  have hl : ∑ q ∈ L, g q ≤ F * ∑ q ∈ L, (1-log q/(4*log z))/((q:ℝ)-1) := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    obtain ⟨hm,hs⟩ := mem_filter.mp hq
    obtain ⟨hp,_,hy⟩ := hQ q hm
    have hp' : 1<(q:ℝ) := by exact_mod_cast hp.one_lt
    have hnn := discount_nonneg hz hp.pos hy
    dsimp only [g]
    rw [small_radius hp.pos hs, ← mul_div_assoc, mul_comm F]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul (discount_linear hz hp.pos) hfge (V_pos ..).le (hnn.trans (discount_linear hz hp.pos))
  have hu : ∑ q ∈ U, g q ≤ F * (((1+η)/2)* ∑ q ∈ U, 1/((q:ℝ)-1)) := by
    rw [← mul_assoc F ((1+η)/2), mul_sum]
    apply sum_le_sum
    intro q hq
    obtain ⟨hm,hs⟩ := mem_filter.mp hq
    obtain ⟨hp,_,hy⟩ := hQ q hm
    let w := radius z q
    have hw : 2 ≤ w := (le_max_right ..).trans (hrad q hp.pos hy)
    have hwM : M ≤ w := (le_max_left ..).trans (hrad q hp.pos hy)
    have hwz : w≤z := min_le_left .. 
    have hwlog := log_pos (by exact_mod_cast (show 1<w by omega) : (1:ℝ)<w)
    have hzlog := log_pos (by exact_mod_cast (show 1<z by omega) : (1:ℝ)<z)
    have hKlog : K/log (w:ℝ) ≤ ρ := by
      rw [div_le_iff₀ hwlog]
      have hh : K/ρ ≤ log (w:ℝ) := by
        rw [← log_exp (K/ρ)]
        exact log_le_log (exp_pos _) (hM.le.trans (by exact_mod_cast hwM))
      linarith only [(div_le_iff₀ hρ).mp hh]
    have hv := hcomp d w z hw hwz
    have hnn := discount_nonneg hz hp.pos hy
    have hp' : 1<(q:ℝ) := by exact_mod_cast hp.one_lt
    have hproduct : discount z q * V d w ≤ F * ((1+η)/2) := calc
      _ ≤ discount z q * (V d z * (log z/log w) * (1+ρ)) := by
        apply mul_le_mul_of_nonneg_left _ hnn
        exact hv.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity [V_pos d z]))
      _ = F * (discount z q*(log z/log w)) := by dsimp [F]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcost q (lt_of_not_ge hs) hy) hF
    calc
      g q ≤ (F*((1+η)/2))/((q:ℝ)-1) := div_le_div_of_nonneg_right hproduct (by linarith)
      _ = _ := by ring
  have hsplit : ∑ q ∈ L,g q + ∑ q ∈ U,g q = ∑ q ∈ Q,g q :=
    sum_filter_add_sum_filter_not .. 
  change (∑ q ∈ Q,g q) ≤ _
  rw [← hsplit]
  exact (add_le_add hl hu).trans (by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hsum L U hsubL hsubU) hF)

end GoldbachCentralSeven.Model

end


-- TH8000Pay
section

namespace GoldbachCentralSeven.Model
open Filter Real Finset GoldbachSevenWeight

theorem margin_choice {η : ℝ} (hη : 0<η) :
    ∃ ε κ : ℝ, 0<ε ∧ 0<κ ∧
      κ ≤ exp eulerMascheroniConstant /2 * log 3 - ε -
        ((exp eulerMascheroniConstant+ε)*(1+ε)*((3/4:ℝ)*log 3-η))/(3/2) := by
  let f (t : ℝ) := exp eulerMascheroniConstant /2 * log 3 - t -
    ((exp eulerMascheroniConstant+t)*(1+t)*((3/4:ℝ)*log 3-η))/(3/2)
  have hzero : f 0 = (2/3:ℝ)*exp eulerMascheroniConstant*η := by dsimp [f]; ring
  have hpos : 0<f 0 := by rw [hzero]; positivity
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨δ,hδ,hh⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x:=0)) (f 0/2) (half_pos hpos)
  have he : dist (δ/2) (0:ℝ)<δ := by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]; linarith
  have hdiff := hh he
  rw [Real.dist_eq] at hdiff
  refine ⟨δ/2,f 0/2,half_pos hδ,half_pos hpos,?_⟩
  change f 0/2 ≤ f (δ/2)
  linarith [(abs_lt.mp hdiff).1]

theorem volume_at_prime_square {c : ℝ} (hc : 0<c)
    (hv : ∀ d z : ℕ, 2≤z → c/log (z:ℝ) ≤ V d z) (d : ℕ) (hd : 0<d) :
    ∀ᶠ p : ℕ in atTop, ∀ H : ℕ, ∀ M : ℝ, (H:ℝ)/2 ≤ M →
      (c/(2*(d.totient:ℝ)))*(H:ℝ) ≤
        ((M / log ((p:ℝ)^2))/d.totient * V d (sieveCut p)) * (log ((p:ℝ)^2))^2 := by
  filter_upwards [CentralUpperGeometry.tendsto_cut.eventually (eventually_ge_atTop 2),
    CentralUpperGeometry.aligned_level_eventually d,eventually_ge_atTop (2:ℕ)]
      with p hz hD hp
  intro H M hM
  have htot : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hx : 1 < (p:ℝ)^2 := by exact_mod_cast (by nlinarith : 1<p^2)
  have hlog := log_pos hx
  have hzlog := log_pos (by exact_mod_cast (show 1<sieveCut p by omega) : (1:ℝ)<sieveCut p)
  have hzp : sieveCut p ≤ p^2 := by
    have ht := hD.2
    have hw : sieveCut p ≤ (sieveCut p)^4 := by
      simpa using Nat.pow_le_pow_right (show 0<sieveCut p by omega) (show 1≤4 by decide)
    have hp2 : p ≤ p^2 := by nlinarith
    omega
  have hlogle : log (sieveCut p:ℝ) ≤ log ((p:ℝ)^2) :=
    log_le_log (by exact_mod_cast (show 0 < sieveCut p by omega)) (by exact_mod_cast hzp)
  have hmain := (div_le_div_of_nonneg_left hc.le hzlog hlogle).trans (hv d _ hz)
  have hmass : 0 ≤ M := (by positivity : (0:ℝ)≤H/2).trans hM
  have hpair := mul_le_mul hM hmain (div_nonneg hc.le hlog.le) hmass
  field_simp [htot.ne',hlog.ne'] at hpair ⊢
  nlinarith only [hpair]

theorem pay_remainders {c κ : ℝ} (hc : 0<c) (hκ : 0<κ) :
    ∀ᶠ p : ℕ in atTop, ∀ H : ℕ, ∀ mass W : ℝ,
      c*(H:ℝ) ≤ mass*(log ((p:ℝ)^2))^2 →
      κ*mass - 2*((H:ℝ)/(log ((p:ℝ)^2))^3) ≤ W →
      (κ*c/2)*(H:ℝ) ≤ W*(log ((p:ℝ)^2))^2 := by
  have hlim := Real.tendsto_log_atTop.comp ((tendsto_pow_atTop (α:=ℝ) (by decide : 2≠0)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hlim.eventually (eventually_ge_atTop (4/(κ*c))),
    eventually_ge_atTop (2:ℕ)] with p hlarge hp
  intro H M W hM hW
  let L := log ((p:ℝ)^2)
  have hL : 0<L := log_pos (by exact_mod_cast (by nlinarith : 1<p^2))
  have hlim' : 4/(κ*c) ≤ L := hlarge
  have hnum : 4 ≤ (κ*c)*L := by linarith only [(div_le_iff₀ (mul_pos hκ hc)).mp hlim']
  change κ*M-2*((H:ℝ)/L^3) ≤ W at hW
  change c*(H:ℝ) ≤ M*L^2 at hM
  change _ ≤ W*L^2
  have hh := mul_le_mul_of_nonneg_right hW (sq_nonneg L)
  have heq : (κ*M-2*((H:ℝ)/L^3))*L^2 = κ*(M*L^2)-2*(H:ℝ)/L := by field_simp <;> ring
  rw [heq] at hh
  have hpayment : 2*(H:ℝ)/L ≤ (κ*c/2)*(H:ℝ) := by
    apply (div_le_iff₀ hL).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hnum (Nat.cast_nonneg H)]
  linarith only [hh,hpayment,mul_le_mul_of_nonneg_left hM hκ.le]

end GoldbachCentralSeven.Model

end


-- TH8000FinalCore
section

namespace GoldbachCentralSeven.Final
open Finset Filter Real Model GoldbachSevenWeight CentralUpperGeometry

theorem actual_seven
    (hPrincipal : ∃ P : ℕ, ∀ p ≥ P, ∀ H : ℕ, H^3 ≤ p^4 → p^4 < (H+1)^3 →
      (H:ℝ)/2 ≤ fullPsiMass (p^2) H) :
    ∀ d : ℕ, 0<d → ∃ c : ℝ, 0<c ∧ ∃ P : ℕ, ∀ p H b : ℕ,
      P≤p → p.Prime → b<d → b.Coprime d → (2*p^2-b).Coprime d →
      H^3≤p^4 → p^4<(H+1)^3 →
      c*(H:ℝ) ≤ ((hits p H d b).card:ℝ)*(log ((p:ℝ)^2))^2 := by
  apply seven_of_weighted_lower
  intro d hd
  obtain ⟨K,hK,_,hcomp⟩ := local_product_control
  obtain ⟨η,hη,_,hbudget⟩ := row_main_budget hK hcomp
  obtain ⟨ε,κ,hε,hκ,hmargin⟩ := margin_choice hη
  obtain ⟨c,hc,hfloor⟩ := volume_floor hK hcomp
  let c₀ := c/(2*(d.totient:ℝ))
  have hφ : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hc₀ : 0<c₀ := by dsimp [c₀]; positivity
  obtain ⟨Pw,hw⟩ := actual_weighted_comparison d 3 hd ε hε
  obtain ⟨Pl,hl⟩ := hPrincipal
  have hevent : ∀ᶠ p : ℕ in atTop, ∀ H b : ℕ, p.Prime → b<d →
      b.Coprime d → (2*p^2-b).Coprime d → H^3≤p^4 → p^4<(H+1)^3 →
      (κ*c₀/2)*(H:ℝ) ≤ (∑ h ∈ roughOffsets p H d b, weight (p^2) (p^2-h)) *
        (log ((p:ℝ)^2))^2 := by
    filter_upwards [eventually_ge_atTop (max 2 (max Pw Pl)),volume_at_prime_square hc hfloor d hd,
      tendsto_cut.eventually (hbudget ε hε),pay_remainders hc₀ hκ]
      with p hp hvol hsum hpay
    intro H b hprime hb hab hab' hlo hhi
    let X := p^2
    let z := sieveCut p
    let Q := penaltyBand X z
    let M := fullPsiMass X H
    let L := log ((p:ℝ)^2)
    let J := M/L
    let B := J / d.totient * V d z
    let E := (H:ℝ)/L^3
    have hp2 : 2≤p := by omega
    have hlog : 0<L := log_pos (by exact_mod_cast (by nlinarith : 1<p^2))
    have hml : (H:ℝ)/2 ≤ M := hl p (by omega) H hlo hhi
    have hM : 0≤M := (by positivity : (0:ℝ)≤H/2).trans hml
    have hJ : 0≤J := div_nonneg hM hlog.le
    have hB : 0≤B := mul_nonneg (div_nonneg hJ hφ.le) (V_pos ..).le
    have hE : 0≤E := div_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog.le _)
    have hQ (q) (hq : q∈Q) : q.Prime ∧ z≤q ∧ (q:ℝ)≤penaltyEnd z := by
      obtain ⟨hi,hq',hy⟩ := mem_filter.mp hq
      exact ⟨hq',(mem_Icc.mp hi).1,hy.le.trans (level_alignment (by omega : 0<p)).2⟩
    have hmain := hsum d Q hQ
    have hw' := hw p (by omega) hprime H b hb hab hab' hlo hhi
    change (fullPsiMass (p^2) H / log ((p^2:ℕ):ℝ) / d.totient) * V d z *
        (exp eulerMascheroniConstant / 2 * log 3 - ε) - (H:ℝ)/(log ((p^2:ℕ):ℝ))^3 -
        ((fullPsiMass (p^2) H / log ((p^2:ℕ):ℝ) / d.totient) * (exp eulerMascheroniConstant+ε) *
          (∑ q ∈ Q, discount z q * V d (radius z q) / ((q:ℝ)-1)) +
          (H:ℝ)/(log ((p^2:ℕ):ℝ))^3)/(3/2) ≤ _ at hw'
    simp only [Nat.cast_pow] at hw'
    change B*(exp eulerMascheroniConstant / 2 * log 3 - ε) - E -
        ((J/d.totient)*(exp eulerMascheroniConstant+ε) *
          (∑ q ∈ Q, discount z q * V d (radius z q) / ((q:ℝ)-1)) + E)/(3/2) ≤ _ at hw'
    apply hpay H B _
    · exact hvol H M hml
    · have hweight := mul_le_mul_of_nonneg_left hmain
        (show 0≤(J/d.totient)*(exp eulerMascheroniConstant+ε) by positivity)
      have hkB := mul_le_mul_of_nonneg_left hmargin hB
      dsimp only [B] at hw' hkB ⊢
      linarith only [hw',hweight,hkB,hE]
  obtain ⟨P,hP⟩ := eventually_atTop.mp hevent
  exact ⟨κ*c₀/2,by positivity,P,fun p H b hp => hP p hp H b⟩

end GoldbachCentralSeven.Final

end


-- TH8000Final
section

theorem Conjectures.Goldbach.CentralPrimeAlmostPrimeSeven :
    ∀ d : ℕ, 0 < d → ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p H b : ℕ,
      p₀ ≤ p → p.Prime → b < d → b.Coprime d → (2*p^2-b).Coprime d →
      H^3 ≤ p^4 → p^4 < (H+1)^3 →
      let hits := (Finset.Icc 1 H).filter (fun h => (p^2+h)%d=b ∧ (p^2+h).Prime ∧
        (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7)
      c * (H : ℝ) ≤ (hits.card : ℝ) * (Real.log ((p : ℝ)^2))^2 :=
  GoldbachCentralSeven.Final.actual_seven TH8000Zeta.principal_square_mass

end
