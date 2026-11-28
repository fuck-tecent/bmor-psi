import Mathlib
import Conjectures.Goldbach.PolynomialFourierTransference

/-! Asymmetric restriction exponents for polynomial binary transference.
Adapted from Conjectures.Goldbach.PolynomialFourierTransference (accepted lemma
L-goldbach-polynomial-fourier-transference): the symmetric moment bound for the
product spectrum is replaced by a mixed Holder estimate coming from weighted
AM-GM, so the two ends may carry different restriction exponents, and one of
them may exceed four. -/

namespace Conjectures.Goldbach.TransferenceMixedRestriction_aux
open Finset PolynomialTransfer
open scoped ComplexConjugate BigOperators
noncomputable section

theorem mixedMoment {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hα : r/p + r/q = 1)
    {A B : ℝ} (hA : ∑ i, a i^p ≤ A) (hB : ∑ i, b i^q ≤ B) :
    ∑ i, (a i*b i)^r ≤ (r/p)*A + (r/q)*B := by
  have w1 : 0 ≤ r/p := div_nonneg hr.le hp.le
  have w2 : 0 ≤ r/q := div_nonneg hr.le hq.le
  have pt (i : ι) : (a i*b i)^r ≤ (r/p)*(a i)^p + (r/q)*(b i)^q := by
    rw [Real.mul_rpow (ha i) (hb i)]
    have e1 : ((a i)^p)^(r/p) = (a i)^r := by
      rw [← Real.rpow_mul (ha i), mul_div_cancel₀ r hp.ne']
    have e2 : ((b i)^q)^(r/q) = (b i)^r := by
      rw [← Real.rpow_mul (hb i), mul_div_cancel₀ r hq.ne']
    calc
      _ = ((a i)^p)^(r/p) * ((b i)^q)^(r/q) := by rw [e1, e2]
      _ ≤ _ := Real.geom_mean_le_arith_mean2_weighted w1 w2
        (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _) hα
  calc
    _ ≤ ∑ i, ((r/p)*(a i)^p + (r/q)*(b i)^q) := sum_le_sum fun i _ => pt i
    _ = (r/p)*(∑ i, a i^p) + (r/q)*(∑ i, b i^q) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hA w1) (mul_le_mul_of_nonneg_left hB w2)
end
end Conjectures.Goldbach.TransferenceMixedRestriction_aux

namespace Conjectures.Goldbach.TransferenceMixedRestriction_aux
open Finset PolynomialTransfer
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]
set_option maxHeartbeats 2000000 in
theorem mainBound {p q M : ℝ} (p2 : 2<p) (q2 : 2<q) (hpq : 1/2 < 1/p+1/q) (m1 : 1 ≤ M) :
    ∃ c K : ℝ, 0<c ∧ 0<K ∧ ∀ δ η : ℝ, 0<δ → δ ≤ 1 → 0<η → η ≤ 1 →
    ∀ (N : ℕ) [NeZero N] (f g u v : G N → ℝ),
    (∀ x,0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ E f+E g →
    (∑ r, ‖F f r‖^p) ≤ M^p → (∑ r, ‖F g r‖^q) ≤ M^q →
    (∀ r, ‖F (fun x=>u x-1) r‖ ≤ c*(δ*η)^K ∧ ‖F (fun x=>v x-1) r‖ ≤ c*(δ*η)^K) →
    ((univ.filter (fun n=> conv f g n < δ^3/1000)).card:ℝ) ≤ η*N := by
  classical
  let D := 10+M^p+M^q
  have hpp : 0 < p := by linarith
  have hqq : 0 < q := by linarith
  have mp : 0 ≤ M^p := Real.rpow_nonneg (by linarith) _
  have mq : 0 ≤ M^q := Real.rpow_nonneg (by linarith) _
  have d10 : 10 ≤ D := by dsimp [D]; linarith
  have dpos : 0<D := by linarith
  have hsum : 0 < 1/p+1/q := add_pos (div_pos one_pos hpp) (div_pos one_pos hqq)
  let rr := 1/(1/p+1/q)
  have rpos : 0 < rr := by dsimp [rr]; positivity
  have rlt : rr < 2 := by dsimp [rr]; rw [div_lt_iff₀ hsum]; linarith
  have rlt2 : 0 < 2-rr := by linarith
  have halpha : rr/p + rr/q = 1 := by
    have e : rr * (1/p+1/q) = 1 := by dsimp [rr]; field_simp
    calc rr/p + rr/q = rr*(1/p+1/q) := by ring
      _ = 1 := e
  obtain ⟨k,kk⟩ := exists_nat_ge (4/(2-rr))
  have gain : 4 ≤ (k:ℝ)*(2-rr) := (div_le_iff₀ rlt2).mp kk
  let K := 4*k+4
  let a : ℝ := 1/(100*D)
  have ap : 0<a := by dsimp [a]; positivity
  refine ⟨a^K,(K:ℝ),pow_pos ap _,by dsimp [K]; positivity,?_⟩
  intro δ η dp d1 ep e1 n inst f g u v dom size ff fg dec
  let s := a*(δ*η)
  let t := s^k
  let ε := s^K
  have sp : 0<s := mul_pos ap (mul_pos dp ep)
  have ds : 100*D*s=δ*η := by dsimp [s,a]; field_simp
  have dsle : 100*D*s ≤ δ := by rw [ds]; exact mul_le_of_le_one_right dp.le e1
  have sη : s ≤ η := by nlinarith [mul_le_of_le_one_left ep.le d1,mul_nonneg (by linarith : 0 ≤ 100*D-1) sp.le]
  have s1 : s ≤ 1 := sη.trans e1
  have tp : 0<t := pow_pos sp k
  have t1 : t ≤ 1 := pow_le_one₀ sp.le s1
  have ee : ε=t^4*s^4 := by simp only [ε,K,t,pow_add,pow_mul]; ring_nf
  have εpos : 0 ≤ ε := (pow_pos sp _).le
  have es : ε ≤ s^2 := by
    rw [ee]; calc
      _ ≤ 1*s^4 := mul_le_mul_of_nonneg_right (pow_le_one₀ tp.le t1) (by positivity)
      _ ≤ _ := by rw [one_mul]; exact pow_le_pow_of_le_one sp.le s1 (by omega)
  have ε1 : ε ≤ 1 := es.trans (pow_le_one₀ sp.le s1)
  have eh : a^K*(δ*η)^(K:ℝ)=ε := by rw [Real.rpow_natCast,←mul_pow]
  simp only [eh] at dec
  have gm : E g ≤ 2 := by
    have h := (dec 0).2
    rw [Fzero,Complex.norm_real,Real.norm_eq_abs,Esub,Econst] at h
    have vv := (abs_le.mp h).2
    have gv := Emono (fun x=>(dom x).2.2.2)
    linarith
  by_contra! too
  obtain ⟨b,bn,mass,b2,low⟩ := badWeights f g sp ((show s^2 ≤ s by nlinarith [mul_nonneg sp.le (sub_nonneg.mpr s1)]).trans sη) too
  have hm := mixedMoment (fun r=>‖F f r‖) (fun r=>‖F g r‖) (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
    hpp hqq rpos halpha ff fg
  have w1 : rr/p ≤ 1 := by linarith [div_nonneg rpos.le hqq.le]
  have w2 : rr/q ≤ 1 := by linarith [div_nonneg rpos.le hpp.le]
  have hmD : ∑ r, (‖F f r‖*‖F g r‖)^rr ≤ D := by
    refine hm.trans ?_
    have l1 : (rr/p)*M^p ≤ M^p := mul_le_of_le_one_left mp w1
    have l2 : (rr/q)*M^q ≤ M^q := mul_le_of_le_one_left mq w2
    dsimp [D]; linarith
  obtain ⟨S,h0,lone,tail⟩ := spectrumBudgets b f g bn mass (fun x=>(dom x).2.2.1) gm
    (q:=rr) (D:=D) rpos rlt (by dsimp [D]; linarith) sp s1 gain hmD b2
  have cr := corrError b v mass sp (fun r=>(dec r).2) εpos es b2
  have bar := corrBarrier b g v mass bn (fun x=>(dom x).2.2) sp.le cr
  have cut := truncated b f g u S h0 (fun x=>⟨(dom x).1,(dom x).2.1⟩) (fun r=>(dec r).1) lone εpos tail
  have cost : ε*(3+2*D/t^2)^2 ≤ δ/10 := by
    have id : ε*(3+2*D/t^2)^2=(s^2*(3*t^2+2*D))^2 := by rw [ee]; field_simp <;> ring
    rw [id]
    have l : s^2*(3*t^2+2*D) ≤ s*(5*D) := by
      apply mul_le_mul _ _ (by positivity) sp.le
      · nlinarith [mul_nonneg sp.le (sub_nonneg.mpr s1)]
      · nlinarith [show t^2 ≤ 1 from pow_le_one₀ tp.le t1]
    have l' : s^2*(3*t^2+2*D) ≤ δ/10 := by linarith
    have nn : 0 ≤ s^2*(3*t^2+2*D) := by positivity
    nlinarith [mul_nonneg nn (show 0 ≤ 1-s^2*(3*t^2+2*D) by linarith)]
  change E f ≤ _ + ε*(3+2*D/t^2)^2+2*(_+D*s) at cut
  have sδ : s ≤ δ/100 := by nlinarith [mul_nonneg (show 0 ≤ D-1 by linarith) sp.le]
  have cube : δ^3 ≤ δ := by nlinarith [mul_nonneg (show 0 ≤ δ*(1+δ) by positivity) (sub_nonneg.mpr d1)]
  nlinarith [mul_nonneg sp.le (sub_nonneg.mpr s1)]
end
end Conjectures.Goldbach.TransferenceMixedRestriction_aux

theorem Conjectures.Goldbach.TransferenceMixedRestriction :
by
  classical
  exact ∀ p q M : ℝ, 2 < p → 2 < q → 1/2 < 1/p+1/q → 1 ≤ M → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ δ η : ℝ, 0 < δ → δ ≤ 1 → 0 < η → η ≤ 1 →
    ∀ (N : ℕ) [NeZero N], ∀ f g u v : ZMod N → ℝ,
    let avg := fun h : ZMod N → ℝ => (∑ x, h x)/(N : ℝ)
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ avg f + avg g →
    (∑ r : ZMod N, ‖ft f r‖^p) ≤ M^p → (∑ r : ZMod N, ‖ft g r‖^q) ≤ M^q →
    (∀ r, ‖ft (fun x => u x-1) r‖ ≤ c*(δ*η)^K ∧ ‖ft (fun x => v x-1) r‖ ≤ c*(δ*η)^K) →
    ((Finset.univ.filter (fun n : ZMod N => avg (fun x => f x*g (n-x)) < δ^3/1000)).card : ℝ) ≤ η*(N : ℝ) := by
  classical
  intro p q M hp hq hpq hM
  obtain ⟨c,K,hc,hK,h⟩ := Conjectures.Goldbach.TransferenceMixedRestriction_aux.mainBound hp hq hpq hM
  refine ⟨c,K,hc,hK,?_⟩
  intro δ η hd hD he hE N inst f g u v
  dsimp only
  simpa only [PolynomialTransfer.expForm,PolynomialTransfer.conv,PolynomialTransfer.E] using
    h δ η hd hD he hE N f g u v
