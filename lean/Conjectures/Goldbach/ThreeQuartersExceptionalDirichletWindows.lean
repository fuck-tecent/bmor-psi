import Mathlib

/-!
# Exceptional Dirichlet windows at the three-quarters threshold

A mesh cell of length 1/n meets at most seven square-root Dirichlet windows:
relative to the largest denominator, the integral determinants lie between -3
and 3 and distinguish all reduced pairs. Arbitrary samples in the mesh cells
are controlled by the total variation of the squared Fourier sum.

The continuous Parseval helper below reuses Clrs17's accepted proof from
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/138
at commit 5ab2bcbb94ec2a8224686cc2cf35f1736f882a64. The namespace and
helper name are local to this file. The fixed-centre large-sieve roadmap
is https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/451.
-/

section
open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace GoldbachMovingWindows

private theorem continuous_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

end GoldbachMovingWindows
end

section
open Set Finset MeasureTheory Filter intervalIntegral
noncomputable section
namespace GoldbachMovingWindows

private theorem variation_on_cell {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {l r x y : ℝ} (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    F x ≤ F y + ∫ u in l..r, |D u| := by
  have step {a b : ℝ} (ha : l≤a) (hab : a≤b) (hb : b≤r) :
      |F b-F a| ≤ ∫ u in l..r, |D u| := by
    rw [← integral_eq_sub_of_hasDerivAt (fun t _ => dF t) (cD.intervalIntegrable ..)]
    exact (abs_integral_le_integral_abs hab).trans (integral_mono_interval ha hab hb
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (cD.abs.intervalIntegrable ..))
  rcases le_total y x with h|h
  · linarith [(le_abs_self (F x-F y)).trans (step hy.1 h hx.2)]
  · linarith [(neg_le_abs (F y-F x)).trans (step hx.1 h hy.2)]

private theorem scaled_cell {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {l r x : ℝ} (hx : x ∈ Icc l r) :
    (r-l)*F x ≤ (∫ u in l..r, F u) + (r-l)*(∫ u in l..r, |D u|) := by
  let V := ∫ u in l..r, |D u|
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t => (dF t).continuousAt)
  have h := integral_mono_on (μ:=volume) (hx.1.trans hx.2) (f:=fun _ : ℝ => F x) (g:=fun y => F y+V)
    (continuous_const.intervalIntegrable ..) ((hF.add continuous_const).intervalIntegrable ..)
    (fun _ hy => variation_on_cell dF cD hx hy)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add (hF.intervalIntegrable ..) (continuous_const.intervalIntegrable ..),intervalIntegral.integral_const] at h
  exact h

/-- Sample anywhere in each of the n equal closed cells; the variation budget
is charged just once across the whole interval. -/
theorem sample_mesh {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {n : ℕ} (hn : 0<n) (t : ℕ→ℝ)
    (h : ∀ j<n, t j ∈ Icc ((j:ℝ)/n) (((j:ℝ)+1)/n)) :
    (∑ j ∈ range n,F (t j)) ≤ (n:ℝ)*(∫ x in (0:ℝ)..1,F x) + ∫ x in (0:ℝ)..1, |D x| := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let b := fun j : ℕ => (j:ℝ)/n
  have width (j : ℕ) : b (j+1)-b j = 1/(n:ℝ) := by dsimp [b];push_cast;ring
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t => (dF t).continuousAt)
  have cell (j : ℕ) (hj : j∈range n) :
      F (t j) ≤ (n:ℝ)*(∫ x in (b j)..(b (j+1)), F x) + ∫ x in (b j)..(b (j+1)), |D x| := by
    have mem : t j ∈ Icc (b j) (b (j+1)) := by simpa [b] using h j (mem_range.mp hj)
    have z := scaled_cell dF cD mem
    rw [width] at z
    have zz := mul_le_mul_of_nonneg_left z hn0.le
    field_simp at zz
    linarith
  calc
    _ ≤ ∑ j ∈ range n, ((n:ℝ)*(∫ x in (b j)..(b (j+1)), F x) + ∫ x in (b j)..(b (j+1)), |D x|) :=
      sum_le_sum cell
    _ = _ := by
      rw [sum_add_distrib,←mul_sum,sum_integral_adjacent_intervals (fun _ _ => hF.intervalIntegrable ..),
        sum_integral_adjacent_intervals (fun _ _ => cD.abs.intervalIntegrable ..)]
      simp [b,hn0.ne']

end GoldbachMovingWindows
end
end

section
open Finset Set
noncomputable section
namespace GoldbachMovingWindows

private def det (p v : ℕ × ℕ) : ℤ := (p.2:ℤ)*v.1 - (v.2:ℤ)*p.1

private theorem det_injective {r b : ℕ} (hr : 0<r) (hb : b.Coprime r)
    {p u : ℕ×ℕ} (h1 : 0<p.1) (h2 : p.1≤r) (h3 : 0<u.1) (h4 : u.1≤r)
    (h : det p (r,b) = det u (r,b)) : p=u := by
  classical
  let : NeZero r := ⟨hr.ne'⟩
  have hz := congrArg (fun z : ℤ => (z : ZMod r)) h
  simp [det,Int.cast_sub,Int.cast_mul] at hz
  have hu := (ZMod.isUnit_iff_coprime b r).mpr hb
  have eq : (p.1 : ZMod r) = (u.1 : ZMod r) := hu.mul_left_cancel hz
  have pre : ((p.1-1:ℕ):ZMod r) = ((u.1-1:ℕ):ZMod r) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),eq]
  have hv := congrArg ZMod.val pre
  simp only [ZMod.val_natCast_of_lt (by omega : p.1-1<r),ZMod.val_natCast_of_lt (by omega : u.1-1<r)] at hv
  have eqd : p.1=u.1 := by omega
  have hmul : (p.2:ℤ)*r=(u.2:ℤ)*r := by
    dsimp [det] at h
    rw [eqd] at h
    linarith
  exact Prod.ext eqd (by exact_mod_cast (mul_right_cancel₀ (show (r:ℤ)≠0 by exact_mod_cast hr.ne') hmul))

private theorem det_bound {p v : ℕ×ℕ} {S x y : ℝ} (hS : 0<S) (hp : 0<p.1) (hv : 0<v.1)
    (hpS : (p.1:ℝ)≤S) (hvS : (v.1:ℝ)≤S)
    (hx : |x-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*S)) (hy : |y-(v.2:ℝ)/v.1| ≤ 1/((v.1:ℝ)*S))
    (hxy : |x-y| ≤ 1/S^2) : |det p v| ≤ 3 := by
  have hP : 0<(p.1:ℝ) := by exact_mod_cast hp
  have hV : 0<(v.1:ℝ) := by exact_mod_cast hv
  have raw : ((det p v : ℤ):ℝ) = ((p.2/p.1:ℝ)-x+(x-y)+(y-v.2/v.1))*(p.1*v.1) := by
    simp only [det,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    field_simp
    ring
  have htriangle : |((det p v : ℤ):ℝ)| ≤
      (1/((p.1:ℝ)*S)+1/S^2+1/((v.1:ℝ)*S))*(p.1*v.1) := by
    rw [raw,abs_mul,abs_of_pos (mul_pos hP hV)]
    apply mul_le_mul_of_nonneg_right _ (mul_pos hP hV).le
    apply (abs_add_le ..).trans
    apply add_le_add _ hy
    exact (abs_add_le ..).trans (add_le_add (by rwa [abs_sub_comm]) hxy)
  have e : (1/((p.1:ℝ)*S)+1/S^2+1/((v.1:ℝ)*S))*(p.1*v.1) =
      v.1/S + (p.1:ℝ)*v.1/S^2 + p.1/S := by field_simp
  rw [e] at htriangle
  have hA := (div_le_one hS).mpr hvS
  have hB := (div_le_one hS).mpr hpS
  have hC : (p.1:ℝ)*v.1/S^2 ≤ 1 := (div_le_one (sq_pos_of_pos hS)).mpr
    (by simpa [sq] using mul_le_mul hpS hvS hV.le hS.le)
  exact_mod_cast (show |((det p v : ℤ):ℝ)|≤3 by linarith)

/-- At most seven distinct reduced fractions can have their square-root
Dirichlet windows touch the same cell of length 1/S². -/
theorem at_most_seven (A : Finset (ℕ×ℕ)) (S l : ℝ) (hS : 0<S)
    (good : ∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤S ∧ p.2.Coprime p.1 ∧
      ∃ x ∈ Set.Icc l (l+1/S^2), |x-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*S)) : A.card≤7 := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨v,hv,hm⟩ := A.exists_max_image Prod.fst hA
    obtain ⟨hv0,hvS,hc,y,hy,hyv⟩ := good v hv
    have inj : Set.InjOn (fun p => det p v) A := by
      intro p hp u hu h
      exact det_injective hv0 hc (good p hp).1 (hm p hp) (good u hu).1 (hm u hu) h
    have sub : A.image (fun p => det p v) ⊆ Finset.Icc (-3:ℤ) 3 := by
      intro k hk
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
      obtain ⟨hp0,hpS,_,x,hx,hxp⟩ := good p hp
      have hxy : |x-y|≤1/S^2 := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
      exact mem_Icc.mpr (abs_le.mp (det_bound hS hp0 hv0 hpS hvS hxp hyv hxy))
    simpa [card_image_of_injOn inj] using Finset.card_le_card sub
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

end GoldbachMovingWindows
end
end

section
open Set Finset MeasureTheory intervalIntegral Complex
noncomputable section
namespace GoldbachMovingWindows

private def c : ℂ := (2*Real.pi:ℝ)*I
def wave (k : ℕ) (t : ℝ) : ℂ := Complex.exp (c * k * (t : ℂ))
def series (n : ℕ) (w : ℕ→ℝ) (t : ℝ) : ℂ := ∑ k ∈ range (n+1), (w k : ℂ)*wave k t

theorem wave_eq (k : ℕ) (t : ℝ) :
    wave k t = Complex.exp ((((2*Real.pi*((k:ℝ)*t):ℝ):ℂ))*I) := by
  unfold wave c
  apply congrArg Complex.exp
  push_cast
  ring

theorem energy (n : ℕ) (w : ℕ→ℝ) :
    (∫ t in (0:ℝ)..1, ‖series n w t‖^2) = ∑ k ∈ range (n+1), (w k)^2 := by
  simpa only [series,wave_eq] using continuous_parseval n w

private theorem wave_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (wave k) (wave k t * (c*k)) t := by
  let C := c*(k:ℂ)
  have hd := (Complex.hasDerivAt_exp (C*(t:ℂ))).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).const_mul C)
  change HasDerivAt (fun x : ℝ => Complex.exp (C*(x:ℂ))) (Complex.exp (C*(t:ℂ))*C) t
  simpa [C] using! hd.comp_ofReal

theorem series_deriv (n : ℕ) (w : ℕ→ℝ) (t : ℝ) :
    HasDerivAt (series n w) (c * series n (fun k => k*w k) t) t := by
  have h := HasDerivAt.fun_sum (u:=range (n+1)) (fun k _ => (wave_deriv k t).const_mul (w k:ℂ))
  apply h.congr_deriv
  unfold series
  rw [Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem series_cont (n : ℕ) (w : ℕ→ℝ) : Continuous (series n w) :=
  continuous_iff_continuousAt.mpr (fun t => (series_deriv n w t).continuousAt)

private theorem energy_deriv_abs (n : ℕ) (w : ℕ→ℝ) (hn : 0<n) :
    (∫ t in (0:ℝ)..1, |2 * inner ℝ (series n w t) (c*series n (fun k => k*w k) t)|) ≤
      (4*Real.pi)*(n:ℝ)*(∑ k ∈ range (n+1),(w k)^2) := by
  let F := series n w
  let G := series n (fun k => k*w k)
  have cF : Continuous F := series_cont ..
  have cG : Continuous G := series_cont ..
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hc : ‖c‖ = 2*Real.pi := by simp [c]
  have major (t : ℝ) : |2 * inner ℝ (F t) (c*G t)| ≤
      (2*Real.pi)*((n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hv := abs_real_inner_le_norm (F t) (c*G t)
    rw [norm_mul,hc] at hv
    have key : 2*‖F t‖*‖G t‖ ≤ (n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2 := by
      apply (mul_le_mul_iff_right₀ hn0).mp
      field_simp
      nlinarith [sq_nonneg ((n:ℝ)*‖F t‖-‖G t‖)]
    nlinarith only [hv,mul_le_mul_of_nonneg_left key (show (0:ℝ)≤Real.pi by positivity)]
  have ci : Continuous (fun t => |2 * inner ℝ (F t) (c*G t)|) := by fun_prop
  have cj : Continuous (fun t => (2*Real.pi)*((n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2)) := by fun_prop
  have ii := intervalIntegral.integral_mono (μ:=volume) (by norm_num : (0:ℝ)≤1)
    (ci.intervalIntegrable ..) (cj.intervalIntegrable ..) major
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (by exact (continuous_const.mul (cF.norm.pow 2)).intervalIntegrable ..)
    (by exact (continuous_const.mul (cG.norm.pow 2)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at ii
  dsimp only [F,G] at ii
  rw [energy,energy] at ii
  have edge : (∑ k ∈ range (n+1), ((k:ℝ)*w k)^2) ≤ (n:ℝ)^2 * ∑ k ∈ range (n+1),(w k)^2 := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast (show k≤n by have := mem_range.mp hk;omega)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hk' 2) (sq_nonneg _)
  apply ii.trans
  have e := mul_le_mul_of_nonneg_left edge (show 0≤1/(n:ℝ) by positivity)
  have simpN : 1/(n:ℝ)*((n:ℝ)^2*(∑ k ∈ range (n+1),(w k)^2)) = n*(∑ k ∈ range (n+1),(w k)^2) := by field_simp
  rw [simpN] at e
  nlinarith only [mul_le_mul_of_nonneg_left e Real.pi_pos.le]

/-- A frequency polynomial may be sampled at an arbitrary point in every mesh
cell. The sample locations may depend on the coefficients. -/
theorem sample_series {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (t : ℕ→ℝ)
    (h : ∀ j<n,t j ∈ Icc ((j:ℝ)/n) (((j:ℝ)+1)/n)) :
    (∑ j ∈ range n, ‖series n w (t j)‖^2) ≤
      (1+4*Real.pi)*(n:ℝ)*(∑ k ∈ range (n+1),(w k)^2) := by
  have cF := series_cont n w
  have cG := series_cont n (fun k => k*w k)
  have ht := sample_mesh (fun x => (series_deriv n w x).norm_sq)
    (by fun_prop) hn t h
  rw [energy] at ht
  linarith only [ht,energy_deriv_abs n w hn]

end GoldbachMovingWindows
end
end

section
open Set Finset Complex
noncomputable section
namespace GoldbachMovingWindows
private def cell (n : ℕ) (t : ℝ) := min ⌊(n:ℝ)*t⌋₊ (n-1)

private theorem cell_mem {n : ℕ} (hn : 0<n) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    cell n t < n ∧ t ∈ Set.Icc ((cell n t:ℝ)/n) (((cell n t:ℝ)+1)/n) := by
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have h0 := mul_nonneg hN.le ht.1
  have upper := Nat.lt_floor_add_one ((n:ℝ)*t)
  have lower := Nat.floor_le h0
  have clamp : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  constructor
  · exact (min_le_right _ _).trans_lt (by omega)
  · rw [Set.mem_Icc,div_le_iff₀ hN,le_div_iff₀ hN]
    by_cases h : ⌊(n:ℝ)*t⌋₊ ≤ n-1
    · rw [cell,min_eq_left h]
      constructor <;> linarith
    · rw [cell,min_eq_right (by omega : n-1≤⌊(n:ℝ)*t⌋₊),clamp]
      have hv : n≤⌊(n:ℝ)*t⌋₊ := by omega
      have hvR : (n:ℝ)≤⌊(n:ℝ)*t⌋₊ := by exact_mod_cast hv
      have ht1 := mul_le_mul_of_nonneg_left ht.2 hN.le
      constructor <;> linarith

/-- A maximal large sieve over the square-root Dirichlet windows. Each sample
may be chosen independently after seeing the coefficients. -/
theorem moving_large_sieve {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (A : Finset (ℕ×ℕ)) (t : ℕ×ℕ → ℝ)
    (good : ∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
      t p ∈ Set.Icc (0:ℝ) 1 ∧ |t p-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n)) :
    (∑ p ∈ A, ‖series n w (t p)‖^2) ≤ 7*(1+4*Real.pi)*(n:ℝ)*∑ k ∈ range (n+1), (w k)^2 := by
  classical
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hS := Real.sqrt_pos.mpr hN
  let bucket (j : ℕ) := A.filter (fun p => cell n (t p)=j)
  have bucketMem (j : ℕ) (p : ℕ×ℕ) (hp : p ∈ bucket j) :
      t p ∈ Set.Icc ((j:ℝ)/n) (((j:ℝ)+1)/n) := by
    obtain ⟨ha,he⟩ := mem_filter.mp hp
    simpa only [←he] using (cell_mem hn (good p ha).2.2.2.1).2
  have few (j : ℕ) : (bucket j).card ≤ 7 := by
    apply at_most_seven (bucket j) (Real.sqrt n) ((j:ℝ)/n) hS
    intro p hp
    have ha := (mem_filter.mp hp).1
    obtain ⟨hp0,hpS,hcop,_⟩ := good p ha
    refine ⟨hp0,hpS,hcop,t p,?_,(good p ha).2.2.2.2⟩
    simpa only [Real.sq_sqrt hN.le,add_div] using bucketMem j p hp

  let v := fun p : ℕ×ℕ => ‖series n w (t p)‖^2
  let pick (j : ℕ) (h : (bucket j).Nonempty) := ((bucket j).exists_max_image v h).choose
  have best (j : ℕ) (h : (bucket j).Nonempty) :
      pick j h ∈ bucket j ∧ ∀ p ∈ bucket j, v p ≤ v (pick j h) :=
    ((bucket j).exists_max_image v h).choose_spec
  let sample (j : ℕ) := if h : (bucket j).Nonempty then t (pick j h) else (j:ℝ)/n
  have samples (j : ℕ) (_ : j<n) : sample j ∈ Set.Icc ((j:ℝ)/n) (((j:ℝ)+1)/n) := by
    by_cases h : (bucket j).Nonempty
    · simpa only [sample,dite_eq_left h] using bucketMem j (pick j h) (best j h).1
    · simp only [sample,dite_eq_right h,Set.mem_Icc,le_refl,true_and]
      exact div_le_div_of_nonneg_right (by linarith) hN.le
  have charge (j : ℕ) : (∑ p ∈ bucket j,v p) ≤ 7*‖series n w (sample j)‖^2 := by
    by_cases h : (bucket j).Nonempty
    · have h7 : ((bucket j).card:ℝ)≤7 := by exact_mod_cast few j
      rw [show sample j = t (pick j h) by simp [sample,h]]
      exact (Finset.sum_le_sum (best j h).2).trans (by
        simpa only [sum_const,nsmul_eq_mul] using
          (show ((bucket j).card : ℝ)*v (pick j h) ≤ 7*v (pick j h) from
            mul_le_mul_of_nonneg_right h7 (sq_nonneg _)))
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp
  have cover (p : ℕ×ℕ) (hp : p∈A) : cell n (t p) ∈ range n :=
    mem_range.mpr (cell_mem hn (good p hp).2.2.2.1).1
  change (∑ p ∈ A, v p) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to cover v]
  calc
    _ ≤ ∑ j ∈ range n, 7*‖series n w (sample j)‖^2 := sum_le_sum (fun j _ => charge j)
    _ = 7*∑ j ∈ range n, ‖series n w (sample j)‖^2 := (Finset.mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sample_series hn w sample samples) (by norm_num : (0:ℝ)≤7)).trans_eq (by ring)

/-- A single exceptional point in the allowed window suffices to count the
entire reduced rational pair. -/
theorem moving_large_values {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (B : ℝ) (hB : 0≤B) (A : Finset (ℕ×ℕ))
    (good : ∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
      ∃ t ∈ Set.Icc (0:ℝ) 1, |t-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n) ∧ B≤‖series n w t‖) :
    (A.card:ℝ)*B^2 ≤ 7*(1+4*Real.pi)*(n:ℝ)*∑ k ∈ range (n+1), (w k)^2 := by
  classical
  let t (p : ℕ×ℕ) := if hp : p∈A then (good p hp).2.2.2.choose else 0
  have spec (p : ℕ×ℕ) (hp : p∈A) :
      t p ∈ Set.Icc 0 1 ∧ |t p-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*Real.sqrt n) ∧ B≤‖series n w (t p)‖ := by
    simpa only [t,dite_eq_left hp] using (good p hp).2.2.2.choose_spec
  have allgood (p : ℕ×ℕ) (hp : p∈A) : 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧ t p∈Set.Icc (0:ℝ) 1 ∧ |t p-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*Real.sqrt n) :=
    And.intro (good p hp).1 ⟨(good p hp).2.1,(good p hp).2.2.1,(spec p hp).1,(spec p hp).2.1⟩
  have hsum := Finset.sum_le_sum (s:=A) (fun p hp => pow_le_pow_left₀ hB (spec p hp).2.2 2)
  exact (by simpa only [sum_const,nsmul_eq_mul] using hsum : (A.card:ℝ)*B^2 ≤ _).trans
    (moving_large_sieve hn w A t allgood)

end GoldbachMovingWindows
end
end

section
open Finset Real Filter
noncomputable section
namespace GoldbachMovingWindows

def primeLog (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

theorem primeLog_energy (n : ℕ) :
    (∑ k ∈ range (n+1),(primeLog k)^2) ≤ Real.log 4*(n:ℝ)*Real.log n := by
  have mass : (∑ k ∈ range (n+1),primeLog k) = Chebyshev.theta n := by
    unfold primeLog
    rw [←Finset.sum_filter,Chebyshev.theta_eq_sum_primesLE_log]
    congr 1
  calc
    _ ≤ ∑ k ∈ range (n+1),Real.log n*primeLog k := by
      refine sum_le_sum fun k hk => ?_
      have hn : k≤n := by have := mem_range.mp hk;omega
      by_cases hp : k.Prime
      · have hk0 : 0 < (k:ℝ) := by exact_mod_cast hp.pos
        have hu := Real.log_le_log hk0 (by exact_mod_cast hn : (k:ℝ)≤n)
        have h0 := Real.log_natCast_nonneg k
        simpa [primeLog,hp,pow_two] using mul_le_mul_of_nonneg_right hu h0
      · simp [primeLog,hp]
    _ ≤ _ := by
      rw [← mul_sum,mass]
      have := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) (Real.log_natCast_nonneg n)
      linarith only [this]

def windowConstant : ℝ := 7*(1+4*Real.pi)*Real.log 4

theorem prime_window_count {n : ℕ} (hn : 0<n) (η : ℝ) (A : Finset (ℕ×ℕ))
    (good : ∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
      ∃ t ∈ Set.Icc (0:ℝ) 1, |t-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n) ∧
        (n:ℝ)^(3/4+η) ≤ ‖series n primeLog t‖) :
    (A.card:ℝ) ≤ windowConstant*(n:ℝ)^(1/2-2*η)*Real.log n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := moving_large_values hn primeLog _ (Real.rpow_nonneg hnR.le _) A good
  have h' := h.trans (mul_le_mul_of_nonneg_left (primeLog_energy n)
    (show 0≤7*(1+4*Real.pi)*(n:ℝ) by positivity))
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (Real.rpow_pos_of_pos hnR (3/4+η)))).mp
  apply h'.trans_eq
  have power : (n:ℝ)^(1/2-2*η)*((n:ℝ)^(3/4+η))^2 = (n:ℝ)^2 := by
    rw [←Real.rpow_mul_natCast hnR.le,←Real.rpow_add hnR]
    norm_num [show (1/2-2*η)+(3/4+η)*(2:ℝ) = 2 by ring]
  dsimp [windowConstant]
  linear_combination -(7*(1+4*Real.pi)*Real.log 4*Real.log n)*power

/-- The logarithm and the fixed numerical constant can be absorbed into a
single arbitrarily small exponent in the number of exceptional windows. -/
theorem eventually_prime_window_count {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ A : Finset (ℕ×ℕ),
      (∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
        ∃ t ∈ Set.Icc (0:ℝ) 1, |t-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*Real.sqrt n) ∧
          (n:ℝ)^(3/4+η)≤‖series n primeLog t‖) →
      (A.card:ℝ) ≤ (n:ℝ)^(1/2-η) := by
  have lim : Filter.Tendsto (fun n : ℕ => (n:ℝ)^(η/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hη)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (lim.eventually_ge_atTop (windowConstant/(η/2)))
  refine ⟨max 1 N,?_⟩
  intro n hn A hA
  have hpos : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hpos
  have hC : 0≤windowConstant := by unfold windowConstant;positivity
  have logle := Real.log_le_rpow_div hnR.le (half_pos hη)
  have c := hN n (by omega)
  have hc : windowConstant*Real.log n ≤ (n:ℝ)^η := by
    calc
      _ ≤ windowConstant*((n:ℝ)^(η/2)/(η/2)) := mul_le_mul_of_nonneg_left logle hC
      _ = (windowConstant/(η/2))*(n:ℝ)^(η/2) := by ring
      _ ≤ (n:ℝ)^(η/2)*(n:ℝ)^(η/2) := mul_le_mul_of_nonneg_right c (Real.rpow_nonneg hnR.le _)
      _ = _ := by rw [←Real.rpow_add hnR];congr 1;ring
  exact (prime_window_count hpos η A hA).trans (by
    calc
      _ = (windowConstant*Real.log n)*(n:ℝ)^(1/2-2*η) := by ring
      _ ≤ (n:ℝ)^η*(n:ℝ)^(1/2-2*η) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hnR.le _)
      _ = _ := by rw [←Real.rpow_add hnR];congr 1;ring)
end GoldbachMovingWindows
end
end

section
open GoldbachMovingWindows Finset
theorem Conjectures.Goldbach.ThreeQuartersExceptionalDirichletWindows :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
let S := fun (n : ℕ) (u : ℕ→ℝ) (t : ℝ) => ∑ k ∈ Finset.range (n+1), (u k:ℂ)*E ((k:ℝ)*t)
(∀ n : ℕ, 0<n → ∀ η : ℝ, ∀ A : Finset (ℕ×ℕ),
  (∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
    ∃ t ∈ Set.Icc (0:ℝ) 1, |t-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*Real.sqrt n) ∧ (n:ℝ)^(3/4+η)≤‖S n w t‖) →
  (A.card:ℝ) ≤ 7*(1+4*Real.pi)*Real.log 4*(n:ℝ)^(1/2-2*η)*Real.log n) ∧
(∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n →
  ∃ bad : Finset ℕ, (bad.card:ℝ) ≤ (n:ℝ)^(1/2-η) ∧
    ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt n → q ∉ bad → ∀ a : ℕ, a≤q → a.Coprime q →
    ∀ t ∈ Set.Icc (0:ℝ) 1, |t-(a:ℝ)/q|≤1/((q:ℝ)*Real.sqrt n) → ‖S n w t‖ < (n:ℝ)^(3/4+η)) := by
  classical
  intro w E S
  have eqS (n : ℕ) (t : ℝ) : S n w t = series n primeLog t := by
    dsimp only [S,series,w,primeLog,E]
    simp only [wave_eq]
  simp_rw [eqS]
  constructor
  · exact fun n hn η A h => prime_window_count hn η A h
  · intro η hη
    obtain ⟨N,hN⟩ := eventually_prime_window_count hη
    refine ⟨max N 1,?_⟩
    intro n hn
    have hn0 : 0<n := by omega
    let U := (range (n+1)) ×ˢ (range (n+1))
    let A := U.filter (fun p => 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
      ∃ t ∈ Set.Icc (0:ℝ) 1, |t-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*Real.sqrt n) ∧ (n:ℝ)^(3/4+η)≤‖series n primeLog t‖)
    have count := hN n (by omega) A (fun _ hp => (mem_filter.mp hp).2)
    refine ⟨A.image Prod.fst, (show ((A.image Prod.fst).card:ℝ)≤A.card by exact_mod_cast card_image_le).trans count,?_⟩
    intro q hq hqS hgood a ha hc t ht htq
    by_contra! hv
    have hs : Real.sqrt n ≤ (n:ℝ) := by
      have h1 : (1:ℝ)≤n := by exact_mod_cast hn0
      nlinarith only [Real.sq_sqrt (Nat.cast_nonneg n),Real.sqrt_nonneg (n:ℝ),h1,sq_nonneg ((n:ℝ)-1)]
    have hqn : q≤n := by exact_mod_cast hqS.trans hs
    have hm : (q,a)∈U := mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
    exact hgood (mem_image.mpr ⟨(q,a),mem_filter.mpr ⟨hm,hq,hqS,hc,t,ht,htq,hv⟩,rfl⟩)
end
