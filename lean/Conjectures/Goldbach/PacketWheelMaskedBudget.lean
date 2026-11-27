import Mathlib

namespace Conjectures.Goldbach.PacketWheelMaskedBudget_aux
namespace GoldbachBudget
noncomputable section

private def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
private def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  ∑ k ∈ Finset.range (n+1), (a k : ℂ) * phase ((k:ℝ)*t)
private def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
private theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := (Nat.log 2 (n+2))^2
  let Index := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have cover : arcs n = ⋃ i : Index,
      {t : ℝ | |t-(i.val.2:ℝ)/(i.val.1:ℝ)| ≤ (Q:ℝ)/((i.val.1:ℝ)*(n:ℝ))} := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hQ,ha,hc,ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q,a),hq,hQ,ha,hc⟩,ht⟩
    · intro ht
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1,i.val.2,i.property.1,i.property.2.1,i.property.2.2.1,i.property.2.2.2,hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet

end
end GoldbachBudget

namespace GoldbachPacket
noncomputable section

private def packet (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)
private def length (n : ℕ) := max 1 (Nat.log 2 n / 2)
private def resonant (n : ℕ) := {t : ℝ | t ∉ GoldbachBudget.arcs n ∧
  (1:ℝ)/2 < packet (length n) t / (length n:ℝ)}
private def wheel (k : ℕ) := if Nat.Coprime k 30 then (30:ℝ)/8 else 0
theorem wheelGeometric (n : ℕ) (t : ℝ) :
    GoldbachBudget.spec n wheel t = ((30:ℝ)/8:ℂ) *
      ∑ r ∈ (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n),
        GoldbachBudget.phase ((r:ℝ)*t) *
          ∑ j ∈ Finset.range ((n-r)/30+1), GoldbachBudget.phase ((30:ℝ)*(j:ℝ)*t) := by
  let W := (Finset.range (n+1)).filter (fun k => Nat.Coprime k 30)
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let D := R.sigma (fun r => Finset.range ((n-r)/30+1))
  let E := GoldbachBudget.phase
  have cop (k : ℕ) : Nat.Coprime (k % 30) 30 ↔ Nat.Coprime k 30 := by
    unfold Nat.Coprime
    rw [← Nat.gcd_rec 30 k, Nat.gcd_comm 30 k]
  have addE (x y : ℝ) : E (x+y) = E x * E y := by
    dsimp [E,GoldbachBudget.phase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have wsum : GoldbachBudget.spec n wheel t = ((30:ℝ)/8:ℂ) * ∑ k ∈ W, E ((k:ℝ)*t) := by
    rw [Finset.mul_sum]
    unfold GoldbachBudget.spec
    dsimp only [W]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hc : Nat.Coprime k 30
    · simp only [wheel, if_pos hc, Complex.ofReal_div, Complex.ofReal_ofNat, E]
    · simp only [wheel, if_neg hc, Complex.ofReal_zero, zero_mul]
  rw [wsum]
  apply congrArg (fun z : ℂ => ((30:ℝ)/8:ℂ)*z)
  calc
    _ = ∑ d ∈ D, E ((d.1:ℝ)*t) * E (30*(d.2:ℝ)*t) := by
      apply Finset.sum_nbij' (fun k : ℕ => (⟨k % 30, k / 30⟩ : Σ _ : ℕ, ℕ)) (fun d => d.1+30*d.2)
      · intro k hk
        simp only [W,Finset.mem_filter,Finset.mem_range] at hk
        simp only [D,R,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range]
        exact ⟨⟨by omega, (cop k).mpr hk.2, by omega⟩,by omega⟩
      · rintro ⟨r,j⟩ hd
        simp only [D,R,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hd
        simp only [W,Finset.mem_filter,Finset.mem_range]
        refine ⟨by omega,(cop _).mp ?_⟩
        simpa only [show (r + 30 * j) % 30 = r by omega] using hd.1.2.1
      · intro k _; dsimp; omega
      · rintro ⟨r,j⟩ hd
        simp only [D,R,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hd
        change (⟨(r + 30 * j) % 30, (r + 30 * j) / 30⟩ : Σ _ : ℕ, ℕ) = ⟨r,j⟩
        rw [show (r + 30 * j) % 30 = r by omega, show (r + 30 * j) / 30 = j by omega]
      · intro k _
        change E ((k:ℝ)*t) = E (((k % 30 : ℕ):ℝ)*t) * E (30*((k / 30 : ℕ):ℝ)*t)
        rw [← addE]
        have he : (k:ℝ) = ((k % 30 : ℕ):ℝ)+30*((k / 30 : ℕ):ℝ) := by
          exact_mod_cast (show k = k % 30 + 30*(k / 30) by omega)
        congr 1
        linear_combination t * he
    _ = _ := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r _
      change (∑ j ∈ Finset.range ((n-r)/30+1), E ((r:ℝ)*t)*E (30*(j:ℝ)*t)) =
        E ((r:ℝ)*t)*(∑ j ∈ Finset.range ((n-r)/30+1), E (30*(j:ℝ)*t))
      rw [Finset.mul_sum]

private def gridDistance (t : ℝ) := ‖GoldbachBudget.phase (30*t) - 1‖
private def gridEnvelope (n : ℕ) (t : ℝ) :=
  ((n:ℝ)+1)^2 / (1+((n:ℝ)+1)^2 * (gridDistance t)^2)

private theorem phaseUnit (x : ℝ) : ‖GoldbachBudget.phase x‖ = 1 := by
  simp [GoldbachBudget.phase, Complex.norm_exp]

private theorem wheelDistanceBound (n : ℕ) (t : ℝ) :
    ‖GoldbachBudget.spec n wheel t‖ * gridDistance t ≤ 60 := by
  let z := GoldbachBudget.phase (30*t)
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let G := fun r : ℕ => GoldbachBudget.phase ((r:ℝ)*t) *
    ∑ j ∈ Finset.range ((n-r)/30+1), GoldbachBudget.phase (30*(j:ℝ)*t)
  have hz : ‖z‖ = 1 := phaseUnit _
  have phasePow (j : ℕ) : GoldbachBudget.phase (30*(j:ℝ)*t) = z^j := by
    dsimp [z,GoldbachBudget.phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have gb (r : ℕ) : ‖G r‖*gridDistance t ≤ 2 := by
    simp only [G,gridDistance,norm_mul,phaseUnit,one_mul,phasePow]
    change ‖∑ j ∈ Finset.range ((n-r)/30+1), z^j‖ * ‖z-1‖ ≤ 2
    rw [← norm_mul, geom_sum_mul]
    exact (norm_sub_le ..).trans (by norm_num [norm_pow,hz])
  have card : R.card ≤ 8 := by
    have hsub : R ⊆ (Finset.range 30).filter (fun r => Nat.Coprime r 30) := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2.1⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  have whole : ‖∑ r ∈ R, G r‖ * gridDistance t ≤ 16 := by
    calc
      _ ≤ (∑ r ∈ R, ‖G r‖)*gridDistance t :=
        mul_le_mul_of_nonneg_right (norm_sum_le ..) (norm_nonneg _)
      _ = ∑ r ∈ R, ‖G r‖*gridDistance t := Finset.sum_mul ..
      _ ≤ ∑ _r ∈ R, (2:ℝ) := Finset.sum_le_sum fun r _ => gb r
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul]; linarith [show (R.card:ℝ) ≤ 8 by exact_mod_cast card]
  have coeff : ‖((30:ℝ)/8:ℂ)‖ = 30/8 := by norm_num [norm_div]
  rw [wheelGeometric, norm_mul, coeff, mul_assoc]
  change (30/8:ℝ)*(‖∑ r ∈ R, G r‖ * gridDistance t) ≤ _
  linarith only [whole]

/-- A smooth, arithmetic-free upper bound valid even at the exact resonances. -/
theorem wheelEnvelope (n : ℕ) (t : ℝ) :
    ‖GoldbachBudget.spec n wheel t‖^2 ≤ 3616 * gridEnvelope n t := by
  let S := ‖GoldbachBudget.spec n wheel t‖
  let A := (n:ℝ)+1
  let d := gridDistance t
  have hS : 0 ≤ S := norm_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have ht : S ≤ 4*A := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖(wheel k:ℂ)*GoldbachBudget.phase ((k:ℝ)*t)‖ := norm_sum_le ..
      _ ≤ ∑ _k ∈ Finset.range (n+1), (4:ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul,phaseUnit,mul_one,Complex.norm_real,Real.norm_eq_abs]
        dsimp [wheel]; split <;> norm_num
      _ = _ := by simp [A]; ring
  have hsd : S*d ≤ 60 := wheelDistanceBound n t
  have h1 := pow_le_pow_left₀ hS ht 2
  have h2 := pow_le_pow_left₀ (mul_nonneg hS hd) hsd 2
  change S^2 ≤ 3616*(A^2/(1+A^2*d^2))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [h1,mul_le_mul_of_nonneg_left h2 (sq_nonneg A)]

theorem wheelLeakageTransfer
    (pointwise : ∀ n t, ‖GoldbachBudget.spec n wheel t‖^2 ≤ 3616 * gridEnvelope n t)
    (leak : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε*(n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (fun u => ‖GoldbachBudget.spec n wheel u‖^2) t)
        ≤ ε*(n:ℝ) := by
  intro ε hε
  obtain ⟨N,hN⟩ := leak (ε/3616) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance GoldbachBudget.phase
    fun_prop (disch := intro t; positivity)
  have hs : Continuous (fun u => ‖GoldbachBudget.spec n wheel u‖^2) := by
    unfold GoldbachBudget.spec GoldbachBudget.phase; fun_prop
  have maskInt {f : ℝ → ℝ} (hc : Continuous f) :
      IntervalIntegrable ((GoldbachBudget.arcs n)ᶜ.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (GoldbachBudget.measurableArcs n).compl
  calc
    _ ≤ ∫ t in (0:ℝ)..1, 3616 * (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (maskInt hs) ((maskInt hg).const_mul 3616)
      intro t _
      by_cases ht : t ∈ (GoldbachBudget.arcs n)ᶜ
      · simpa only [Set.indicator_of_mem ht] using pointwise n t
      · simp [ht]
    _ ≤ _ := by rw [intervalIntegral.integral_const_mul]; linarith only [hN n hn]

private def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2
private def lorentz (r c t : ℝ) := 1/(r^2+(t-c)^2)

private theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) : Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

/-- The integral is bounded uniformly in the location of the center, including endpoints. -/
private theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in (0:ℝ)..1, lorentz r c t) ≤ Real.pi/r := by
  let F := fun t : ℝ => Real.arctan ((t-c)/r)/r
  have deriv (t : ℝ) : HasDerivAt F (lorentz r c t) t := by
    have h := (((Real.hasDerivAt_arctan ((t-c)/r)).comp t
      (((hasDerivAt_id t).sub_const c).div_const r)).div_const r)
    have eq : lorentz r c t = 1 / (1 + ((t-c)/r)^2) * (1/r) / r := by
      unfold lorentz
      field_simp <;> ring
    rw [eq]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t)
    ((lorentzContinuous hr c).intervalIntegrable ..)]
  dsimp [F]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha := Real.arctan_lt_pi_div_two ((1-c)/r)
  have hb := Real.neg_pi_div_two_lt_arctan ((0-c)/r)
  linarith

/-- All rationals with unreduced denominator d ≤ Q are protected by the frozen arcs. -/
private theorem denominatorExclusion {n k d : ℕ} {t : ℝ} (hn : 0 < n) (hd : 0 < d) (hQ : d ≤ gridQ n)
    (hk : k ≤ d) (hm : t ∉ GoldbachBudget.arcs n) :
    (gridQ n:ℝ)/(d*(n:ℝ)) < |t-(k:ℝ)/d| := by
  obtain ⟨g,a,q,hg,hcop,hk',hq'⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right k hd)
  have hq : 0 < q := by
    by_contra! hz
    have he : q=0 := by omega
    rw [he, zero_mul] at hq'
    omega
  have hqd : q ≤ d := Nat.le_of_dvd hd ⟨g,hq'⟩
  have haq : a ≤ q := by
    exact (Nat.mul_le_mul_right_iff hg).mp (show a*g ≤ q*g by omega)
  have eq : (k:ℝ)/d = (a:ℝ)/(q:ℝ) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    have cross : k*q = a*d := by rw [hk',hq']; ring
    exact_mod_cast cross
  by_contra! h
  apply hm
  refine ⟨q,a,hq,hqd.trans hQ,haq,hcop,?_⟩
  rw [← eq]
  exact h.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqd : (q:ℝ) ≤ d) (Nat.cast_nonneg _)))

private theorem integerChord (v : ℝ) (k : ℕ) (hk : |v-(k:ℝ)| ≤ 1/2) :
    4*|v-(k:ℝ)| ≤ ‖GoldbachBudget.phase v-1‖ := by
  let u := v-(k:ℝ)
  let x := Real.pi*u
  let y := 2*Real.pi*(v)
  have hangle : y = 2*x + (k:ℝ)*(2*Real.pi) := by dsimp [y,x,u]; ring
  have hs : ‖GoldbachBudget.phase v-1‖ ^ 2 = 2-2*Real.cos y := by
    change ‖Complex.exp ((y:ℂ)*Complex.I)-1‖^2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    nlinarith only [Real.sin_sq_add_cos_sq y]
  have he : ‖GoldbachBudget.phase v-1‖ = 2*|Real.sin x| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    change ‖GoldbachBudget.phase v-1‖ ^ 2 = (2*|Real.sin x|)^2
    rw [hs,hangle,Real.cos_add_nat_mul_two_pi,Real.cos_two_mul]
    nlinarith only [sq_abs (Real.sin x), Real.sin_sq_add_cos_sq x]
  have hx : |x| ≤ Real.pi/2 := by
    dsimp [x]; rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [mul_le_mul_of_nonneg_left hk Real.pi_pos.le]
  have hj := Real.mul_abs_le_abs_sin hx
  have hxu : |x| = Real.pi*|u| := by dsimp [x]; rw [abs_mul,abs_of_pos Real.pi_pos]
  rw [hxu,show 2/Real.pi*(Real.pi*|u|) = 2*|u| by field_simp] at hj
  rw [he]
  change 4*|u| ≤ _
  linarith only [hj]

private theorem gridChord (t : ℝ) (k : ℕ) (hk : |30*t-(k:ℝ)| ≤ 1/2) :
    |t-(k:ℝ)/30| ≤ gridDistance t := by
  have h := integerChord (30*t) k hk
  have eq : 30*t-(k:ℝ) = 30*(t-(k:ℝ)/30) := by ring
  rw [eq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<30)] at h
  change _ ≤ ‖GoldbachBudget.phase (30*t)-1‖
  linarith [abs_nonneg (t-(k:ℝ)/30)]

private theorem gridPointMajorant {n : ℕ} (hn : 0 < n) (hQ : 30 ≤ gridQ n)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t ≤
      ∑ k ∈ Finset.range 31, 2*lorentz ((gridQ n:ℝ)/(30*(n:ℝ))) ((k:ℝ)/30) t := by
  let r := (gridQ n:ℝ)/(30*(n:ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have nonneg (k : ℕ) : 0 ≤ 2*lorentz r ((k:ℝ)/30) t := by unfold lorentz; positivity
  by_cases hm : t ∈ (GoldbachBudget.arcs n)ᶜ
  · rw [Set.indicator_of_mem hm]
    let k := ⌊30*t+1/2⌋₊
    obtain ⟨h0,h1⟩ := ht
    have hlo : (k:ℝ) ≤ 30*t+1/2 := Nat.floor_le (by linarith)
    have hhi : 30*t+1/2 < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hk : k ≤ 30 := by
      by_contra! h
      have h' : (31:ℝ) ≤ k := by exact_mod_cast h
      linarith
    have close : |30*t-(k:ℝ)| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hdist := gridChord t k close
    have hcut : r ≤ |t-(k:ℝ)/30| := (denominatorExclusion hn (by decide : 0<30) hQ hk hm).le
    have h1' := pow_le_pow_left₀ hr.le (hcut.trans hdist) 2
    have h2' := pow_le_pow_left₀ (abs_nonneg _) hdist 2
    rw [sq_abs] at h2'
    have bound : gridEnvelope n t ≤ 2*lorentz r ((k:ℝ)/30) t := by
      unfold gridEnvelope lorentz
      rw [← mul_div_assoc, mul_one]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add h1' h2') (sq_nonneg ((n:ℝ)+1))]
    exact bound.trans (Finset.single_le_sum (fun k _ => nonneg k) (Finset.mem_range.mpr (by omega : k<31)))
  · rw [Set.indicator_of_notMem hm]
    exact Finset.sum_nonneg fun k _ => nonneg k

/-- The minor-arc tail is bounded by an explicit multiple of n/Q(n). -/
theorem gridTailQuantitative (n : ℕ) (hn : 0 < n) (hQ : 30 ≤ gridQ n) :
    (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t) ≤
      1860*Real.pi*(n:ℝ)/(gridQ n:ℝ) := by
  let r := (gridQ n:ℝ)/(30*(n:ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance GoldbachBudget.phase
    fun_prop (disch := intro t; positivity)
  have hi : IntervalIntegrable ((GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n)) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (GoldbachBudget.measurableArcs n).compl
  let f := fun (k : ℕ) (t : ℝ) => 2*lorentz r ((k:ℝ)/30) t
  have hf (k : ℕ) : Continuous (f k) := continuous_const.mul (lorentzContinuous hr _)
  have hsum : Continuous (fun t => ∑ k ∈ Finset.range 31, f k t) := by fun_prop
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ∑ k ∈ Finset.range 31, f k t :=
      intervalIntegral.integral_mono_on (by norm_num) hi (hsum.intervalIntegrable ..)
        (fun t ht => gridPointMajorant hn hQ t ht)
    _ = ∑ k ∈ Finset.range 31, 2*(∫ t in (0:ℝ)..1, lorentz r ((k:ℝ)/30) t) := by
      rw [intervalIntegral.integral_finsetSum (fun k _ => (hf k).intervalIntegrable ..)]
      simp only [f,intervalIntegral.integral_const_mul]
    _ ≤ ∑ _k ∈ Finset.range 31, 2*(Real.pi/r) := Finset.sum_le_sum
      fun k _ => mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by norm_num)
    _ = _ := by simp [r]; field_simp; ring

theorem gridTail (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε*(n:ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (1860*Real.pi/ε)
  let B := max 30 M
  refine ⟨2^B, ?_⟩
  intro n hn
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^B) hn
  have hb : B ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by
    unfold gridQ; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  apply (gridTailQuantitative n hn' ((le_max_left ..).trans hq)).trans
  have hq' : 0 < gridQ n := by have : 30 ≤ B := le_max_left ..; omega
  have hM' : 1860*Real.pi/ε ≤ (gridQ n:ℝ) := hM.trans (by exact_mod_cast (le_trans (le_max_right 30 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM') (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]

theorem wheelMinorLeakage : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (fun u => ‖GoldbachBudget.spec n wheel u‖^2) t) ≤ ε*(n:ℝ) := wheelLeakageTransfer wheelEnvelope gridTail

theorem wheelMaskedBudget :
    ∃ N : ℕ, ∀ n ≥ N, Even n →
      (∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => ‖GoldbachBudget.spec n wheel u‖^2) t) ≤ (n:ℝ)/2304 := by
  obtain ⟨N,hN⟩ := wheelMinorLeakage (1/2304) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn _
  let f := fun t : ℝ => ‖GoldbachBudget.spec n wheel t‖^2
  have hc : Continuous f := by unfold f GoldbachBudget.spec GoldbachBudget.phase; fun_prop
  have hi {s : Set ℝ} (hs : MeasurableSet s) :
      IntervalIntegrable (s.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  have hm : MeasurableSet (resonant n) := (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet
  have bound : (∫ t in (0:ℝ)..1, (resonant n).indicator f t) ≤
      ∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator f t := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hi hm) (hi (GoldbachBudget.measurableArcs n).compl)
    intro t _
    by_cases ht : t ∈ resonant n
    · have ha : t ∈ (GoldbachBudget.arcs n)ᶜ := ht.1
      simp [ht,ha]
    · by_cases ha : t ∈ (GoldbachBudget.arcs n)ᶜ <;> simp [ht,ha,f,sq_nonneg]
  exact bound.trans (by linarith only [hN n hn])

end
end GoldbachPacket
end Conjectures.Goldbach.PacketWheelMaskedBudget_aux

open Conjectures.Goldbach.PacketWheelMaskedBudget_aux

theorem Conjectures.Goldbach.PacketWheelMaskedBudget : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → U n model ≤ (n:ℝ)/2304 := by
  simpa only [GoldbachBudget.phase, GoldbachBudget.spec, GoldbachBudget.arcs,
    GoldbachPacket.packet, GoldbachPacket.length, GoldbachPacket.resonant,
    GoldbachPacket.wheel] using GoldbachPacket.wheelMaskedBudget
