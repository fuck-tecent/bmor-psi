import Mathlib

namespace Conjectures.Goldbach.PacketWheelGridTail_aux
noncomputable section

def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
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

def gridDistance (t : ℝ) := ‖phase (30*t) - 1‖
def gridEnvelope (n : ℕ) (t : ℝ) :=
  ((n:ℝ)+1)^2 / (1+((n:ℝ)+1)^2 * (gridDistance t)^2)
def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2
def lorentz (r c t : ℝ) := 1/(r^2+(t-c)^2)

theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) : Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
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

theorem denominatorExclusion {n k d : ℕ} {t : ℝ} (hn : 0 < n) (hd : 0 < d) (hQ : d ≤ gridQ n)
    (hk : k ≤ d) (hm : t ∉ arcs n) :
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
theorem integerChord (v : ℝ) (k : ℕ) (hk : |v-(k:ℝ)| ≤ 1/2) :
    4*|v-(k:ℝ)| ≤ ‖phase v-1‖ := by
  let u := v-(k:ℝ)
  let x := Real.pi*u
  let y := 2*Real.pi*(v)
  have hangle : y = 2*x + (k:ℝ)*(2*Real.pi) := by dsimp [y,x,u]; ring
  have hs : ‖phase v-1‖ ^ 2 = 2-2*Real.cos y := by
    change ‖Complex.exp ((y:ℂ)*Complex.I)-1‖^2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    nlinarith only [Real.sin_sq_add_cos_sq y]
  have he : ‖phase v-1‖ = 2*|Real.sin x| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    change ‖phase v-1‖ ^ 2 = (2*|Real.sin x|)^2
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
theorem gridChord (t : ℝ) (k : ℕ) (hk : |30*t-(k:ℝ)| ≤ 1/2) :
    |t-(k:ℝ)/30| ≤ gridDistance t := by
  have h := integerChord (30*t) k hk
  have eq : 30*t-(k:ℝ) = 30*(t-(k:ℝ)/30) := by ring
  rw [eq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<30)] at h
  change _ ≤ ‖phase (30*t)-1‖
  linarith [abs_nonneg (t-(k:ℝ)/30)]
theorem gridPointMajorant {n : ℕ} (hn : 0 < n) (hQ : 30 ≤ gridQ n)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (arcs n)ᶜ.indicator (gridEnvelope n) t ≤
      ∑ k ∈ Finset.range 31, 2*lorentz ((gridQ n:ℝ)/(30*(n:ℝ))) ((k:ℝ)/30) t := by
  let r := (gridQ n:ℝ)/(30*(n:ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have nonneg (k : ℕ) : 0 ≤ 2*lorentz r ((k:ℝ)/30) t := by unfold lorentz; positivity
  by_cases hm : t ∈ (arcs n)ᶜ
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

theorem gridTailQuantitative (n : ℕ) (hn : 0 < n) (hQ : 30 ≤ gridQ n) :
    (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (gridEnvelope n) t) ≤
      1860*Real.pi*(n:ℝ)/(gridQ n:ℝ) := by
  let r := (gridQ n:ℝ)/(30*(n:ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance phase
    fun_prop (disch := intro t; positivity)
  have hi : IntervalIntegrable ((arcs n)ᶜ.indicator (gridEnvelope n)) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (measurableArcs n).compl
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
    ∃ N : ℕ, ∀ n ≥ N, (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε*(n:ℝ) := by
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


end
end Conjectures.Goldbach.PacketWheelGridTail_aux

theorem Conjectures.Goldbach.PacketWheelGridTail :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
     let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
     let D := fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*‖E (30*t)-1‖^2);
     ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, intervalIntegral ((arcs n)ᶜ.indicator (D n)) (0:ℝ) 1 MeasureTheory.volume ≤ ε*(n:ℝ)) := by
  intro E Q arcs D ε hε
  exact Conjectures.Goldbach.PacketWheelGridTail_aux.gridTail ε hε
