import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

/-!
The high band has an expansion in short-step geometric sums.
Away from their rational centres, a weighted square-mean estimate controls the integral.
Near the centres, the Ramanujan-sum expansion reduces the smoothed integral to
primitive Dirichlet characters. The character large sieve on dyadic conductor
intervals gives the needed saving after summing the denominator weights.
-/
section

/- Adapted from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0).
The geometric estimates there adapt openai/math, revision
3344da59991ed94f9ba711217b29c1d760badfa6, module GeometricCharacterBound
(Apache-2.0). These selected estimates use a common grid-neighbourhood radius. -/

namespace DyadicMixedB4Geometric
open Finset MeasureTheory
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
def wave (u l r : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Ioc l r, phase ((u*h:ℕ)*t)
/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]


/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  field_simp
@[simp] theorem norm_phase' (x : ℝ) : ‖phase x‖=1 := by simp [phase, Complex.norm_exp]

theorem wave_cap (u l r : ℕ) (x : ℝ) : ‖wave u l r x‖ ≤ r := by
  unfold wave
  calc
    _ ≤ ∑ h∈Ioc l r,‖phase ((u*h:ℕ)*x)‖ := norm_sum_le _ _
    _ ≤ (r:ℝ) := by simp

theorem wave_sin (u l r : ℕ) (x : ℝ) (hs : Real.sin (Real.pi*(u*x))≠0) :
    ‖wave u l r x‖ ≤ 1/|Real.sin (Real.pi*(u*x))| := by
  let z := Complex.exp (Complex.I*((2*Real.pi*((u:ℝ)*x):ℝ):ℂ))
  have hz : ‖z‖=1 := Complex.norm_exp_I_mul_ofReal _
  have heq : wave u l r x = z^(l+1)*∑ j∈range (r-l),z^j := by
    have hs' : Ioc l r = Ico (l+1) (r+1) := by ext h; simp only [mem_Ioc,mem_Ico]; omega
    rw [wave,hs',sum_Ico_eq_sum_range,Nat.add_sub_add_right,mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← pow_add]
    dsimp [z,phase]
    rw [← Complex.exp_nat_mul]
    push_cast; congr 1; ring
  rw [heq,norm_mul,norm_pow,hz,one_pow,one_mul]
  exact norm_geometric_phase_sum_le hs _
def centers (u v : ℕ) := range (u+1) ×ˢ range (v+1)
def delta (U V : ℕ) (z : ℕ×ℕ) : ℤ := (z.1:ℤ)*V-(z.2:ℤ)*U

private theorem sameMod {U V i j a b : ℕ} (hc : U.Coprime V)
    (h : delta U V (i,j)=delta U V (a,b)) : i ≡ a [MOD U] := by
  apply Nat.ModEq.cancel_right_of_coprime hc
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨(b:ℤ)-j,?_⟩
  unfold delta at h;push_cast;dsimp at h;linarith

private theorem codeInj {U V : ℕ} (hU : 0<U) (hc : U.Coprime V) :
    Function.Injective (fun z : ℕ×ℕ => ((decide (0≤delta U V z), (delta U V z).natAbs),z.1/U)) := by
  rintro ⟨i,j⟩ ⟨a,b⟩ he
  have hs := congrArg (fun z: (Bool×ℕ)×ℕ => z.1.1) he
  have hm := congrArg (fun z: (Bool×ℕ)×ℕ => z.1.2) he
  have hd := congrArg (fun z: (Bool×ℕ)×ℕ => z.2) he
  change decide (0≤delta U V (i,j))=decide (0≤delta U V (a,b)) at hs
  change (delta U V (i,j)).natAbs=(delta U V (a,b)).natAbs at hm
  change i/U=a/U at hd
  have hD : delta U V (i,j)=delta U V (a,b) := by
    have hsign : 0≤delta U V (i,j) ↔ 0≤delta U V (a,b) := by simpa using hs
    omega
  have hmod := sameMod hc hD
  change i % U = a % U at hmod
  have hie : i=a := by
    have h1 := Nat.mod_add_div i U
    have h2 := Nat.mod_add_div a U
    rw [hd,hmod] at h1;omega
  subst a
  simp only [delta,sub_right_inj] at hD
  have he' : (j:ℤ)=(b:ℤ) := mul_right_cancel₀ (by exact_mod_cast hU.ne') hD
  simp [show j=b by exact_mod_cast he']

theorem latticeSum (g U V : ℕ) (hg : 0<g) (hU : 0<U) (hV : 0<V) (hc : U.Coprime V)
    (f : ℕ→ℝ) (hf : ∀a,0≤f a) :
    (∑ z ∈ centers (g*U) (g*V), f (delta U V z).natAbs) ≤
      2*((g:ℝ)+1)*∑ a ∈ range (g*U*V+1), f a := by
  let code := fun z : ℕ×ℕ => ((decide (0≤delta U V z),(delta U V z).natAbs),z.1/U)
  let T := (univ (α:=Bool) ×ˢ range (g*U*V+1)) ×ˢ range (g+1)
  calc
    _ ≤ ∑ a ∈ T,f a.1.2 := by
      apply Finset.sum_le_sum_of_injOn code (codeInj hU hc).injOn
      · intro a ha
        obtain ⟨⟨i,j⟩,hz,rfl⟩ := mem_image.mp ha
        obtain ⟨hi,hj⟩ := mem_product.mp hz
        have hi' : i≤g*U := Nat.le_of_lt_succ (mem_range.mp hi)
        have hj' : j≤g*V := Nat.le_of_lt_succ (mem_range.mp hj)
        have h1 : (i:ℤ)*V≤(g:ℤ)*U*V := by exact_mod_cast Nat.mul_le_mul_right V hi'
        have h2 : (j:ℤ)*U≤(g:ℤ)*U*V := by
          simpa [mul_comm,mul_assoc,mul_left_comm] using (show (j:ℤ)*U≤(g:ℤ)*V*U by exact_mod_cast Nat.mul_le_mul_right U hj')
        have hf1 : 0≤(i:ℤ)*V := by positivity
        have hf2 : 0≤(j:ℤ)*U := by positivity
        have hL : (delta U V (i,j)).natAbs≤g*U*V := by
          unfold delta;dsimp;zify;push_cast;apply abs_le.mpr;constructor <;> omega
        have hG : i/U≤g := (Nat.div_le_div_right hi').trans_eq (Nat.mul_div_cancel _ hU)
        exact mem_product.mpr ⟨mem_product.mpr ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le hL)⟩,mem_range.mpr (Nat.lt_succ_of_le hG)⟩
      · intro _ _;exact le_rfl
      · intro a _ _;exact hf _
    _ = _ := by
      simp [T,sum_product,sum_mul,mul_sum,mul_comm,mul_left_comm,mul_assoc]

theorem commonCenter (u v i j : ℕ) (hu : 0<u) (hv : 0<v) (hi : i≤u)
    (h : (i:ℝ)/u=(j:ℝ)/v) : ∃ k≤u.gcd v, (i:ℝ)/u=(k:ℝ)/(u.gcd v) := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g*U=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hU : 0<U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hg
  have hc : U.Coprime V := Nat.coprime_div_gcd_div_gcd hg
  have h' := (div_eq_div_iff (by exact_mod_cast hu.ne') (by exact_mod_cast hv.ne')).mp h
  have hnat : i*v=j*u := by exact_mod_cast h'
  rw [←hgu,←hgv] at hnat
  have hev : i*V=j*U := Nat.eq_of_mul_eq_mul_left hg (by simpa [mul_comm,mul_assoc,mul_left_comm] using hnat)
  have hdiv : U ∣ i := hc.dvd_of_dvd_mul_right (hev ▸ dvd_mul_left _ _)
  obtain ⟨k,hk⟩ := hdiv
  have hle : U*k ≤ U*g := by rw [←hk,Nat.mul_comm U g,hgu]; exact hi
  have hkg : k≤g := Nat.le_of_mul_le_mul_left hle hU
  refine ⟨k,hkg,?_⟩
  change (i:ℝ)/u=(k:ℝ)/g
  rw [←hgu,hk];push_cast;field_simp
def sep (u v : ℕ) (z : ℕ×ℕ) : ℝ := |(z.1:ℝ)/u-(z.2:ℝ)/v|

private theorem sep_reduced (g U V : ℕ) (hg : 0<g) (hU : 0<U) (hV : 0<V) (z : ℕ×ℕ) :
    sep (g*U) (g*V) z=((delta U V z).natAbs:ℝ)/(g*U*V) := by
  have hdelta : ((delta U V z).natAbs:ℝ) = |(z.1:ℝ)*V-z.2*U| := by
    calc
      _ = |((delta U V z:ℤ):ℝ)| := by simp only [Nat.cast_natAbs,Int.cast_abs]
      _ = _ := by simp [delta]
  rw [hdelta,←abs_of_pos (show (0:ℝ)<g*U*V by positivity),←abs_div]
  unfold sep
  congr 1;push_cast;field_simp

private theorem inverse_sum (m : ℕ) : (∑ j ∈ range (m+1),(j:ℝ)⁻¹) ≤ 1+Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have he : range (m+1)=insert 0 (Icc 1 m) := by ext j;simp;omega
  simpa [he] using h

theorem spacingSum (n u v : ℕ) (hu : 0<u) (hv : 0<v) (hun : u≤n) (hvn : v≤n) :
    (∑ z ∈ centers u v, (sep u v z)⁻¹) ≤ 8*((u:ℝ)*v)*(1+Real.log ((n:ℝ)+2)) := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g*U=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hU : 0<U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hg
  have hV : 0<V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) hg
  have hc : U.Coprime V := Nat.coprime_div_gcd_div_gcd hg
  have hL := latticeSum g U V hg hU hV hc (fun m => (m:ℝ)⁻¹) (fun m => by positivity)
  let N := g*U*V
  have hN : 0<N := by dsimp [N];positivity
  have hNn : N≤n*n := by
    dsimp [N];rw [hgu];exact Nat.mul_le_mul hun ((Nat.div_le_self ..).trans hvn)
  have hlog : 1+Real.log (N:ℝ) ≤ 2*(1+Real.log ((n:ℝ)+2)) := by
    have he : (N:ℝ) ≤ ((n:ℝ)+2)^2 := by
      calc _ ≤ (n:ℝ)*n := by exact_mod_cast hNn
           _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have h := Real.log_le_log (by exact_mod_cast hN) he
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hgr : (1:ℝ)≤g := by exact_mod_cast hg
  have hlogpos : 0≤1+Real.log ((n:ℝ)+2) := by linarith [Real.log_nonneg (show 1≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hmul := (inverse_sum N).trans hlog
  rw [←hgu,←hgv]
  simp_rw [sep_reduced g U V hg hU hV, inv_div,div_eq_mul_inv,←Finset.mul_sum]
  push_cast
  have hcore := (hL.trans (mul_le_mul_of_nonneg_left hmul (by positivity)))
  calc
    _ ≤ ((g:ℝ)*U*V)*(2*((g:ℝ)+1)*(2*(1+Real.log ((n:ℝ)+2)))) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ _ := by
      have hx := mul_le_mul_of_nonneg_right hgr (show 0≤(g:ℝ)*U*V*(1+Real.log ((n:ℝ)+2)) by positivity)
      nlinarith only [hx]

theorem coincidentCount (u v : ℕ) (hu : 0<u) (hv : 0<v) :
    (∑ z ∈ centers u v, if sep u v z=0 then (1:ℝ) else 0) ≤ 4*(u.gcd v:ℝ) := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g*U=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hU : 0<U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hg
  have hV : 0<V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) hg
  have hc : U.Coprime V := Nat.coprime_div_gcd_div_gcd hg
  have h := latticeSum g U V hg hU hV hc (fun m => if m=0 then (1:ℝ) else 0) (fun m => by split_ifs <;> norm_num)
  change _≤4*(g:ℝ)
  conv_lhs => rw [←hgu,←hgv]
  simp_rw [sep_reduced g U V hg hU hV]
  have hgr : (1:ℝ)≤g := by exact_mod_cast hg
  simp [show (g:ℝ)*U*V≠0 by positivity] at h ⊢
  linarith

def smoothKernel (a c t : ℝ) := 1/(a+|t-c|)
theorem cont_smoothKernel {a c : ℝ} (ha : 0<a) : Continuous (smoothKernel a c) := by
  unfold smoothKernel; fun_prop (disch := intro t; positivity)
theorem nonneg_smoothKernel {a c t : ℝ} (ha : 0≤a) : 0 ≤ smoothKernel a c t := by
  unfold smoothKernel;positivity

private theorem shift_center (f : ℝ→ℝ) (hc : Continuous f) (hf : ∀t,0≤f t)
    (hev : ∀t,f (-t)=f t) (c : ℝ) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1, f (t-c)) ≤ 2 * ∫ t in (0:ℝ)..1, f t := by
  have hh := intervalIntegral.integral_comp_neg f (a:=0) (b:=1)
  simp only [hev,neg_zero] at hh
  rw [intervalIntegral.integral_comp_sub_right]
  calc
    _ ≤ ∫ t in (-1:ℝ)..1, f t := by
      apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall hf) (hc.intervalIntegrable _ _)
    _ = _ := by
      rw [←intervalIntegral.integral_add_adjacent_intervals (b:=0) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),←hh]
      ring

theorem integral_smoothKernel {a c : ℝ} (ha : 0<a) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1,smoothKernel a c t) ≤ 2*Real.log ((1+a)/a) := by
  let f := fun x:ℝ => 1/(a+|x|)
  have hcont : Continuous f := by dsimp [f];fun_prop (disch := intro t; positivity)
  have h := shift_center f hcont (fun t => by dsimp [f];positivity) (fun t => by simp [f]) c hc0 hc1
  have hid : (∫ t in (0:ℝ)..1,f t) = Real.log ((1+a)/a) := by
    calc
      _ = ∫ t in (0:ℝ)..1, 1/(t+a) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num)] at ht
        simp [f,abs_of_nonneg ht.1,add_comm]
      _ = ∫ t in a..1+a, 1/t := by simpa using intervalIntegral.integral_comp_add_right (fun x:ℝ=>1/x) a (a:=0) (b:=1)
      _ = _ := integral_one_div_of_pos ha (by positivity)
  rwa [hid] at h

theorem integral_smoothKernel_sq {a c : ℝ} (ha : 0<a) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1,(smoothKernel a c t)^2) ≤ 2/a := by
  let f := fun x:ℝ => (1/(a+|x|))^2
  have hcont : Continuous f := by dsimp [f];fun_prop (disch := intro t; positivity)
  have h := shift_center f hcont (fun t => sq_nonneg _) (fun t => by simp [f]) c hc0 hc1
  have he : (∫ t in (0:ℝ)..1,f t) ≤ 1/a := by
    calc
      _ = ∫ t in (0:ℝ)..1, (t+a)^(-2:ℤ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num)] at ht
        simp [f,abs_of_nonneg ht.1,add_comm,one_div,zpow_neg,pow_two]
      _ = ∫ t in a..1+a,t^(-2:ℤ) := by simpa using intervalIntegral.integral_comp_add_right (fun x:ℝ=>x^(-2:ℤ)) a (a:=0) (b:=1)
      _ ≤ _ := by
        rw [integral_zpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt ha (by positivity)⟩)]
        norm_num
        have hh : 0≤(1+a)⁻¹ := by positivity
        linarith
  change _≤2*(∫ t in (0:ℝ)..1, f t) at h
  exact h.trans (by rw [div_eq_mul_one_div 2 a]; linarith)

theorem distinct_kernel {a x y t : ℝ} (ha : 0<a) (hxy : x≠y) :
    smoothKernel a x t*smoothKernel a y t ≤
      (smoothKernel a x t+smoothKernel a y t)/|x-y| := by
  have hx : 0<a+|t-x| := by positivity
  have hy : 0<a+|t-y| := by positivity
  have h := abs_sub_le x t y
  rw [abs_sub_comm x t] at h
  unfold smoothKernel
  apply (le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy))).mpr
  field_simp
  linarith

theorem nearestCenter (u : ℕ) (t : ℝ) (h0 : 0≤t) (h1 : t≤1) :
    ∃ i ∈ range (u+1), |(u:ℝ)*t-i|≤1/2 := by
  let i := ⌊(u:ℝ)*t+1/2⌋₊
  have hlow : (i:ℝ) ≤ (u:ℝ)*t+1/2 := Nat.floor_le (by positivity)
  have hhigh : (u:ℝ)*t+1/2 < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have hle : (u:ℝ)*t≤u := by simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg u)
  have hi : (i:ℝ)<(u:ℝ)+1 := by linarith
  refine ⟨i,mem_range.mpr (by exact_mod_cast hi),abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem waveBound {n u l r i : ℕ} {t : ℝ} (hu : 0<u) (hr : r≤n/u)
    (hi : |(u:ℝ)*t-i|≤1/2) :
    ‖wave u l r t‖ ≤ (2/(u:ℝ))*smoothKernel (1/((n:ℝ)+1)) ((i:ℝ)/u) t := by
  have hur : (0:ℝ)<u := by exact_mod_cast hu
  let a : ℝ := 1/((n:ℝ)+1)
  let c : ℝ := (i:ℝ)/u
  let y : ℝ := (u:ℝ)*t-i
  have hnorm : ‖wave u l r t‖≤(n:ℝ)/u := by
    calc
      _ ≤ ∑ h ∈ Ioc l r, ‖phase ((u*h:ℕ)*t)‖ := norm_sum_le ..
      _ = ((r-l:ℕ):ℝ) := by simp [phase,Complex.norm_exp]
      _ ≤ ((n/u:ℕ):ℝ) := by exact_mod_cast (Nat.sub_le r l).trans hr
      _ ≤ _ := Nat.cast_div_le
  have h1 : ‖wave u l r t‖*a ≤ 1/(u:ℝ) := by
    dsimp [a]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    exact hnorm.trans (by rw [one_div_mul_eq_div];gcongr;linarith)
  have h2 : ‖wave u l r t‖*|t-c| ≤ 1/(u:ℝ) := by
    have hcy : |y|=(u:ℝ)*|t-c| := by
      rw [←abs_of_pos hur,←abs_mul]
      congr 1;dsimp [y,c];field_simp
    rcases eq_or_ne y 0 with hy|hy
    · have hzero : |t-c|=0 := by rw [hy,abs_zero] at hcy;exact (mul_eq_zero.mp hcy.symm).resolve_left hur.ne'
      rw [hzero,mul_zero];positivity
    have hper : |Real.sin (Real.pi*((u:ℝ)*t))|=|Real.sin (Real.pi*y)| := by
      rw [show Real.pi*((u:ℝ)*t)=Real.pi*y+(i:ℝ)*Real.pi by dsimp [y];ring,
        Real.sin_add_nat_mul_pi,abs_mul,abs_pow];simp
    have hpi : |Real.pi*y|≤Real.pi/2 := by rw [abs_mul,abs_of_pos Real.pi_pos];nlinarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le]
    have hj := Real.mul_abs_le_abs_sin hpi
    rw [abs_mul,abs_of_pos Real.pi_pos,←mul_assoc,div_mul_cancel₀ _ Real.pi_ne_zero,←hper] at hj
    have hs := (mul_pos (by norm_num : (0:ℝ)<2) (abs_pos.mpr hy)).trans_le hj
    have hw := (le_div_iff₀ hs).mp (wave_sin u l r t (abs_pos.mp hs))
    have hbound := mul_le_mul_of_nonneg_left hj (norm_nonneg (wave u l r t))
    rw [hcy] at hbound
    apply (le_div_iff₀ hur).mpr
    linarith
  have hden : 0<a+|t-c| := by dsimp [a];positivity
  change _ ≤ (2/(u:ℝ))*(1/(a+|t-c|))
  rw [mul_one_div]
  apply (le_div_iff₀ hden).mpr
  rw [mul_add,show (2:ℝ)/u=1/(u:ℝ)+1/(u:ℝ) by ring]
  exact add_le_add h1 h2
def pairEnv (a b : ℝ) (u v : ℕ) (z : ℕ×ℕ) (t : ℝ) : ℝ :=
  let x := (z.1:ℝ)/u
  let y := (z.2:ℝ)/v
  if sep u v z=0 then (16/((u:ℝ)*v))*(smoothKernel b x t)^2 else
    (4/((u:ℝ)*v))*(sep u v z)⁻¹*(smoothKernel a x t+smoothKernel a y t)

theorem pair_nonneg (a b : ℝ) (ha : 0≤a) (u v : ℕ) (z : ℕ×ℕ) (t : ℝ) :
    0≤pairEnv a b u v z t := by
  unfold pairEnv;split_ifs
  · positivity
  · exact mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr (abs_nonneg _))) (add_nonneg (nonneg_smoothKernel ha) (nonneg_smoothKernel ha))

theorem pair_cont (a b : ℝ) (ha : 0<a) (hb : 0<b) (u v : ℕ) (z : ℕ×ℕ) :
    Continuous (pairEnv a b u v z) := by
  unfold pairEnv
  split_ifs
  · exact continuous_const.mul ((cont_smoothKernel hb).pow 2)
  · exact continuous_const.mul ((cont_smoothKernel ha).add (cont_smoothKernel ha))


def gridNear (b : ℝ) (g : ℕ) : Set ℝ :=
  {t | ∃ j : ℕ, j ≤ g ∧ |t - (j : ℝ) / g| ≤ b}

theorem awayPoint (n u v l r k s : ℕ) (b : ℝ) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hr : r ≤ n / u) (hs : s ≤ n / v) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (gridNear b (u.gcd v))ᶜ.indicator (fun x => ‖wave u l r x * wave v k s x‖) t ≤
      ∑ z ∈ centers u v, pairEnv (1 / ((n : ℝ) + 1)) b u v z t := by
  classical
  let a : ℝ := 1/((n:ℝ)+1)
  have ha : 0<a := by dsimp [a]; positivity
  by_cases hm : t∈(gridNear b (u.gcd v))ᶜ
  · rw [Set.indicator_of_mem hm,norm_mul]
    obtain ⟨i,hi,hi'⟩ := nearestCenter u t ht.1 ht.2
    obtain ⟨j,hj,hj'⟩ := nearestCenter v t ht.1 ht.2
    let x := (i:ℝ)/u
    let y := (j:ℝ)/v
    have hby := mul_le_mul (waveBound (l:=l) hu hr hi') (waveBound (l:=k) hv hs hj') (norm_nonneg _) (mul_nonneg (by positivity) (nonneg_smoothKernel ha.le))
    change _≤(2/(u:ℝ)*smoothKernel a x t)*(2/(v:ℝ)*smoothKernel a y t) at hby
    have hpre : ‖wave u l r t‖*‖wave v k s t‖≤4/((u:ℝ)*v)*(smoothKernel a x t*smoothKernel a y t) := by
      refine hby.trans_eq ?_;ring
    refine le_trans ?_ (single_le_sum (f:=fun z=>pairEnv a b u v z t) (fun z _=>pair_nonneg a b ha.le u v z t) (show (i,j)∈centers u v from mem_product.mpr ⟨hi,hj⟩))
    change _≤pairEnv a b u v (i,j) t
    unfold pairEnv
    by_cases he : x=y
    · have hsep : sep u v (i,j)=0 := by change |x-y|=0;rw [he];simp
      rw [if_pos hsep]
      obtain ⟨h,hh,heh⟩ := commonCenter u v i j hu hv (Nat.le_of_lt_succ (mem_range.mp hi)) he
      have hdist : b < |t-x| := by
        by_contra! hsmall
        apply hm;exact ⟨h,hh,by change |t-(h:ℝ)/(u.gcd v:ℝ)|≤b;rw [←heh];exact hsmall⟩
      have hk : smoothKernel a x t≤2*smoothKernel b x t := by
        unfold smoothKernel
        have hp : 0<a+|t-x| := by positivity
        have hp' : 0<b+|t-x| := by positivity
        rw [mul_one_div]
        apply (div_le_div_iff₀ hp hp').mpr
        linarith
      rw [←he] at hpre
      calc
        _ ≤ _ := hpre
        _ ≤ 4/((u:ℝ)*v)*((2*smoothKernel b x t)*(2*smoothKernel b x t)) :=
          mul_le_mul_of_nonneg_left (mul_self_le_mul_self (nonneg_smoothKernel ha.le) hk) (by positivity)
        _ = _ := by dsimp [x];ring
    · have hsep : sep u v (i,j)≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr he)
      rw [if_neg hsep]
      exact hpre.trans ((mul_le_mul_of_nonneg_left (distinct_kernel ha he) (by positivity : 0≤4/((u:ℝ)*v))).trans_eq (by change _=4/((u:ℝ)*v)*|x-y|⁻¹*_;ring))
  · rw [Set.indicator_of_notMem hm]
    exact sum_nonneg (fun z _=>pair_nonneg a b ha.le u v z t)

theorem gridNear_measurable (b : ℝ) (g : ℕ) : MeasurableSet (gridNear b g) := by
  unfold gridNear
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases h : j≤g
  · simp only [h,true_and]
    exact measurableSet_le (f:= fun t:ℝ => |t-(j:ℝ)/g|) (g:=fun _=>b) (by fun_prop) measurable_const
  · simp [h]

private theorem pair_integral (n : ℕ) (b : ℝ) (hb : 0<b) (u v : ℕ) (hu : 0<u) (hv : 0<v)
    (z : ℕ×ℕ) (hz : z∈centers u v) :
    (∫ t in (0:ℝ)..1,pairEnv (1/((n:ℝ)+1)) b u v z t) ≤
    (32/((u:ℝ)*v*b))*(if sep u v z=0 then 1 else 0)+
      (16*Real.log ((n:ℝ)+2)/((u:ℝ)*v))*(sep u v z)⁻¹ := by
  let a : ℝ := 1/((n:ℝ)+1)
  have ha : 0<a := by dsimp [a]; positivity
  let x := (z.1:ℝ)/u
  let y := (z.2:ℝ)/v
  obtain ⟨hi,hj⟩ := mem_product.mp hz
  have hcX : x≤1 := (div_le_one (by exact_mod_cast hu)).mpr (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hi))
  have hcY : y≤1 := (div_le_one (by exact_mod_cast hv)).mpr (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hj))
  have hlog : (1+a)/a=(n:ℝ)+2 := by dsimp [a];field_simp;ring
  by_cases h : sep u v z=0
  · simp only [pairEnv,h,ite_true,inv_zero,mul_zero,add_zero,mul_one]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ (16/((u:ℝ)*v))*(2/b) := mul_le_mul_of_nonneg_left (integral_smoothKernel_sq hb (by dsimp [x];positivity) hcX) (by positivity)
      _ = _ := by ring
  · simp only [pairEnv,h,ite_false,mul_zero,zero_add]
    have hi := integral_smoothKernel ha (by dsimp [x];positivity) hcX
    have hj := integral_smoothKernel ha (by dsimp [y];positivity) hcY
    rw [hlog] at hi hj
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add ((cont_smoothKernel ha).intervalIntegrable _ _)
      ((cont_smoothKernel ha).intervalIntegrable _ _)]
    calc
      _ ≤ (4/((u:ℝ)*v))*(sep u v z)⁻¹*(4*Real.log ((n:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by positivity) (inv_nonneg.mpr (abs_nonneg _)))
      _ = _ := by ring

theorem awayBound (n u v l r k s : ℕ) (b : ℝ) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) (hun : u ≤ n) (hvn : v ≤ n)
    (hr : r ≤ n / u) (hs : s ≤ n / v) :
    (∫ t in (0 : ℝ)..1, (gridNear b (u.gcd v))ᶜ.indicator
      (fun x => ‖wave u l r x * wave v k s x‖) t) ≤
      128 * ((1 + Real.log ((n : ℝ) + 2)) ^ 2 + (u.gcd v : ℝ) / ((u : ℝ) * v * b)) := by
  let a : ℝ := 1 / ((n : ℝ) + 1)
  let W : ℝ := Real.log ((n : ℝ) + 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hw : 0 ≤ W := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have integrable : IntervalIntegrable ((gridNear b (u.gcd v))ᶜ.indicator
      (fun x => ‖wave u l r x * wave v k s x‖)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have continuous : Continuous (fun x => ‖wave u l r x * wave v k s x‖) := by
      unfold wave phase
      fun_prop
    exact (continuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (gridNear_measurable b (u.gcd v)).compl
  have pairIntegrable (z : ℕ × ℕ) :=
    (pair_cont a b ha hb u v z).intervalIntegrable (μ := volume) 0 1
  have bound := intervalIntegral.integral_mono_on zero_le_one integrable
    (IntervalIntegrable.sum (centers u v) (fun z _ => pairIntegrable z))
    (fun t ht => by simpa only [Finset.sum_apply] using awayPoint n u v l r k s b hb hu hv hr hs t ht)
  simp only [Finset.sum_apply] at bound
  rw [intervalIntegral.integral_finsetSum (fun z _ => pairIntegrable z)] at bound
  have pairBound := bound.trans (sum_le_sum (s := centers u v)
    (fun z hz => pair_integral n b hb u v hu hv z hz))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at pairBound
  have equalBound := mul_le_mul_of_nonneg_left (coincidentCount u v hu hv)
    (show 0 ≤ 32 / ((u : ℝ) * v * b) by positivity)
  have distinctBound := mul_le_mul_of_nonneg_left (spacingSum n u v hu hv hun hvn)
    (show 0 ≤ 16 * W / ((u : ℝ) * v) by positivity)
  rw [show (32 / ((u : ℝ) * v * b)) * (4 * (u.gcd v : ℝ)) =
      128 * ((u.gcd v : ℝ) / ((u : ℝ) * v * b)) by ring] at equalBound
  change _ ≤ (16 * W / ((u : ℝ) * v)) * (8 * ((u : ℝ) * v) * (1 + W)) at distinctBound
  rw [show (16 * W / ((u : ℝ) * v)) * (8 * ((u : ℝ) * v) * (1 + W)) =
      128 * W * (1 + W) by field_simp; ring] at distinctBound
  change _ ≤ 128 * ((1 + W) ^ 2 + (u.gcd v : ℝ) / ((u : ℝ) * v * b))
  have logBound : 128 * W * (1 + W) ≤ 128 * (1 + W) ^ 2 := by nlinarith only [hw]
  exact pairBound.trans (by linarith only [equalBound, distinctBound, logBound])

theorem gridNear_subset_of_dvd {g u : ℕ} (b : ℝ) (hg : 0 < g) (hu : 0 < u) (dvd : g ∣ u) :
    gridNear b g ⊆ gridNear b u := by
  intro t member
  obtain ⟨j, jBound, distance⟩ := member
  obtain ⟨k, rfl⟩ := dvd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hu
  refine ⟨j * k, Nat.mul_le_mul_right k jBound, ?_⟩
  have same : ((j * k : ℕ) : ℝ) / ((g * k : ℕ) : ℝ) = (j : ℝ) / g := by
    push_cast
    field_simp
  simpa only [same] using distance

def offWave (b : ℝ) (u l r : ℕ) : ℝ → ℂ := (gridNear b u)ᶜ.indicator (wave u l r)

theorem norm_offWave_mul_le (b : ℝ) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (l r k s : ℕ) (t : ℝ) :
    ‖offWave b u l r t * offWave b v k s t‖ ≤
      (gridNear b (u.gcd v))ᶜ.indicator (fun x => ‖wave u l r x * wave v k s x‖) t := by
  have rhsNonnegative := Set.indicator_nonneg (s := (gridNear b (u.gcd v))ᶜ)
    (f := fun x => ‖wave u l r x * wave v k s x‖) (fun _ _ => norm_nonneg _) t
  by_cases nearU : t ∈ gridNear b u
  · simpa [offWave, nearU] using rhsNonnegative
  by_cases nearV : t ∈ gridNear b v
  · simpa [offWave, nearV] using rhsNonnegative
  have nearNotGcd : t ∉ gridNear b (u.gcd v) := fun member =>
    nearU (gridNear_subset_of_dvd b (Nat.gcd_pos_of_pos_left v hu) hu (Nat.gcd_dvd_left u v) member)
  simp [offWave, nearU, nearV, nearNotGcd]


end
end DyadicMixedB4Geometric

end

section

/- Rational-centre reductions adapted from goldbach-proofs PR #2468,
revision 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/

namespace DyadicMixedB4ArcGeometry
open Finset MeasureTheory DyadicMixedB4Geometric
noncomputable section

def numSet (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)

private theorem centerSep {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (h : a*r ≠ b*q) : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q-b/r| := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  rw [show (a:ℝ)/q-b/r = (a*r-b*q)/(q*r) by field_simp, abs_div,
    abs_of_pos (mul_pos hq' hr')]
  apply (div_le_div_iff_of_pos_right (mul_pos hq' hr')).mpr
  rcases lt_or_gt_of_ne h with hab | hba
  · have hgap : (a:ℝ)*r+1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
    linarith [neg_le_abs ((a:ℝ)*r-b*q)]
  · have hgap : (b:ℝ)*q+1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
    linarith [le_abs_self ((a:ℝ)*r-b*q)]

private theorem centerEq {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (he : a*r=b*q) : q=r ∧ a=b := by
  have h₁ : q ∣ a*r := he ▸ Nat.dvd_mul_left q b
  have h₂ : r ∣ b*q := he.symm ▸ Nat.dvd_mul_left r a
  have eq := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left h₁) (hb.symm.dvd_of_dvd_mul_left h₂)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

private theorem centerOfGrid (j g : ℕ) (hg : 0<g) (hj : j≤g) :
    ∃ q ∈ g.divisors, ∃ a ∈ numSet q, (j:ℝ)/g=(a:ℝ)/q := by
  let z := j.gcd g
  have hz : 0 < z := Nat.gcd_pos_of_pos_right j hg
  have hd : z ∣ g := Nat.gcd_dvd_right j g
  have hjd : z ∣ j := Nat.gcd_dvd_left j g
  have hq : 0 < g/z := Nat.div_pos (Nat.le_of_dvd hg hd) hz
  refine ⟨g/z,Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd,hg.ne'⟩,j/z,?_,?_⟩
  · exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hj)),
      Nat.coprime_div_gcd_div_gcd hz⟩
  · apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    exact_mod_cast (show j*(g/z)=(j/z)*g from calc
      j*(g/z) = ((j/z)*z)*(g/z) := by rw [Nat.div_mul_cancel hjd]
      _ = (j/z)*((g/z)*z) := by ring
      _ = (j/z)*g := by rw [Nat.div_mul_cancel hd])

private theorem gridOfCenter {g q a : ℕ} (hq : q ∈ g.divisors) (ha : a ∈ numSet q) :
    ∃ j ≤ g, (j:ℝ)/g=(a:ℝ)/q := by
  obtain ⟨hd,hg⟩ := Nat.mem_divisors.mp hq
  have hqp := Nat.pos_of_mem_divisors hq
  have hap : a ≤ q := by have := mem_range.mp (mem_filter.mp ha).1; omega
  refine ⟨a*(g/q), ?_, ?_⟩
  · calc _ ≤ q*(g/q) := Nat.mul_le_mul_right _ hap
         _ = g := Nat.mul_div_cancel' hd
  · apply (div_eq_div_iff (by exact_mod_cast hg) (by exact_mod_cast hqp.ne')).mpr
    exact_mod_cast (show a*(g/q)*q=a*g by rw [mul_assoc,Nat.div_mul_cancel hd])

def radius (M : ℕ) : ℝ := 1 / (8 * (M : ℝ) ^ 2)

def wide (n B H : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)}

def window (n M B H q : ℕ) : Set ℝ :=
  {x | |x| ≤ radius M ∧ (B < q ∨ (H : ℝ) / ((q : ℝ) * n) < |x|)}

def cell (n M B H q a : ℕ) : Set ℝ :=
  {t | t - (a : ℝ) / q ∈ window n M B H q}

theorem radius_le_product {M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (qBound : q ≤ M) (rBound : r ≤ M) : radius M ≤ 1 / (4 * (q : ℝ) * r) := by
  have productBound : (q : ℝ) * r ≤ (M : ℝ) ^ 2 := by
    norm_cast
    rw [pow_two]
    exact Nat.mul_le_mul qBound rBound
  unfold radius
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith only [productBound, show 0 ≤ (M : ℝ) ^ 2 by positivity]

private theorem centers_eq_of_close {a b q r : ℕ} {t : ℝ} (hq : 0 < q) (hr : 0 < r)
    (nearA : |t - (a : ℝ) / q| ≤ 1 / (4 * (q : ℝ) * r))
    (nearB : |t - (b : ℝ) / r| ≤ 1 / (4 * (q : ℝ) * r)) : a * r = b * q := by
  by_contra different
  have separated := centerSep hq hr different
  have triangle := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / r)
  rw [abs_sub_comm ((a : ℝ) / q) t] at triangle
  have quotient : 1 / ((q : ℝ) * r) = 4 * (1 / (4 * (q : ℝ) * r)) := by ring
  rw [quotient] at separated
  linarith only [nearA, nearB, triangle, separated,
    show 0 < 1 / (4 * (q : ℝ) * r) by positivity]

theorem wide_at_cell_center {a q n M g B H : ℕ} {t : ℝ} (hn : 0 < n) (hg : 0 < g)
    (gBound : g ≤ M) (Bbound : B ≤ M) (smallWidth : 4 * H * M ≤ n)
    (qMember : q ∈ g.divisors) (aMember : a ∈ numSet q)
    (nearCenter : |t - (a : ℝ) / q| ≤ radius M) :
    t ∈ wide n B H ↔ q ≤ B ∧ |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n) := by
  have hq := Nat.pos_of_mem_divisors qMember
  have qBound : q ≤ M := (Nat.le_of_dvd hg (Nat.mem_divisors.mp qMember).1).trans gBound
  obtain ⟨aRange, aCoprime⟩ := mem_filter.mp aMember
  constructor
  · rintro ⟨r, b, hr, rBound, _, bCoprime, nearB⟩
    have hWidth : (H : ℝ) / ((r : ℝ) * n) ≤ 1 / (4 * (q : ℝ) * r) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have qWidth : (4 : ℝ) * H * q ≤ n := by
        exact_mod_cast (Nat.mul_le_mul_left (4 * H) qBound).trans smallWidth
      nlinarith only [mul_le_mul_of_nonneg_right qWidth (Nat.cast_nonneg (α := ℝ) r)]
    obtain ⟨rfl, rfl⟩ := centerEq hq hr aCoprime bCoprime
      (centers_eq_of_close hq hr (nearCenter.trans (radius_le_product hq hr qBound (rBound.trans Bbound)))
        (nearB.trans hWidth))
    exact ⟨rBound, nearB⟩
  · rintro ⟨qLe, near⟩
    exact ⟨q, a, hq, qLe, Nat.le_of_lt_succ (mem_range.mp aRange), aCoprime, near⟩

theorem mem_deep_cell (n M g B H : ℕ) (hn : 0 < n) (hg : 0 < g) (gBound : g ≤ M)
    (Bbound : B ≤ M) (smallWidth : 4 * H * M ≤ n) (t : ℝ) :
    t ∈ gridNear (radius M) g ∩ (wide n B H)ᶜ ↔
      ∃ q ∈ g.divisors, ∃ a ∈ numSet q, t ∈ cell n M B H q a := by
  constructor
  · rintro ⟨⟨j, jBound, near⟩, deep⟩
    obtain ⟨q, qMember, a, aMember, center⟩ := centerOfGrid j g hg jBound
    rw [center] at near
    refine ⟨q, qMember, a, aMember, near, ?_⟩
    have outside := (wide_at_cell_center hn hg gBound Bbound smallWidth qMember aMember near).not.mp deep
    simpa only [not_and_or, not_le] using outside
  · rintro ⟨q, qMember, a, aMember, near, deep⟩
    obtain ⟨j, jBound, center⟩ := gridOfCenter qMember aMember
    refine ⟨⟨j, jBound, center.symm ▸ near⟩, ?_⟩
    apply (wide_at_cell_center hn hg gBound Bbound smallWidth qMember aMember near).not.mpr
    simpa only [not_and_or, not_le] using deep

private theorem unique_deep_cell {n M g B H q r a b : ℕ} {t : ℝ} (hg : 0 < g) (gBound : g ≤ M)
    (qMember : q ∈ g.divisors) (rMember : r ∈ g.divisors)
    (aMember : a ∈ numSet q) (bMember : b ∈ numSet r)
    (htq : t ∈ cell n M B H q a) (htr : t ∈ cell n M B H r b) : q = r ∧ a = b := by
  have hq := Nat.pos_of_mem_divisors qMember
  have hr := Nat.pos_of_mem_divisors rMember
  have cap := radius_le_product hq hr
    ((Nat.le_of_dvd hg (Nat.mem_divisors.mp qMember).1).trans gBound)
    ((Nat.le_of_dvd hg (Nat.mem_divisors.mp rMember).1).trans gBound)
  exact centerEq hq hr (mem_filter.mp aMember).2 (mem_filter.mp bMember).2
    (centers_eq_of_close hq hr (htq.1.trans cap) (htr.1.trans cap))

theorem deep_cell_indicator (f : ℝ → ℂ) (n M g B H : ℕ) (hn : 0 < n) (hg : 0 < g)
    (gBound : g ≤ M) (Bbound : B ≤ M) (smallWidth : 4 * H * M ≤ n) (t : ℝ) :
    (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t =
    ∑ q ∈ g.divisors, ∑ a ∈ numSet q, (cell n M B H q a).indicator f t := by
  classical
  have description := mem_deep_cell n M g B H hn hg gBound Bbound smallWidth t
  by_cases membership : t ∈ gridNear (radius M) g ∩ (wide n B H)ᶜ
  · obtain ⟨q, qMember, a, aMember, cellMember⟩ := description.mp membership
    rw [Set.indicator_of_mem membership, sum_eq_single_of_mem q qMember]
    · rw [sum_eq_single_of_mem a aMember, Set.indicator_of_mem cellMember]
      intro b bMember different
      exact Set.indicator_of_notMem (fun h => different
        (unique_deep_cell hg gBound qMember qMember bMember aMember h cellMember).2) _
    · intro r rMember different
      apply sum_eq_zero
      intro b bMember
      exact Set.indicator_of_notMem (fun h => different
        (unique_deep_cell hg gBound rMember qMember bMember aMember h cellMember).1) _
  · rw [Set.indicator_of_notMem membership]
    symm
    apply sum_eq_zero
    intro q qMember
    apply sum_eq_zero
    intro a aMember
    exact Set.indicator_of_notMem (fun h => membership (description.mpr ⟨q, qMember, a, aMember, h⟩)) _

theorem window_empty_of_small_modulus {n M B H q R : ℕ} (hn : 0 < n) (hq : 0 < q)
    (qBound : q ≤ R) (RBound : R ≤ B) (cover : (R : ℝ) * n * radius M ≤ H) :
    window n M B H q = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have qCover : (q : ℝ) * n * radius M ≤ H := by
    refine le_trans ?_ cover
    gcongr
    unfold radius
    positivity
  have radiusBound : radius M ≤ (H : ℝ) / ((q : ℝ) * n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm (radius M)] using qCover
  exact ht.2.elim (fun h => (not_lt_of_ge (qBound.trans RBound)) h)
    (fun h => (not_lt_of_ge (ht.1.trans radiusBound)) h)


end
end DyadicMixedB4ArcGeometry

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcGeometry

namespace DyadicMixedB4ArcCenters

noncomputable section

theorem window_measurable (n M B H q : ℕ) : MeasurableSet (window n M B H q) := by
  have radiusMeasurable : MeasurableSet {x : ℝ | |x| ≤ radius M} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have widthMeasurable : MeasurableSet {x : ℝ | (H : ℝ) / ((q : ℝ) * n) < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  by_cases h : B < q
  · simpa [window, h] using radiusMeasurable
  · have eq : window n M B H q =
        {x : ℝ | |x| ≤ radius M} ∩ {x : ℝ | (H : ℝ) / ((q : ℝ) * n) < |x|} := by
        ext t
        simp [window, h]
    rw [eq]
    exact radiusMeasurable.inter widthMeasurable

theorem cell_measurable (n M B H q a : ℕ) : MeasurableSet (cell n M B H q a) :=
  (window_measurable n M B H q).preimage (measurable_id.sub measurable_const)

theorem cell_within_unit_interval {n M B H q a : ℕ} (qLower : 1 < q) (qBound : q ≤ M)
    (aMember : a ∈ numSet q) : cell n M B H q a ⊆ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨aRange, aCoprime⟩ := mem_filter.mp aMember
  have qPositive : 0 < q := by omega
  have qRealPositive : (0 : ℝ) < q := by exact_mod_cast qPositive
  have aPositive : 0 < a := by
    by_contra! zero
    have aZero : a = 0 := by omega
    subst a
    exact (by omega : q ≠ 1) (q.coprime_zero_left.mp aCoprime)
  have aLt : a < q := by
    have aLe := Nat.le_of_lt_succ (mem_range.mp aRange)
    apply lt_of_le_of_ne aLe
    intro equal
    subst a
    have impossible : q.gcd q = 1 := aCoprime
    rw [Nat.gcd_self] at impossible
    omega
  have left : 1 / (q : ℝ) ≤ (a : ℝ) / q := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast aPositive) qRealPositive.le
  have right : (a : ℝ) / q ≤ 1 - 1 / (q : ℝ) := by
    rw [show (1 : ℝ) - 1 / (q : ℝ) = ((q : ℝ) - 1) / q by field_simp]
    have space : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt aLt
    exact div_le_div_of_nonneg_right (by linarith only [space]) qRealPositive.le
  have cap : radius M ≤ 1 / (q : ℝ) := (radius_le_product qPositive (r := 1) (by decide) qBound (by omega)).trans
    (one_div_le_one_div_of_le qRealPositive (by push_cast; nlinarith only [qRealPositive]))
  intro t member
  have distance := abs_le.mp member.1
  exact ⟨by linarith only [distance.1, cap, left], by linarith only [distance.2, cap, right]⟩

private theorem integral_indicator_closed {f : ℝ → ℂ} {s : Set ℝ} {a b : ℝ}
    (ordered : a ≤ b) (measurable : MeasurableSet s) (contained : s ⊆ Set.Icc a b) :
    (∫ t in a..b, s.indicator f t) = ∫ t in s, f t := by
  rw [intervalIntegral.integral_of_le ordered, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurable, Set.inter_eq_right.mpr contained]

theorem integral_cell_translate {f : ℝ → ℂ} {n M B H q a : ℕ}
    (qLower : 1 < q) (qBound : q ≤ M) (aMember : a ∈ numSet q) :
    (∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator f t) =
      ∫ t in window n M B H q, f (t + (a : ℝ) / q) := by
  let s := cell n M B H q a
  let w := window n M B H q
  let centre := (a : ℝ) / q
  let d := radius M
  have dNonnegative : 0 ≤ d := by dsimp [d, radius]; positivity
  have measurableS : MeasurableSet s := cell_measurable n M B H q a
  have measurableW : MeasurableSet w := window_measurable n M B H q
  have containedS : s ⊆ Set.Icc (-d + centre) (d + centre) := by
    intro t ht
    have distance := abs_le.mp ht.1
    change -d ≤ t - centre ∧ t - centre ≤ d at distance
    exact ⟨by linarith only [distance.1], by linarith only [distance.2]⟩
  have containedW : w ⊆ Set.Icc (-d) d := fun t ht => abs_le.mp ht.1
  have translateIndicator (t : ℝ) : s.indicator f (t + centre) =
      w.indicator (fun x => f (x + centre)) t := by
    have memIff : t + centre ∈ s ↔ t ∈ w := by
      change t + centre - centre ∈ w ↔ _
      rw [add_sub_cancel_right]
    by_cases membership : t ∈ w
    · rw [Set.indicator_of_mem (memIff.mpr membership), Set.indicator_of_mem membership]
    · rw [Set.indicator_of_notMem (fun other => membership (memIff.mp other)), Set.indicator_of_notMem membership]
  calc
    _ = ∫ t in s, f t := integral_indicator_closed zero_le_one measurableS
      (cell_within_unit_interval qLower qBound aMember)
    _ = ∫ t in -d + centre..d + centre, s.indicator f t :=
      (integral_indicator_closed (by linarith only [dNonnegative]) measurableS containedS).symm
    _ = ∫ t in -d..d, s.indicator f (t + centre) := (intervalIntegral.integral_comp_add_right _ centre).symm
    _ = ∫ t in -d..d, w.indicator (fun x => f (x + centre)) t :=
      intervalIntegral.integral_congr fun t _ => translateIndicator t
    _ = _ := integral_indicator_closed (by linarith only [dNonnegative]) measurableW containedW

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have argument : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [argument]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)

theorem wave_at_cell_center {q g : ℕ} (qPositive : 0 < q) (divides : q ∣ g)
    (l r a : ℕ) (t : ℝ) : wave g l r (t + (a : ℝ) / q) = wave g l r t := by
  unfold wave
  refine sum_congr rfl fun j _ => ?_
  obtain ⟨v, identity⟩ := divides
  have centerTerm : ((g * j : ℕ) : ℝ) * ((a : ℝ) / q) = ((v * j * a : ℕ) : ℝ) := by
    rw [identity]
    push_cast
    field_simp
  rw [mul_add, phase_add, centerTerm, phase_nat, mul_one]

theorem integral_cell_wave {n M B H q a g : ℕ} (qLower : 1 < q) (qBound : q ≤ M)
    (aMember : a ∈ numSet q) (divides : q ∣ g) (l r : ℕ) (k : ℤ) :
    (∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator (fun x =>
      phase ((k : ℝ) * x) * wave g l r x) t) = phase ((k : ℝ) * ((a : ℝ) / q)) *
      ∫ t in window n M B H q, phase ((k : ℝ) * t) * wave g l r t := by
  rw [integral_cell_translate qLower qBound aMember, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  change phase ((k : ℝ) * (t + (a : ℝ) / q)) * wave g l r (t + (a : ℝ) / q) = _
  rw [wave_at_cell_center (by omega : 0 < q) divides, mul_add, phase_add]
  ring

def ramanujan (q : ℕ) (k : ℤ) : ℂ := ∑ a ∈ numSet q, phase ((k : ℝ) * ((a : ℝ) / q))

theorem centered_deep_wave_integral (n M B H R g l r : ℕ) (k : ℤ)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator
        (fun x => phase ((k : ℝ) * x) * wave g l r x) t) =
      ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q k *
        ∫ t in window n M B H q, phase ((k : ℝ) * t) * wave g l r t := by
  classical
  let f (x : ℝ) := phase ((k : ℝ) * x) * wave g l r x
  have fContinuous : Continuous f := by unfold f wave phase; fun_prop
  have cellIntegrable (q a : ℕ) : IntervalIntegrable ((cell n M B H q a).indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (fContinuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (cell_measurable n M B H q a)
  have split : (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) =
      ∑ q ∈ g.divisors, ∑ a ∈ numSet q, ∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, ∑ q ∈ g.divisors, ∑ a ∈ numSet q, (cell n M B H q a).indicator f t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact deep_cell_indicator f n M g B H nPositive gPositive gBound Bbound width t
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum]
        · refine sum_congr rfl fun q _ => ?_
          rw [intervalIntegral.integral_finsetSum]
          exact fun a _ => cellIntegrable q a
        · intro q _
          have integrated := IntervalIntegrable.sum (numSet q) (fun a _ => cellIntegrable q a)
          convert integrated using 1
          funext t
          simp only [Finset.sum_apply]
  change (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) = _
  rw [split, Finset.sum_filter]
  refine sum_congr rfl fun q qMember => ?_
  have qPositive := Nat.pos_of_mem_divisors qMember
  by_cases large : R < q
  · have qLower : 1 < q := Rpositive.trans_lt large
    have divides := (Nat.mem_divisors.mp qMember).1
    have qBound : q ≤ M := (Nat.le_of_dvd gPositive divides).trans gBound
    rw [if_pos large, ramanujan, sum_mul]
    exact sum_congr rfl fun a aMember => integral_cell_wave qLower qBound aMember divides l r k
  · rw [if_neg large]
    apply sum_eq_zero
    intro a _
    have emptyWindow := window_empty_of_small_modulus nPositive qPositive (le_of_not_gt large) Rbound cover
    have emptyCell : cell n M B H q a = ∅ := by simp [cell, emptyWindow]
    simp [emptyCell]


end
end DyadicMixedB4ArcCenters

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcCenters

namespace DyadicMixedB4ProgressionApprox

noncomputable section

theorem continuous_phase_scale (t : ℝ) : Continuous (fun x : ℝ => phase (x * t)) := by
  unfold phase
  fun_prop

theorem norm_phase_sub_one_le (x : ℝ) : ‖phase x - 1‖ ≤ 2 * Real.pi * |x| := by
  unfold phase
  rw [mul_comm _ Complex.I, norm_exp_phase_sub_one]
  have sinBound := Real.abs_sin_le_abs (x := Real.pi * x)
  rw [abs_mul, abs_of_pos Real.pi_pos] at sinBound
  linarith only [sinBound]

def binAverage (g : ℕ) (t : ℝ) : ℂ :=
  (g : ℂ)⁻¹ * ∫ x in -(g : ℝ) / 2..(g : ℝ) / 2, phase (x * t)

theorem norm_binAverage_sub_one (g : ℕ) (gPositive : 0 < g) (t : ℝ) :
    ‖binAverage g t - 1‖ ≤ Real.pi * (g : ℝ) * |t| := by
  have gCastPositive : (0 : ℝ) < g := by exact_mod_cast gPositive
  have gComplexNe : (g : ℂ) ≠ 0 := by exact_mod_cast gPositive.ne'
  let a : ℝ := -(g : ℝ) / 2
  let b : ℝ := (g : ℝ) / 2
  have ordered : a ≤ b := by dsimp [a, b]; linarith only [gCastPositive]
  have length : b - a = (g : ℝ) := by dsimp [a, b]; ring
  have representation : binAverage g t - 1 = (g : ℂ)⁻¹ * ∫ x in a..b, phase (x * t) - 1 := by
    have constantIntegrable : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a b := intervalIntegrable_const
    rw [intervalIntegral.integral_sub ((continuous_phase_scale t).intervalIntegrable a b) constantIntegrable,
      intervalIntegral.integral_const, length, Complex.real_smul, Complex.ofReal_natCast, mul_one, mul_sub,
      inv_mul_cancel₀ gComplexNe]
    rfl
  rw [representation, norm_mul, norm_inv, Complex.norm_natCast]
  have pointwise (x : ℝ) (member : x ∈ Set.Icc a b) :
      ‖phase (x * t) - 1‖ ≤ Real.pi * (g : ℝ) * |t| := by
    have xBound : |x| ≤ (g : ℝ) / 2 := abs_le.mpr ⟨by simpa only [a, neg_div] using member.1, member.2⟩
    refine (norm_phase_sub_one_le (x * t)).trans ?_
    rw [abs_mul]
    calc
      _ ≤ 2 * Real.pi * (((g : ℝ) / 2) * |t|) := by gcongr
      _ = _ := by ring
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) ordered
    (((continuous_phase_scale t).sub continuous_const).norm.intervalIntegrable a b)
    (intervalIntegrable_const (c := Real.pi * (g : ℝ) * |t|)) pointwise
  rw [intervalIntegral.integral_const, length, smul_eq_mul] at integralBound
  have normBound := (intervalIntegral.norm_integral_le_integral_norm (f := fun x => phase (x * t) - 1) ordered).trans
    integralBound
  calc
    _ ≤ (g : ℝ)⁻¹ * ((g : ℝ) * (Real.pi * (g : ℝ) * |t|)) :=
      mul_le_mul_of_nonneg_left normBound (inv_nonneg.mpr gCastPositive.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ gCastPositive.ne', one_mul]

theorem translate_progression_bin (g j : ℕ) (t : ℝ) :
    (∫ x in (g : ℝ) * ((j : ℝ) - 1 / 2)..(g : ℝ) * ((j : ℝ) + 1 / 2), phase (x * t)) =
      phase (((g * j : ℕ) : ℝ) * t) * ∫ x in -(g : ℝ) / 2..(g : ℝ) / 2, phase (x * t) := by
  have translation := intervalIntegral.integral_comp_add_right (fun x => phase (x * t))
    (a := -(g : ℝ) / 2) (b := (g : ℝ) / 2) (((g * j : ℕ) : ℝ))
  rw [show -(g : ℝ) / 2 + ((g * j : ℕ) : ℝ) = (g : ℝ) * ((j : ℝ) - 1 / 2) by push_cast; ring,
    show (g : ℝ) / 2 + ((g * j : ℕ) : ℝ) = (g : ℝ) * ((j : ℝ) + 1 / 2) by push_cast; ring] at translation
  rw [← translation, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change phase ((x + ((g * j : ℕ) : ℝ)) * t) = _
  rw [add_mul, phase_add, mul_comm]

def progressionAverage (g l r : ℕ) (t : ℝ) : ℂ :=
  if l ≤ r then (g : ℂ)⁻¹ *
    ∫ x in (g : ℝ) * ((l : ℝ) + 1 / 2)..(g : ℝ) * ((r : ℝ) + 1 / 2), phase (x * t) else 0

theorem progressionAverage_eq (g l r : ℕ) (t : ℝ) :
    progressionAverage g l r t = wave g l r t * binAverage g t := by
  by_cases ordered : l ≤ r
  · let endpoint (k : ℕ) := (g : ℝ) * ((k : ℝ) + 1 / 2)
    rw [progressionAverage, if_pos ordered, binAverage]
    change (g : ℂ)⁻¹ * (∫ x in endpoint l..endpoint r, phase (x * t)) = _
    rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico ordered (a := endpoint)
      (fun i _ => (continuous_phase_scale t).intervalIntegrable (endpoint i) (endpoint (i + 1)))]
    have eachBin (i : ℕ) : (∫ x in endpoint i..endpoint (i + 1), phase (x * t)) =
        phase (((g * (i + 1) : ℕ) : ℝ) * t) * ∫ x in -(g : ℝ) / 2..(g : ℝ) / 2, phase (x * t) := by
      unfold endpoint
      rw [show (g : ℝ) * ((i : ℝ) + 1 / 2) = (g : ℝ) * ((((i + 1 : ℕ) : ℝ)) - 1 / 2) by push_cast; ring]
      exact translate_progression_bin g (i + 1) t
    simp_rw [eachBin, ← sum_mul]
    have reindex : (∑ i ∈ Ico l r, phase (((g * (i + 1) : ℕ) : ℝ) * t)) = wave g l r t := by
      unfold wave
      apply sum_bij (fun i _ => i + 1)
      · intro i hi
        obtain ⟨lower, upper⟩ := mem_Ico.mp hi
        exact mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro i _ j _ equal
        omega
      · intro j hj
        obtain ⟨lower, upper⟩ := mem_Ioc.mp hj
        exact ⟨j - 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _
        rfl
    rw [reindex]
    ring
  · have empty : Ioc l r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i member
      have := mem_Ioc.mp member
      omega
    simp [progressionAverage, ordered, wave, empty]

theorem wave_local_bound {g : ℕ} (l r : ℕ) {t : ℝ} (gPositive : 0 < g) (tNonzero : t ≠ 0)
    (near : (g : ℝ) * |t| ≤ 1 / 2) : ‖wave g l r t‖ ≤ 2 / ((g : ℝ) * |t|) := by
  have gRealPositive : (0 : ℝ) < g := by exact_mod_cast gPositive
  have bound := waveBound (l := l) (u := g) (n := g * r) (i := 0) gPositive
    (by rw [Nat.mul_div_cancel_left r gPositive]) (by simpa [abs_mul, abs_of_pos gRealPositive] using near)
  calc
    _ ≤ (2 / (g : ℝ)) * smoothKernel (1 / (((g * r : ℕ) : ℝ) + 1)) 0 t := by simpa using bound
    _ ≤ (2 / (g : ℝ)) * (1 / |t|) := by
      unfold smoothKernel
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (abs_pos.mpr tNonzero) (le_add_of_nonneg_left (by positivity))) (by positivity)
    _ = _ := by ring

theorem norm_wave_sub_average_le {g : ℕ} (l r : ℕ) {t : ℝ} (gPositive : 0 < g)
    (near : (g : ℝ) * |t| ≤ 1 / 2) : ‖wave g l r t - progressionAverage g l r t‖ ≤ 2 * Real.pi := by
  rw [progressionAverage_eq, ← mul_one_sub, norm_mul, norm_sub_rev]
  have binBound := norm_binAverage_sub_one g gPositive t
  have step := mul_le_mul_of_nonneg_left binBound (norm_nonneg (wave g l r t))
  refine step.trans ?_
  by_cases tZero : t = 0
  · simp [tZero, Real.pi_pos.le]
  have prodPositive : 0 < (g : ℝ) * |t| := mul_pos (by exact_mod_cast gPositive) (abs_pos.mpr tZero)
  calc
    _ ≤ (2 / ((g : ℝ) * |t|)) * (Real.pi * (g : ℝ) * |t|) :=
      mul_le_mul_of_nonneg_right (wave_local_bound l r gPositive tZero near) (by positivity)
    _ = _ := by field_simp


end
end DyadicMixedB4ProgressionApprox

end

section

open MeasureTheory

namespace DyadicMixedB4SineKernel

noncomputable section

private theorem abs_sub_bound (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa using abs_sub_le x 0 y

theorem integral_cos_inv_sq_le {b : ℝ} (bLower : 1 ≤ b) :
    |∫ t in (1 : ℝ)..b, Real.cos t / t ^ 2| ≤ 1 := by
  have positive {t : ℝ} (member : t ∈ Set.Icc 1 b) : 0 < t :=
    zero_lt_one.trans_le member.1
  have denominator : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc 1 b) :=
    (continuous_id.pow 2).continuousOn
  have cosineContinuous : ContinuousOn (fun t => Real.cos t / t ^ 2) (Set.Icc 1 b) :=
    Real.continuous_cos.continuousOn.div denominator fun t ht => pow_ne_zero 2 (positive ht).ne'
  have inverseContinuous : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.Icc 1 b) :=
    continuousOn_const.div denominator fun t ht => pow_ne_zero 2 (positive ht).ne'
  rw [← Set.uIcc_of_le bLower] at cosineContinuous inverseContinuous
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) bLower
    cosineContinuous.abs.intervalIntegrable inverseContinuous.intervalIntegrable
    (fun t ht => by
      rw [abs_div, abs_of_nonneg (sq_nonneg t)]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t) (sq_nonneg t))
  have inverseIntegral : (∫ t in (1 : ℝ)..b, 1 / t ^ 2) = 1 - b⁻¹ := by
    calc
      _ = ∫ t in (1 : ℝ)..b, t ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [zpow_neg, zpow_ofNat, one_div]
      _ = _ := by
        rw [integral_zpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt zero_lt_one
          (zero_lt_one.trans_le bLower)⟩)]
        norm_num <;> ring
  exact (intervalIntegral.abs_integral_le_integral_abs bLower).trans
    (integralBound.trans (by rw [inverseIntegral]; exact sub_le_self _ (by positivity)))

theorem integral_sinc_tail {b : ℝ} (bLower : 1 ≤ b) :
    |∫ t in (1 : ℝ)..b, Real.sinc t| ≤ 3 := by
  let primitive (t : ℝ) := -Real.cos t / t
  let correction (t : ℝ) := Real.cos t / t ^ 2
  have positive {t : ℝ} (member : t ∈ Set.uIcc 1 b) : 0 < t := by
    rw [Set.uIcc_of_le bLower] at member
    exact zero_lt_one.trans_le member.1
  have derivative (t : ℝ) (member : t ∈ Set.uIcc 1 b) :
      HasDerivAt primitive (Real.sinc t + correction t) t := by
    have tNonzero := (positive member).ne'
    have calcDeriv := (Real.hasDerivAt_cos t).neg.div (hasDerivAt_id t) tNonzero
    convert calcDeriv using 1
    · rfl
    · rw [Real.sinc_of_ne_zero tNonzero]
      simp only [correction, id_eq, neg_neg, Pi.neg_apply]
      field_simp
      ring
  have correctionContinuous : ContinuousOn correction (Set.uIcc 1 b) :=
    Real.continuous_cos.continuousOn.div (continuous_id.pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (positive ht).ne')
  have sincInt := Real.continuous_sinc.intervalIntegrable (μ := volume) 1 b
  have correctionInt : IntervalIntegrable correction volume 1 b := correctionContinuous.intervalIntegrable
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative (sincInt.add correctionInt)
  rw [intervalIntegral.integral_add sincInt correctionInt] at integral
  have boundary (t : ℝ) (h : 1 ≤ t) : |primitive t| ≤ 1 := by
    have tPositive : 0 < t := zero_lt_one.trans_le h
    unfold primitive
    rw [abs_div, abs_neg, abs_of_pos tPositive]
    exact (div_le_one tPositive).mpr ((Real.abs_cos_le_one t).trans h)
  have exactIntegral : (∫ t in (1 : ℝ)..b, Real.sinc t) =
      (primitive b - primitive 1) - ∫ t in (1 : ℝ)..b, correction t := by linarith only [integral]
  rw [exactIntegral]
  have correctionBound : |∫ t in (1 : ℝ)..b, correction t| ≤ 1 := integral_cos_inv_sq_le bLower
  have boundaryBound := (abs_sub_bound (primitive b) (primitive 1)).trans
    (add_le_add (boundary b bLower) (boundary 1 le_rfl))
  exact (abs_sub_bound _ _).trans (by linarith only [boundaryBound, correctionBound])

private theorem integral_sinc_small {b : ℝ} (bNonnegative : 0 ≤ b) (bUpper : b ≤ 1) :
    |∫ t in (0 : ℝ)..b, Real.sinc t| ≤ 1 := by
  refine (intervalIntegral.abs_integral_le_integral_abs bNonnegative).trans ?_
  have integrated := intervalIntegral.integral_mono_on (μ := volume) bNonnegative
    (Real.continuous_sinc.abs.intervalIntegrable 0 b) intervalIntegrable_const
    (fun t _ => Real.abs_sinc_le_one t)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at integrated
  exact integrated.trans bUpper

theorem integral_sinc_from_zero (b : ℝ) : |∫ t in (0 : ℝ)..b, Real.sinc t| ≤ 4 := by
  have positiveBound (u : ℝ) (uNonnegative : 0 ≤ u) :
      |∫ t in (0 : ℝ)..u, Real.sinc t| ≤ 4 := by
    rcases le_total u 1 with small | large
    · exact (integral_sinc_small uNonnegative small).trans (by norm_num)
    rw [← intervalIntegral.integral_add_adjacent_intervals (Real.continuous_sinc.intervalIntegrable 0 1)
      (Real.continuous_sinc.intervalIntegrable 1 u)]
    have smallBound := integral_sinc_small (b := 1) zero_le_one le_rfl
    have tailBound := integral_sinc_tail large
    exact (abs_add_le _ _).trans (by linarith only [smallBound, tailBound])
  rcases le_total 0 b with bNonnegative | bNonpositive
  · exact positiveBound b bNonnegative
  have reflect := intervalIntegral.integral_comp_neg Real.sinc (a := 0) (b := -b)
  simp only [Real.sinc_neg, neg_zero, neg_neg] at reflect
  rw [intervalIntegral.integral_symm, ← reflect, abs_neg]
  exact positiveBound (-b) (neg_nonneg.mpr bNonpositive)

theorem integral_sinc_uniform (a b : ℝ) : |∫ t in a..b, Real.sinc t| ≤ 8 := by
  have partition := intervalIntegral.integral_add_adjacent_intervals
    (Real.continuous_sinc.intervalIntegrable (μ := volume) 0 a) (Real.continuous_sinc.intervalIntegrable a b)
  have subtract : (∫ t in a..b, Real.sinc t) =
      (∫ t in (0 : ℝ)..b, Real.sinc t) - ∫ t in (0 : ℝ)..a, Real.sinc t := by linarith only [partition]
  rw [subtract]
  exact (abs_sub_bound _ _).trans (by linarith only [integral_sinc_from_zero a, integral_sinc_from_zero b])

def sineKernel (B x : ℝ) : ℝ := 2 * B * Real.sinc (2 * Real.pi * B * x)

theorem sineKernel_continuous (B : ℝ) : Continuous (sineKernel B) :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

theorem integral_sineKernel_uniform (B a b : ℝ) (BNonnegative : 0 ≤ B) :
    |∫ t in a..b, sineKernel B t| ≤ 8 := by
  rcases eq_or_lt_of_le BNonnegative with zero | positive
  · simp [← zero, sineKernel]
  let dilation : ℝ := 2 * Real.pi * B
  have dilationPositive : 0 < dilation := by unfold dilation; positivity
  change |∫ t in a..b, (2 * B) * Real.sinc (dilation * t)| ≤ 8
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ dilationPositive.ne',
    smul_eq_mul, ← mul_assoc]
  have scale : (2 * B) * dilation⁻¹ = Real.pi⁻¹ := by
    unfold dilation
    field_simp [positive.ne', Real.pi_ne_zero]
  rw [scale, abs_mul, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  have divisor : Real.pi⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  calc
    _ ≤ 1 * |∫ t in dilation * a..dilation * b, Real.sinc t| :=
      mul_le_mul_of_nonneg_right divisor (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using integral_sinc_uniform (dilation * a) (dilation * b)

theorem hasDerivAt_slidingSineIntegral (B u v x : ℝ) :
    HasDerivAt (fun m => ∫ t in m + u..m + v, sineKernel B t)
      (sineKernel B (x + v) - sineKernel B (x + u)) x := by
  have primitive (y : ℝ) : HasDerivAt (fun z => ∫ t in (0 : ℝ)..z, sineKernel B t) (sineKernel B y) y :=
    intervalIntegral.integral_hasDerivAt_right ((sineKernel_continuous B).intervalIntegrable 0 y)
      (sineKernel_continuous B).aestronglyMeasurable.stronglyMeasurableAtFilter
      (sineKernel_continuous B).continuousAt
  have atV := (primitive (x + v)).comp x ((hasDerivAt_id x).add_const v)
  have atU := (primitive (x + u)).comp x ((hasDerivAt_id x).add_const u)
  have difference := atV.sub atU
  simp only [id_eq, Function.comp_def, mul_one] at difference
  have functions : (fun y => ∫ t in y + u..y + v, sineKernel B t) =
      (fun y => ∫ t in (0 : ℝ)..y + v, sineKernel B t) -
      (fun y => ∫ t in (0 : ℝ)..y + u, sineKernel B t) := by
    funext y
    have partition := intervalIntegral.integral_add_adjacent_intervals
      ((sineKernel_continuous B).intervalIntegrable (μ := volume) 0 (y + u))
      ((sineKernel_continuous B).intervalIntegrable (y + u) (y + v))
    change _ = (∫ t in (0 : ℝ)..y + v, sineKernel B t) - ∫ t in (0 : ℝ)..y + u, sineKernel B t
    linarith only [partition]
  rw [functions]
  exact difference


end
end DyadicMixedB4SineKernel

end

section

open MeasureTheory DyadicMixedB4SineKernel DyadicMixedB4Geometric

namespace DyadicMixedB4KernelVariation

noncomputable section

theorem abs_sineKernel_le (B x : ℝ) (BNonnegative : 0 ≤ B) : |sineKernel B x| ≤ 2 * B := by
  rw [sineKernel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * B)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

theorem abs_sineKernel_mul_abs_le (B x : ℝ) (BNonnegative : 0 ≤ B) : |sineKernel B x| * |x| ≤ 1 := by
  rcases eq_or_lt_of_le BNonnegative with zeroB | positiveB
  · simp [← zeroB, sineKernel]
  by_cases zeroX : x = 0
  · simp [zeroX]
  have argNonzero : 2 * Real.pi * B * x ≠ 0 := mul_ne_zero (by positivity) zeroX
  rw [sineKernel, Real.sinc_of_ne_zero argNonzero, abs_mul, abs_div,
    abs_of_pos (by positivity : 0 < 2 * B), abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi * B)]
  have absNonzero := (abs_pos.mpr zeroX).ne'
  have cancel : 2 * B * (|Real.sin (2 * Real.pi * B * x)| / (2 * Real.pi * B * |x|)) * |x| =
      |Real.sin (2 * Real.pi * B * x)| / Real.pi := by
    field_simp [positiveB.ne', Real.pi_ne_zero, absNonzero]
  rw [cancel]
  exact (div_le_one Real.pi_pos).mpr ((Real.abs_sin_le_one _).trans (by linarith [Real.pi_gt_three]))

theorem abs_sineKernel_le_smooth (B x : ℝ) (BNonnegative : 0 ≤ B) (BUpper : B ≤ 1) :
    |sineKernel B x| ≤ 3 * smoothKernel 1 0 x := by
  rw [smoothKernel, sub_zero, mul_one_div]
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_add, mul_one]
  linarith only [abs_sineKernel_le B x BNonnegative, abs_sineKernel_mul_abs_le B x BNonnegative, BUpper]

theorem exists_closer_centre (c : ℝ) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |t - r| ≤ |t - c| := by
  rcases le_total c 0 with lower | cNonnegative
  · refine ⟨0, by simp, fun t ht => ?_⟩
    rw [sub_zero, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr (lower.trans ht.1))]
    linarith only [lower]
  rcases le_total c 1 with cUpper | upper
  · exact ⟨c, ⟨cNonnegative, cUpper⟩, fun _ _ => le_rfl⟩
  · refine ⟨1, by simp, fun t ht => ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr (ht.2.trans upper))]
    linarith only [upper]

theorem integral_smoothKernel_rescale (N c : ℝ) (NPositive : 0 < N) :
    (∫ t in (0 : ℝ)..N, smoothKernel 1 c t) = ∫ t in (0 : ℝ)..1, smoothKernel N⁻¹ (c / N) t := by
  have scaling := intervalIntegral.smul_integral_comp_mul_left (smoothKernel 1 c)
    (a := 0) (b := 1) N
  rw [smul_eq_mul, mul_zero, mul_one] at scaling
  rw [← scaling, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change N * smoothKernel 1 c (N * t) = smoothKernel N⁻¹ (c / N) t
  unfold smoothKernel
  rw [show N * t - c = N * (t - c / N) by field_simp]
  rw [abs_mul, abs_of_pos NPositive, mul_one_div]
  have inversePositive : 0 < N⁻¹ := inv_pos.mpr NPositive
  field_simp

theorem integral_smoothKernel_shift_le (N c : ℝ) (NPositive : 0 < N) :
    (∫ t in (0 : ℝ)..N, smoothKernel 1 c t) ≤ 2 * Real.log (N + 1) := by
  obtain ⟨r, rMember, closer⟩ := exists_closer_centre (c / N)
  have aPositive : 0 < N⁻¹ := inv_pos.mpr NPositive
  have ratio : (1 + N⁻¹) / N⁻¹ = N + 1 := by field_simp
  rw [integral_smoothKernel_rescale N c NPositive]
  have compare := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((cont_smoothKernel aPositive (c := c / N)).intervalIntegrable 0 1)
    ((cont_smoothKernel aPositive (c := r)).intervalIntegrable 0 1) (fun t member => by
      unfold smoothKernel
      exact one_div_le_one_div_of_le (by positivity) (add_le_add_right (closer t member) _))
  have original := integral_smoothKernel aPositive rMember.1 rMember.2
  rw [ratio] at original
  exact compare.trans original

theorem integral_abs_shifted_sineKernel_le (N B x : ℝ) (NPositive : 0 < N)
    (BNonnegative : 0 ≤ B) (BUpper : B ≤ 1) :
    (∫ t in (0 : ℝ)..N, |sineKernel B (t + x)|) ≤ 6 * Real.log (N + 1) := by
  have shifted : Continuous (fun t => sineKernel B (t + x)) :=
    (sineKernel_continuous B).comp (continuous_id.add continuous_const)
  have smooth : Continuous (fun t => 3 * smoothKernel 1 (-x) t) :=
    continuous_const.mul (cont_smoothKernel zero_lt_one)
  have compare := intervalIntegral.integral_mono_on (μ := volume) NPositive.le
    (shifted.abs.intervalIntegrable 0 N) (smooth.intervalIntegrable 0 N) (fun t _ => by
      simpa only [smoothKernel, sub_zero, sub_neg_eq_add] using
        abs_sineKernel_le_smooth B (t + x) BNonnegative BUpper)
  rw [intervalIntegral.integral_const_mul] at compare
  exact compare.trans (by linarith only [integral_smoothKernel_shift_le N (-x) NPositive])

theorem integral_slidingSine_deriv_bound (N B u v : ℝ) (NPositive : 0 < N)
    (BNonnegative : 0 ≤ B) (BUpper : B ≤ 1) :
    (∫ t in (0 : ℝ)..N, |sineKernel B (t + v) - sineKernel B (t + u)|) ≤ 12 * Real.log (N + 1) := by
  have continuousShift (x : ℝ) : Continuous (fun t => sineKernel B (t + x)) :=
    (sineKernel_continuous B).comp (continuous_id.add continuous_const)
  have normSum : IntervalIntegrable (fun t => |sineKernel B (t + v)| + |sineKernel B (t + u)|) volume 0 N :=
    ((continuousShift v).abs.add (continuousShift u).abs).intervalIntegrable 0 N
  have normDifference : IntervalIntegrable (fun t => |sineKernel B (t + v) - sineKernel B (t + u)|)
      volume 0 N := ((continuousShift v).sub (continuousShift u)).abs.intervalIntegrable 0 N
  have integrated := intervalIntegral.integral_mono_on (μ := volume) NPositive.le
    normDifference normSum (fun t _ => by simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (sineKernel B (t + v)) 0 (sineKernel B (t + u))))
  rw [intervalIntegral.integral_add ((continuousShift v).abs.intervalIntegrable 0 N)
    ((continuousShift u).abs.intervalIntegrable 0 N)] at integrated
  exact integrated.trans (by linarith only [integral_abs_shifted_sineKernel_le N B v NPositive BNonnegative BUpper,
    integral_abs_shifted_sineKernel_le N B u NPositive BNonnegative BUpper])


end
end DyadicMixedB4KernelVariation

end

section

open MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcCenters
open DyadicMixedB4ProgressionApprox DyadicMixedB4SineKernel

namespace DyadicMixedB4NearKernelFourier

noncomputable section

theorem phase_integral_symmetric (B x : ℝ) :
    (∫ β in -B..B, phase (x * β)) = (sineKernel B x : ℂ) := by
  by_cases BZero : B = 0
  · simp [BZero, sineKernel]
  by_cases xZero : x = 0
  · simp only [xZero, zero_mul, phase, Complex.ofReal_zero, Complex.exp_zero, sineKernel,
      mul_zero, Real.sinc_zero, mul_one, intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  let c : ℂ := (2 * (Real.pi : ℂ) * (x : ℂ)) * Complex.I
  let θ : ℝ := 2 * Real.pi * B * x
  have cNonzero : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast xZero)) Complex.I_ne_zero
  have θNonzero : θ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) BZero) xZero
  have frequency (β : ℝ) : phase (x * β) = Complex.exp (c * (β : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have plus : c * (B : ℂ) = (θ : ℂ) * Complex.I := by unfold c θ; push_cast; ring
  have minus : c * ((-B : ℝ) : ℂ) = (-(θ : ℂ)) * Complex.I := by unfold c θ; push_cast; ring
  simp_rw [frequency]
  rw [integral_exp_mul_complex cNonzero, plus, minus, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg, sineKernel, Real.sinc_of_ne_zero θNonzero]
  push_cast
  unfold c θ
  push_cast
  field_simp [Real.pi_ne_zero, BZero, xZero, Complex.I_ne_zero]
  ring

theorem swap_phase_integral (B L R s : ℝ) :
    (∫ β in -B..B, ∫ x in L..R, phase ((s + x) * β)) =
      ∫ x in L..R, ∫ β in -B..B, phase ((s + x) * β) := by
  apply intervalIntegral_intervalIntegral_swap
  have continuous : Continuous (fun p : ℝ × ℝ => phase ((s + p.2) * p.1)) := by
    unfold phase
    fun_prop
  exact (continuous.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

theorem integrated_progressionAverage (g l r : ℕ) (B s : ℝ) (ordered : l ≤ r) :
    (∫ β in -B..B, phase (s * β) * progressionAverage g l r β) = (g : ℂ)⁻¹ *
      Complex.ofReal (∫ x in s + (g : ℝ) * ((l : ℝ) + 1 / 2)..s + (g : ℝ) * ((r : ℝ) + 1 / 2),
        sineKernel B x) := by
  let L := (g : ℝ) * ((l : ℝ) + 1 / 2)
  let R := (g : ℝ) * ((r : ℝ) + 1 / 2)
  simp_rw [progressionAverage, if_pos ordered]
  calc
    _ = (g : ℂ)⁻¹ * ∫ β in -B..B, ∫ x in L..R, phase ((s + x) * β) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro β _
      change phase (s * β) * ((g : ℂ)⁻¹ * ∫ x in L..R, phase (x * β)) = _
      rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      change phase (s * β) * phase (x * β) = phase ((s + x) * β)
      rw [add_mul, phase_add]
    _ = (g : ℂ)⁻¹ * ∫ x in L..R, ∫ β in -B..B, phase ((s + x) * β) := by rw [swap_phase_integral]
    _ = _ := by
      simp_rw [phase_integral_symmetric]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_comp_add_left]


end
end DyadicMixedB4NearKernelFourier

end

section

open MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4Geometric
open DyadicMixedB4ProgressionApprox DyadicMixedB4SineKernel DyadicMixedB4NearKernelFourier

namespace DyadicMixedB4WindowKernel

noncomputable section

def innerRadius (n M H q : ℕ) : ℝ := min (radius M) ((H : ℝ) / ((q : ℝ) * n))

theorem radius_nonnegative (M : ℕ) : 0 ≤ radius M := by unfold radius; positivity

theorem innerRadius_nonnegative (n M H q : ℕ) : 0 ≤ innerRadius n M H q := by
  unfold innerRadius
  exact le_min (radius_nonnegative M) (by positivity)

theorem window_subset_interval (n M B H q : ℕ) : window n M B H q ⊆ Set.Icc (-radius M) (radius M) :=
  fun _ member => abs_le.mp member.1

theorem set_integral_window (n M B H q : ℕ) {f : ℝ → ℂ} (continuous : Continuous f) :
    (∫ t in window n M B H q, f t) = (∫ t in -radius M..radius M, f t) -
      if q ≤ B then ∫ t in -innerRadius n M H q..innerRadius n M H q, f t else 0 := by
  let R := radius M
  let r := innerRadius n M H q
  have radiusOrdered : -R ≤ R := by have h := radius_nonnegative M; change -radius M ≤ radius M; linarith only [h]
  have innerOrdered : -r ≤ r := by
    have h := innerRadius_nonnegative n M H q
    change -innerRadius n M H q ≤ innerRadius n M H q
    linarith only [h]
  have innerCap : r ≤ R := min_le_left _ _
  have innerSubset : Set.Icc (-r) r ⊆ Set.Icc (-R) R := Set.Icc_subset_Icc (neg_le_neg innerCap) innerCap
  by_cases inside : q ≤ B
  · have setEquality : window n M B H q = Set.Icc (-R) R \ Set.Icc (-r) r := by
      ext t
      have notLarge : ¬B < q := not_lt_of_ge inside
      change (|t| ≤ R ∧ (B < q ∨ (H : ℝ) / ((q : ℝ) * n) < |t|)) ↔
        t ∈ Set.Icc (-R) R \ Set.Icc (-r) r
      simp only [notLarge, false_or, Set.mem_sdiff, Set.mem_Icc, ← abs_le, not_le]
      change (_ ∧ _) ↔ |t| ≤ R ∧ min R ((H : ℝ) / ((q : ℝ) * n)) < |t|
      rw [min_lt_iff]
      constructor
      · rintro ⟨upper, width⟩
        exact ⟨upper, Or.inr width⟩
      · rintro ⟨upper, outside | width⟩
        · exact (not_lt_of_ge upper outside).elim
        · exact ⟨upper, width⟩
    rw [setEquality, setIntegral_sdiff measurableSet_Icc continuous.continuousOn.integrableOn_Icc innerSubset,
      if_pos inside, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le radiusOrdered, ← intervalIntegral.integral_of_le innerOrdered]
  · have setEquality : window n M B H q = Set.Icc (-R) R := by
      ext t
      have large : B < q := lt_of_not_ge inside
      simp [window, large, R, ← abs_le]
    rw [setEquality, if_neg inside, sub_zero, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le radiusOrdered]

theorem norm_window_replacement_le (n M B H q g l r : ℕ) (s : ℝ) (gPositive : 0 < g)
    (radiusBound : (g : ℝ) * radius M ≤ 1 / 2) :
    ‖∫ t in window n M B H q, phase (s * t) * (wave g l r t - progressionAverage g l r t)‖ ≤
      (2 * Real.pi) * (2 * radius M) := by
  have massBound : volume (window n M B H q) ≤ volume (Set.Icc (-radius M) (radius M)) :=
    measure_mono (window_subset_interval n M B H q)
  have intervalFinite : volume (Set.Icc (-radius M) (radius M)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have massFinite : volume (window n M B H q) < ⊤ := massBound.trans_lt intervalFinite
  have realMassBound : volume.real (window n M B H q) ≤ 2 * radius M := by
    calc
      _ ≤ (volume (Set.Icc (-radius M) (radius M))).toReal :=
        ENNReal.toReal_mono intervalFinite.ne massBound
      _ = _ := by rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [radius_nonnegative M])]; ring
  have pointBound (t : ℝ) (member : t ∈ window n M B H q) :
      ‖phase (s * t) * (wave g l r t - progressionAverage g l r t)‖ ≤ 2 * Real.pi := by
    have near := (mul_le_mul_of_nonneg_left member.1 (Nat.cast_nonneg g : (0 : ℝ) ≤ g)).trans radiusBound
    rw [norm_mul, norm_phase', one_mul]
    exact norm_wave_sub_average_le l r gPositive near
  exact (norm_setIntegral_le_of_norm_le_const massFinite pointBound).trans
    (mul_le_mul_of_nonneg_left realMassBound (by positivity))

def scalarKernel (g l r : ℕ) (W s : ℝ) : ℝ :=
  if l ≤ r then (g : ℝ)⁻¹ *
    ∫ x in s + (g : ℝ) * ((l : ℝ) + 1 / 2)..s + (g : ℝ) * ((r : ℝ) + 1 / 2), sineKernel W x else 0

theorem progressionAverage_continuous (g l r : ℕ) : Continuous (progressionAverage g l r) := by
  have binIdentity (t : ℝ) : binAverage g t = (g : ℂ)⁻¹ * (sineKernel ((g : ℝ) / 2) t : ℂ) := by
    unfold binAverage
    rw [neg_div]
    simp_rw [mul_comm _ t, phase_integral_symmetric]
  change Continuous (fun t : ℝ => progressionAverage g l r t)
  simp_rw [progressionAverage_eq, binIdentity]
  have waveContinuous : Continuous (wave g l r) := by unfold wave phase; fun_prop
  exact waveContinuous.mul (continuous_const.mul (Complex.continuous_ofReal.comp (sineKernel_continuous _)))

theorem integral_progression_window (n M B H q g l r : ℕ) (s : ℝ) :
    (∫ t in window n M B H q, phase (s * t) * progressionAverage g l r t) =
      Complex.ofReal (scalarKernel g l r (radius M) s -
        if q ≤ B then scalarKernel g l r (innerRadius n M H q) s else 0) := by
  have continuous : Continuous (fun t : ℝ => phase (s * t) * progressionAverage g l r t) := by
    have left : Continuous (fun t : ℝ => phase (s * t)) := by unfold phase; fun_prop
    exact left.mul (progressionAverage_continuous g l r)
  have identify (W : ℝ) : (∫ t in -W..W, phase (s * t) * progressionAverage g l r t) =
      (scalarKernel g l r W s : ℂ) := by
    by_cases ordered : l ≤ r
    · rw [integrated_progressionAverage g l r W s ordered, scalarKernel, if_pos ordered,
        Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    · simp [progressionAverage, scalarKernel, ordered]
  rw [set_integral_window n M B H q continuous, identify]
  by_cases inside : q ≤ B
  · rw [if_pos inside, if_pos inside, identify, Complex.ofReal_sub]
  · simp [inside]


end
end DyadicMixedB4WindowKernel

end

section

open Finset MeasureTheory

namespace DyadicMixedB4Abel

theorem kernel_sum_range_bound (n : ℕ) (coefficient : ℕ → ℂ) (kernel derivative : ℝ → ℝ)
    {P K : ℝ} (PNonnegative : 0 ≤ P) (KNonnegative : 0 ≤ K)
    (prefixBound : ∀ x ≤ n, ‖∑ j ∈ range x, coefficient j‖ ≤ P)
    (endpointBound : |kernel ((n - 1 : ℕ) : ℝ)| ≤ K)
    (hasDerivative : ∀ t, HasDerivAt kernel (derivative t) t) (continuous : Continuous derivative) :
    ‖∑ j ∈ range n, kernel (j : ℝ) • coefficient j‖ ≤
      (K + ∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t|) * P := by
  have endBound : ‖kernel ((n - 1 : ℕ) : ℝ) • (∑ j ∈ range n, coefficient j)‖ ≤ K * P := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul endpointBound (prefixBound n le_rfl) (norm_nonneg _) KNonnegative
  have differenceBound (i : ℕ) : |kernel ((i + 1 : ℕ) : ℝ) - kernel (i : ℝ)| ≤
      ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), |derivative t| := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivative t)
      (continuous.intervalIntegrable (i : ℝ) ((i + 1 : ℕ) : ℝ))]
    exact intervalIntegral.abs_integral_le_integral_abs (by exact_mod_cast Nat.le_succ i)
  have integralPartition :
      (∑ i ∈ range (n - 1), ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), |derivative t|) =
        ∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t| := by
    simpa only [Nat.cast_zero] using (intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => (i : ℝ)) (n := n - 1) (μ := volume)
      (fun i _ => continuous.abs.intervalIntegrable (i : ℝ) ((i + 1 : ℕ) : ℝ)))
  have variationBound : ‖∑ i ∈ range (n - 1), (kernel ((i + 1 : ℕ) : ℝ) - kernel (i : ℝ)) •
      (∑ j ∈ range (i + 1), coefficient j)‖ ≤
      (∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t|) * P := by
    refine (norm_sum_le _ _).trans ?_
    rw [← integralPartition, sum_mul]
    refine sum_le_sum fun i iMember => ?_
    have iBound := mem_range.mp iMember
    have prefixEstimate := prefixBound (i + 1) (by omega)
    have segmentNonnegative : 0 ≤ ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), |derivative t| :=
      intervalIntegral.integral_nonneg_of_forall (by exact_mod_cast Nat.le_succ i) (fun t => abs_nonneg _)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (differenceBound i) prefixEstimate (norm_nonneg _) segmentNonnegative
  rw [Finset.sum_range_by_parts (fun j : ℕ => kernel (j : ℝ)) coefficient n]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ K * P + (∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t|) * P :=
      (add_le_add endBound variationBound)
    _ = _ := by ring


end DyadicMixedB4Abel

end

section

open MeasureTheory Finset DyadicMixedB4ArcGeometry DyadicMixedB4WindowKernel
open DyadicMixedB4SineKernel DyadicMixedB4KernelVariation

namespace DyadicMixedB4KernelControl

noncomputable section

def scalarGradient (g l r : ℕ) (W s : ℝ) : ℝ :=
  if l ≤ r then (g : ℝ)⁻¹ * (sineKernel W (s + (g : ℝ) * ((r : ℝ) + 1 / 2)) -
      sineKernel W (s + (g : ℝ) * ((l : ℝ) + 1 / 2))) else 0

theorem scalarKernel_derivative (g l r : ℕ) (W s : ℝ) :
    HasDerivAt (scalarKernel g l r W) (scalarGradient g l r W s) s := by
  unfold scalarKernel scalarGradient
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered]
    exact (hasDerivAt_slidingSineIntegral W _ _ s).const_mul (g : ℝ)⁻¹
  · simp only [if_neg ordered]
    exact hasDerivAt_const s 0

theorem scalarGradient_continuous (g l r : ℕ) (W : ℝ) : Continuous (scalarGradient g l r W) := by
  unfold scalarGradient
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered]
    exact continuous_const.mul (((sineKernel_continuous W).comp (continuous_id.add continuous_const)).sub
      ((sineKernel_continuous W).comp (continuous_id.add continuous_const)))
  · simp only [if_neg ordered]
    exact continuous_const

theorem abs_scalarKernel_le (g l r : ℕ) (W s : ℝ) (Wnonnegative : 0 ≤ W) :
    |scalarKernel g l r W s| ≤ 8 / (g : ℝ) := by
  unfold scalarKernel
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    calc
      _ ≤ (g : ℝ)⁻¹ * 8 := mul_le_mul_of_nonneg_left (integral_sineKernel_uniform W _ _ Wnonnegative)
        (inv_nonneg.mpr (Nat.cast_nonneg g))
      _ = _ := by ring
  · simp [ordered] <;> positivity

theorem scalarGradient_variation_le (g l r : ℕ) (W N shift : ℝ) (NPositive : 0 < N)
    (Wnonnegative : 0 ≤ W) (Wupper : W ≤ 1) :
    (∫ t in (0 : ℝ)..N, |scalarGradient g l r W (t + shift)|) ≤ 12 / (g : ℝ) * Real.log (N + 1) := by
  unfold scalarGradient
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g), add_assoc]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ (g : ℝ)⁻¹ * (12 * Real.log (N + 1)) :=
        mul_le_mul_of_nonneg_left (integral_slidingSine_deriv_bound N W _ _ NPositive Wnonnegative Wupper) (by positivity)
      _ = _ := by ring
  · simp only [if_neg ordered, abs_zero, intervalIntegral.integral_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith only [NPositive]))

def windowKernel (n M B H q g l r : ℕ) (s : ℝ) : ℝ := scalarKernel g l r (radius M) s -
  if q ≤ B then scalarKernel g l r (innerRadius n M H q) s else 0

def windowGradient (n M B H q g l r : ℕ) (s : ℝ) : ℝ := scalarGradient g l r (radius M) s -
  if q ≤ B then scalarGradient g l r (innerRadius n M H q) s else 0

theorem windowKernel_derivative (n M B H q g l r : ℕ) (s : ℝ) :
    HasDerivAt (windowKernel n M B H q g l r) (windowGradient n M B H q g l r s) s := by
  unfold windowKernel windowGradient
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    exact (scalarKernel_derivative g l r (radius M) s).sub (scalarKernel_derivative g l r (innerRadius n M H q) s)
  · simp only [if_neg inside, sub_zero]
    exact scalarKernel_derivative g l r (radius M) s

theorem windowGradient_continuous (n M B H q g l r : ℕ) : Continuous (windowGradient n M B H q g l r) := by
  unfold windowGradient
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    exact (scalarGradient_continuous g l r (radius M)).sub (scalarGradient_continuous g l r (innerRadius n M H q))
  · simp only [if_neg inside, sub_zero]
    exact scalarGradient_continuous g l r (radius M)

theorem abs_windowKernel_le (n M B H q g l r : ℕ) (s : ℝ) :
    |windowKernel n M B H q g l r s| ≤ 16 / (g : ℝ) := by
  unfold windowKernel
  have first := abs_scalarKernel_le g l r (radius M) s (radius_nonnegative M)
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    have second := abs_scalarKernel_le g l r (innerRadius n M H q) s (innerRadius_nonnegative n M H q)
    have difference : |scalarKernel g l r (radius M) s - scalarKernel g l r (innerRadius n M H q) s| ≤
        |scalarKernel g l r (radius M) s| + |scalarKernel g l r (innerRadius n M H q) s| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (scalarKernel g l r (radius M) s) 0 (scalarKernel g l r (innerRadius n M H q) s))
    refine difference.trans ?_
    rw [show (16 : ℝ) / g = 8 / g + 8 / g by ring]
    exact add_le_add first second
  · simp only [if_neg inside, sub_zero]
    exact first.trans (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))

theorem windowGradient_variation_le (n M B H q g l r : ℕ) (N shift : ℝ) (NPositive : 0 < N)
    (radiusUpper : radius M ≤ 1) :
    (∫ t in (0 : ℝ)..N, |windowGradient n M B H q g l r (t + shift)|) ≤
      24 / (g : ℝ) * Real.log (N + 1) := by
  let first (t : ℝ) := scalarGradient g l r (radius M) (t + shift)
  let second (t : ℝ) := scalarGradient g l r (innerRadius n M H q) (t + shift)
  have firstContinuous : Continuous first :=
    (scalarGradient_continuous g l r (radius M)).comp (continuous_id.add continuous_const)
  have secondContinuous : Continuous second :=
    (scalarGradient_continuous g l r (innerRadius n M H q)).comp (continuous_id.add continuous_const)
  have boundFirst := scalarGradient_variation_le g l r (radius M) N shift NPositive (radius_nonnegative M) radiusUpper
  have logNonnegative : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith only [NPositive])
  unfold windowGradient
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    have boundSecond := scalarGradient_variation_le g l r (innerRadius n M H q) N shift NPositive
      (innerRadius_nonnegative n M H q) ((min_le_left _ _).trans radiusUpper)
    change (∫ t in (0 : ℝ)..N, |first t - second t|) ≤ _
    have differenceIntegrable : IntervalIntegrable (fun t => |first t - second t|) volume 0 N :=
      (firstContinuous.sub secondContinuous).abs.intervalIntegrable 0 N
    have sumIntegrable : IntervalIntegrable (fun t => |first t| + |second t|) volume 0 N :=
      (firstContinuous.abs.add secondContinuous.abs).intervalIntegrable 0 N
    have compare := intervalIntegral.integral_mono_on NPositive.le differenceIntegrable sumIntegrable
      (fun t _ => by simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (first t) 0 (second t)))
    rw [intervalIntegral.integral_add (firstContinuous.abs.intervalIntegrable 0 N)
      (secondContinuous.abs.intervalIntegrable 0 N)] at compare
    apply compare.trans
    rw [show (24 : ℝ) / g * Real.log (N + 1) =
      12 / g * Real.log (N + 1) + 12 / g * Real.log (N + 1) by ring]
    exact add_le_add boundFirst boundSecond
  · simp only [if_neg inside, sub_zero]
    exact boundFirst.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)) logNonnegative)

theorem weighted_windowKernel_sum_le (n M B H q g l r a X : ℕ) (coefficient : ℕ → ℂ)
    (nPositive : 0 < n) (aPositive : 0 < a) (lengthBound : a * X ≤ n)
    (radiusUpper : radius M ≤ 1) {P : ℝ} (PNonnegative : 0 ≤ P)
    (prefixBound : ∀ x ≤ X, ‖∑ j ∈ range x, coefficient j‖ ≤ P) :
    ‖∑ j ∈ range X, windowKernel n M B H q g l r ((a : ℝ) * ((j : ℝ) + 1) - n) • coefficient j‖ ≤
      (16 / (g : ℝ) + 24 / (g : ℝ) * Real.log ((n : ℝ) + 1)) * P := by
  let shift : ℝ := (a : ℝ) - n
  let f (t : ℝ) := windowKernel n M B H q g l r ((a : ℝ) * t + shift)
  let D (t : ℝ) := windowGradient n M B H q g l r ((a : ℝ) * t + shift) * (a : ℝ)
  have aRealPositive : (0 : ℝ) < a := by exact_mod_cast aPositive
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have fDerivative (t : ℝ) : HasDerivAt f (D t) t := by
    have linear := ((hasDerivAt_id t).const_mul (a : ℝ)).add_const shift
    simp only [id_eq, mul_one] at linear
    exact (windowKernel_derivative n M B H q g l r ((a : ℝ) * t + shift)).comp t linear
  have DContinuous : Continuous D :=
    ((windowGradient_continuous n M B H q g l r).comp
      ((continuous_const.mul continuous_id).add continuous_const)).mul continuous_const
  let upper : ℝ := ((X - 1 : ℕ) : ℝ)
  have compareUpper : (a : ℝ) * upper ≤ n := by
    dsimp [upper]
    exact_mod_cast (Nat.mul_le_mul_left a (Nat.sub_le X 1)).trans lengthBound
  have variationBound : (∫ t in (0 : ℝ)..upper, |D t|) ≤ 24 / (g : ℝ) * Real.log ((n : ℝ) + 1) := by
    let gradient (t : ℝ) := |windowGradient n M B H q g l r (t + shift)|
    have gradientContinuous : Continuous gradient :=
      ((windowGradient_continuous n M B H q g l r).comp (continuous_id.add continuous_const)).abs
    have scaling := intervalIntegral.smul_integral_comp_mul_left gradient (a := 0) (b := upper) (a : ℝ)
    rw [smul_eq_mul, mul_zero] at scaling
    calc
      _ = (a : ℝ) * ∫ t in (0 : ℝ)..upper, gradient ((a : ℝ) * t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        change |windowGradient n M B H q g l r ((a : ℝ) * t + shift) * (a : ℝ)| = _
        rw [abs_mul, abs_of_pos aRealPositive, mul_comm]
      _ = ∫ t in (0 : ℝ)..(a : ℝ) * upper, gradient t := scaling
      _ ≤ ∫ t in (0 : ℝ)..n, gradient t := intervalIntegral.integral_mono_interval le_rfl (by positivity)
        compareUpper (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (gradientContinuous.intervalIntegrable _ _)
      _ ≤ _ := windowGradient_variation_le n M B H q g l r n shift nRealPositive radiusUpper
  have kernelBound := DyadicMixedB4Abel.kernel_sum_range_bound X coefficient f D PNonnegative
    (show 0 ≤ 16 / (g : ℝ) by positivity) prefixBound
    (abs_windowKernel_le n M B H q g l r _) fDerivative DContinuous
  have sameArgument (j : ℕ) : (a : ℝ) * ((j : ℝ) + 1) - n = (a : ℝ) * (j : ℝ) + shift := by
    unfold shift
    ring
  simp_rw [sameArgument]
  change ‖∑ j ∈ range X, f (j : ℝ) • coefficient j‖ ≤ _
  exact kernelBound.trans (mul_le_mul_of_nonneg_right (add_le_add_right variationBound _) PNonnegative)


end
end DyadicMixedB4KernelControl

end

section

open Finset MeasureTheory
open scoped ComplexConjugate

namespace DyadicMixedB4Fourier

noncomputable section

def frequency (k : ℤ) : ℂ := (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

def mode (k : ℤ) (t : ℝ) : ℂ := Complex.exp (frequency k * (t : ℂ))

theorem continuous_mode (k : ℤ) : Continuous (mode k) := by
  unfold mode
  fun_prop

theorem periodic_mode (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  unfold mode
  rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, Complex.exp_add]
  have onePhase : Complex.exp (frequency k * 1) = 1 := by
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]
  rw [onePhase, mul_one]

theorem hasDerivAt_mode (k : ℤ) (t : ℝ) :
    HasDerivAt (mode k) (frequency k * mode k t) t := by
  have linear : HasDerivAt (fun z : ℂ => frequency k * z) (frequency k) (t : ℂ) := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (t : ℂ)).const_mul (frequency k)
  change HasDerivAt (fun x : ℝ => Complex.exp (frequency k * (x : ℂ)))
    (frequency k * Complex.exp (frequency k * (t : ℂ))) t
  rw [mul_comm (frequency k)]
  exact linear.cexp.comp_ofReal (z := t)

theorem mode_integral (k : ℤ) :
    (∫ t in (0 : ℝ)..1, mode k t) = if k = 0 then 1 else 0 := by
  by_cases zero : k = 0
  · simp [zero, mode, frequency]
  · have kNonzero : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have frequencyNonzero : frequency k ≠ 0 := by
      exact mul_ne_zero kNonzero (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero) Complex.I_ne_zero)
    change (∫ t in (0 : ℝ)..1, Complex.exp (frequency k * (t : ℂ))) = _
    rw [ite_eq_right zero, integral_exp_mul_complex frequencyNonzero]
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]

theorem mode_mul_conj (j k : ℤ) (t : ℝ) :
    mode j t * star (mode k t) = mode (j - k) t := by
  change Complex.exp (frequency j * (t : ℂ)) *
    conj (Complex.exp (frequency k * (t : ℂ))) = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  unfold mode frequency
  congr 1
  have conjTwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp [map_mul, Complex.conj_I, Int.cast_sub, conjTwo]
  ring

theorem parseval_finite_modes (limit : ℕ) (coefficient : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1,
      ((‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ j ∈ range limit, ((‖coefficient j‖ ^ 2 : ℝ) : ℂ) := by
  let entry (j k : ℕ) (t : ℝ) : ℂ :=
    coefficient j * star (coefficient k) * mode ((j : ℤ) - (k : ℤ)) t
  have entryContinuous (j k : ℕ) : Continuous (entry j k) :=
    continuous_const.mul (continuous_mode ((j : ℤ) - (k : ℤ)))
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ j ∈ range limit, ∑ k ∈ range limit, entry j k t := by
      apply intervalIntegral.integral_congr
      intro t _
      change ((‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2 : ℝ) : ℂ) = _
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      change (∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) *
          star (∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) = _
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      rw [star_mul]
      calc
        _ = coefficient j * star (coefficient k) *
            (mode (j : ℤ) t * star (mode (k : ℤ) t)) := by ac_rfl
        _ = _ := by rw [mode_mul_conj]
    _ = ∑ j ∈ range limit, ∑ k ∈ range limit, ∫ t in (0 : ℝ)..1, entry j k t := by
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        exact fun k _ => (entryContinuous j k).intervalIntegrable _ _
      · intro j _
        exact (continuous_finsetSum _ fun k _ => entryContinuous j k).intervalIntegrable _ _
    _ = _ := by
      refine sum_congr rfl fun j jMember => ?_
      rw [sum_eq_single_of_mem j jMember]
      · simp [entry, intervalIntegral.integral_const_mul, mode_integral, Complex.mul_conj']
      · intro k _ different
        have frequencyNonzero : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [entry, intervalIntegral.integral_const_mul, mode_integral, frequencyNonzero]

theorem periodic_mode_sum (limit : ℕ) (coefficient : ℕ → ℂ) :
    Function.Periodic (fun t => ∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) 1 := by
  intro t
  refine sum_congr rfl fun j _ => ?_
  rw [periodic_mode]

theorem hasDerivAt_mode_sum (limit : ℕ) (coefficient : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun x => ∑ j ∈ range limit, coefficient j * mode (j : ℤ) x)
      (∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t) t := by
  apply HasDerivAt.fun_sum
  intro j _
  simpa only [mul_assoc] using (hasDerivAt_mode (j : ℤ) t).const_mul (coefficient j)


end
end DyadicMixedB4Fourier

end

section

open Finset MeasureTheory Set

namespace DyadicMixedB4Sampling

theorem sample_mul_length_le_integrals {f gradient : ℝ → ℝ} {a b centre : ℝ}
    (derivative : ∀ x, HasDerivAt f (gradient x) x) (gradientContinuous : Continuous gradient)
    (centreLower : a ≤ centre) (centreUpper : centre ≤ b) :
    (b - a) * f centre ≤ (∫ x in a..b, f x) + (b - a) * ∫ x in a..b, |gradient x| := by
  have fDifferentiable : Differentiable ℝ f := fun x => (derivative x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  let variation : ℝ := ∫ x in a..b, |gradient x|
  have difference {x y : ℝ} (left : a ≤ x) (ordered : x ≤ y) (right : y ≤ b) :
      |f y - f x| ≤ variation := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => derivative z)
      (gradientContinuous.intervalIntegrable x y)]
    exact (intervalIntegral.abs_integral_le_integral_abs ordered).trans
      (intervalIntegral.integral_mono_interval left ordered right
        (Filter.Eventually.of_forall fun z => abs_nonneg (gradient z))
        (gradientContinuous.abs.intervalIntegrable a b))
  have pointwise (x : ℝ) (membership : x ∈ Icc a b) : f centre ≤ f x + variation := by
    have absoluteDifference : |f centre - f x| ≤ variation := by
      rcases le_total x centre with ordered | ordered
      · exact difference membership.1 ordered centreUpper
      · rw [abs_sub_comm]
        exact difference centreLower ordered membership.2
    linarith only [absoluteDifference, le_abs_self (f centre - f x)]
  have integrated := intervalIntegral.integral_mono_on (μ := volume) (centreLower.trans centreUpper)
    ((continuous_const : Continuous fun _ : ℝ => f centre).intervalIntegrable a b)
    ((fContinuous.add continuous_const).intervalIntegrable a b) pointwise
  change (∫ _ in a..b, f centre) ≤ (∫ x in a..b, f x + variation) at integrated
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (fContinuous.intervalIntegrable a b)
      ((continuous_const : Continuous fun _ : ℝ => variation).intervalIntegrable a b),
    intervalIntegral.integral_const] at integrated
  simpa only [variation, smul_eq_mul] using integrated

theorem separated_samples_le_integrals {f gradient : ℝ → ℝ} {a b radius : ℝ}
    (points : Finset ℝ) (ordered : a ≤ b) (radiusPositive : 0 < radius)
    (windowFits : ∀ x ∈ points, a ≤ x - radius ∧ x + radius ≤ b)
    (separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|))
    (fNonnegative : ∀ x, 0 ≤ f x) (derivative : ∀ x, HasDerivAt f (gradient x) x)
    (gradientContinuous : Continuous gradient) :
    (2 * radius) * (∑ x ∈ points, f x) ≤
      (∫ x in a..b, f x) + (2 * radius) * ∫ x in a..b, |gradient x| := by
  classical
  let window (x : ℝ) := Ioc (x - radius) (x + radius)
  have windowOrdered (x : ℝ) : x - radius ≤ x + radius := by linarith
  have disjoint : Set.Pairwise (points : Set ℝ) (fun x y => Disjoint (window x) (window y)) := by
    intro x xMember y yMember distinct
    rw [Set.disjoint_left]
    intro z inX inY
    have hx : x - radius < z ∧ z ≤ x + radius := inX
    have hy : y - radius < z ∧ z ≤ y + radius := inY
    have close : |x - y| < 2 * radius := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    exact (not_lt_of_ge (separated xMember yMember distinct)) close
  have unionFits : (⋃ x ∈ points, window x) ⊆ Ioc a b := by
    intro z membership
    obtain ⟨x, atPoint, inside⟩ := Set.mem_iUnion₂.mp membership
    obtain ⟨left, right⟩ := windowFits x atPoint
    exact Ioc_subset_Ioc left right inside
  have compare {g : ℝ → ℝ} (gContinuous : Continuous g) (gNonnegative : ∀ x, 0 ≤ g x) :
      (∑ x ∈ points, ∫ t in x - radius..x + radius, g t) ≤ ∫ t in a..b, g t := by
    calc
      _ = ∫ t in ⋃ x ∈ points, window x, g t := by
        rw [integral_biUnion_finset points (fun x _ => measurableSet_Ioc) disjoint
          (fun x _ => (gContinuous.intervalIntegrable (x - radius) (x + radius)).1)]
        exact sum_congr rfl fun x _ => intervalIntegral.integral_of_le (windowOrdered x)
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le ordered]
        exact setIntegral_mono_set (gContinuous.intervalIntegrable a b).1
          (Filter.Eventually.of_forall gNonnegative) unionFits.eventuallySubset
  have fDifferentiable : Differentiable ℝ f := fun x => (derivative x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  calc
    _ = ∑ x ∈ points, (2 * radius) * f x := mul_sum points _ _
    _ ≤ ∑ x ∈ points, ((∫ t in x - radius..x + radius, f t) +
        (2 * radius) * (∫ t in x - radius..x + radius, |gradient t|)) := by
      refine sum_le_sum fun x _ => ?_
      have localInequality := sample_mul_length_le_integrals derivative gradientContinuous
        (by linarith : x - radius ≤ x) (by linarith : x ≤ x + radius)
      rwa [show x + radius - (x - radius) = 2 * radius by ring] at localInequality
    _ = (∑ x ∈ points, ∫ t in x - radius..x + radius, f t) +
        (2 * radius) * (∑ x ∈ points, ∫ t in x - radius..x + radius, |gradient t|) := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add (compare fContinuous fNonnegative)
      (mul_le_mul_of_nonneg_left (compare gradientContinuous.abs fun t => abs_nonneg (gradient t))
        (by positivity))


end DyadicMixedB4Sampling

end

section

open Finset Set
open scoped RealInnerProductSpace

namespace DyadicMixedB4Fourier

noncomputable section

theorem integral_three_periods {f : ℝ → ℝ} (continuous : Continuous f)
    (periodic : Function.Periodic f 1) :
    (∫ t in (-1 : ℝ)..2, f t) = 3 * ∫ t in (0 : ℝ)..1, f t := by
  have shift (a b : ℝ) : (∫ t in a..b, f t) = ∫ t in a + 1..b + 1, f t := by
    calc
      _ = ∫ t in a..b, f (t + 1) := intervalIntegral.integral_congr fun t _ => (periodic t).symm
      _ = _ := intervalIntegral.integral_comp_add_right f 1
  have first : (∫ t in (-1 : ℝ)..0, f t) = ∫ t in (0 : ℝ)..1, f t := by
    convert shift (-1) 0 using 2 <;> norm_num
  have last : (∫ t in (0 : ℝ)..1, f t) = ∫ t in (1 : ℝ)..2, f t := by
    convert shift 0 1 using 2 <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable (-1) 1)
      (continuous.intervalIntegrable 1 2),
    ← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable (-1) 0)
      (continuous.intervalIntegrable 0 1), first, ← last]
  ring

theorem parseval_real (limit : ℕ) (coefficient : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2) =
      ∑ j ∈ range limit, ‖coefficient j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, ← intervalIntegral.integral_ofReal]
  exact parseval_finite_modes limit coefficient

theorem norm_frequency_nat (j : ℕ) : ‖frequency (j : ℤ)‖ = (j : ℝ) * (2 * Real.pi) := by
  rw [frequency, Int.cast_natCast, norm_mul, Complex.norm_natCast, norm_mul, Complex.norm_I,
    mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

theorem additive_large_sieve (limit : ℕ) (coefficient : ℕ → ℂ) (points : Finset ℝ)
    {radius : ℝ} (radiusPositive : 0 < radius) (radiusUpper : radius ≤ 1)
    (unitInterval : (points : Set ℝ) ⊆ Icc 0 1)
    (separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|)) :
    (∑ x ∈ points, ‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) x‖ ^ 2) ≤
      (3 / (2 * radius) + 6 * (1 + 2 * Real.pi * limit)) *
        ∑ j ∈ range limit, ‖coefficient j‖ ^ 2 := by
  let polynomial (t : ℝ) := ∑ j ∈ range limit, coefficient j * mode (j : ℤ) t
  let derivativePolynomial (t : ℝ) :=
    ∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t
  let energy (t : ℝ) := ‖polynomial t‖ ^ 2
  let derivativeEnergy (t : ℝ) := ‖derivativePolynomial t‖ ^ 2
  let variation (t : ℝ) := 2 * ⟪polynomial t, derivativePolynomial t⟫
  let band : ℝ := 1 + 2 * Real.pi * limit
  let mass := ∑ j ∈ range limit, ‖coefficient j‖ ^ 2
  have bandPositive : 0 < band := by dsimp [band]; positivity
  have polynomialDerivative (t : ℝ) : HasDerivAt polynomial (derivativePolynomial t) t :=
    hasDerivAt_mode_sum limit coefficient t
  have energyDerivative (t : ℝ) : HasDerivAt energy (variation t) t :=
    (polynomialDerivative t).norm_sq
  have polynomialContinuous : Continuous polynomial :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_mode (j : ℤ))
  have derivativeContinuous : Continuous derivativePolynomial :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_mode (j : ℤ))
  have energyContinuous : Continuous energy := polynomialContinuous.norm.pow 2
  have derivativeEnergyContinuous : Continuous derivativeEnergy := derivativeContinuous.norm.pow 2
  have variationContinuous : Continuous variation :=
    continuous_const.mul (polynomialContinuous.inner derivativeContinuous)
  have polynomialPeriodic : Function.Periodic polynomial 1 := periodic_mode_sum limit coefficient
  have derivativePeriodic : Function.Periodic derivativePolynomial 1 := periodic_mode_sum limit _
  have energyPeriodic : Function.Periodic energy 1 := fun t => by
    unfold energy
    rw [polynomialPeriodic]
  have variationPeriodic : Function.Periodic (fun t => |variation t|) 1 := fun t => by
    change |variation (t + 1)| = |variation t|
    dsimp only [variation]
    rw [polynomialPeriodic, derivativePeriodic]
  have energyIntegral : (∫ t in (0 : ℝ)..1, energy t) = mass := parseval_real limit coefficient
  have derivativeIntegral : (∫ t in (0 : ℝ)..1, derivativeEnergy t) ≤ band ^ 2 * mass := by
    change (∫ t in (0 : ℝ)..1,
      ‖∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t‖ ^ 2) ≤ _
    rw [parseval_real]
    unfold mass
    rw [mul_sum]
    refine sum_le_sum fun j member => ?_
    have jBound : (j : ℝ) ≤ limit := by exact_mod_cast (mem_range.mp member).le
    have frequencyBound : ‖frequency (j : ℤ)‖ ≤ band := by
      rw [norm_frequency_nat]
      dsimp [band]
      nlinarith [mul_nonneg (sub_nonneg.mpr jBound) Real.pi_pos.le]
    calc
      _ = ‖frequency (j : ℤ)‖ ^ 2 * ‖coefficient j‖ ^ 2 := by rw [norm_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) frequencyBound 2) (sq_nonneg _)
  have pointwise (t : ℝ) : |variation t| ≤ band * energy t + band⁻¹ * derivativeEnergy t := by
    have quadratic : 2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ ≤
        band * energy t + band⁻¹ * derivativeEnergy t := by
      have square := sq_nonneg (band * ‖polynomial t‖ - ‖derivativePolynomial t‖)
      have multiplied :
          (2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ - band * energy t) * band ≤
            derivativeEnergy t := by
        dsimp [energy, derivativeEnergy]
        nlinarith only [square]
      have divided := (le_div_iff₀ bandPositive).mpr multiplied
      rw [inv_mul_eq_div]
      linarith only [divided]
    calc
      _ ≤ 2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ := by
        unfold variation
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ _ := quadratic
  have variationIntegral : (∫ t in (0 : ℝ)..1, |variation t|) ≤ 2 * band * mass := by
    have scaledEnergy : IntervalIntegrable (fun t => band * energy t)
        MeasureTheory.volume 0 1 := (continuous_const.mul energyContinuous).intervalIntegrable 0 1
    have scaledDerivative : IntervalIntegrable (fun t => band⁻¹ * derivativeEnergy t)
        MeasureTheory.volume 0 1 := (continuous_const.mul derivativeEnergyContinuous).intervalIntegrable 0 1
    have integrated := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num : (0 : ℝ) ≤ 1)
      (variationContinuous.abs.intervalIntegrable 0 1)
      (((continuous_const.mul energyContinuous).add
        (continuous_const.mul derivativeEnergyContinuous)).intervalIntegrable 0 1)
      (fun t _ => pointwise t)
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, band * energy t + band⁻¹ * derivativeEnergy t := integrated
      _ = band * mass + band⁻¹ * ∫ t in (0 : ℝ)..1, derivativeEnergy t := by
        rw [intervalIntegral.integral_add scaledEnergy scaledDerivative,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, energyIntegral]
      _ ≤ band * mass + band⁻¹ * (band ^ 2 * mass) :=
        (add_le_add_right (mul_le_mul_of_nonneg_left derivativeIntegral (inv_nonneg.mpr bandPositive.le)) _)
      _ = _ := by field_simp [bandPositive.ne']; ring
  have windowFits (t : ℝ) (member : t ∈ points) : -1 ≤ t - radius ∧ t + radius ≤ 2 := by
    obtain ⟨lower, upper⟩ := unitInterval member
    constructor <;> linarith
  have samples := DyadicMixedB4Sampling.separated_samples_le_integrals points
    (by norm_num : (-1 : ℝ) ≤ 2) radiusPositive windowFits separated
    (fun t => sq_nonneg ‖polynomial t‖) energyDerivative variationContinuous
  rw [integral_three_periods energyContinuous energyPeriodic, energyIntegral,
    integral_three_periods variationContinuous.abs variationPeriodic] at samples
  change (∑ t ∈ points, energy t) ≤ (3 / (2 * radius) + 6 * band) * mass
  have multiplied : (∑ t ∈ points, energy t) * (2 * radius) ≤
      3 * mass + (2 * radius) * (3 * (2 * band * mass)) := by
    rw [mul_comm]
    exact samples.trans (by gcongr)
  calc
    _ ≤ (3 * mass + (2 * radius) * (3 * (2 * band * mass))) / (2 * radius) :=
      (le_div_iff₀ (by positivity)).mpr multiplied
    _ = _ := by field_simp [radiusPositive.ne']; ring


end
end DyadicMixedB4Fourier

end

section

/- Adapted from the corresponding Additive, Farey, CharacterSums, and
CharacterOrthogonality modules of kimihiro64/bombieri-vinogradov
at 7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0).
The original notices are retained. The imports have been combined. -/


/-!
# Rational spacing for the additive large sieve

Reduced rational points with denominators at most `Q` are separated by at
least `1 / Q^2`.  This is the arithmetic spacing input in Vaughan's additive
large-sieve theorem.
-/


namespace BombieriVinogradov.LargeSieve

/-- A nonzero rational with denominator at most `D` has absolute value at least `1 / D`. -/
theorem ratAbsLowerBound {D : Nat} (hD : 0 < D) {z : Rat}
    (hzden : z.den <= D) (hz : Ne z 0) :
    (1 : Real) / (D : Real) <= |(z : Real)| := by
  have hnumNat : 1 <= z.num.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hz))
  have hnum : (1 : Real) <= |(z.num : Real)| := by
    calc
      (1 : Real) <= (z.num.natAbs : Real) := by exact_mod_cast hnumNat
      _ = |(z.num : Real)| := by simp
  have hDReal : 0 < (D : Real) := by exact_mod_cast hD
  have hdenReal : 0 < (z.den : Real) := by exact_mod_cast z.den_pos
  have hrecip : (1 : Real) / (D : Real) <= 1 / (z.den : Real) := by
    gcongr
  calc
    (1 : Real) / (D : Real) <= 1 / (z.den : Real) := hrecip
    _ <= |(z.num : Real)| / (z.den : Real) := by gcongr
    _ = |(z : Real)| := by
      rw [Rat.cast_def, abs_div, abs_of_pos hdenReal]

/-- Distinct rationals with denominators at most `Q` are at least `1 / Q^2` apart. -/
theorem ratAbsSubLowerBound {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx : x.den <= Q) (hy : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= |(x : Real) - (y : Real)| := by
  let z : Rat := x - y
  have hz : Ne z 0 := sub_ne_zero.mpr hxy
  have hden : z.den <= x.den * y.den :=
    Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
  have hdenQ : z.den <= Q ^ 2 := by
    calc
      z.den <= x.den * y.den := hden
      _ <= Q * Q := Nat.mul_le_mul hx hy
      _ = Q ^ 2 := by ring
  simpa [z, Nat.cast_pow] using
    ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hdenQ hz

/-- Circular distance between representatives in the half-open interval `[0, 1)`. -/
def ratCircleDistance (x y : Rat) : Real :=
  min |(x : Real) - (y : Real)| (1 - |(x : Real) - (y : Real)|)

/-- Farey-type rationals in `[0, 1)` remain `1 / Q^2` apart around the circle. -/
theorem ratCircleSeparation {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx0 : 0 <= x) (hx1 : x < 1) (hy0 : 0 <= y) (hy1 : y < 1)
    (hxden : x.den <= Q) (hyden : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance x y := by
  have hlinear := ratAbsSubLowerBound hQ hxden hyden hxy
  have hsub_lt_one : |x - y| < (1 : Rat) := by
    rw [abs_lt]
    constructor <;> linarith
  let w : Rat := 1 - |x - y|
  have hwpos : 0 < w := sub_pos.mpr hsub_lt_one
  have hwden : w.den <= Q ^ 2 := by
    have hxyden : (x - y).den <= Q ^ 2 := by
      apply Nat.le_trans
      · exact Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
      · simpa [pow_two] using Nat.mul_le_mul hxden hyden
    simpa [w] using hxyden
  have hcircular : (1 : Real) / (Q : Real) ^ 2 <= |(w : Real)| := by
    simpa only [Nat.cast_pow] using
      ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hwden hwpos.ne'
  have hwcast : |(w : Real)| = 1 - |(x : Real) - (y : Real)| := by
    rw [abs_of_pos]
    · simp [w]
    · exact_mod_cast hwpos
  rw [ratCircleDistance, le_min_iff]
  exact And.intro hlinear (hwcast ▸ hcircular)

end BombieriVinogradov.LargeSieve

/-!
# Reduced Farey points for the additive large sieve

This module packages the reduced fractions `a / q`, with `1 <= q <= Q` and
`a` a unit modulo `q`, and proves their circular `1 / Q^2` separation.
-/


namespace BombieriVinogradov.LargeSieve

/-- The reduced rational representative of a unit modulo `q`. -/
def unitFraction {q : Nat} (a : (ZMod q)ˣ) : Rat :=
  (a.val.val : Rat) / (q : Rat)

/-- A unit representative is coprime to its modulus. -/
theorem unitFraction_coprime {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.Coprime a.val.val q := by
  rw [← ZMod.isUnit_iff_coprime]
  simpa only [ZMod.natCast_zmod_val] using a.isUnit

/-- The reduced denominator of `unitFraction a` is exactly the modulus. -/
theorem unitFraction_den {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).den = q := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  have hden : ((unitFraction a).den : Int) = (q : Int) := by
    simpa [unitFraction] using Rat.den_div_eq_of_coprime hqInt hcInt
  exact Int.ofNat_inj.mp hden

/-- The reduced numerator of `unitFraction a` is the standard unit representative. -/
theorem unitFraction_num {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).num = (a.val.val : Int) := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  simpa [unitFraction] using Rat.num_div_eq_of_coprime hqInt hcInt

/-- The finite dependent index of reduced fractions with denominator at most `Q`. -/
abbrev FareyIndex (Q : Nat) :=
  Sigma fun q : {q : Nat // q ∈ Finset.Icc 1 Q} => (ZMod q.1)ˣ

/-- The rational value represented by a Farey index. -/
def fareyValue {Q : Nat} (i : FareyIndex Q) : Rat :=
  unitFraction i.2

theorem fareyValue_den {Q : Nat} (i : FareyIndex Q) :
    (fareyValue i).den = i.1.1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  exact unitFraction_den i.2

theorem fareyValue_nonneg {Q : Nat} (i : FareyIndex Q) :
    0 <= fareyValue i := by
  unfold fareyValue unitFraction
  positivity

theorem fareyValue_lt_one {Q : Nat} (i : FareyIndex Q) :
    fareyValue i < 1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  unfold fareyValue unitFraction
  rw [div_lt_one]
  · exact_mod_cast ZMod.val_lt i.2.val
  · exact_mod_cast NeZero.pos i.1.1

/-- Reduced Farey indices have unique rational values. -/
theorem fareyValue_injective (Q : Nat) :
    Function.Injective (fareyValue (Q := Q)) := by
  intro x y hxy
  have hxpos : 0 < x.1.1 := (Finset.mem_Icc.mp x.1.2).1
  have hypos : 0 < y.1.1 := (Finset.mem_Icc.mp y.1.2).1
  let _ : NeZero x.1.1 := ⟨hxpos.ne'⟩
  let _ : NeZero y.1.1 := ⟨hypos.ne'⟩
  have hq : x.1.1 = y.1.1 := by
    calc
      x.1.1 = (fareyValue x).den := (fareyValue_den x).symm
      _ = (fareyValue y).den := congrArg Rat.den hxy
      _ = y.1.1 := fareyValue_den y
  cases x with
  | mk q a =>
      cases y with
      | mk r b =>
          simp only at hq
          have hqr : q = r := Subtype.ext hq
          subst r
          have hnum : (a.val.val : Int) = (b.val.val : Int) := by
            calc
              (a.val.val : Int) = (unitFraction a).num := (unitFraction_num a).symm
              _ = (unitFraction b).num := congrArg Rat.num hxy
              _ = (b.val.val : Int) := unitFraction_num b
          have habNat : a.val.val = b.val.val := Int.ofNat_inj.mp hnum
          have habZMod : a.val = b.val := ZMod.val_injective q.1 habNat
          have hab : a = b := Units.ext habZMod
          subst b
          rfl

/-- Distinct reduced Farey points are separated by at least `1 / Q^2` on the circle. -/
theorem fareyValue_circle_separation {Q : Nat} (hQ : 0 < Q)
    {x y : FareyIndex Q} (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance (fareyValue x) (fareyValue y) := by
  apply ratCircleSeparation hQ
  · exact fareyValue_nonneg x
  · exact fareyValue_lt_one x
  · exact fareyValue_nonneg y
  · exact fareyValue_lt_one y
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp x.1.2).2
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp y.1.2).2
  · intro hvalue
    exact hxy (fareyValue_injective Q hvalue)

end BombieriVinogradov.LargeSieve

/-!
# Character sums for the large-sieve route

This module fixes the exact source-level objects used in Vaughan's character
large-sieve theorem.  Proofs live under `Proof/LargeSieve` so that changes to
the analytic argument do not destabilize the project-wide statement surface.
-/


noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- The finite set of primitive complex Dirichlet characters of level `q`. -/
def primitiveCharacters (q : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive

/-- The interval character sum `S(chi)` in Vaughan's Theorem 4. -/
def intervalCharacterSum (a : Int -> Complex) (M : Int) (N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)), a n * chi (n : ZMod q)

/-- A character transform of a function on the unit group of `ZMod q`. -/
def unitCharacterSum {q : Nat} (a : (ZMod q)ˣ -> Complex)
    (chi : DirichletCharacter Complex q) : Complex := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  exact ∑ x, a x * chi (x : ZMod q)

/--
The source-faithful asymptotic statement of Vaughan's primitive-character
large sieve.  The existential constant is absolute: it precedes every
interval, length, level, and coefficient sequence.
-/
def CharacterLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (M : Int) (N Q : Nat) (a : Int -> Complex), 1 <= Q ->
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q,
              ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
          C * ((N : Real) + (Q : Real) ^ 2) *
            ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2

end BombieriVinogradov.LargeSieve

/-!
# Character orthogonality and Parseval

This file isolates the exact finite Fourier calculation used in the
multiplicative large-sieve route.  It deliberately sums over the unit group,
where conjugating a character value is the same as evaluating at the inverse.
-/


noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

noncomputable local instance unitFintype (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- A nonnegative sum over primitive characters is bounded by the sum over all characters. -/
theorem primitiveSum_le_all (q : Nat) (f : DirichletCharacter Complex q -> Real)
    (hf : ∀ chi, 0 <= f chi) :
    ∑ chi ∈ primitiveCharacters q, f chi <= ∑ chi, f chi := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg (s := primitiveCharacters q) hf

/-- On units, complex conjugation of a character value is evaluation at the inverse. -/
theorem star_character_apply_unit {q : Nat} (chi : DirichletCharacter Complex q)
    (x : (ZMod q)ˣ) :
    star (chi (x : ZMod q)) = chi ((x : ZMod q)⁻¹) := by
  rw [MulChar.star_apply']
  rw [MulChar.inv_apply_eq_inv']
  simp

/-- Orthogonality of all complex Dirichlet characters on the unit group. -/
theorem characterOrthogonalityOnUnits {q : Nat} [NeZero q]
    (x y : (ZMod q)ˣ) :
    (∑ chi : DirichletCharacter Complex q,
        star (chi (x : ZMod q)) * chi (y : ZMod q)) =
      if x = y then (q.totient : Complex) else 0 := by
  simp_rw [star_character_apply_unit]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq (R := Complex)
      x.isUnit (y : ZMod q))

/-- Finite Parseval identity for the Dirichlet-character transform on `(ZMod q)^*`. -/
theorem characterParseval {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q,
        star (unitCharacterSum a chi) * unitCharacterSum a chi) =
      (q.totient : Complex) * ∑ x, star (a x) * a x := by
  classical
  unfold unitCharacterSum
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  have rearrange (chi : DirichletCharacter Complex q) (x y : (ZMod q)ˣ) :
      star (chi (x : ZMod q)) * star (a x) *
          (a y * chi (y : ZMod q)) =
        (star (a x) * a y) *
          (star (chi (x : ZMod q)) * chi (y : ZMod q)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [characterOrthogonalityOnUnits]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring

/-- Real norm-squared form of character Parseval, ready for analytic inequalities. -/
theorem characterParseval_normSq {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q, ‖unitCharacterSum a chi‖ ^ 2) =
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using
    (characterParseval a)

/--
Discarding imprimitive characters gives the fixed-modulus primitive-character
bound that feeds the large-sieve argument.
-/
theorem primitiveCharacterParseval_le {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum a chi‖ ^ 2 <=
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  calc
    _ <= ∑ chi : DirichletCharacter Complex q,
        ‖unitCharacterSum a chi‖ ^ 2 :=
      primitiveSum_le_all q _ (fun chi => sq_nonneg ‖unitCharacterSum a chi‖)
    _ = _ := characterParseval_normSq a

end BombieriVinogradov.LargeSieve

end

section

open Complex Finset Real

namespace BombieriVinogradov.LargeSieve

noncomputable section

noncomputable local instance fareyUnitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

def additivePhase (x : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * x)

theorem additivePhase_add (x y : ℝ) : additivePhase (x + y) = additivePhase x * additivePhase y := by
  dsimp [additivePhase]
  rw [circleMap_zero_mul, one_mul, mul_add]

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 := by
  simp [additivePhase, norm_circleMap_zero]

def fareyIndices (Q : ℕ) : Finset (FareyIndex Q) :=
  (Icc 1 Q).attach.sigma fun _ => Finset.univ

def fareyAdditiveSample {Q : ℕ} (a : ℕ → ℂ) (N : ℕ) (i : FareyIndex Q) : ℂ :=
  ∑ n ∈ range N, a n * additivePhase ((n : ℝ) * (fareyValue i : ℝ))

theorem mode_nat_additivePhase (n : ℕ) (t : ℝ) :
    DyadicMixedB4Fourier.mode (n : ℤ) t = additivePhase ((n : ℝ) * t) := by
  rw [DyadicMixedB4Fourier.mode, DyadicMixedB4Fourier.frequency, additivePhase, circleMap_zero]
  simp only [Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  ring

theorem norm_gaussSum_stdAddChar_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (primitive : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar primitive, Real.sq_sqrt (Nat.cast_nonneg q)]

theorem additiveLargeSieve {Q N : ℕ} (QPositive : 0 < Q) (a : ℕ → ℂ) :
    ∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2 ≤
      64 * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ range N, ‖a k‖ ^ 2 := by
  classical
  let realFarey : FareyIndex Q ↪ ℝ :=
    ⟨fun i => fareyValue i, fun _ _ equal => fareyValue_injective Q (Rat.cast_injective equal)⟩
  let points := (fareyIndices Q).map realFarey
  let radius : ℝ := 1 / (2 * (Q : ℝ) ^ 2)
  have QCast : (0 : ℝ) < Q := by exact_mod_cast QPositive
  have QOne : (1 : ℝ) ≤ Q := by exact_mod_cast QPositive
  have QSquared : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ QOne
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusUpper : radius ≤ 1 := by
    dsimp [radius]
    apply (div_le_one (by positivity)).mpr
    linarith
  have radiusDouble : 2 * radius = 1 / (Q : ℝ) ^ 2 := by
    dsimp [radius]
    field_simp [QCast.ne']
  have contained : (points : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro t member
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp member
    change (fareyValue i : ℝ) ∈ Set.Icc 0 1
    constructor
    · exact_mod_cast fareyValue_nonneg i
    · exact_mod_cast (fareyValue_lt_one i).le
  have separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|) := by
    intro x xMember y yMember different
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp xMember
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp yMember
    rw [radiusDouble]
    have indexDifferent : i ≠ j := fun equal => different (congrArg realFarey equal)
    exact (fareyValue_circle_separation QPositive indexDifferent).trans (min_le_left _ _)
  have bound := DyadicMixedB4Fourier.additive_large_sieve N a points radiusPositive radiusUpper
    contained separated
  rw [show 3 / (2 * radius) = 3 * (Q : ℝ) ^ 2 by rw [radiusDouble]; field_simp [QCast.ne']] at bound
  dsimp only [points] at bound
  rw [Finset.sum_map] at bound
  simp_rw [mode_nat_additivePhase] at bound
  change (∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2) ≤ _ at bound
  refine bound.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
  nlinarith only [QSquared, Nat.cast_nonneg (α := ℝ) N,
    mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (Nat.cast_nonneg (α := ℝ) N)]


end
end BombieriVinogradov.LargeSieve

end

section

/- Adapted from CharacterReduction.lean in kimihiro64/bombieri-vinogradov
at 7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0).
The additive-sieve input uses real interval sampling, with constant 64. -/

/-!
# Reduction from primitive characters to additive Farey samples

This module proves Vaughan's primitive Dirichlet-character large sieve from
the additive large sieve. The reduction uses the composite-modulus primitive
Gauss-sum norm, character Parseval on the unit group, and an exact translation
of arbitrary integer intervals to the coefficient convention used by the
Farey additive theorem.
-/


noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

noncomputable local instance characterReductionUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- The real additive phase at an integral multiple of a reduced fraction is
Mathlib's standard additive character on the corresponding residue. -/
theorem additivePhase_int_unitFraction {q : Nat} [NeZero q]
    (n : Int) (u : (ZMod q)ˣ) :
    additivePhase ((n : Real) * (unitFraction u : Real)) =
      ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
  rw [show (n : ZMod q) * (u : ZMod q) =
    (n * u.val.val : Int) by norm_num]
  rw [ZMod.stdAddChar_coe]
  rw [additivePhase, circleMap_zero]
  unfold unitFraction
  push_cast
  field_simp [NeZero.ne q]

/-- A Dirichlet-character-weighted sum over units equals the corresponding
sum over all residues, since character values vanish on nonunits. -/
theorem sum_units_eq_sum_residues {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (f : ZMod q -> Complex) :
    ∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u =
      ∑ x : ZMod q, chi x * f x := by
  classical
  let s : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u) =
      ∑ x ∈ s, chi x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := s) (fun u hu => (u : ZMod q))
    · intro u hu
      simp [s, u.isUnit]
    · intro u hu v hv huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u hu
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hxuniv hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit chi hxnonunit, zero_mul]

/-- The additive interval sum at one reduced residue modulo `q`. -/
def intervalAdditiveResidueSum (a : Int -> Complex) (M : Int) (N q : Nat)
    [NeZero q] (u : (ZMod q)ˣ) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)),
    a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))

/-- Primitive Gauss-sum inversion converts one multiplicative character sum
to a character transform of additive interval samples. -/
theorem gauss_mul_intervalCharacterSum {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi =
      unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹ := by
  classical
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  have hshift (n : Int) :
      ∑ u : (ZMod q)ˣ,
          chi⁻¹ (u : ZMod q) *
            ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) =
        chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar := by
    calc
      _ = ∑ x : ZMod q,
          chi⁻¹ x * ZMod.stdAddChar ((n : ZMod q) * x) :=
        sum_units_eq_sum_residues chi⁻¹ _
      _ = gaussSum chi⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) := by
        simp only [gaussSum, AddChar.mulShift_apply]
      _ = _ := by
        simpa using
          (gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hchiInv (n : ZMod q))
  unfold intervalCharacterSum unitCharacterSum intervalAdditiveResidueSum
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    gaussSum chi⁻¹ ZMod.stdAddChar * (a n * chi (n : ZMod q)) =
        a n * (chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar) := by ring
    _ = a n * ∑ u : (ZMod q)ˣ,
        chi⁻¹ (u : ZMod q) * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
      rw [hshift n]
    _ = ∑ u : (ZMod q)ˣ,
        a n * (chi⁻¹ (u : ZMod q) *
          ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))) := by
      rw [Finset.mul_sum]
    _ = ∑ u : (ZMod q)ˣ,
        a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) *
          chi⁻¹ (u : ZMod q) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Squared-norm form of primitive Gauss-sum inversion. -/
theorem q_mul_norm_intervalCharacterSum_sq {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
      ‖unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹‖ ^ 2 := by
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  calc
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
        ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ ^ 2 *
          ‖intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_gaussSum_stdAddChar_sq hchiInv]
    _ = ‖gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ = _ := by
      rw [gauss_mul_intervalCharacterSum hchi a M N]

/-- Inversion permutes the finite set of primitive characters. -/
theorem sum_primitive_inv (q : Nat) (f : DirichletCharacter Complex q -> Real) :
    ∑ chi ∈ primitiveCharacters q, f chi⁻¹ =
      ∑ chi ∈ primitiveCharacters q, f chi := by
  classical
  apply Finset.sum_bij (s := primitiveCharacters q) (t := primitiveCharacters q)
    (fun chi hchi => chi⁻¹)
  · intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    have hinv : DirichletCharacter.IsPrimitive chi⁻¹ := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprimitive
    simpa [primitiveCharacters] using hinv
  · intro chi hchi psi hpsi heq
    simpa only [inv_inv] using congrArg Inv.inv heq
  · intro psi hpsi
    refine ⟨psi⁻¹, ?_, ?_⟩
    · have hprimitive : DirichletCharacter.IsPrimitive psi := by
        simpa [primitiveCharacters] using hpsi
      have hinv : DirichletCharacter.IsPrimitive psi⁻¹ := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        exact hprimitive
      simpa [primitiveCharacters] using hinv
    · simp
  · intro chi hchi
    rfl

/-- At a fixed positive modulus, the source weight `q / phi(q)` cancels
exactly against the Gauss norm and character Parseval constants. -/
theorem weightedPrimitiveCharacterSum_le_additive {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  classical
  let b : (ZMod q)ˣ -> Complex := intervalAdditiveResidueSum a M N q
  let S : Real := ∑ chi ∈ primitiveCharacters q,
    ‖intervalCharacterSum a M N q chi‖ ^ 2
  let E : Real := ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2
  have hscaled : (q : Real) * S =
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2 := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    exact q_mul_norm_intervalCharacterSum_sq hprimitive a M N
  have hinv :
      (∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2) =
        ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 := by
    exact sum_primitive_inv q (fun chi => ‖unitCharacterSum b chi‖ ^ 2)
  have hparseval :
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 <=
        (q.totient : Real) * E := by
    simpa [E] using primitiveCharacterParseval_le b
  have hcore : (q : Real) * S <= (q.totient : Real) * E := by
    rw [hscaled, hinv]
    exact hparseval
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ((q : Real) / (q.totient : Real)) * S <= E
  calc
    ((q : Real) / (q.totient : Real)) * S =
        ((q : Real) * S) / (q.totient : Real) := by ring
    _ <= ((q.totient : Real) * E) / (q.totient : Real) := by
      exact (div_le_div_iff_of_pos_right hphi).2 hcore
    _ = E := by field_simp

/-- Reindex an integer interval of length `N` by `range N`. -/
theorem sum_int_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R]
    (f : Int -> R) (M : Int) (N : Nat) :
    ∑ n ∈ Ioc M (M + (N : Int)), f n =
      ∑ k ∈ range N, f (M + (k : Int) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hle : M <= M + (N : Int) := by omega
      rw [Nat.cast_succ]
      rw [← add_assoc]
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hle]
      rw [Finset.sum_insert]
      · rw [Finset.sum_range_succ, ih]
        simp [add_comm, add_assoc]
      · simp

/-- Coefficients on `M < n <= M + N`, shifted to indices `0 <= k < N`. -/
def shiftedIntervalCoefficients (a : Int -> Complex) (M : Int) (k : Nat) : Complex :=
  a (M + (k : Int) + 1)

/-- Translation of an additive interval sum produces only a unit-norm common
phase, followed by the Farey sample of the shifted coefficients. -/
theorem intervalAdditiveResidueSum_eq_phase_mul_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    intervalAdditiveResidueSum a M N q u =
      additivePhase (((M + 1 : Int) : Real) * (unitFraction u : Real)) *
        fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩ := by
  rw [intervalAdditiveResidueSum, sum_int_Ioc_eq_sum_range]
  unfold fareyAdditiveSample shiftedIntervalCoefficients fareyValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← additivePhase_int_unitFraction (M + (k : Int) + 1) u]
  rw [show (((M + (k : Int) + 1 : Int) : Real) * (unitFraction u : Real)) =
      (((M + 1 : Int) : Real) * (unitFraction u : Real)) +
        ((k : Real) * (unitFraction u : Real)) by
    push_cast
    ring]
  rw [additivePhase_add]
  ring

/-- Norm form of interval translation, ready for the additive large sieve. -/
theorem norm_intervalAdditiveResidueSum_eq_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    ‖intervalAdditiveResidueSum a M N q u‖ =
      ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩‖ := by
  rw [intervalAdditiveResidueSum_eq_phase_mul_fareySample hq a M N u]
  rw [norm_mul, norm_additivePhase, one_mul]

/-- Expand a sum over the explicit dependent Farey index into moduli and
units. -/
theorem sum_fareyIndices_eq_sum_attach {Q : Nat} (f : FareyIndex Q -> Real) :
    ∑ i ∈ fareyIndices Q, f i =
      ∑ q ∈ (Icc 1 Q).attach, ∑ u : (ZMod q.1)ˣ, f ⟨q, u⟩ := by
  unfold fareyIndices
  rw [Finset.sum_sigma]

/-- Total additive energy at one modulus, defined as zero at the unused
modulus `q = 0`. -/
def modulusAdditiveEnergy (a : Int -> Complex) (M : Int) (N q : Nat) : Real :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2

theorem modulusAdditiveEnergy_eq {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    modulusAdditiveEnergy a M N q =
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  simp [modulusAdditiveEnergy, NeZero.ne q]

/-- The sum of fixed-modulus additive energies is exactly the Farey energy of
the shifted coefficient sequence. -/
theorem sum_modulusAdditiveEnergy_eq_fareySamples
    (Q : Nat) (a : Int -> Complex) (M : Int) (N : Nat) :
    ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q =
      ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 := by
  rw [sum_fareyIndices_eq_sum_attach]
  rw [← Finset.sum_attach (Icc 1 Q) (modulusAdditiveEnergy a M N)]
  apply Finset.sum_congr rfl
  intro q hqattach
  let _ : NeZero q.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp q.2).1⟩
  rw [modulusAdditiveEnergy_eq]
  apply Finset.sum_congr rfl
  intro u hu
  rw [norm_intervalAdditiveResidueSum_eq_fareySample q.2 a M N u]

/-- The primitive Dirichlet-character large sieve with explicit constant
`64`, including arbitrary integer interval origin. -/
theorem characterLargeSieveNat (M : Int) (N Q : Nat) (a : Int -> Complex)
    (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      64 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
  by_cases hNzero : N = 0
  · subst N
    simp [intervalCharacterSum]
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQ
  have hfixed :
      (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖intervalCharacterSum a M N q chi‖ ^ 2) <=
        ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := by
    apply Finset.sum_le_sum
    intro q hq
    let _ : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    rw [modulusAdditiveEnergy_eq]
    exact weightedPrimitiveCharacterSum_le_additive a M N
  calc
    _ <= ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := hfixed
    _ = ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 :=
      sum_modulusAdditiveEnergy_eq_fareySamples Q a M N
    _ <= 64 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ k ∈ range N, ‖shiftedIntervalCoefficients a M k‖ ^ 2 :=
      additiveLargeSieve hQpos (shiftedIntervalCoefficients a M)
    _ = 64 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
      rw [sum_int_Ioc_eq_sum_range (fun n => ‖a n‖ ^ 2) M N]
      rfl

/-- Vaughan's source-faithful character large-sieve statement. -/
theorem characterLargeSieve : CharacterLargeSieveStatement := by
  refine ⟨64, by norm_num, ?_⟩
  intro M N Q a hQ
  exact characterLargeSieveNat M N Q a hQ

end BombieriVinogradov.LargeSieve

end

section

open Finset
open scoped Classical

namespace DyadicMixedB4DualCharacter

noncomputable section

theorem character_pair_orthogonality {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) :
    (∑ x : ZMod q, χ x * star (ψ x)) = if χ = ψ then (q.totient : ℂ) else 0 := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  simp_rw [MulChar.star_apply', ← MulChar.mul_apply]
  by_cases same : χ = ψ
  · subst ψ
    simp only [mul_inv_cancel, ite_true]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · rw [if_neg same]
    exact MulChar.sum_eq_zero_of_ne_one (fun eq => same (mul_inv_eq_one.mp eq))

theorem dual_parseval {q : ℕ} [NeZero q] (characters : Finset (DirichletCharacter ℂ q))
    (c : DirichletCharacter ℂ q → ℂ) :
    (∑ x : ZMod q, ‖∑ χ ∈ characters, c χ * χ x‖ ^ 2) =
      (q.totient : ℝ) * ∑ χ ∈ characters, ‖c χ‖ ^ 2 := by
  let entry (χ ψ : DirichletCharacter ℂ q) (x : ZMod q) :=
    c χ * star (c ψ) * (χ x * star (ψ x))
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_pow,
    ← Complex.mul_conj']
  change (∑ x : ZMod q, (∑ χ ∈ characters, c χ * χ x) *
      star (∑ ψ ∈ characters, c ψ * ψ x)) =
    (q.totient : ℂ) * ∑ χ ∈ characters, c χ * star (c χ)
  calc
    _ = ∑ x : ZMod q, ∑ χ ∈ characters, ∑ ψ ∈ characters, entry χ ψ x := by
      refine sum_congr rfl fun x _ => ?_
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun χ _ => sum_congr rfl fun ψ _ => ?_
      rw [star_mul]
      unfold entry
      ac_rfl
    _ = ∑ χ ∈ characters, ∑ ψ ∈ characters, ∑ x : ZMod q, entry χ ψ x := by
      rw [Finset.sum_comm]
      exact sum_congr rfl fun χ _ => Finset.sum_comm
    _ = _ := by
      rw [mul_sum]
      refine sum_congr rfl fun χ member => ?_
      rw [sum_eq_single_of_mem χ member]
      · simp only [entry, ← Finset.mul_sum, character_pair_orthogonality, ite_true]
        ring
      · intro ψ _ different
        simp only [entry, ← Finset.mul_sum, character_pair_orthogonality,
          if_neg (Ne.symm different), mul_zero]

theorem sum_natCast_range_eq_zmod {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : ZMod q → R) :
    ∑ u ∈ range q, f (u : ZMod q) = ∑ z : ZMod q, f z := by
  apply sum_bij (s := range q) (t := (univ : Finset (ZMod q))) (fun u _ => (u : ZMod q))
  · simp
  · intro u uMember v vMember equal
    have valEqual := congrArg ZMod.val equal
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp uMember),
      Nat.mod_eq_of_lt (mem_range.mp vMember)] using valEqual
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro u _
    rfl

theorem sum_natCast_mul_range {q : ℕ} [NeZero q] (k : ℕ) (f : ZMod q → ℝ) :
    ∑ u ∈ range (k * q), f (u : ZMod q) = (k : ℝ) * ∑ z : ZMod q, f z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have periodic (u : ℕ) : ((k * q + u : ℕ) : ZMod q) = (u : ZMod q) := by push_cast; simp
    simp_rw [periodic]
    rw [sum_natCast_range_eq_zmod]
    push_cast
    ring

theorem sum_natCast_le_cover {q : ℕ} [NeZero q] (X : ℕ) (f : ZMod q → ℝ)
    (nonnegative : ∀ x, 0 ≤ f x) :
    ∑ u ∈ range X, f (u : ZMod q) ≤ ((X / q + 1 : ℕ) : ℝ) * ∑ z : ZMod q, f z := by
  have bound : X ≤ (X / q + 1) * q := by
    calc
      X = X / q * q + X % q := by rw [Nat.mul_comm, Nat.div_add_mod]
      _ ≤ X / q * q + q := Nat.add_le_add_left (Nat.mod_lt _ (NeZero.pos q)).le _
      _ = _ := by ring
  refine (sum_le_sum_of_subset_of_nonneg (range_mono bound) (fun _ _ _ => nonnegative _)).trans_eq ?_
  exact sum_natCast_mul_range (X / q + 1) f

theorem dual_interval_le {q : ℕ} [NeZero q] (X : ℕ) (characters : Finset (DirichletCharacter ℂ q))
    (c : DirichletCharacter ℂ q → ℂ) :
    (∑ u ∈ range X, ‖∑ χ ∈ characters, c χ * χ (u : ZMod q)‖ ^ 2) ≤
      ((X : ℝ) + q) * ∑ χ ∈ characters, ‖c χ‖ ^ 2 := by
  have coefficientBound : ((X / q + 1 : ℕ) : ℝ) * (q.totient : ℝ) ≤ (X : ℝ) + q := by
    exact_mod_cast (show (X / q + 1) * q.totient ≤ X + q from calc
      _ ≤ (X / q + 1) * q := Nat.mul_le_mul_left _ (Nat.totient_le q)
      _ = X / q * q + q := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self X q) _)
  calc
    _ ≤ ((X / q + 1 : ℕ) : ℝ) * ∑ z : ZMod q, ‖∑ χ ∈ characters, c χ * χ z‖ ^ 2 :=
      sum_natCast_le_cover X _ (fun _ => sq_nonneg _)
    _ = (((X / q + 1 : ℕ) : ℝ) * (q.totient : ℝ)) * ∑ χ ∈ characters, ‖c χ‖ ^ 2 := by
      rw [dual_parseval, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficientBound (sum_nonneg fun _ _ => sq_nonneg _)


end
end DyadicMixedB4DualCharacter

end

section

open Finset MeasureTheory

namespace DyadicMixedB4MaximalSieve

open DyadicMixedB4Fourier DyadicMixedB4Geometric BombieriVinogradov.LargeSieve

noncomputable section

theorem wave_one_eq_mode_sum (x : ℕ) (t : ℝ) :
    wave 1 0 x t = ∑ k ∈ range x, mode ((k : ℤ) + 1) t := by
  have indices : Ioc (0 : ℕ) x = Ico 1 (x + 1) := by
    ext k
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [wave, indices, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun k _ => ?_
  simp only [one_mul, Nat.cast_add, Nat.cast_one]
  unfold phase mode frequency
  congr 1
  push_cast
  ring

theorem prefix_integral {x Y : ℕ} (xBound : x ≤ Y) (a : ℕ → ℂ) :
    (∑ j ∈ range x, a j) = ∫ t in (0 : ℝ)..1,
      (∑ j ∈ range Y, a j * mode ((j : ℤ) + 1) t) * star (wave 1 0 x t) := by
  let entry (j k : ℕ) (t : ℝ) := a j * mode ((j : ℤ) - (k : ℤ)) t
  have continuousEntry (j k : ℕ) : Continuous (entry j k) :=
    continuous_const.mul (continuous_mode ((j : ℤ) - (k : ℤ)))
  symm
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ j ∈ range Y, ∑ k ∈ range x, entry j k t := by
      apply intervalIntegral.integral_congr
      intro t _
      change (∑ j ∈ range Y, a j * mode ((j : ℤ) + 1) t) * star (wave 1 0 x t) = _
      rw [wave_one_eq_mode_sum, star_sum, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      rw [mul_assoc, mode_mul_conj]
      simp only [entry, add_sub_add_right_eq_sub]
    _ = ∑ j ∈ range Y, ∑ k ∈ range x, ∫ t in (0 : ℝ)..1, entry j k t := by
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        exact fun k _ => (continuousEntry j k).intervalIntegrable 0 1
      · intro j _
        exact (continuous_finsetSum _ fun k _ => continuousEntry j k).intervalIntegrable 0 1
    _ = ∑ k ∈ range x, ∑ j ∈ range Y, ∫ t in (0 : ℝ)..1, entry j k t := sum_comm
    _ = _ := by
      refine sum_congr rfl fun k membership => ?_
      have membershipY : k ∈ range Y := mem_range.mpr ((mem_range.mp membership).trans_le xBound)
      rw [sum_eq_single_of_mem k membershipY]
      · simp [entry, intervalIntegral.integral_const_mul, mode_integral]
      · intro j _ different
        have nonzero : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [entry, intervalIntegral.integral_const_mul, mode_integral, nonzero]

def prefixMajorant (Y : ℕ) (t : ℝ) : ℝ :=
  2 * smoothKernel (1 / ((Y : ℝ) + 1)) 0 t + 2 * smoothKernel (1 / ((Y : ℝ) + 1)) 1 t

theorem prefixMajorant_continuous (Y : ℕ) : Continuous (prefixMajorant Y) := by
  have positive : (0 : ℝ) < 1 / ((Y : ℝ) + 1) := by positivity
  exact (continuous_const.mul (cont_smoothKernel positive)).add
    (continuous_const.mul (cont_smoothKernel positive))

theorem prefixMajorant_positive (Y : ℕ) (t : ℝ) : 0 < prefixMajorant Y t := by
  unfold prefixMajorant smoothKernel
  positivity

theorem wave_one_le_prefixMajorant {x Y : ℕ} (xBound : x ≤ Y) {t : ℝ}
    (membership : t ∈ Set.Icc (0 : ℝ) 1) : ‖wave 1 0 x t‖ ≤ prefixMajorant Y t := by
  obtain ⟨i, iMember, dist⟩ := nearestCenter 1 t membership.1 membership.2
  have bound := waveBound (l := 0) (u := 1) (n := Y) (by decide) (by simpa using xBound) dist
  have iRange : i < 2 := mem_range.mp iMember
  have aNonnegative : (0 : ℝ) ≤ 1 / ((Y : ℝ) + 1) := by positivity
  obtain zero | one : i = 0 ∨ i = 1 := by omega
  · simpa [prefixMajorant, zero] using bound.trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (nonneg_smoothKernel (c := 1) (t := t) aNonnegative)))
  · simpa [prefixMajorant, one] using bound.trans
      (le_add_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (nonneg_smoothKernel (c := 0) (t := t) aNonnegative)))

theorem integral_prefixMajorant_positive (Y : ℕ) :
    0 < ∫ t in (0 : ℝ)..1, prefixMajorant Y t := by
  exact intervalIntegral.integral_pos (by norm_num) (prefixMajorant_continuous Y).continuousOn
    (fun t _ => (prefixMajorant_positive Y t).le)
    ⟨0, by simp, prefixMajorant_positive Y 0⟩

theorem integral_prefixMajorant_le (Y : ℕ) :
    (∫ t in (0 : ℝ)..1, prefixMajorant Y t) ≤ 8 * Real.log ((Y : ℝ) + 2) := by
  let a : ℝ := 1 / ((Y : ℝ) + 1)
  have aPositive : 0 < a := by dsimp [a]; positivity
  have left := integral_smoothKernel aPositive (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
  have right := integral_smoothKernel aPositive (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
  have ratio : (1 + a) / a = (Y : ℝ) + 2 := by dsimp [a]; field_simp; ring
  rw [ratio] at left right
  have intLeft : IntervalIntegrable (fun t => 2 * smoothKernel a 0 t) volume 0 1 :=
    (continuous_const.mul (cont_smoothKernel aPositive)).intervalIntegrable 0 1
  have intRight : IntervalIntegrable (fun t => 2 * smoothKernel a 1 t) volume 0 1 :=
    (continuous_const.mul (cont_smoothKernel aPositive)).intervalIntegrable 0 1
  change (∫ t in (0 : ℝ)..1, 2 * smoothKernel a 0 t + 2 * smoothKernel a 1 t) ≤ _
  rw [intervalIntegral.integral_add intLeft intRight, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  linarith only [left, right]

theorem integral_weighted_cauchy {w f : ℝ → ℝ} (wContinuous : Continuous w)
    (fContinuous : Continuous f) (wNonnegative : ∀ t, 0 ≤ w t)
    (massPositive : 0 < ∫ t in (0 : ℝ)..1, w t) :
    (∫ t in (0 : ℝ)..1, w t * f t) ^ 2 ≤
      (∫ t in (0 : ℝ)..1, w t) * (∫ t in (0 : ℝ)..1, w t * f t ^ 2) := by
  let mass : ℝ := ∫ t in (0 : ℝ)..1, w t
  let first : ℝ := ∫ t in (0 : ℝ)..1, w t * f t
  let second : ℝ := ∫ t in (0 : ℝ)..1, w t * f t ^ 2
  have nonnegative := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (fun t => mul_nonneg (wNonnegative t) (sq_nonneg (mass * f t - first)))
  have integral1 : IntervalIntegrable (fun t => mass ^ 2 * (w t * f t ^ 2)) volume 0 1 :=
    (continuous_const.mul (wContinuous.mul (fContinuous.pow 2))).intervalIntegrable 0 1
  have integral2 : IntervalIntegrable (fun t => (-2 * mass * first) * (w t * f t)) volume 0 1 :=
    (continuous_const.mul (wContinuous.mul fContinuous)).intervalIntegrable 0 1
  have integral3 : IntervalIntegrable (fun t => first ^ 2 * w t) volume 0 1 :=
    (continuous_const.mul wContinuous).intervalIntegrable 0 1
  have expanded : (∫ t in (0 : ℝ)..1, w t * (mass * f t - first) ^ 2) =
      mass ^ 2 * second + (-2 * mass * first) * first + first ^ 2 * mass := by
    calc
      _ = ∫ t in (0 : ℝ)..1, mass ^ 2 * (w t * f t ^ 2) +
          (-2 * mass * first) * (w t * f t) + first ^ 2 * w t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        have sumIntegrable : IntervalIntegrable (fun t => mass ^ 2 * (w t * f t ^ 2) +
          (-2 * mass * first) * (w t * f t)) volume 0 1 := integral1.add integral2
        rw [intervalIntegral.integral_add sumIntegrable integral3,
          intervalIntegral.integral_add integral1 integral2]
        simp only [intervalIntegral.integral_const_mul, mass, first, second]
  rw [expanded] at nonnegative
  change first ^ 2 ≤ mass * second
  apply (mul_le_mul_iff_right₀ massPositive).mp
  nlinarith only [nonnegative]

def twist (a : ℤ → ℂ) (t : ℝ) (m : ℤ) : ℂ := a m * mode m t

theorem continuous_twistedCharacterSum (a : ℤ → ℂ) (Y q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous (fun t => intervalCharacterSum (twist a t) 0 Y q χ) := by
  unfold intervalCharacterSum twist
  exact continuous_finsetSum _ fun m _ => (continuous_const.mul (continuous_mode m)).mul continuous_const

theorem prefix_character_integral {x Y q : ℕ} (xBound : x ≤ Y)
    (a : ℤ → ℂ) (χ : DirichletCharacter ℂ q) :
    intervalCharacterSum a 0 x q χ = ∫ t in (0 : ℝ)..1,
      intervalCharacterSum (twist a t) 0 Y q χ * star (wave 1 0 x t) := by
  unfold intervalCharacterSum
  simp_rw [sum_int_Ioc_eq_sum_range, zero_add]
  let coefficient (j : ℕ) := a ((j : ℤ) + 1) * χ (((j : ℤ) + 1 : ℤ) : ZMod q)
  calc
    _ = ∫ t in (0 : ℝ)..1,
        (∑ j ∈ range Y, coefficient j * mode ((j : ℤ) + 1) t) * star (wave 1 0 x t) :=
      prefix_integral xBound coefficient
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change (∑ j ∈ range Y, coefficient j * mode ((j : ℤ) + 1) t) * star (wave 1 0 x t) = _
      congr 1
      refine sum_congr rfl fun j _ => ?_
      unfold coefficient twist
      ring

def prefixEnergy (Y q : ℕ) (a : ℤ → ℂ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (range (Y + 1)).sup' (by simp) (fun x => ‖intervalCharacterSum a 0 x q χ‖ ^ 2)

def finitePrefixEnergy (Y : ℕ) (a : ℕ → ℂ) : ℝ :=
  (range (Y + 1)).sup' (by simp) (fun x => ‖∑ j ∈ range x, a j‖ ^ 2)

def finiteTwistedSum (Y : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range Y, a j * mode ((j : ℤ) + 1) t

theorem continuous_finiteTwistedSum (Y : ℕ) (a : ℕ → ℂ) : Continuous (finiteTwistedSum Y a) :=
  continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_mode _))

theorem finitePrefixEnergy_le_twists (Y : ℕ) (a : ℕ → ℂ) :
    finitePrefixEnergy Y a ≤ (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t * ‖finiteTwistedSum Y a t‖ ^ 2) := by
  unfold finitePrefixEnergy
  apply Finset.sup'_le (by simp) _
  intro x xMember
  have xBound : x ≤ Y := Nat.le_of_lt_succ (mem_range.mp xMember)
  let polynomial := finiteTwistedSum Y a
  have polynomialContinuous : Continuous polynomial := continuous_finiteTwistedSum Y a
  have waveContinuous : Continuous (wave 1 0 x) := by unfold wave phase; fun_prop
  have integrandContinuous : Continuous (fun t => polynomial t * star (wave 1 0 x t)) :=
    polynomialContinuous.mul waveContinuous.star
  have normBound : ‖∑ j ∈ range x, a j‖ ≤
      ∫ t in (0 : ℝ)..1, prefixMajorant Y t * ‖polynomial t‖ := by
    rw [prefix_integral xBound]
    apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (integrandContinuous.norm.intervalIntegrable 0 1)
      (((prefixMajorant_continuous Y).mul polynomialContinuous.norm).intervalIntegrable 0 1)
    intro t member
    rw [norm_mul, norm_star, mul_comm]
    exact mul_le_mul_of_nonneg_right (wave_one_le_prefixMajorant xBound member) (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) normBound 2).trans
    (integral_weighted_cauchy (prefixMajorant_continuous Y) polynomialContinuous.norm
      (fun t => (prefixMajorant_positive Y t).le) (integral_prefixMajorant_positive Y))

theorem finiteTwistedSum_character_coefficients (Y q : ℕ) (a : ℤ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    finiteTwistedSum Y (fun j => a ((j : ℤ) + 1) * χ (((j : ℤ) + 1 : ℤ) : ZMod q)) t =
      intervalCharacterSum (twist a t) 0 Y q χ := by
  rw [finiteTwistedSum, intervalCharacterSum, sum_int_Ioc_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  simp only [zero_add, twist]
  ring

theorem prefixEnergy_le_twists (Y q : ℕ) (a : ℤ → ℂ) (χ : DirichletCharacter ℂ q) :
    prefixEnergy Y q a χ ≤ (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t * ‖intervalCharacterSum (twist a t) 0 Y q χ‖ ^ 2) := by
  have maxEquality : prefixEnergy Y q a χ =
      finitePrefixEnergy Y (fun j => a ((j : ℤ) + 1) * χ (((j : ℤ) + 1 : ℤ) : ZMod q)) := by
    simp_rw [prefixEnergy, finitePrefixEnergy, intervalCharacterSum, sum_int_Ioc_eq_sum_range, zero_add]
  rw [maxEquality]
  simpa only [finiteTwistedSum_character_coefficients] using finitePrefixEnergy_le_twists Y
    (fun j => a ((j : ℤ) + 1) * χ (((j : ℤ) + 1 : ℤ) : ZMod q))

theorem weightedCharacterPrefixSieve (Y Q : ℕ) (a : ℤ → ℂ) (QPositive : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ primitiveCharacters q, prefixEnergy Y q a χ) ≤
      (8 * Real.log ((Y : ℝ) + 2)) ^ 2 * (64 * ((Y : ℝ) + (Q : ℝ) ^ 2) *
        ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2) := by
  let weight (q : ℕ) : ℝ := (q : ℝ) / (q.totient : ℝ)
  let w := prefixMajorant Y
  let mass : ℝ := ∫ t in (0 : ℝ)..1, w t
  let square (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :=
    ‖intervalCharacterSum (twist a t) 0 Y q χ‖ ^ 2
  let energy (t : ℝ) := ∑ q ∈ Icc 1 Q, weight q * ∑ χ ∈ primitiveCharacters q, square q χ t
  let envelope : ℝ := 64 * ((Y : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2
  have wContinuous : Continuous w := prefixMajorant_continuous Y
  have wPositive (t : ℝ) : 0 < w t := prefixMajorant_positive Y t
  have massPositive : 0 < mass := integral_prefixMajorant_positive Y
  have weightNonnegative (q : ℕ) : 0 ≤ weight q := by dsimp [weight]; positivity
  have envelopeNonnegative : 0 ≤ envelope := by dsimp [envelope]; positivity
  have continuousSquare (q : ℕ) (χ : DirichletCharacter ℂ q) : Continuous (square q χ) :=
    (continuous_twistedCharacterSum a Y q χ).norm.pow 2
  have continuousAtModulus (q : ℕ) : Continuous (fun t => ∑ χ ∈ primitiveCharacters q, square q χ t) :=
    continuous_finsetSum _ (fun χ _ => continuousSquare q χ)
  have continuousEnergy : Continuous energy :=
    continuous_finsetSum _ (fun q _ => continuous_const.mul (continuousAtModulus q))
  have boundAtPhase (t : ℝ) : energy t ≤ envelope := by
    have bound := characterLargeSieveNat 0 Y Q (twist a t) QPositive
    have normTwist (m : ℤ) : ‖twist a t m‖ = ‖a m‖ := by
      rw [twist, norm_mul, show ‖mode m t‖ = 1 by
        simp [mode, frequency, Complex.norm_exp]]
      ring
    simpa only [energy, weight, square, envelope, zero_add, normTwist] using bound
  have integralAtModulus (q : ℕ) :
      (∫ t in (0 : ℝ)..1, w t * (weight q * ∑ χ ∈ primitiveCharacters q, square q χ t)) =
        weight q * ∑ χ ∈ primitiveCharacters q, ∫ t in (0 : ℝ)..1, w t * square q χ t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, weight q * ∑ χ ∈ primitiveCharacters q, w t * square q χ t := by
        apply intervalIntegral.integral_congr
        intro t _
        change w t * (weight q * ∑ χ ∈ primitiveCharacters q, square q χ t) =
          weight q * ∑ χ ∈ primitiveCharacters q, w t * square q χ t
        rw [← mul_sum, mul_left_comm]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        exact fun χ _ => (wContinuous.mul (continuousSquare q χ)).intervalIntegrable 0 1
  have totalIntegral : (∫ t in (0 : ℝ)..1, w t * energy t) =
      ∑ q ∈ Icc 1 Q, weight q * ∑ χ ∈ primitiveCharacters q,
        ∫ t in (0 : ℝ)..1, w t * square q χ t := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          ∑ q ∈ Icc 1 Q, w t * (weight q * ∑ χ ∈ primitiveCharacters q, square q χ t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change w t * energy t = _
        simp only [energy, mul_sum]
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum]
        · exact sum_congr rfl fun q _ => integralAtModulus q
        · intro q _
          exact (wContinuous.mul (continuous_const.mul (continuousAtModulus q))).intervalIntegrable 0 1
  change (∑ q ∈ Icc 1 Q, weight q * ∑ χ ∈ primitiveCharacters q, prefixEnergy Y q a χ) ≤
    (8 * Real.log ((Y : ℝ) + 2)) ^ 2 * envelope
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, weight q * ∑ χ ∈ primitiveCharacters q,
        mass * ∫ t in (0 : ℝ)..1, w t * square q χ t := by
      refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => ?_) (weightNonnegative q)
      exact prefixEnergy_le_twists Y q a χ
    _ = mass * ∫ t in (0 : ℝ)..1, w t * energy t := by
      rw [totalIntegral, mul_sum]
      refine sum_congr rfl fun q _ => ?_
      rw [← mul_sum, mul_left_comm]
    _ ≤ mass * ∫ t in (0 : ℝ)..1, w t * envelope := by
      refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
        ((wContinuous.mul continuousEnergy).intervalIntegrable 0 1)
        ((wContinuous.mul continuous_const).intervalIntegrable 0 1) ?_) massPositive.le
      exact fun t _ => mul_le_mul_of_nonneg_left (boundAtPhase t) (wPositive t).le
    _ = mass ^ 2 * envelope := by rw [intervalIntegral.integral_mul_const]; change mass * (mass * envelope) = _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ massPositive.le (integral_prefixMajorant_le Y) 2) envelopeNonnegative


end
end DyadicMixedB4MaximalSieve

end

section

open Finset MeasureTheory DyadicMixedB4MaximalSieve DyadicMixedB4DualCharacter

namespace DyadicMixedB4MixedCharacter

noncomputable section

def characterCoefficients {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (j : ℕ) : ℂ :=
  a j * χ ((j + 1 : ℕ) : ZMod q)

def mixture {q : ℕ} (characters : Finset (DirichletCharacter ℂ q))
    (a : ℕ → ℂ) (c : DirichletCharacter ℂ q → ℂ) (u j : ℕ) : ℂ :=
  a j * ∑ χ ∈ characters, c χ * χ (u : ZMod q) * χ ((j + 1 : ℕ) : ZMod q)

theorem finiteTwistedSum_mixture {q : ℕ} (Y : ℕ) (characters : Finset (DirichletCharacter ℂ q))
    (a : ℕ → ℂ) (c : DirichletCharacter ℂ q → ℂ) (u : ℕ) (t : ℝ) :
    finiteTwistedSum Y (mixture characters a c u) t =
      ∑ χ ∈ characters, (c χ * finiteTwistedSum Y (characterCoefficients a χ) t) * χ (u : ZMod q) := by
  let entry (j : ℕ) (χ : DirichletCharacter ℂ q) :=
    ((c χ * characterCoefficients a χ j) * DyadicMixedB4Fourier.mode ((j : ℤ) + 1) t) * χ (u : ZMod q)
  calc
    _ = ∑ j ∈ range Y, ∑ χ ∈ characters, entry j χ := by
      unfold finiteTwistedSum mixture
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun χ _ => ?_
      unfold entry characterCoefficients
      ring
    _ = ∑ χ ∈ characters, ∑ j ∈ range Y, entry j χ := sum_comm
    _ = _ := by
      refine sum_congr rfl fun χ _ => ?_
      unfold finiteTwistedSum
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      unfold entry
      ring

theorem mixed_character_prefix_moment {q : ℕ} [NeZero q] (X Y : ℕ)
    (characters : Finset (DirichletCharacter ℂ q)) (a : ℕ → ℂ)
    (c : DirichletCharacter ℂ q → ℂ) {C : ℝ}
    (cBound : ∀ χ ∈ characters, ‖c χ‖ ≤ C) :
    (∑ u ∈ range X, finitePrefixEnergy Y (mixture characters a c u)) ≤
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t) * (((X : ℝ) + q) * C ^ 2) *
        ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
          ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2 := by
  let w := prefixMajorant Y
  let mass : ℝ := ∫ t in (0 : ℝ)..1, w t
  let bound : ℝ := ((X : ℝ) + q) * C ^ 2
  let polynomial (u : ℕ) := finiteTwistedSum Y (mixture characters a c u)
  let characterEnergy (t : ℝ) := ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2
  have wContinuous : Continuous w := prefixMajorant_continuous Y
  have wPositive (t : ℝ) : 0 < w t := prefixMajorant_positive Y t
  have massPositive : 0 < mass := integral_prefixMajorant_positive Y
  have polynomialContinuous (u : ℕ) : Continuous (polynomial u) := continuous_finiteTwistedSum _ _
  have characterEnergyContinuous : Continuous characterEnergy :=
    continuous_finsetSum _ fun χ _ => (continuous_finiteTwistedSum Y (characterCoefficients a χ)).norm.pow 2
  have atPhase (t : ℝ) : (∑ u ∈ range X, ‖polynomial u t‖ ^ 2) ≤ bound * characterEnergy t := by
    have dual := dual_interval_le X characters
      (fun χ => c χ * finiteTwistedSum Y (characterCoefficients a χ) t)
    simp only [polynomial, finiteTwistedSum_mixture]
    refine dual.trans ?_
    unfold bound characterEnergy
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_sum]
    refine sum_le_sum fun χ member => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (cBound χ member) 2) (sq_nonneg _)
  have integralSum :
      (∑ u ∈ range X, ∫ t in (0 : ℝ)..1, w t * ‖polynomial u t‖ ^ 2) =
        ∫ t in (0 : ℝ)..1, w t * ∑ u ∈ range X, ‖polynomial u t‖ ^ 2 := by
    have intPolynomial (u : ℕ) : IntervalIntegrable (fun t => w t * ‖polynomial u t‖ ^ 2)
        volume 0 1 := (wContinuous.mul ((polynomialContinuous u).norm.pow 2)).intervalIntegrable 0 1
    rw [← intervalIntegral.integral_finsetSum (fun u _ => intPolynomial u)]
    apply intervalIntegral.integral_congr
    intro t _
    change (∑ u ∈ range X, w t * ‖polynomial u t‖ ^ 2) = w t * ∑ u ∈ range X, ‖polynomial u t‖ ^ 2
    exact (mul_sum _ _ _).symm
  have continuousSquareSum : Continuous (fun t => ∑ u ∈ range X, ‖polynomial u t‖ ^ 2) :=
    continuous_finsetSum _ fun u _ => (polynomialContinuous u).norm.pow 2
  change _ ≤ mass * bound * ∫ t in (0 : ℝ)..1, w t * characterEnergy t
  calc
    _ ≤ ∑ u ∈ range X, mass * ∫ t in (0 : ℝ)..1, w t * ‖polynomial u t‖ ^ 2 := by
      exact sum_le_sum fun u _ => finitePrefixEnergy_le_twists Y (mixture characters a c u)
    _ = mass * ∫ t in (0 : ℝ)..1, w t * ∑ u ∈ range X, ‖polynomial u t‖ ^ 2 := by
      rw [← mul_sum, integralSum]
    _ ≤ mass * ∫ t in (0 : ℝ)..1, w t * (bound * characterEnergy t) := by
      refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
        ((wContinuous.mul continuousSquareSum).intervalIntegrable 0 1)
        ((wContinuous.mul (continuous_const.mul characterEnergyContinuous)).intervalIntegrable 0 1)
        (fun t _ => mul_le_mul_of_nonneg_left (atPhase t) (wPositive t).le)) massPositive.le
    _ = _ := by
      have commute : (∫ t in (0 : ℝ)..1, w t * (bound * characterEnergy t)) =
          ∫ t in (0 : ℝ)..1, bound * (w t * characterEnergy t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change w t * (bound * characterEnergy t) = bound * (w t * characterEnergy t)
        exact mul_left_comm _ _ _
      rw [commute, intervalIntegral.integral_const_mul, ← mul_assoc]


end
end DyadicMixedB4MixedCharacter

end

section

open Finset MeasureTheory DyadicMixedB4KernelControl DyadicMixedB4WindowKernel
open DyadicMixedB4ArcGeometry DyadicMixedB4MixedCharacter DyadicMixedB4MaximalSieve

namespace DyadicMixedB4DyadicBlock

noncomputable section

theorem sum_sqrt_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (nonnegative : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, Real.sqrt (f i)) ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, f i) := by
  have squares : (∑ i ∈ s, Real.sqrt (f i)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i := by
    have cs := sum_mul_sq_le_sq_mul_sq s (fun _ : ι => (1 : ℝ)) (fun i => Real.sqrt (f i))
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at cs
    have simplify : (∑ i ∈ s, Real.sqrt (f i) ^ 2) = ∑ i ∈ s, f i :=
      sum_congr rfl fun i member => Real.sq_sqrt (nonnegative i member)
    rwa [simplify] at cs
  calc
    _ = Real.sqrt ((∑ i ∈ s, Real.sqrt (f i)) ^ 2) :=
      (Real.sqrt_sq (sum_nonneg fun i _ => Real.sqrt_nonneg (f i))).symm
    _ ≤ _ := Real.sqrt_le_sqrt squares

theorem prefix_norm_le_sqrt_energy (Y x : ℕ) (a : ℕ → ℂ) (xBound : x ≤ Y) :
    ‖∑ j ∈ range x, a j‖ ≤ Real.sqrt (finitePrefixEnergy Y a) := by
  have member : x ∈ range (Y + 1) := mem_range.mpr (Nat.lt_succ_of_le xBound)
  have square := Finset.le_sup' (fun k => ‖∑ j ∈ range k, a j‖ ^ 2) member
  calc
    _ = Real.sqrt (‖∑ j ∈ range x, a j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt square

theorem finitePrefixEnergy_nonnegative (Y : ℕ) (a : ℕ → ℂ) : 0 ≤ finitePrefixEnergy Y a := by
  have member : 0 ∈ range (Y + 1) := by simp
  exact (sq_nonneg ‖∑ j ∈ range 0, a j‖).trans (Finset.le_sup' (fun x => ‖∑ j ∈ range x, a j‖ ^ 2) member)

theorem weighted_mixture_block_le {d : ℕ} [NeZero d] (n M B H q g l r X Y : ℕ)
    (nPositive : 0 < n) (radiusUpper : radius M ≤ 1)
    (characters : Finset (DirichletCharacter ℂ d)) (a : ℕ → ℂ) (c : DirichletCharacter ℂ d → ℂ)
    (support : Finset ℕ) (supportBound : support ⊆ range X) (start length : ℕ → ℕ) (weight : ℕ → ℂ)
    (startPositive : ∀ u ∈ support, 0 < start u) (lengthBound : ∀ u ∈ support, length u ≤ Y)
    (productBound : ∀ u ∈ support, start u * length u ≤ n)
    {W C : ℝ} (WNonnegative : 0 ≤ W) (CNonnegative : 0 ≤ C)
    (weightBound : ∀ u ∈ support, ‖weight u‖ ≤ W) (characterBound : ∀ χ ∈ characters, ‖c χ‖ ≤ C) :
    ‖∑ u ∈ support, weight u * (∑ j ∈ range (length u), windowKernel n M B H q g l r
      ((start u : ℝ) * ((j : ℝ) + 1) - n) • mixture characters a c u j)‖ ≤
      W * (16 / (g : ℝ) + 24 / (g : ℝ) * Real.log ((n : ℝ) + 1)) * C *
        Real.sqrt ((X : ℝ) * ((X : ℝ) + d) *
          (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
          ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
            ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2) := by
  let L : ℝ := 16 / (g : ℝ) + 24 / (g : ℝ) * Real.log ((n : ℝ) + 1)
  let E (u : ℕ) := finitePrefixEnergy Y (mixture characters a c u)
  let I : ℝ := ∫ t in (0 : ℝ)..1, prefixMajorant Y t
  let J : ℝ := ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
    ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2
  have logNonnegative : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have LNonnegative : 0 ≤ L := by dsimp [L]; positivity
  have Epositive (u : ℕ) : 0 ≤ E u := finitePrefixEnergy_nonnegative Y _
  have oneBound (u : ℕ) (uMember : u ∈ support) :
      ‖∑ j ∈ range (length u), windowKernel n M B H q g l r
        ((start u : ℝ) * ((j : ℝ) + 1) - n) • mixture characters a c u j‖ ≤ L * Real.sqrt (E u) :=
    weighted_windowKernel_sum_le n M B H q g l r (start u) (length u) (mixture characters a c u)
      nPositive (startPositive u uMember) (productBound u uMember) radiusUpper (Real.sqrt_nonneg _)
      (fun x xBound => prefix_norm_le_sqrt_energy Y x _ (xBound.trans (lengthBound u uMember)))
  have moment : (∑ u ∈ range X, E u) ≤ I * (((X : ℝ) + d) * C ^ 2) * J :=
    mixed_character_prefix_moment X Y characters a c characterBound
  change _ ≤ W * L * C * Real.sqrt ((X : ℝ) * ((X : ℝ) + d) * I * J)
  calc
    _ ≤ ∑ u ∈ support, ‖weight u * (∑ j ∈ range (length u), windowKernel n M B H q g l r
        ((start u : ℝ) * ((j : ℝ) + 1) - n) • mixture characters a c u j)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ support, W * (L * Real.sqrt (E u)) := by
      refine sum_le_sum fun u uMember => ?_
      rw [norm_mul]
      exact mul_le_mul (weightBound u uMember) (oneBound u uMember) (norm_nonneg _) WNonnegative
    _ ≤ ∑ u ∈ range X, W * (L * Real.sqrt (E u)) :=
      sum_le_sum_of_subset_of_nonneg supportBound
        (fun u _ _ => mul_nonneg WNonnegative (mul_nonneg LNonnegative (Real.sqrt_nonneg (E u))))
    _ = W * L * ∑ u ∈ range X, Real.sqrt (E u) := by simp only [← mul_assoc, ← mul_sum]
    _ ≤ W * L * Real.sqrt ((X : ℝ) * ∑ u ∈ range X, E u) :=
      mul_le_mul_of_nonneg_left (by simpa only [card_range] using sum_sqrt_le (range X) E (fun u _ => Epositive u))
        (mul_nonneg WNonnegative LNonnegative)
    _ ≤ W * L * Real.sqrt ((X : ℝ) * (I * (((X : ℝ) + d) * C ^ 2) * J)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left moment (Nat.cast_nonneg _)))
        (mul_nonneg WNonnegative LNonnegative)
    _ = _ := by
      rw [show (X : ℝ) * (I * (((X : ℝ) + d) * C ^ 2) * J) =
        C ^ 2 * ((X : ℝ) * ((X : ℝ) + d) * I * J) by ring, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq CNonnegative]
      ring


end
end DyadicMixedB4DyadicBlock

end

section

open Finset MeasureTheory ArithmeticFunction DyadicMixedB4DyadicBlock
open DyadicMixedB4ArcGeometry DyadicMixedB4KernelControl DyadicMixedB4MixedCharacter DyadicMixedB4MaximalSieve

namespace DyadicMixedB4FixedBlock

noncomputable section

def mangoldtAbove (U j : ℕ) : ℂ := if U < j + 1 then (Λ (j + 1) : ℂ) else 0

theorem sum_Ioc_as_range_prefix {R : Type*} [AddCommMonoid R] (U L : ℕ) (F : ℕ → R) :
    (∑ b ∈ Ioc U L, F b) = ∑ j ∈ range L, if U < j + 1 then F (j + 1) else 0 := by
  rw [← sum_filter]
  symm
  apply sum_bij (s := (range L).filter (fun j => U < j + 1)) (t := Ioc U L) (fun j _ => j + 1)
  · intro j membership
    obtain ⟨upper, lower⟩ := mem_filter.mp membership
    exact mem_Ioc.mpr ⟨lower, Nat.succ_le_of_lt (mem_range.mp upper)⟩
  · intro j _ k _ equality
    omega
  · intro b membership
    obtain ⟨lower, upper⟩ := mem_Ioc.mp membership
    exact ⟨b - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩, by omega⟩
  · intro j _
    rfl

theorem fixed_conductor_block_le {d : ℕ} [NeZero d] (n M B H q step lower upper A g U : ℕ)
    (nPositive : 0 < n) (APositive : 0 < A) (gPositive : 0 < g) (radiusUpper : radius M ≤ 1)
    (indices : Finset ℕ) (indexRange : indices ⊆ Ico A (2 * A)) (indexDivisible : ∀ a ∈ indices, g ∣ a)
    (weight : ℕ → ℂ) {W C : ℝ} (WNonnegative : 0 ≤ W) (CNonnegative : 0 ≤ C)
    (weightBound : ∀ a ∈ indices, ‖weight a‖ ≤ W) (characters : Finset (DirichletCharacter ℂ d))
    (c : DirichletCharacter ℂ d → ℂ) (cBound : ∀ χ ∈ characters, ‖c χ‖ ≤ C) :
    let X := (2 * A) / g + 1
    let Y := n / A
    ‖∑ a ∈ indices, weight a * (∑ j ∈ range (n / a), windowKernel n M B H q step lower upper
      ((a : ℝ) * ((j : ℝ) + 1) - n) • mixture characters (mangoldtAbove U) c (a / g) j)‖ ≤
      W * (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) * C *
        Real.sqrt ((X : ℝ) * ((X : ℝ) + d) *
          (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
          ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
            ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients (mangoldtAbove U) χ) t‖ ^ 2) := by
  dsimp only
  let X := (2 * A) / g + 1
  let Y := n / A
  let quotients := indices.image (fun a => a / g)
  let start (u : ℕ) := g * u
  let length (u : ℕ) := n / start u
  have startExact (a : ℕ) (member : a ∈ indices) : start (a / g) = a := Nat.mul_div_cancel' (indexDivisible a member)
  have injOn : Set.InjOn (fun a => a / g) (indices : Set ℕ) := by
    intro a aMember b bMember equality
    exact (startExact a aMember).symm.trans ((congrArg start equality).trans (startExact b bMember))
  have supportBound : quotients ⊆ range X := by
    intro u membership
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    have upperA := (mem_Ico.mp (indexRange member)).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right upperA.le))
  have startPositive (u : ℕ) (membership : u ∈ quotients) : 0 < start u := by
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    rw [startExact a member]
    exact APositive.trans_le (mem_Ico.mp (indexRange member)).1
  have lengthBound (u : ℕ) (membership : u ∈ quotients) : length u ≤ Y := by
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    unfold length
    rw [startExact a member]
    apply (Nat.le_div_iff_mul_le APositive).mpr
    exact (Nat.mul_le_mul_left _ (mem_Ico.mp (indexRange member)).1).trans (Nat.div_mul_le_self n a)
  have productBound (u : ℕ) (_ : u ∈ quotients) : start u * length u ≤ n := by
    unfold length
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  have mappedWeightBound (u : ℕ) (membership : u ∈ quotients) : ‖weight (start u)‖ ≤ W := by
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    rw [startExact a member]
    exact weightBound a member
  have main := weighted_mixture_block_le n M B H q step lower upper X Y nPositive radiusUpper characters
    (mangoldtAbove U) c quotients supportBound start length (fun u => weight (start u)) startPositive lengthBound
    productBound WNonnegative CNonnegative mappedWeightBound cBound
  unfold quotients at main
  rw [sum_image injOn] at main
  have convertSum : (∑ a ∈ indices, weight (start (a / g)) *
      (∑ j ∈ range (length (a / g)), windowKernel n M B H q step lower upper
        ((start (a / g) : ℝ) * ((j : ℝ) + 1) - n) • mixture characters (mangoldtAbove U) c (a / g) j)) =
      ∑ a ∈ indices, weight a * (∑ j ∈ range (n / a), windowKernel n M B H q step lower upper
        ((a : ℝ) * ((j : ℝ) + 1) - n) • mixture characters (mangoldtAbove U) c (a / g) j) := by
    refine sum_congr rfl fun a member => ?_
    unfold length
    rw [startExact a member]
  rwa [convertSum] at main


end
end DyadicMixedB4FixedBlock

end

section

open Finset MeasureTheory DyadicMixedB4MaximalSieve BombieriVinogradov.LargeSieve

namespace DyadicMixedB4PrimitiveEnergy

noncomputable section

def primitiveEnergy (Y q : ℕ) (a : ℤ → ℂ) (t : ℝ) : ℝ :=
  ∑ χ ∈ primitiveCharacters q, ‖intervalCharacterSum (twist a t) 0 Y q χ‖ ^ 2

def integratedPrimitiveEnergy (Y q : ℕ) (a : ℤ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, prefixMajorant Y t * primitiveEnergy Y q a t

theorem primitiveEnergy_nonnegative (Y q : ℕ) (a : ℤ → ℂ) (t : ℝ) : 0 ≤ primitiveEnergy Y q a t :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem primitiveEnergy_continuous (Y q : ℕ) (a : ℤ → ℂ) : Continuous (primitiveEnergy Y q a) :=
  continuous_finsetSum _ fun χ _ => (continuous_twistedCharacterSum a Y q χ).norm.pow 2

theorem integratedPrimitiveEnergy_nonnegative (Y q : ℕ) (a : ℤ → ℂ) : 0 ≤ integratedPrimitiveEnergy Y q a :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun t => mul_nonneg (prefixMajorant_positive Y t).le (primitiveEnergy_nonnegative Y q a t))

theorem sum_primitiveEnergy_le (Y Q : ℕ) (a : ℤ → ℂ) (t : ℝ) (QPositive : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, primitiveEnergy Y q a t) ≤ 64 * ((Y : ℝ) + (Q : ℝ) ^ 2) *
      ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2 := by
  have normTwist (m : ℤ) : ‖twist a t m‖ = ‖a m‖ := by
    rw [twist, norm_mul, show ‖DyadicMixedB4Fourier.mode m t‖ = 1 by
      simp [DyadicMixedB4Fourier.mode, DyadicMixedB4Fourier.frequency, Complex.norm_exp], mul_one]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * primitiveEnergy Y q a t := by
      refine sum_le_sum fun q member => ?_
      have qPositive := (mem_Icc.mp member).1
      have totientPositive : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr qPositive
      have weight : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
        (one_le_div totientPositive).mpr (by exact_mod_cast Nat.totient_le q)
      exact le_mul_of_one_le_left (primitiveEnergy_nonnegative Y q a t) weight
    _ ≤ _ := by
      simpa only [primitiveEnergy, zero_add, normTwist] using characterLargeSieveNat 0 Y Q (twist a t) QPositive

theorem sum_integratedPrimitiveEnergy_le (Y Q : ℕ) (a : ℤ → ℂ) (QPositive : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, integratedPrimitiveEnergy Y q a) ≤
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t) * (64 * ((Y : ℝ) + (Q : ℝ) ^ 2) *
        ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2) := by
  let w := prefixMajorant Y
  let P : ℝ := 64 * ((Y : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2
  have wContinuous : Continuous w := prefixMajorant_continuous Y
  have integrable (q : ℕ) : IntervalIntegrable (fun t => w t * primitiveEnergy Y q a t) volume 0 1 :=
    (wContinuous.mul (primitiveEnergy_continuous Y q a)).intervalIntegrable 0 1
  have sumContinuous : Continuous (fun t => ∑ q ∈ Icc 1 Q, primitiveEnergy Y q a t) :=
    continuous_finsetSum _ fun q _ => primitiveEnergy_continuous Y q a
  change _ ≤ (∫ t in (0 : ℝ)..1, w t) * P
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ q ∈ Icc 1 Q, w t * primitiveEnergy Y q a t := by
      unfold integratedPrimitiveEnergy
      rw [intervalIntegral.integral_finsetSum (fun q _ => integrable q)]
    _ = ∫ t in (0 : ℝ)..1, w t * ∑ q ∈ Icc 1 Q, primitiveEnergy Y q a t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (mul_sum _ _ _).symm
    _ ≤ ∫ t in (0 : ℝ)..1, w t * P := by
      exact intervalIntegral.integral_mono_on zero_le_one
        ((wContinuous.mul sumContinuous).intervalIntegrable 0 1)
        ((wContinuous.mul continuous_const).intervalIntegrable 0 1)
        (fun t _ => mul_le_mul_of_nonneg_left (sum_primitiveEnergy_le Y Q a t QPositive)
          (prefixMajorant_positive Y t).le)
    _ = _ := intervalIntegral.integral_mul_const _ _

theorem dyadic_integratedPrimitiveEnergy_le (Y D : ℕ) (a : ℤ → ℂ) (DPositive : 0 < D) :
    (∑ q ∈ Ico D (2 * D), integratedPrimitiveEnergy Y q a) ≤
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t) * (64 * ((Y : ℝ) + ((2 * D : ℕ) : ℝ) ^ 2) *
        ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2) := by
  have subset : Ico D (2 * D) ⊆ Icc 1 (2 * D) := by
    intro q member
    obtain ⟨lower, upper⟩ := mem_Ico.mp member
    exact mem_Icc.mpr ⟨DPositive.trans_le lower, upper.le⟩
  exact (sum_le_sum_of_subset_of_nonneg subset (fun q _ _ => integratedPrimitiveEnergy_nonnegative Y q a)).trans
    (sum_integratedPrimitiveEnergy_le Y (2 * D) a (by omega))

def naturalCoefficientExtension (a : ℕ → ℂ) (m : ℤ) : ℂ := a ((m - 1).toNat)

theorem characterCoefficients_eq_extension {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    DyadicMixedB4MixedCharacter.characterCoefficients a χ =
      fun (j : ℕ) => naturalCoefficientExtension a ((j : ℤ) + 1) * χ (((j : ℤ) + 1 : ℤ) : ZMod q) := by
  funext j
  simp [DyadicMixedB4MixedCharacter.characterCoefficients, naturalCoefficientExtension]


end
end DyadicMixedB4PrimitiveEnergy

end

section

open Finset MeasureTheory ArithmeticFunction BombieriVinogradov.LargeSieve
open DyadicMixedB4FixedBlock DyadicMixedB4PrimitiveEnergy DyadicMixedB4DyadicBlock
open DyadicMixedB4MaximalSieve DyadicMixedB4MixedCharacter

namespace DyadicMixedB4BilinearEnergy

noncomputable section

def prefixMass (Y : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, prefixMajorant Y t

theorem prefixMass_nonnegative (Y : ℕ) : 0 ≤ prefixMass Y :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (prefixMajorant_positive Y t).le)

def mangoldtExtension (U : ℕ) : ℤ → ℂ := naturalCoefficientExtension (mangoldtAbove U)

def blockEnergy (n A U g d : ℕ) : ℝ :=
  let X := (2 * A) / g + 1
  let Y := n / A
  Real.sqrt ((X : ℝ) * ((X : ℝ) + d) * prefixMass Y *
    integratedPrimitiveEnergy Y d (mangoldtExtension U))

theorem finiteTwistedSum_eq_primitiveEnergy {d : ℕ} (Y U : ℕ) (χ : DirichletCharacter ℂ d) (t : ℝ) :
    finiteTwistedSum Y (characterCoefficients (mangoldtAbove U) χ) t =
      intervalCharacterSum (twist (mangoldtExtension U) t) 0 Y d χ := by
  unfold finiteTwistedSum intervalCharacterSum
  rw [sum_int_Ioc_eq_sum_range]
  simp only [zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [characterCoefficients_eq_extension]
  unfold twist mangoldtExtension
  ring

theorem energy_mangoldt_le (U Y : ℕ) :
    (∑ b ∈ Ioc (0 : ℤ) (Y : ℤ), ‖mangoldtExtension U b‖ ^ 2) ≤
      (Y : ℝ) * Real.log ((Y : ℝ) + 2) ^ 2 := by
  have atOne (j : ℕ) (membership : j ∈ range Y) : ‖mangoldtAbove U j‖ ≤ Real.log ((Y : ℝ) + 2) := by
    unfold mangoldtAbove
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
        (by exact_mod_cast (show j + 1 ≤ Y + 2 by have := mem_range.mp membership; omega)))
    · rw [norm_zero]
      exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  calc
    _ = ∑ j ∈ range Y, ‖mangoldtAbove U j‖ ^ 2 := by
      rw [← zero_add (Y : ℤ), sum_int_Ioc_eq_sum_range]
      simp [mangoldtExtension, naturalCoefficientExtension]
    _ ≤ ∑ _ ∈ range Y, Real.log ((Y : ℝ) + 2) ^ 2 :=
      sum_le_sum fun j member => pow_le_pow_left₀ (norm_nonneg _) (atOne j member) 2
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_range]

theorem sum_sqrt_dyadic_energy_le (Y U D : ℕ) (DPositive : 0 < D) :
    (∑ d ∈ Ico D (2 * D), Real.sqrt (integratedPrimitiveEnergy Y d (mangoldtExtension U))) ≤
      16 * Real.log ((Y : ℝ) + 2) * Real.sqrt ((D : ℝ) * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * Y) := by
  let J d := integratedPrimitiveEnergy Y d (mangoldtExtension U)
  let L := Real.log ((Y : ℝ) + 2)
  have LNonnegative : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  have massNonnegative := prefixMass_nonnegative Y
  have setCard : (Ico D (2 * D)).card = D := by rw [Nat.card_Ico]; omega
  have bound : (∑ d ∈ Ico D (2 * D), J d) ≤
      256 * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * (Y : ℝ) * L ^ 2 := by
    calc
      _ ≤ prefixMass Y * (64 * ((Y : ℝ) + ((2 * D : ℕ) : ℝ) ^ 2) *
          ∑ b ∈ Ioc (0 : ℤ) (Y : ℤ), ‖mangoldtExtension U b‖ ^ 2) :=
        dyadic_integratedPrimitiveEnergy_le Y D (mangoldtExtension U) DPositive
      _ ≤ prefixMass Y * (64 * ((Y : ℝ) + ((2 * D : ℕ) : ℝ) ^ 2) * ((Y : ℝ) * L ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (energy_mangoldt_le U Y) (by positivity)) massNonnegative
      _ ≤ _ := by
        push_cast
        nlinarith only [mul_nonneg massNonnegative (mul_nonneg (sq_nonneg (Y : ℝ)) (sq_nonneg L))]
  calc
    _ ≤ Real.sqrt ((D : ℝ) * ∑ d ∈ Ico D (2 * D), J d) := by
      simpa only [setCard] using sum_sqrt_le (Ico D (2 * D)) J
        (fun d _ => integratedPrimitiveEnergy_nonnegative Y d (mangoldtExtension U))
    _ ≤ Real.sqrt ((D : ℝ) * (256 * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * (Y : ℝ) * L ^ 2)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _))
    _ = _ := by
      have factor : (D : ℝ) * (256 * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * (Y : ℝ) * L ^ 2) =
          (16 * L) ^ 2 * ((D : ℝ) * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * Y) := by ring
      rw [factor, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 16 * L)]


end
end DyadicMixedB4BilinearEnergy

end

section

open Finset BombieriVinogradov.LargeSieve DyadicMixedB4DualCharacter
open scoped Classical

namespace DyadicMixedB4GaussLift

noncomputable section

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (d f : ℕ) (F : ℕ → R) :
    ∑ x ∈ range (d * f), F x = ∑ j ∈ range f, ∑ a ∈ range d, F (d * j + a) := by
  induction f with
  | zero => simp
  | succ f ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem stdAddChar_nat_fraction {q : ℕ} [NeZero q] (k : ℕ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
  unfold additivePhase
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem stdAddChar_mul_nat_fraction {q : ℕ} [NeZero q] (k a : ℕ) :
    ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) = additivePhase ((k : ℝ) * a / q) := by
  rw [← Nat.cast_mul, stdAddChar_nat_fraction, Nat.cast_mul]

set_option maxHeartbeats 600000 in
theorem sum_phase_fraction_eq_if_dvd {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ a ∈ range q, additivePhase ((k : ℝ) * a / q)) = if q ∣ k then (q : ℂ) else 0 := by
  simp_rw [← stdAddChar_mul_nat_fraction]
  rw [sum_natCast_range_eq_zmod (fun z => ZMod.stdAddChar ((k : ZMod q) * z))]
  simp_rw [mul_comm (k : ZMod q)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have zeroIff : (k : ZMod q) = 0 ↔ q ∣ k := by rw [ZMod.natCast_eq_zero_iff]
  by_cases divides : q ∣ k
  · simp [divides, zeroIff.mpr divides]
  · have nonzero : (k : ZMod q) ≠ 0 := fun zero => divides (zeroIff.mp zero)
    simp [divides, nonzero]

theorem gaussSum_as_fraction_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod d)) =
      ∑ a ∈ range d, χ (a : ZMod d) * additivePhase ((k : ℝ) * a / d) := by
  unfold gaussSum
  rw [← sum_natCast_range_eq_zmod]
  simp_rw [AddChar.mulShift_apply, stdAddChar_mul_nat_fraction]

set_option maxHeartbeats 600000 in
theorem lift_gaussSum {d f : ℕ} [NeZero d] [NeZero f]
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (∑ u ∈ range (d * f), χ (u : ZMod d) * additivePhase ((k : ℝ) * u / ((d : ℝ) * f))) =
      if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
  have dNonzero : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have fNonzero : (f : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne f
  rw [sum_range_blocks, Finset.sum_comm]
  have liftEntry (a j : ℕ) :
      χ ((d * j + a : ℕ) : ZMod d) * additivePhase ((k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f)) =
        (χ (a : ZMod d) * additivePhase ((k : ℝ) * a / ((d : ℝ) * f))) *
          additivePhase ((k : ℝ) * j / f) := by
    have angle : (k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f) =
        (k : ℝ) * a / ((d : ℝ) * f) + (k : ℝ) * j / f := by
      push_cast
      field_simp
      ring
    rw [angle, additivePhase_add, ← mul_assoc]
    have same : ((d * j + a : ℕ) : ZMod d) = (a : ZMod d) := by push_cast; simp
    rw [same]
  simp_rw [liftEntry, ← mul_sum, sum_phase_fraction_eq_if_dvd]
  by_cases divisible : f ∣ k
  · simp only [if_pos divisible, ← Finset.sum_mul, gaussSum_as_fraction_sum]
    rw [mul_comm _ (f : ℂ)]
    apply congrArg (fun z : ℂ => (f : ℂ) * z)
    refine sum_congr rfl fun a _ => ?_
    have h : (k : ℝ) = ((k / f : ℕ) : ℝ) * f := by
      exact_mod_cast (Nat.div_mul_cancel divisible).symm
    have sameAngle : (k : ℝ) * a / ((d : ℝ) * f) = (((k / f : ℕ) : ℝ)) * a / d := by
      conv_lhs => rw [h]
      field_simp
    rw [sameAngle]
  · simp [divisible]


end
end DyadicMixedB4GaussLift

end

section

open Finset ArithmeticFunction BombieriVinogradov.LargeSieve DyadicMixedB4GaussLift
open scoped ArithmeticFunction.Moebius Classical

namespace DyadicMixedB4MoebiusGauss

noncomputable section

def moebiusComplex (m : ℕ) : ℂ := (μ m : ℂ)

theorem norm_moebiusComplex_le_one (m : ℕ) : ‖moebiusComplex m‖ ≤ 1 := by
  rw [moebiusComplex, Complex.norm_intCast]
  exact_mod_cast (abs_moebius_le_one (n := m))

theorem moebius_coprime_indicator {M : ℕ} (MPositive : 0 < M) (u : ℕ) :
    (∑ e ∈ M.divisors.filter (fun e => e ∣ u), moebiusComplex e) =
      if u.Coprime M then (1 : ℂ) else 0 := by
  let g := u.gcd M
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right u MPositive
  have divisorsEquality : M.divisors.filter (fun e => e ∣ u) = g.divisors := by
    ext e
    rw [mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨eDividesM, _⟩, eDividesU⟩
      exact ⟨Nat.dvd_gcd eDividesU eDividesM, gPositive.ne'⟩
    · rintro ⟨eDividesG, _⟩
      exact ⟨⟨eDividesG.trans (Nat.gcd_dvd_right u M), MPositive.ne'⟩,
        eDividesG.trans (Nat.gcd_dvd_left u M)⟩
  have convolution : (∑ e ∈ g.divisors, μ e) = (1 : ArithmeticFunction ℤ) g := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta]
  rw [divisorsEquality]
  simp_rw [moebiusComplex, ← Int.cast_sum, convolution]
  change (((1 : ArithmeticFunction ℤ) g : ℤ) : ℂ) = if g = 1 then (1 : ℂ) else 0
  by_cases one : g = 1
  · simp [one, one_apply]
  · simp [one, one_apply]

theorem changeLevel_nat_indicator {d M : ℕ} (dDivides : d ∣ M) (χ : DirichletCharacter ℂ d)
    (u : ℕ) : DirichletCharacter.changeLevel dDivides χ (u : ZMod M) =
      (if u.Coprime M then (1 : ℂ) else 0) * χ (u : ZMod d) := by
  by_cases coprime : u.Coprime M
  · rw [if_pos coprime, one_mul]
    have same := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dDivides (ZMod.unitOfCoprime u coprime)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast dDivides] at same
    exact same
  · rw [if_neg coprime, zero_mul]
    exact MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime u M).mp unit))

theorem sum_filter_dvd_range {R : Type*} [AddCommMonoid R] {e M : ℕ}
    (ePositive : 0 < e) (eDivides : e ∣ M) (F : ℕ → R) :
    (∑ u ∈ (range M).filter (fun u => e ∣ u), F u) = ∑ v ∈ range (M / e), F (e * v) := by
  have quotient : e * (M / e) = M := Nat.mul_div_cancel' eDivides
  symm
  apply sum_bij (s := range (M / e)) (t := (range M).filter (fun u => e ∣ u)) (fun v _ => e * v)
  · intro v vMember
    refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right e v⟩
    rw [← quotient]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp vMember) ePositive
  · intro v _ w _ eq
    exact Nat.eq_of_mul_eq_mul_left ePositive eq
  · intro u uMember
    obtain ⟨uRange, v, h⟩ := mem_filter.mp uMember
    refine ⟨v, mem_range.mpr ?_, h.symm⟩
    have prodLt : e * v < e * (M / e) := h ▸ quotient.symm ▸ mem_range.mp uRange
    exact Nat.lt_of_mul_lt_mul_left prodLt
  · intro v _
    rfl

theorem sum_inducedGauss_moebius {d M : ℕ} [NeZero M] (dDivides : d ∣ M)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M)) =
      ∑ e ∈ M.divisors, moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) * additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) := by
  rw [gaussSum_as_fraction_sum]
  calc
    _ = ∑ u ∈ range M, ∑ e ∈ M.divisors.filter (fun e => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [changeLevel_nat_indicator, ← moebius_coprime_indicator (NeZero.pos M), mul_assoc, sum_mul]
    _ = ∑ e ∈ M.divisors, ∑ u ∈ (range M).filter (fun u => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun e eMember => ?_
      have eDivides := (Nat.mem_divisors.mp eMember).1
      have ePositive := Nat.pos_of_mem_divisors eMember
      have eNonzero : (e : ℝ) ≠ 0 := by exact_mod_cast ePositive.ne'
      have MNonzero : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
      have quotientNonzero : ((M / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast quotientPositive.ne'
      have quotient : (M : ℝ) = e * ((M / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' eDivides).symm
      rw [sum_filter_dvd_range ePositive eDivides, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      have scales : (k : ℝ) * (e * v : ℕ) / M = (k : ℝ) * v / ((M / e : ℕ) : ℝ) := by
        push_cast
        rw [quotient]
        field_simp
      rw [scales, Nat.cast_mul, map_mul]
      ring


end
end DyadicMixedB4MoebiusGauss

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open scoped Classical

namespace DyadicMixedB4ImprimitiveBound

noncomputable section

theorem norm_primitive_gauss_shift_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (x : ZMod d) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ ≤ Real.sqrt d := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar primitive, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar primitive]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem conductor_cofactor {M d e : ℕ} [NeZero d] [NeZero M] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (coprime : e.Coprime d) :
    0 < M / e / d ∧ d * (M / e / d) = M / e ∧ e * (d * (M / e / d)) = M := by
  have eDivides := (Nat.mem_divisors.mp eMember).1
  have ePositive := Nat.pos_of_mem_divisors eMember
  have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
  have joint : e * d ∣ M := coprime.mul_dvd_of_dvd_of_dvd eDivides dDivides
  have dividesQuotient : d ∣ M / e := (Nat.dvd_div_iff_mul_dvd eDivides).mpr (by simpa [mul_comm] using joint)
  have quotient := Nat.mul_div_cancel' dividesQuotient
  exact ⟨Nat.div_pos (Nat.le_of_dvd quotientPositive dividesQuotient) (NeZero.pos d), quotient,
    by rw [quotient, Nat.mul_div_cancel' eDivides]⟩

theorem norm_induced_gauss_term {M d e : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (k : ℕ) {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) :
    ‖moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) *
          BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ)))‖ ≤
      if e.Coprime d ∧ (M / e / d) ∣ k then ((M / e / d : ℕ) : ℝ) * Real.sqrt d else 0 := by
  by_cases coprime : e.Coprime d
  · obtain ⟨fPositive, hFactor, _⟩ := conductor_cofactor dDivides eMember coprime
    let f := M / e / d
    letI : NeZero f := ⟨fPositive.ne'⟩
    have liftIdentity : (∑ v ∈ range (M / e), χ (v : ZMod d) *
        BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) =
        if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
      convert lift_gaussSum (f := f) χ k using 1
      rw [show (M / e : ℕ) = d * f from hFactor.symm, Nat.cast_mul]
    rw [liftIdentity]
    by_cases divides : f ∣ k
    · have divides' : (M / e / d) ∣ k := divides
      have relevant : e.Coprime d ∧ (M / e / d) ∣ k := ⟨coprime, divides'⟩
      simp only [if_pos divides, if_pos relevant, norm_mul, Complex.norm_natCast]
      have factor : ‖moebiusComplex e‖ * ‖χ (e : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)).trans
          (by simpa only [mul_one] using norm_moebiusComplex_le_one e)
      refine (mul_le_of_le_one_left (by positivity) factor).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_primitive_gauss_shift_le primitive _) (Nat.cast_nonneg _)
    · have divides' : ¬(M / e / d) ∣ k := divides
      simp [divides, divides', coprime]
  · have valZero : χ (e : ZMod d) = 0 := MulChar.map_nonunit _
      (fun h => coprime ((ZMod.isUnit_iff_coprime e d).mp h))
    simp [coprime, valZero]

theorem norm_induced_gauss_le {M d : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M))‖ ≤
      Real.sqrt d * ∑ f ∈ k.divisors.filter (fun f => d * f ∣ M), (f : ℝ) := by
  let cof (e : ℕ) := M / e / d
  let support := M.divisors.filter (fun e => e.Coprime d ∧ cof e ∣ k)
  let bound := k.divisors.filter (fun f => d * f ∣ M)
  have imageSubset : support.image cof ⊆ bound := by
    intro f member
    obtain ⟨e, eMember, rfl⟩ := mem_image.mp member
    obtain ⟨divisor, coprime, divides⟩ := mem_filter.mp eMember
    obtain ⟨_, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, kPositive.ne'⟩,
      ⟨e, by rw [mul_comm]; exact identity.symm⟩⟩
  have injectiveOn : Set.InjOn cof (support : Set ℕ) := by
    intro e eMember e' e'Member same
    obtain ⟨divisor, coprime, _⟩ := mem_filter.mp eMember
    obtain ⟨divisor', coprime', _⟩ := mem_filter.mp e'Member
    obtain ⟨fPositive, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    obtain ⟨_, _, identity'⟩ := conductor_cofactor dDivides divisor' coprime'
    change e * (d * cof e) = M at identity
    change e' * (d * cof e') = M at identity'
    rw [← same] at identity'
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (NeZero.pos d) fPositive) (identity.trans identity'.symm)
  have sumBound : (∑ e ∈ support, (cof e : ℝ)) ≤ ∑ f ∈ bound, (f : ℝ) := by
    rw [← sum_image injectiveOn]
    exact sum_le_sum_of_subset_of_nonneg imageSubset fun _ _ _ => Nat.cast_nonneg _
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ?_
  have boundTerms := sum_le_sum (s := M.divisors)
    (fun e member => norm_induced_gauss_term dDivides member k primitive)
  refine boundTerms.trans ?_
  change (∑ e ∈ M.divisors, if e.Coprime d ∧ cof e ∣ k then (cof e : ℝ) * Real.sqrt d else 0) ≤
    Real.sqrt d * ∑ f ∈ bound, (f : ℝ)
  rw [← sum_filter, ← sum_mul, mul_comm (Real.sqrt d)]
  exact mul_le_mul_of_nonneg_right sumBound (Real.sqrt_nonneg _)


end
end DyadicMixedB4ImprimitiveBound

end

section

open Finset DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss BombieriVinogradov.LargeSieve
open scoped Classical ComplexConjugate

namespace DyadicMixedB4Ramanujan

noncomputable section

theorem phase_eq_additivePhase (x : ℝ) : phase x = additivePhase x := by
  simp only [phase, additivePhase, circleMap_zero, Complex.ofReal_one, one_mul]

theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  have conjTwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, conjTwo]
  ring

theorem norm_ramanujan_neg (q : ℕ) (k : ℤ) : ‖ramanujan q (-k)‖ = ‖ramanujan q k‖ := by
  have equality : ramanujan q (-k) = conj (ramanujan q k) := by
    simp only [ramanujan, Int.cast_neg, neg_mul, phase_neg, map_sum]
  rw [equality, Complex.norm_conj]

theorem numSet_eq_coprime_filter {q : ℕ} (qLower : 1 < q) :
    numSet q = (range q).filter (fun a => a.Coprime q) := by
  ext a
  simp only [numSet, mem_filter, mem_range]
  constructor
  · rintro ⟨upper, coprime⟩
    refine ⟨?_, coprime⟩
    by_contra! lower
    have equality : a = q := by omega
    subst a
    change q.gcd q = 1 at coprime
    rw [Nat.gcd_self] at coprime
    omega
  · rintro ⟨upper, coprime⟩
    exact ⟨upper.trans (Nat.lt_succ_self q), coprime⟩

theorem ramanujan_natural_gauss {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℕ) :
    ramanujan q (k : ℤ) = gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (k : ZMod q)) := by
  rw [ramanujan, numSet_eq_coprime_filter qLower, sum_filter, gaussSum_as_fraction_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [Int.cast_natCast, phase_eq_additivePhase, mul_div_assoc]
  by_cases coprime : a.Coprime q
  · rw [if_pos coprime, MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr coprime), one_mul]
  · rw [if_neg coprime, MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime a q).mp unit)), zero_mul]

theorem ramanujan_moebius {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℕ) :
    ramanujan q (k : ℤ) = ∑ e ∈ q.divisors,
      moebiusComplex e * if (q / e) ∣ k then ((q / e : ℕ) : ℂ) else 0 := by
  rw [ramanujan_natural_gauss qLower]
  have lifted := sum_inducedGauss_moebius (one_dvd q) (1 : DirichletCharacter ℂ 1) k
  rw [DirichletCharacter.changeLevel_one] at lifted
  rw [lifted]
  have oneValue (m : ℕ) : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
    rw [Subsingleton.elim (m : ZMod 1) (1 : ZMod 1), map_one]
  refine sum_congr rfl fun e eMember => ?_
  have positive : 0 < q / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) (Nat.mem_divisors.mp eMember).1)
    (Nat.pos_of_mem_divisors eMember)
  letI : NeZero (q / e) := ⟨positive.ne'⟩
  simp only [oneValue, mul_one, one_mul, sum_phase_fraction_eq_if_dvd]

theorem norm_ramanujan_le_divisor_sum {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℕ) :
    ‖ramanujan q (k : ℤ)‖ ≤ ∑ e ∈ q.divisors,
      if (q / e) ∣ k then ((q / e : ℕ) : ℝ) else 0 := by
  rw [ramanujan_moebius qLower]
  refine (norm_sum_le _ _).trans (sum_le_sum fun e _ => ?_)
  by_cases divides : (q / e) ∣ k
  · simp only [if_pos divides, norm_mul, Complex.norm_natCast]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (norm_moebiusComplex_le_one e)
  · simp [divides]

theorem sum_multiples_weight (N d : ℕ) :
    (∑ x ∈ range (N + 1), if d ∣ x then (d : ℝ) else 0) ≤ (N : ℝ) + d := by
  have decompose : (range (N + 1)).filter (fun x => d ∣ x) =
      insert 0 ((range (N + 1)).filter (fun x => x ≠ 0 ∧ d ∣ x)) := by
    ext x
    by_cases zero : x = 0
    · subst x; simp
    · simp [zero]
  have count : ((range (N + 1)).filter (fun x => d ∣ x)).card = N / d + 1 := by
    rw [decompose, card_insert_of_notMem (by simp), Nat.card_multiples']
  rw [← sum_filter, sum_const, count, nsmul_eq_mul]
  exact_mod_cast (show (N / d + 1) * d ≤ N + d by rw [add_mul, one_mul]; exact Nat.add_le_add_right (Nat.div_mul_le_self N d) _)

theorem sum_norm_ramanujan_le {q : ℕ} [NeZero q] (qLower : 1 < q) (N : ℕ) :
    (∑ k ∈ range (N + 1), ‖ramanujan q (k : ℤ)‖) ≤ (q.divisors.card : ℝ) * ((N : ℝ) + q) := by
  calc
    _ ≤ ∑ k ∈ range (N + 1), ∑ e ∈ q.divisors, if (q / e) ∣ k then ((q / e : ℕ) : ℝ) else 0 :=
      sum_le_sum fun k _ => norm_ramanujan_le_divisor_sum qLower k
    _ = ∑ e ∈ q.divisors, ∑ k ∈ range (N + 1), if (q / e) ∣ k then ((q / e : ℕ) : ℝ) else 0 := sum_comm
    _ ≤ ∑ _ ∈ q.divisors, ((N : ℝ) + q) := by
      refine sum_le_sum fun e _ => (sum_multiples_weight N (q / e)).trans ?_
      exact add_le_add_right (by exact_mod_cast Nat.div_le_self q e) _
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem sum_norm_shifted_ramanujan_le {q : ℕ} [NeZero q] (qLower : 1 < q) (N : ℕ) :
    (∑ k ∈ range (N + 1), ‖ramanujan q ((k : ℤ) - (N : ℤ))‖) ≤
      (q.divisors.card : ℝ) * ((N : ℝ) + q) := by
  calc
    _ = ∑ k ∈ range (N + 1), ‖ramanujan q ((N - k : ℕ) : ℤ)‖ := by
      refine sum_congr rfl fun k membership => ?_
      have bound := Nat.le_of_lt_succ (mem_range.mp membership)
      rw [show (k : ℤ) - (N : ℤ) = -((N - k : ℕ) : ℤ) by rw [Nat.cast_sub bound, neg_sub], norm_ramanujan_neg]
    _ = ∑ k ∈ range (N + 1), ‖ramanujan q (k : ℤ)‖ := by
      simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun k : ℕ => ‖ramanujan q (k : ℤ)‖) (N + 1)
    _ ≤ _ := sum_norm_ramanujan_le qLower N


end
end DyadicMixedB4Ramanujan

end

section

open Finset BombieriVinogradov.LargeSieve

namespace DyadicMixedB4RamanujanCharacters

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

theorem unit_character_expansion {r : ℕ} [NeZero r] (F : (ZMod r)ˣ → ℂ) (b : (ZMod r)ˣ) :
    F b = (∑ χ : DirichletCharacter ℂ r,
      (∑ x : (ZMod r)ˣ, star (χ (x : ZMod r)) * F x) * χ (b : ZMod r)) / (r.totient : ℂ) := by
  classical
  have positive : 0 < r.totient := Nat.totient_pos.mpr (NeZero.pos r)
  have divisor : (r.totient : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  apply (eq_div_iff divisor).mpr
  symm
  calc
    _ = ∑ χ : DirichletCharacter ℂ r, ∑ x : (ZMod r)ˣ,
        F x * (star (χ (x : ZMod r)) * χ (b : ZMod r)) := by
      refine sum_congr rfl fun χ _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun x _ => by ring
    _ = ∑ x : (ZMod r)ˣ, ∑ χ : DirichletCharacter ℂ r,
        F x * (star (χ (x : ZMod r)) * χ (b : ZMod r)) := sum_comm
    _ = ∑ x : (ZMod r)ˣ, F x * (if x = b then (r.totient : ℂ) else 0) := by
      exact sum_congr rfl fun x _ => by rw [← mul_sum, characterOrthogonalityOnUnits]
    _ = _ := by simp [mul_ite]

set_option maxHeartbeats 600000 in
theorem unit_twisted_gauss {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (a v : (ZMod r)ˣ) :
    (∑ x : (ZMod r)ˣ, star (χ (x : ZMod r)) *
        ZMod.stdAddChar ((a : ZMod r) * (x : ZMod r) * (v : ZMod r))) =
      χ (a : ZMod r) * χ (v : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  calc
    _ = ∑ x : (ZMod r)ˣ, χ⁻¹ (x : ZMod r) *
        ZMod.stdAddChar (((a * v : (ZMod r)ˣ) : ZMod r) * (x : ZMod r)) := by
      refine sum_congr rfl fun x _ => ?_
      rw [MulChar.star_apply', Units.val_mul]
      rw [show (a : ZMod r) * (x : ZMod r) * (v : ZMod r) =
        ((a : ZMod r) * (v : ZMod r)) * (x : ZMod r) by ring]
    _ = ∑ x : ZMod r, χ⁻¹ x * ZMod.stdAddChar (((a * v : (ZMod r)ˣ) : ZMod r) * x) :=
      sum_units_eq_sum_residues χ⁻¹ (fun x : ZMod r => ZMod.stdAddChar (((a * v : (ZMod r)ˣ) : ZMod r) * x))
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a * v : (ZMod r)ˣ)) := rfl
    _ = (χ⁻¹)⁻¹ ((a * v : (ZMod r)ˣ) : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar :=
      gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (a * v)
    _ = _ := by simp only [inv_inv, Units.val_mul, map_mul]

def twistedRamanujan {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : (ZMod r)ˣ) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((a : ZMod r) * (b : ZMod r) * (ZMod.unitsMap divides u : ZMod r)) *
    ZMod.stdAddChar ((-(n : ZMod q)) * (u : ZMod q))

def characterFactor {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (χ : DirichletCharacter ℂ r) : ℂ :=
  gaussSum χ⁻¹ ZMod.stdAddChar *
    gaussSum (DirichletCharacter.changeLevel divides χ) (ZMod.stdAddChar.mulShift (-(n : ZMod q))) /
      (r.totient : ℂ)

theorem transform_twistedRamanujan {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a : (ZMod r)ˣ) (χ : DirichletCharacter ℂ r) :
    (∑ b : (ZMod r)ˣ, star (χ (b : ZMod r)) * twistedRamanujan divides n a b) =
      χ (a : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar *
        gaussSum (DirichletCharacter.changeLevel divides χ) (ZMod.stdAddChar.mulShift (-(n : ZMod q))) := by
  let lifted := DirichletCharacter.changeLevel divides χ
  have level (u : (ZMod q)ˣ) : χ (ZMod.unitsMap divides u : ZMod r) = lifted (u : ZMod q) := by
    rw [ZMod.unitsMap_val, ← DirichletCharacter.changeLevel_eq_cast_of_dvd]
  unfold twistedRamanujan
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ u : (ZMod q)ˣ, (∑ b : (ZMod r)ˣ, star (χ (b : ZMod r)) *
        ZMod.stdAddChar ((a : ZMod r) * (b : ZMod r) * (ZMod.unitsMap divides u : ZMod r))) *
          ZMod.stdAddChar ((-(n : ZMod q)) * (u : ZMod q)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun b _ => by ring
    _ = (χ (a : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar) *
        ∑ u : (ZMod q)ˣ, lifted (u : ZMod q) * ZMod.stdAddChar ((-(n : ZMod q)) * (u : ZMod q)) := by
      simp_rw [unit_twisted_gauss, level]
      rw [mul_sum]
      exact sum_congr rfl fun u _ => by ring
    _ = _ := by
      apply congrArg (fun z : ℂ => χ (a : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar * z)
      exact sum_units_eq_sum_residues lifted (fun u : ZMod q => ZMod.stdAddChar ((-(n : ZMod q)) * u))

theorem twistedRamanujan_expansion {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : (ZMod r)ˣ) :
    twistedRamanujan divides n a b = ∑ χ : DirichletCharacter ℂ r,
      characterFactor divides n χ * χ (a : ZMod r) * χ (b : ZMod r) := by
  rw [unit_character_expansion (twistedRamanujan divides n a) b]
  simp_rw [transform_twistedRamanujan, sum_div]
  refine sum_congr rfl fun χ _ => ?_
  unfold characterFactor
  ring


end
end DyadicMixedB4RamanujanCharacters

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open BombieriVinogradov.LargeSieve DyadicMixedB4Ramanujan DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4RamanujanUnits

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

theorem stdAddChar_int_fraction {q : ℕ} [NeZero q] (k : ℤ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, additivePhase, circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem ramanujan_as_unit_sum {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℤ) :
    ramanujan q k = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((k : ZMod q) * (u : ZMod q)) := by
  classical
  rw [ramanujan, numSet_eq_coprime_filter qLower]
  apply sum_bij (s := (range q).filter (fun a => a.Coprime q)) (t := (univ : Finset (ZMod q)ˣ))
    (fun a aMember => ZMod.unitOfCoprime a (mem_filter.mp aMember).2)
  · simp
  · intro a aMember b bMember equality
    have residues := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q).val) equality
    simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp aMember).1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp bMember).1)] using residues
  · intro u _
    let a := (u : ZMod q).val
    have raw : (a : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
    have unit : IsUnit (a : ZMod q) := by rw [raw]; exact u.isUnit
    have aCoprime := (ZMod.isUnit_iff_coprime a q).mp unit
    refine ⟨a, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), aCoprime⟩, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact raw
  · intro a aMember
    rw [ZMod.coe_unitOfCoprime, phase_eq_additivePhase]
    have product : (k : ZMod q) * (a : ZMod q) = ((k * (a : ℤ) : ℤ) : ZMod q) := by push_cast; rfl
    rw [product, stdAddChar_int_fraction]
    push_cast
    rw [mul_div_assoc]

theorem stdAddChar_rescale {r q : ℕ} [NeZero r] [NeZero q] (g m : ℕ) (scale : q = g * r) :
    ZMod.stdAddChar ((g * m : ℕ) : ZMod q) = ZMod.stdAddChar (m : ZMod r) := by
  have gNonzero : g ≠ 0 := by
    intro zero
    exact NeZero.ne q (by rw [scale, zero, zero_mul])
  have gCastNonzero : (g : ℝ) ≠ 0 := by exact_mod_cast gNonzero
  have rCastNonzero : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  rw [stdAddChar_nat_fraction, stdAddChar_nat_fraction]
  congr 1
  rw [scale]
  push_cast
  field_simp

theorem twistedRamanujan_eq_ramanujan {r q : ℕ} [NeZero r] [NeZero q]
    (g : ℕ) (scale : q = g * r) (qLower : 1 < q) (divides : r ∣ q) (n : ℤ)
    (a b : (ZMod r)ˣ) (aRep bRep : ℕ)
    (aEq : (a : ZMod r) = (aRep : ZMod r)) (bEq : (b : ZMod r) = (bRep : ZMod r)) :
    twistedRamanujan divides n a b = ramanujan q (((g * aRep * bRep : ℕ) : ℤ) - n) := by
  rw [ramanujan_as_unit_sum qLower]
  unfold twistedRamanujan
  refine sum_congr rfl fun u _ => ?_
  let z := (u : ZMod q).val
  have zQ : (z : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
  have zR : (z : ZMod r) = (ZMod.unitsMap divides u : ZMod r) := by
    rw [ZMod.unitsMap_val, ← zQ, ZMod.cast_natCast divides]
  have productR : (a : ZMod r) * (b : ZMod r) * (ZMod.unitsMap divides u : ZMod r) =
      ((aRep * bRep * z : ℕ) : ZMod r) := by simp only [aEq, bEq, ← zR, Nat.cast_mul]
  have productQ : ((g * aRep * bRep : ℕ) : ZMod q) * (u : ZMod q) =
      ((g * (aRep * bRep * z) : ℕ) : ZMod q) := by rw [← zQ]; push_cast; ring
  rw [Int.cast_sub, Int.cast_natCast, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, ← neg_mul,
    productQ, productR, stdAddChar_rescale g (aRep * bRep * z) scale]


end
end DyadicMixedB4RamanujanUnits

end

section

open Finset DyadicMixedB4ImprimitiveBound DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4CharacterFactorBound

noncomputable section

theorem norm_dirichlet_gauss_induced {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel rDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod q))‖ ≤
      Real.sqrt χ.conductor * ∑ f ∈ k.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  have conductorNonzero : χ.conductor ≠ 0 := fun zero => NeZero.ne r
    (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp zero)
  letI : NeZero χ.conductor := ⟨conductorNonzero⟩
  have inductionBound := norm_induced_gauss_le (χ.conductor_dvd_level.trans rDivides)
    χ.primitiveCharacter_isPrimitive k kPositive
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level rDivides,
    DirichletCharacter.changeLevel_primitiveCharacter] at inductionBound
  exact inductionBound

theorem norm_dirichlet_gauss_standard {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
  have induced := norm_dirichlet_gauss_induced (dvd_refl r) χ 1 (by decide)
  have onlyOne : ((1 : ℕ).divisors.filter (fun f => χ.conductor * f ∣ r)) = {1} := by
    ext f
    simp only [Nat.divisors_one, mem_filter, mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl, by simpa only [mul_one] using χ.conductor_dvd_level⟩
  rw [onlyOne] at induced
  simpa [DirichletCharacter.changeLevel_self, AddChar.mulShift_one] using induced

theorem norm_gauss_neg_shift_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖ ≤ ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  have equality : ZMod.stdAddChar.mulShift (-x) =
      (ZMod.stdAddChar.mulShift x).mulShift ((-1 : (ZMod q)ˣ) : ZMod q) := by
    ext y
    simp [AddChar.mulShift_apply, mul_assoc]
  rw [equality, gaussSum_mulShift_eq χ (ZMod.stdAddChar.mulShift x) (-1), norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem characterFactor_bound {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (n : ℕ) (nPositive : 0 < n) :
    ‖characterFactor rDivides (n : ℤ) χ‖ ≤ (χ.conductor : ℝ) / (r.totient : ℝ) *
      ∑ f ∈ n.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  let mass := ∑ f ∈ n.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ)
  let lifted := DirichletCharacter.changeLevel rDivides χ
  have first := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at first
  have second : ‖gaussSum lifted (ZMod.stdAddChar.mulShift (-(n : ZMod q)))‖ ≤
      Real.sqrt χ.conductor * mass :=
    (norm_gauss_neg_shift_le lifted (n : ZMod q)).trans
      (norm_dirichlet_gauss_induced rDivides χ n nPositive)
  unfold characterFactor
  rw [norm_div, norm_mul, Complex.norm_natCast, Int.cast_natCast]
  have numerator : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖gaussSum lifted (ZMod.stdAddChar.mulShift (-(n : ZMod q)))‖ ≤
      (χ.conductor : ℝ) * mass := by
    calc
      _ ≤ Real.sqrt χ.conductor * (Real.sqrt χ.conductor * mass) :=
        mul_le_mul first second (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [← mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (div_le_div_of_nonneg_right numerator (Nat.cast_nonneg _)).trans_eq (by unfold mass; ring)


end
end DyadicMixedB4CharacterFactorBound

end

section

open Finset ArithmeticFunction

namespace DyadicMixedB4BadPrimeMass

/-- Adapted from BadPrimePowerCover.lean in kimihiro64/bombieri-vinogradov,
revision 7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0). -/
theorem primePower_badUnit_cover {r b Y : ℕ} (rNonzero : r ≠ 0) (bBound : b ≤ Y)
    (bad : ¬b.Coprime r) (primePower : IsPrimePow b) :
    ∃ p ∈ r.primeFactors, ∃ k ∈ Icc 1 (Nat.log 2 Y), b = p ^ k := by
  obtain ⟨k, upper, positive, p, _, equality, prime⟩ := (isPrimePow_nat_iff_bounded_log b).mp primePower
  have divides : p ∣ r := by
    by_contra notDivides
    have pCoprime := prime.coprime_iff_not_dvd.mpr notDivides
    exact bad (equality ▸ pCoprime.pow_left k)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨prime, divides, rNonzero⟩,
    k, mem_Icc.mpr ⟨positive, upper.trans (Nat.log_mono_right bBound)⟩, equality⟩

theorem badUnit_mangoldt_mass_le (r Y : ℕ) (rNonzero : r ≠ 0) (YPositive : 0 < Y) :
    (∑ b ∈ (Icc 1 Y).filter (fun b => ¬b.Coprime r), Λ b) ≤
      (r.divisors.card : ℝ) * (Nat.log 2 Y : ℝ) * Real.log Y := by
  classical
  let bad := (Icc 1 Y).filter (fun b => ¬b.Coprime r)
  let support := bad.filter (fun b => Λ b ≠ 0)
  let codes := r.primeFactors ×ˢ Icc 1 (Nat.log 2 Y)
  have supportSubset : support ⊆ codes.image (fun pair : ℕ × ℕ => pair.1 ^ pair.2) := by
    intro b bMember
    obtain ⟨badMember, nonzero⟩ := mem_filter.mp bMember
    obtain ⟨inRange, noncoprime⟩ := mem_filter.mp badMember
    obtain ⟨p, pMember, k, kMember, equality⟩ := primePower_badUnit_cover rNonzero (mem_Icc.mp inRange).2
      noncoprime (vonMangoldt_ne_zero_iff.mp nonzero)
    exact mem_image.mpr ⟨(p, k), mem_product.mpr ⟨pMember, kMember⟩, equality.symm⟩
  have primeCount : r.primeFactors.card ≤ r.divisors.card := by
    apply card_le_card
    intro p pMember
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors pMember, rNonzero⟩
  have supportCount : support.card ≤ r.divisors.card * Nat.log 2 Y := by
    calc
      _ ≤ (codes.image (fun pair : ℕ × ℕ => pair.1 ^ pair.2)).card := card_le_card supportSubset
      _ ≤ codes.card := card_image_le
      _ = r.primeFactors.card * Nat.log 2 Y := by simp [codes]
      _ ≤ _ := Nat.mul_le_mul_right _ primeCount
  have logNonnegative : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast YPositive)
  change (∑ b ∈ bad, Λ b) ≤ _
  calc
    _ = ∑ b ∈ support, Λ b := by
      symm
      exact sum_subset (filter_subset _ _) fun b member notSupport => by
        by_contra nz
        exact notSupport (mem_filter.mpr ⟨member, nz⟩)
    _ ≤ ∑ _ ∈ support, Real.log Y := by
      refine sum_le_sum fun b member => ?_
      obtain ⟨positive, upper⟩ := mem_Icc.mp (mem_filter.mp (mem_filter.mp member).1).1
      exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast positive) (by exact_mod_cast upper))
    _ = (support.card : ℝ) * Real.log Y := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast supportCount) logNonnegative


end DyadicMixedB4BadPrimeMass

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcCenters DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open DyadicMixedB4RamanujanUnits DyadicMixedB4RamanujanCharacters DyadicMixedB4CharacterFactorBound
open DyadicMixedB4BadPrimeMass BombieriVinogradov.LargeSieve

namespace DyadicMixedB4RamanujanError

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

theorem norm_stdAddChar_eq_one {q : ℕ} [NeZero q] (z : ZMod q) : ‖ZMod.stdAddChar z‖ = 1 := by
  rw [← ZMod.natCast_zmod_val z, stdAddChar_nat_fraction, norm_additivePhase]

theorem norm_ramanujan_le_modulus {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℤ) :
    ‖ramanujan q k‖ ≤ q := by
  rw [ramanujan_as_unit_sum qLower]
  refine (norm_sum_le _ _).trans ?_
  simpa only [norm_stdAddChar_eq_one, sum_const, nsmul_eq_mul, mul_one, card_univ,
    ZMod.card_units_eq_totient] using (show (q.totient : ℝ) ≤ q by exact_mod_cast Nat.totient_le q)

theorem norm_characterFactor_sum_le {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q)
    (n : ℕ) (nPositive : 0 < n) :
    (∑ χ : DirichletCharacter ℂ r, ‖characterFactor divides (n : ℤ) χ‖) ≤ (q : ℝ) * n.divisors.card := by
  have divisorPositive : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have individually (χ : DirichletCharacter ℂ r) : ‖characterFactor divides (n : ℤ) χ‖ ≤
      ((q : ℝ) * (n.divisors.card : ℝ)) / (r.totient : ℝ) := by
    refine (characterFactor_bound divides χ n nPositive).trans ?_
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ divisorPositive.le
    rw [mul_sum]
    calc
      _ ≤ ∑ _ ∈ n.divisors.filter (fun f => χ.conductor * f ∣ q), (q : ℝ) := by
        refine sum_le_sum fun f member => ?_
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (mem_filter.mp member).2
      _ ≤ ∑ _ ∈ n.divisors, (q : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg q)
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have card : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  calc
    _ ≤ ∑ _ : DirichletCharacter ℂ r, ((q : ℝ) * (n.divisors.card : ℝ)) / (r.totient : ℝ) :=
      sum_le_sum fun χ _ => individually χ
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, card]; field_simp

def primitiveMixtureValue {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : ℕ) : ℂ := ∑ χ : DirichletCharacter ℂ r, characterFactor divides n χ *
      χ.primitiveCharacter (a : ZMod χ.conductor) * χ.primitiveCharacter (b : ZMod χ.conductor)

theorem primitiveCharacter_equal_on_coprime {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    {a : ℕ} (coprime : a.Coprime r) : χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod r) := by
  calc
    _ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter (a : ZMod r) := by
      rw [changeLevel_nat_indicator, if_pos coprime, one_mul]
    _ = _ := by rw [DirichletCharacter.changeLevel_primitiveCharacter]

theorem norm_primitiveMixtureValue_le {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q)
    (n : ℕ) (nPositive : 0 < n) (a b : ℕ) :
    ‖primitiveMixtureValue divides (n : ℤ) a b‖ ≤ (q : ℝ) * n.divisors.card := by
  unfold primitiveMixtureValue
  refine (norm_sum_le _ _).trans ((sum_le_sum ?_).trans (norm_characterFactor_sum_le divides n nPositive))
  intro χ _
  simp only [norm_mul]
  exact (mul_le_of_le_one_right (by positivity) (DirichletCharacter.norm_le_one _ _)).trans
    (mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one _ _))

theorem ramanujan_eq_primitiveMixture_of_coprime {r q : ℕ} [NeZero r] [NeZero q] (g : ℕ)
    (scale : q = g * r) (qLower : 1 < q) (divides : r ∣ q) (n : ℤ) {a b : ℕ}
    (aCoprime : a.Coprime r) (bCoprime : b.Coprime r) :
    ramanujan q (((g * a * b : ℕ) : ℤ) - n) = primitiveMixtureValue divides n a b := by
  rw [← twistedRamanujan_eq_ramanujan g scale qLower divides n (ZMod.unitOfCoprime a aCoprime)
      (ZMod.unitOfCoprime b bCoprime) a b (ZMod.coe_unitOfCoprime a aCoprime) (ZMod.coe_unitOfCoprime b bCoprime),
    twistedRamanujan_expansion]
  simp only [primitiveMixtureValue, ZMod.coe_unitOfCoprime,
    primitiveCharacter_equal_on_coprime _ aCoprime, primitiveCharacter_equal_on_coprime _ bCoprime]

theorem norm_ramanujan_primitiveMixture_difference {r q : ℕ} [NeZero r] [NeZero q] (g : ℕ)
    (scale : q = g * r) (qLower : 1 < q) (divides : r ∣ q) (n : ℕ) (nPositive : 0 < n)
    {a : ℕ} (aCoprime : a.Coprime r) (b : ℕ) :
    ‖ramanujan q (((g * a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveMixtureValue divides (n : ℤ) a b‖ ≤
      if b.Coprime r then 0 else (q : ℝ) * (1 + (n.divisors.card : ℝ)) := by
  by_cases bCoprime : b.Coprime r
  · rw [ramanujan_eq_primitiveMixture_of_coprime g scale qLower divides _ aCoprime bCoprime,
      sub_self, norm_zero, if_pos bCoprime]
  · rw [if_neg bCoprime, mul_add, mul_one]
    exact (norm_sub_le _ _).trans (add_le_add (norm_ramanujan_le_modulus qLower _)
      (norm_primitiveMixtureValue_le divides n nPositive a b))


end
end DyadicMixedB4RamanujanError

end

section

open Finset ArithmeticFunction DyadicMixedB4RamanujanError DyadicMixedB4BadPrimeMass
open DyadicMixedB4ArcCenters

namespace DyadicMixedB4PrimitiveAt

noncomputable section

def reducedModulus (q a : ℕ) : ℕ := q / a.gcd q

theorem gcd_positive {q : ℕ} (qPositive : 0 < q) (a : ℕ) : 0 < a.gcd q :=
  Nat.gcd_pos_of_pos_right a qPositive

theorem reducedModulus_positive {q : ℕ} (qPositive : 0 < q) (a : ℕ) : 0 < reducedModulus q a :=
  Nat.div_pos (Nat.le_of_dvd qPositive (Nat.gcd_dvd_right a q)) (gcd_positive qPositive a)

theorem reducedModulus_dvd (q a : ℕ) : reducedModulus q a ∣ q :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a q)

def primitiveAt (q n a b : ℕ) : ℂ :=
  if h : 0 < q then
    letI : NeZero q := ⟨h.ne'⟩
    letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_positive h a).ne'⟩
    primitiveMixtureValue (reducedModulus_dvd q a) (n : ℤ) (a / a.gcd q) b
  else 0

theorem norm_ramanujan_sub_primitiveAt {q n : ℕ} (qLower : 1 < q) (nPositive : 0 < n) (a b : ℕ) :
    ‖ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b‖ ≤
      if b.Coprime (reducedModulus q a) then 0 else (q : ℝ) * (1 + (n.divisors.card : ℝ)) := by
  have qPositive : 0 < q := by omega
  letI : NeZero q := ⟨qPositive.ne'⟩
  letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_positive qPositive a).ne'⟩
  have gPositive := gcd_positive qPositive a
  have scale : q = a.gcd q * reducedModulus q a := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)).symm
  have coprime : (a / a.gcd q).Coprime (reducedModulus q a) := Nat.coprime_div_gcd_div_gcd gPositive
  rw [primitiveAt, dif_pos qPositive]
  have bound := norm_ramanujan_primitiveMixture_difference (a.gcd q) scale qLower (reducedModulus_dvd q a)
    n nPositive coprime b
  rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)] at bound

theorem norm_mangoldt_replacement_le {q n : ℕ} (qLower : 1 < q) (nPositive : 0 < n)
    (a : ℕ) (s : Finset ℕ) (within : s ⊆ Icc 1 n) (K : ℕ → ℂ)
    {V : ℝ} (vNonnegative : 0 ≤ V) (KBound : ∀ b ∈ s, ‖K b‖ ≤ V) :
    ‖∑ b ∈ s, (Λ b : ℂ) * ((ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b) * K b)‖ ≤
      (V * ((q : ℝ) * (1 + (n.divisors.card : ℝ)))) *
        (((reducedModulus q a).divisors.card : ℝ) * (Nat.log 2 n : ℝ) * Real.log n) := by
  let r := reducedModulus q a
  let C : ℝ := V * ((q : ℝ) * (1 + (n.divisors.card : ℝ)))
  let f (b : ℕ) := (Λ b : ℂ) * ((ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b) * K b)
  have qPositive : 0 < q := by omega
  have rNonzero : r ≠ 0 := (reducedModulus_positive qPositive a).ne'
  have CNonnegative : 0 ≤ C := by unfold C; positivity
  change ‖∑ b ∈ s, f b‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ b ∈ s, if b.Coprime r then 0 else Λ b * C := by
      refine sum_le_sum fun b bMember => ?_
      have difference := norm_ramanujan_sub_primitiveAt qLower nPositive a b
      change _ ≤ if b.Coprime r then 0 else _ at difference
      by_cases coprime : b.Coprime r
      · rw [if_pos coprime] at difference ⊢
        have zero := norm_eq_zero.mp (le_antisymm difference (norm_nonneg _))
        unfold f
        rw [zero, zero_mul, mul_zero, norm_zero]
      · rw [if_neg coprime] at difference ⊢
        unfold f C
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        rw [mul_comm V]
        exact mul_le_mul_of_nonneg_left (mul_le_mul difference (KBound b bMember) (norm_nonneg _) (by positivity))
          vonMangoldt_nonneg
    _ = ∑ b ∈ s.filter (fun b => ¬b.Coprime r), Λ b * C := by
      rw [sum_filter]
      exact sum_congr rfl fun b _ => by by_cases coprime : b.Coprime r <;> simp [coprime]
    _ ≤ ∑ b ∈ (Icc 1 n).filter (fun b => ¬b.Coprime r), Λ b * C :=
      sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ within) (fun _ _ _ => mul_nonneg vonMangoldt_nonneg CNonnegative)
    _ = C * ∑ b ∈ (Icc 1 n).filter (fun b => ¬b.Coprime r), Λ b := by rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (badUnit_mangoldt_mass_le r n rNonzero nPositive) CNonnegative


end
end DyadicMixedB4PrimitiveAt

end

section

open Finset BombieriVinogradov.LargeSieve

namespace DyadicMixedB4ConductorPartition

noncomputable section

theorem sum_at_conductor {A : Type*} [AddCommMonoid A] {r d : ℕ} [NeZero r] (divides : d ∣ r)
    (F : DirichletCharacter ℂ r → A) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d), F χ) =
      ∑ ψ ∈ primitiveCharacters d, F (DirichletCharacter.changeLevel divides ψ) := by
  classical
  symm
  apply sum_bij (s := primitiveCharacters d) (t := univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d))
    (fun ψ _ => DirichletCharacter.changeLevel divides ψ)
  · intro ψ membership
    have primitive : ψ.IsPrimitive := (mem_filter.mp membership).2
    exact mem_filter.mpr ⟨mem_univ _, (DirichletCharacter.conductor_changeLevel ψ divides).trans primitive⟩
  · intro χ _ ψ _ equality
    exact DirichletCharacter.changeLevel_injective divides equality
  · intro χ membership
    have equality := (mem_filter.mp membership).2
    subst d
    exact ⟨χ.primitiveCharacter, mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩,
      χ.changeLevel_primitiveCharacter⟩
  · intro ψ _
    rfl

theorem sum_conductor_partition {A : Type*} [AddCommMonoid A] {r : ℕ} [NeZero r]
    (F : DirichletCharacter ℂ r → A) :
    (∑ χ : DirichletCharacter ℂ r, F χ) =
      ∑ d ∈ r.divisors.attach, ∑ ψ ∈ primitiveCharacters d.1,
        F (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 ψ) := by
  classical
  have conductorMembership (χ : DirichletCharacter ℂ r) (_ : χ ∈ (univ : Finset (DirichletCharacter ℂ r))) :
      χ.conductor ∈ r.divisors := Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne r⟩
  calc
    _ = ∑ d ∈ r.divisors, ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d), F χ :=
      (sum_fiberwise_of_maps_to conductorMembership F).symm
    _ = ∑ d ∈ r.divisors.attach, ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d.1), F χ :=
      (sum_attach _ _).symm
    _ = _ := sum_congr rfl fun d _ => sum_at_conductor (Nat.mem_divisors.mp d.2).1 F


end
end DyadicMixedB4ConductorPartition

end

section

open Finset DyadicMixedB4PrimitiveAt DyadicMixedB4RamanujanError DyadicMixedB4RamanujanCharacters
open BombieriVinogradov.LargeSieve DyadicMixedB4ConductorPartition
open DyadicMixedB4CharacterFactorBound

namespace DyadicMixedB4PrimitiveExpansion

noncomputable section

theorem primitiveCharacter_of_primitive_at {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (b : ℕ) : χ.primitiveCharacter (b : ZMod χ.conductor) = χ (b : ZMod d) := by
  by_cases coprime : b.Coprime d
  · exact primitiveCharacter_equal_on_coprime χ coprime
  · have conductor : χ.conductor = d := primitive
    have inducedNonunit : ¬IsUnit (b : ZMod χ.conductor) := by
      intro unit
      have inducedCoprime := (ZMod.isUnit_iff_coprime b χ.conductor).mp unit
      exact coprime (by simpa only [conductor] using inducedCoprime)
    have nonunit : ¬IsUnit (b : ZMod d) := fun unit => coprime ((ZMod.isUnit_iff_coprime b d).mp unit)
    rw [MulChar.map_nonunit _ inducedNonunit, MulChar.map_nonunit _ nonunit]

theorem primitiveCharacter_of_lift_at {r d : ℕ} [NeZero r] [NeZero d] (divides : d ∣ r)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (b : ℕ) :
    (DirichletCharacter.changeLevel divides χ).primitiveCharacter
      (b : ZMod (DirichletCharacter.changeLevel divides χ).conductor) = χ (b : ZMod d) := by
  have transport := DirichletCharacter.primitiveCharacter_changeLevel_apply divides χ (b : ℤ)
  simp only [Int.cast_natCast] at transport
  exact transport.trans (primitiveCharacter_of_primitive_at primitive b)

theorem primitiveMixtureValue_expansion {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : ℕ) : primitiveMixtureValue divides n a b =
      ∑ d ∈ r.divisors.attach, ∑ χ ∈ primitiveCharacters d.1,
        characterFactor divides n (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ) *
          χ (a : ZMod d.1) * χ (b : ZMod d.1) := by
  classical
  unfold primitiveMixtureValue
  rw [sum_conductor_partition (F := fun χ : DirichletCharacter ℂ r => characterFactor divides n χ *
    χ.primitiveCharacter (a : ZMod χ.conductor) * χ.primitiveCharacter (b : ZMod χ.conductor))]
  refine sum_congr rfl fun d _ => sum_congr rfl fun χ χMember => ?_
  have primitive : χ.IsPrimitive := (mem_filter.mp χMember).2
  letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
  rw [primitiveCharacter_of_lift_at _ primitive a, primitiveCharacter_of_lift_at _ primitive b]

theorem lift_characterFactor_bound {d r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q)
    (levelDivides : d ∣ r) (χ : DirichletCharacter ℂ d) (primitive : χ.IsPrimitive) (n : ℕ) (nPositive : 0 < n) :
    ‖characterFactor divides (n : ℤ) (DirichletCharacter.changeLevel levelDivides χ)‖ ≤
      (d : ℝ) / (r.totient : ℝ) * ∑ f ∈ n.divisors.filter (fun f => d * f ∣ q), (f : ℝ) := by
  have conductor : χ.conductor = d := primitive
  simpa only [DirichletCharacter.conductor_changeLevel, conductor] using
    characterFactor_bound divides (DirichletCharacter.changeLevel levelDivides χ) n nPositive


end
end DyadicMixedB4PrimitiveExpansion

end

section

open Finset

namespace DyadicMixedB4GcdHarmonic

theorem sum_inverse_Icc_le (L : ℕ) :
    (∑ t ∈ Icc 1 L, (t : ℝ)⁻¹) ≤ 1 + Real.log L := by
  have bound := harmonic_le_one_add_log L
  rw [harmonic_eq_sum_Icc] at bound
  push_cast at bound
  exact bound

theorem sum_inverse_multiples (D L : ℕ) (DPositive : 0 < D) :
    (∑ u ∈ (Icc 1 L).filter (fun u => D ∣ u), (u : ℝ)⁻¹) =
      (D : ℝ)⁻¹ * ∑ k ∈ Icc 1 (L / D), (k : ℝ)⁻¹ := by
  rw [mul_sum]
  symm
  apply sum_bij (fun k _ => D * k)
  · intro k member
    obtain ⟨lower, upper⟩ := mem_Icc.mp member
    have productUpper : k * D ≤ L := (Nat.le_div_iff_mul_le DPositive).mp upper
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos DPositive lower, by simpa [mul_comm] using productUpper⟩,
      dvd_mul_right D k⟩
  · intro k _ k' _ same
    exact Nat.eq_of_mul_eq_mul_left DPositive same
  · intro u member
    obtain ⟨inIcc, k, identity⟩ := mem_filter.mp member
    obtain ⟨lower, upper⟩ := mem_Icc.mp inIcc
    have productLower : 0 < D * k := identity ▸ lower
    have productUpper : k * D ≤ L := by simpa [identity, Nat.mul_comm] using upper
    refine ⟨k, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left productLower,
      (Nat.le_div_iff_mul_le DPositive).mpr productUpper⟩, identity.symm⟩
  · intro k member
    have kPositive : 0 < k := (mem_Icc.mp member).1
    have kNonzero : (k : ℝ) ≠ 0 := by exact_mod_cast kPositive.ne'
    have DNonzero : (D : ℝ) ≠ 0 := by exact_mod_cast DPositive.ne'
    rw [Nat.cast_mul]
    field_simp

theorem gcd_reciprocal_sum_le (L : ℕ) (LPositive : 0 < L) :
    (∑ u ∈ Icc 1 L, ∑ v ∈ Icc 1 L, (u.gcd v : ℝ) / ((u : ℝ) * v)) ≤
      (1 + Real.log L) ^ 3 := by
  classical
  let support := Icc 1 L
  let row (d u : ℕ) : ℝ := if d ∣ u then (u : ℝ)⁻¹ else 0
  let H := 1 + Real.log (L : ℝ)
  have HNonnegative : 0 ≤ H := by
    have LReal : (1 : ℝ) ≤ L := by exact_mod_cast LPositive
    unfold H
    exact add_nonneg zero_le_one (Real.log_nonneg LReal)
  have rowNonnegative (d u : ℕ) : 0 ≤ row d u := by unfold row; split_ifs <;> positivity
  have pointwise (u v : ℕ) (uMember : u ∈ support) (vMember : v ∈ support) :
      (u.gcd v : ℝ) / ((u : ℝ) * v) ≤ ∑ d ∈ support, (d : ℝ) * row d u * row d v := by
    have uPositive := (mem_Icc.mp uMember).1
    have gPositive := Nat.gcd_pos_of_pos_left v uPositive
    have gMember : u.gcd v ∈ support := mem_Icc.mpr ⟨gPositive, (Nat.gcd_le_left v uPositive).trans (mem_Icc.mp uMember).2⟩
    calc
      _ = (u.gcd v : ℝ) * row (u.gcd v) u * row (u.gcd v) v := by
        have uNonzero : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt uPositive)
        have vNonzero : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp vMember).1)
        simp only [row, if_pos (Nat.gcd_dvd_left u v), if_pos (Nat.gcd_dvd_right u v)]
        field_simp
      _ ≤ _ := single_le_sum (s := support) (f := fun (d : ℕ) => (d : ℝ) * row d u * row d v) (fun d _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (rowNonnegative d u)) (rowNonnegative d v)) gMember
  have rowBound (d : ℕ) (member : d ∈ support) : (∑ u ∈ support, row d u) ≤ (d : ℝ)⁻¹ * H := by
    have dPositive := (mem_Icc.mp member).1
    change (∑ u ∈ Icc 1 L, if d ∣ u then (u : ℝ)⁻¹ else 0) ≤ _
    rw [← sum_filter, sum_inverse_multiples d L dPositive]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self L d))
      (fun _ _ _ => by positivity)).trans ?_
    exact sum_inverse_Icc_le L
  calc
    _ ≤ ∑ u ∈ support, ∑ v ∈ support, ∑ d ∈ support, (d : ℝ) * row d u * row d v :=
      sum_le_sum fun u uMember => sum_le_sum fun v vMember => pointwise u v uMember vMember
    _ = ∑ d ∈ support, (d : ℝ) * (∑ u ∈ support, row d u) ^ 2 := by
      have swapped : (∑ u ∈ support, ∑ v ∈ support, ∑ d ∈ support, (d : ℝ) * row d u * row d v) =
          ∑ d ∈ support, ∑ u ∈ support, ∑ v ∈ support, (d : ℝ) * row d u * row d v := by
        calc
          _ = ∑ u ∈ support, ∑ d ∈ support, ∑ v ∈ support, (d : ℝ) * row d u * row d v :=
            sum_congr rfl fun _ _ => sum_comm
          _ = _ := sum_comm
      rw [swapped]
      refine sum_congr rfl fun d _ => ?_
      calc
        _ = ∑ u ∈ support, ((d : ℝ) * row d u) * (∑ v ∈ support, row d v) :=
          sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
        _ = (∑ u ∈ support, (d : ℝ) * row d u) * (∑ v ∈ support, row d v) :=
          (sum_mul _ _ _).symm
        _ = _ := by rw [← mul_sum, mul_assoc, pow_two]
    _ ≤ ∑ d ∈ support, (d : ℝ)⁻¹ * H ^ 2 := by
      refine sum_le_sum fun d member => ?_
      have dRealPositive : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp member).1
      have energy := pow_le_pow_left₀ (sum_nonneg fun u _ => rowNonnegative d u) (rowBound d member) 2
      calc
        _ ≤ (d : ℝ) * ((d : ℝ)⁻¹ * H) ^ 2 := mul_le_mul_of_nonneg_left energy dRealPositive.le
        _ = _ := by field_simp
    _ = (∑ d ∈ support, (d : ℝ)⁻¹) * H ^ 2 := by rw [sum_mul]
    _ ≤ H ^ 3 := by
      calc
        _ ≤ H * H ^ 2 := mul_le_mul_of_nonneg_right (sum_inverse_Icc_le L) (sq_nonneg _)
        _ = _ := by ring


end DyadicMixedB4GcdHarmonic

end

section

open Finset DyadicMixedB4GcdHarmonic

namespace DyadicMixedB4WeightBudgets

theorem le_totient_mul_divisor_count (n : ℕ) (nPositive : 0 < n) :
    n ≤ n.totient * n.divisors.card := by
  let product : ℕ := ∏ p ∈ n.primeFactors, (p - 1)
  have productPositive : 0 < product := by
    unfold product
    exact prod_pos (s := n.primeFactors) (f := fun p : ℕ => p - 1)
      (fun p membership => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors membership).one_lt)
  have bound : (∏ p ∈ n.primeFactors, p) ≤ n.divisors.card * product := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, (n.factorization p + 1) * (p - 1) := by
        refine prod_le_prod' fun p membership => ?_
        have pLower := (Nat.prime_of_mem_primeFactors membership).two_le
        have exponent := Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization] : p ∈ n.factorization.support)
        calc
          p ≤ 2 * (p - 1) := by omega
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [prod_mul_distrib, Nat.card_divisors nPositive.ne']
  apply Nat.le_of_mul_le_mul_right _ productPositive
  calc
    n * product = n.totient * ∏ p ∈ n.primeFactors, p := (Nat.totient_mul_prod_primeFactors n).symm
    _ ≤ n.totient * (n.divisors.card * product) := Nat.mul_le_mul_left _ bound
    _ = _ := by ring

theorem inverse_totient_le_divisor_count (n : ℕ) (nPositive : 0 < n) :
    1 / (n.totient : ℝ) ≤ (n.divisors.card : ℝ) / (n : ℝ) := by
  have positive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have phiPositive : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr nPositive
  exact (div_le_div_iff₀ phiPositive positive).mpr (by
    simpa only [one_mul, mul_one, mul_comm] using (show (n : ℝ) ≤ (n.totient : ℝ) * (n.divisors.card : ℝ) by
      exact_mod_cast le_totient_mul_divisor_count n nPositive))

theorem step_multiple_weight_le {ι : Type*} (items : Finset ι) (g : ι → ℕ) (w : ι → ℝ)
    (M q : ℕ) (qPositive : 0 < q) {W : ℝ} (WNonnegative : 0 ≤ W)
    (stepRange : ∀ i ∈ items, g i ∈ Icc 1 M)
    (weightBound : ∀ u ∈ Icc 1 M, (∑ i ∈ items.filter (fun i => g i = u), w i) ≤ W) :
    (∑ i ∈ items, if q ∣ g i then w i / (g i : ℝ) else 0) ≤
      W * (q : ℝ)⁻¹ * (1 + Real.log M) := by
  have fibre (u : ℕ) : (∑ i ∈ items.filter (fun i => g i = u), if q ∣ g i then w i / (g i : ℝ) else 0) =
      if q ∣ u then (∑ i ∈ items.filter (fun i => g i = u), w i) / (u : ℝ) else 0 := by
    by_cases divides : q ∣ u
    · rw [if_pos divides, sum_div]
      exact sum_congr rfl fun i member => by simp [(mem_filter.mp member).2, divides]
    · rw [if_neg divides]
      exact sum_eq_zero fun i member => by simp [(mem_filter.mp member).2, divides]
  calc
    _ = ∑ u ∈ Icc 1 M, ∑ i ∈ items.filter (fun i => g i = u), if q ∣ g i then w i / (g i : ℝ) else 0 :=
      (sum_fiberwise_of_maps_to stepRange _).symm
    _ = ∑ u ∈ Icc 1 M, if q ∣ u then (∑ i ∈ items.filter (fun i => g i = u), w i) / (u : ℝ) else 0 :=
      sum_congr rfl fun u _ => fibre u
    _ ≤ ∑ u ∈ Icc 1 M, if q ∣ u then W * (u : ℝ)⁻¹ else 0 := by
      refine sum_le_sum fun u member => ?_
      by_cases divides : q ∣ u
      · rw [if_pos divides, if_pos divides, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (weightBound u member) (by positivity)
      · simp [divides]
    _ = W * ((q : ℝ)⁻¹ * ∑ j ∈ Icc 1 (M / q), (j : ℝ)⁻¹) := by
      rw [← sum_filter, ← mul_sum, sum_inverse_multiples q M qPositive]
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self M q))
        (fun _ _ _ => by positivity)).trans (sum_inverse_Icc_le M)


end DyadicMixedB4WeightBudgets

end

section

open Finset MeasureTheory ArithmeticFunction BombieriVinogradov.LargeSieve
open DyadicMixedB4FixedBlock DyadicMixedB4PrimitiveAt DyadicMixedB4PrimitiveExpansion
open DyadicMixedB4PrimitiveEnergy DyadicMixedB4RamanujanCharacters
open DyadicMixedB4MaximalSieve DyadicMixedB4MixedCharacter DyadicMixedB4WeightBudgets
open DyadicMixedB4ArcGeometry DyadicMixedB4KernelControl
open DyadicMixedB4BilinearEnergy

namespace DyadicMixedB4BilinearBlock

noncomputable section

def primitiveBlock (n M B H q step lo hi U : ℕ) (indices : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ a ∈ indices, w a * ∑ b ∈ Ioc U (n / a), (Λ b : ℂ) * (primitiveAt q n a b *
    (windowKernel n M B H q step lo hi (((a * b : ℕ) : ℤ) - (n : ℤ) : ℝ) : ℂ))

def conductorBlock {r q : ℕ} [NeZero r] [NeZero q] (qr : r ∣ q)
    (n M B H step lo hi U g : ℕ) (indices : Finset ℕ) (w : ℕ → ℂ) (d : r.divisors) : ℂ :=
  ∑ a ∈ indices, w a * ∑ j ∈ range (n / a), windowKernel n M B H q step lo hi
    ((a : ℝ) * ((j : ℝ) + 1) - n) • mixture (primitiveCharacters d.1) (mangoldtAbove U)
      (fun χ => characterFactor qr (n : ℤ) (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ))
      (a / g) j

theorem primitiveBlock_eq_sum_conductorBlock {q g : ℕ} [NeZero q] [NeZero (q / g)] (gq : g ∣ q)
    (n M B H step lo hi U : ℕ) (indices : Finset ℕ) (w : ℕ → ℂ)
    (gcdExact : ∀ a ∈ indices, a.gcd q = g) :
    primitiveBlock n M B H q step lo hi U indices w =
      ∑ d ∈ (q / g).divisors.attach, conductorBlock (Nat.div_dvd_of_dvd gq) n M B H step lo hi U g indices w d := by
  classical
  have qPositive : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let r := q / g
  let qr : r ∣ q := Nat.div_dvd_of_dvd gq
  let coeff (d : r.divisors) (χ : DirichletCharacter ℂ d.1) :=
    characterFactor qr (n : ℤ) (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ)
  have point (a : ℕ) (member : a ∈ indices) (b : ℕ) :
      primitiveAt q n a b = ∑ d ∈ r.divisors.attach,
        ∑ χ ∈ primitiveCharacters d.1, coeff d χ * χ ((a / g : ℕ) : ZMod d.1) * χ (b : ZMod d.1) := by
    have same := gcdExact a member
    subst g
    unfold primitiveAt
    rw [dif_pos qPositive]
    letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_positive qPositive a).ne'⟩
    exact primitiveMixtureValue_expansion (reducedModulus_dvd q a) (n : ℤ) (a / a.gcd q) b
  unfold primitiveBlock conductorBlock
  rw [sum_comm]
  refine sum_congr rfl fun a member => ?_
  rw [← mul_sum, sum_Ioc_as_range_prefix, sum_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  by_cases bLarge : U < j + 1
  · simp only [if_pos bLarge, point a member, Complex.real_smul, mixture, mangoldtAbove,
      Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl fun (d : r.divisors) _ => ?_
    refine sum_congr rfl fun (χ : DirichletCharacter ℂ d.1) _ => ?_
    unfold coeff
    ring
  · simp [bLarge, mixture, mangoldtAbove]

theorem norm_conductorBlock_le {q g : ℕ} [NeZero q] [NeZero (q / g)] (gq : g ∣ q)
    (n M B H step lo hi U A : ℕ) (nPositive : 0 < n) (APositive : 0 < A)
    (gPositive : 0 < g) (radiusUpper : radius M ≤ 1) (indices : Finset ℕ)
    (indexRange : indices ⊆ Ico A (2 * A)) (gcdExact : ∀ a ∈ indices, a.gcd q = g)
    (w : ℕ → ℂ) {T : ℝ} (TNonnegative : 0 ≤ T)
    (wBound : ∀ a ∈ indices, ‖w a‖ ≤ T) (dCount : (((q / g).divisors.card : ℕ) : ℝ) ≤ T)
    (d : (q / g).divisors) :
    ‖conductorBlock (Nat.div_dvd_of_dvd gq) n M B H step lo hi U g indices w d‖ ≤
      (T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1)) / (step : ℝ)) *
        (∑ f ∈ n.divisors, if d.1 * f ∣ q then ((d.1 : ℝ) * g * f) / (q : ℝ) else 0) *
          blockEnergy n A U g d.1 := by
  classical
  let r := q / g
  let qr : r ∣ q := Nat.div_dvd_of_dvd gq
  let F := ∑ f ∈ n.divisors.filter (fun f => d.1 * f ∣ q), (f : ℝ)
  have FNonnegative : 0 ≤ F := sum_nonneg fun f _ => Nat.cast_nonneg f
  have CNonnegative : 0 ≤ (d.1 : ℝ) / (r.totient : ℝ) * F := by positivity
  letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
  have rPositive : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have weight (χ : DirichletCharacter ℂ d.1) (member : χ ∈ primitiveCharacters d.1) :
      ‖characterFactor qr (n : ℤ) (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ)‖ ≤
        (d.1 : ℝ) / (r.totient : ℝ) * F :=
    lift_characterFactor_bound qr _ χ (mem_filter.mp member).2 n nPositive
  have bound := fixed_conductor_block_le (d := d.1) n M B H q step lo hi A g U nPositive APositive
    gPositive radiusUpper indices indexRange (fun a member => gcdExact a member ▸ Nat.gcd_dvd_left a q)
    w TNonnegative CNonnegative wBound (primitiveCharacters d.1) _ weight
  dsimp only at bound
  simp only [finiteTwistedSum_eq_primitiveEnergy] at bound
  have rExact : (r : ℝ) * (g : ℝ) = (q : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel gq
  have rNonzero : (r : ℝ) ≠ 0 := by exact_mod_cast rPositive.ne'
  have gNonzero : (g : ℝ) ≠ 0 := by exact_mod_cast gPositive.ne'
  have phiBound : 1 / (r.totient : ℝ) ≤ T * g / (q : ℝ) := by
    calc
      _ ≤ (r.divisors.card : ℝ) / (r : ℝ) := inverse_totient_le_divisor_count r rPositive
      _ ≤ T / (r : ℝ) := div_le_div_of_nonneg_right dCount (Nat.cast_nonneg _)
      _ = _ := by rw [← rExact]; field_simp
  have coefBound : (d.1 : ℝ) / (r.totient : ℝ) * F ≤
      (d.1 : ℝ) * (T * g / (q : ℝ)) * F := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left phiBound (Nat.cast_nonneg _)) FNonnegative
  have factor : 0 ≤ (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) :=
    (add_nonneg (by positivity) (mul_nonneg (by positivity)
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))))
  calc
    _ ≤ T * (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) *
        ((d.1 : ℝ) / (r.totient : ℝ) * F) * blockEnergy n A U g d.1 := bound
    _ ≤ T * (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) *
        ((d.1 : ℝ) * (T * g / (q : ℝ)) * F) * blockEnergy n A U g d.1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefBound (mul_nonneg TNonnegative factor))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← sum_filter]
      simp_rw [mul_div_assoc (↑d.1 * (g : ℝ))]
      rw [← mul_sum, ← sum_div]
      unfold F
      ring


end
end DyadicMixedB4BilinearBlock

end

section

open Finset

namespace DyadicMixedB4ModulusTail

private theorem reciprocal_telescoping (A length : ℕ) :
    (∑ i ∈ range length, (1 / ((A + i : ℕ) : ℝ) - 1 / ((A + i + 1 : ℕ) : ℝ))) =
      1 / (A : ℝ) - 1 / ((A + length : ℕ) : ℝ) := by
  induction length with
  | zero => simp
  | succ length ih => rw [sum_range_succ, ih, ← add_assoc]; ring

theorem inverse_square_tail_Icc (A L : ℕ) (APositive : 0 < A) :
    (∑ k ∈ Icc A L, 1 / (k : ℝ) ^ 2) ≤ 2 / (A : ℝ) := by
  rw [show Icc A L = Ico A (L + 1) by ext k; simp only [mem_Icc, mem_Ico]; omega,
    sum_Ico_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ range (L + 1 - A), 2 * (1 / ((A + i : ℕ) : ℝ) - 1 / ((A + i + 1 : ℕ) : ℝ)) := by
      refine sum_le_sum fun i _ => ?_
      have lower : (1 : ℝ) ≤ ((A + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ A + i by omega)
      let z : ℝ := ((A + i : ℕ) : ℝ)
      have zLower : 1 ≤ z := lower
      have positive : 0 < z := by linarith only [zLower]
      have nextPositive : 0 < z + 1 := by linarith only [zLower]
      rw [Nat.cast_add (A + i) 1, Nat.cast_one]
      change 1 / z ^ 2 ≤ 2 * (1 / z - 1 / (z + 1))
      field_simp
      nlinarith only [zLower, mul_nonneg (by linarith only [zLower] : 0 ≤ z - 1) positive.le]
    _ = 2 * (1 / (A : ℝ) - 1 / ((A + (L + 1 - A) : ℕ) : ℝ)) := by rw [← mul_sum, reciprocal_telescoping]
    _ ≤ _ := by
      have denomNonnegative : (0 : ℝ) ≤ 1 / ((A + (L + 1 - A) : ℕ) : ℝ) := by positivity
      calc
        _ ≤ 2 * (1 / (A : ℝ)) := mul_le_mul_of_nonneg_left (sub_le_self _ denomNonnegative) (by norm_num)
        _ = _ := by ring

theorem inverse_square_multiples_tail (D R L : ℕ) (DPositive : 0 < D) :
    (∑ q ∈ (Icc (R + 1) L).filter (fun q => D ∣ q), 1 / (q : ℝ) ^ 2) ≤
      2 / ((D : ℝ) * (max R D : ℕ)) := by
  let A := R / D + 1
  have APositive : 0 < A := Nat.zero_lt_succ _
  have DRealPositive : (0 : ℝ) < D := by exact_mod_cast DPositive
  have equality : (∑ q ∈ (Icc (R + 1) L).filter (fun q => D ∣ q), 1 / (q : ℝ) ^ 2) =
      (1 / (D : ℝ) ^ 2) * ∑ k ∈ Icc A (L / D), 1 / (k : ℝ) ^ 2 := by
    rw [mul_sum]
    symm
    apply sum_bij (s := Icc A (L / D)) (t := (Icc (R + 1) L).filter (fun q => D ∣ q))
      (fun k _ => D * k)
    · intro k membership
      obtain ⟨lower, upper⟩ := mem_Icc.mp membership
      have iLower : R / D < k := lower
      have lowerProd : R < k * D := (Nat.div_lt_iff_lt_mul DPositive).mp iLower
      have upperProd : k * D ≤ L := (Nat.le_div_iff_mul_le DPositive).mp upper
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by simpa only [Nat.mul_comm] using Nat.succ_le_of_lt lowerProd,
        by simpa only [Nat.mul_comm] using upperProd⟩, dvd_mul_right _ _⟩
    · intro k _ k' _ same
      exact Nat.eq_of_mul_eq_mul_left DPositive same
    · intro q membership
      obtain ⟨interval, k, identity⟩ := mem_filter.mp membership
      obtain ⟨lower, upper⟩ := mem_Icc.mp interval
      have lowerProd : R < k * D := by rw [Nat.mul_comm, ← identity]; omega
      have upperProd : k * D ≤ L := by rwa [Nat.mul_comm, ← identity]
      exact ⟨k, mem_Icc.mpr ⟨(Nat.div_lt_iff_lt_mul DPositive).mpr lowerProd,
        (Nat.le_div_iff_mul_le DPositive).mpr upperProd⟩, identity.symm⟩
    · intro k membership
      have kPositive : 0 < k := APositive.trans_le (mem_Icc.mp membership).1
      have kNonzero : (k : ℝ) ≠ 0 := by exact_mod_cast kPositive.ne'
      rw [Nat.cast_mul]
      field_simp
  rw [equality]
  have maxBound : max R D ≤ D * A := by
    apply max_le
    · calc
        R = D * (R / D) + R % D := (Nat.div_add_mod R D).symm
        _ ≤ D * (R / D) + D := Nat.add_le_add_left (Nat.mod_lt R DPositive).le _
        _ = D * A := by dsimp [A]; ring
    · exact Nat.le_mul_of_pos_right D APositive
  have denominatorPositive : 0 < (D : ℝ) * (max R D : ℕ) := by
    refine mul_pos DRealPositive ?_
    exact_mod_cast DPositive.trans_le (le_max_right R D)
  calc
    _ ≤ (1 / (D : ℝ) ^ 2) * (2 / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_square_tail_Icc A (L / D) APositive) (by positivity)
    _ = 2 / ((D : ℝ) * ((D : ℝ) * A)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) denominatorPositive
      (mul_le_mul_of_nonneg_left (by exact_mod_cast maxBound) DRealPositive.le)

theorem conductor_modulus_tail (g d f R L : ℕ) (gPositive : 0 < g) (dPositive : 0 < d) (fPositive : 0 < f) :
    (∑ q ∈ (Icc (R + 1) L).filter (fun q => d * g ∣ q ∧ d * f ∣ q),
      ((d : ℝ) * g * f) / (q : ℝ) ^ 2) ≤ 2 * (g.gcd f : ℝ) / (max R (d * g) : ℕ) := by
  let D := d * g.lcm f
  have lcmPositive : 0 < g.lcm f := Nat.lcm_pos gPositive fPositive
  have DPositive : 0 < D := Nat.mul_pos dPositive lcmPositive
  have DRealPositive : (0 : ℝ) < D := by exact_mod_cast DPositive
  have lcmEq : Nat.lcm (d * g) (d * f) = D := by
    change lcm (d * g) (d * f) = d * lcm g f
    rw [lcm_mul_left, normalize_eq]
  have supportEq : (Icc (R + 1) L).filter (fun q => d * g ∣ q ∧ d * f ∣ q) =
      (Icc (R + 1) L).filter (fun q => D ∣ q) := by
    ext q
    rw [mem_filter, mem_filter, ← lcmEq, Nat.lcm_dvd_iff]
  have numerator : (d : ℝ) * g * f = (D : ℝ) * (g.gcd f : ℝ) := by
    exact_mod_cast (show d * g * f = D * g.gcd f from calc
      _ = d * (g * f) := mul_assoc d g f
      _ = d * (g.gcd f * g.lcm f) := by rw [Nat.gcd_mul_lcm]
      _ = _ := by dsimp [D]; ring)
  have stepLower : d * g ≤ D := Nat.mul_le_mul_left _ (Nat.le_of_dvd lcmPositive (Nat.dvd_lcm_left g f))
  have maxLower : (0 : ℝ) < (max R (d * g) : ℕ) := by
    exact_mod_cast (Nat.mul_pos dPositive gPositive).trans_le (le_max_right R (d * g))
  have maxUpper : ((max R (d * g) : ℕ) : ℝ) ≤ (max R D : ℕ) := by
    exact_mod_cast max_le_max_left R stepLower
  rw [supportEq]
  calc
    _ = ((d : ℝ) * g * f) * ∑ q ∈ (Icc (R + 1) L).filter (fun q => D ∣ q), 1 / (q : ℝ) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun q _ => (mul_one_div _ _).symm
    _ ≤ ((d : ℝ) * g * f) * (2 / ((D : ℝ) * (max R D : ℕ))) :=
      mul_le_mul_of_nonneg_left (inverse_square_multiples_tail D R L DPositive) (by positivity)
    _ = 2 * (g.gcd f : ℝ) / (max R D : ℕ) := by rw [numerator]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) maxLower maxUpper


end DyadicMixedB4ModulusTail

end

section

open Finset DyadicMixedB4ModulusTail DyadicMixedB4WeightBudgets

namespace DyadicMixedB4ModulusAggregate

noncomputable section

def conductorCost (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, if d * g ∣ q ∧ d * f ∣ q then
    ((d : ℝ) * g * f) / (q : ℝ) * energy g d else 0

theorem conductorCost_nonnegative (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ)
    (energyNonnegative : ∀ g ∈ G, ∀ d ∈ D, 0 ≤ energy g d) (q : ℕ) :
    0 ≤ conductorCost G D F energy q := by
  unfold conductorCost
  refine sum_nonneg fun g gMember => sum_nonneg fun d dMember => sum_nonneg fun f _ => ?_
  split_ifs
  · exact mul_nonneg (by positivity) (energyNonnegative g gMember d dMember)
  · exact le_rfl

theorem sum_modulus_cost_le (R M : ℕ) (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ)
    (gPositive : ∀ g ∈ G, 0 < g) (dPositive : ∀ d ∈ D, 0 < d) (fPositive : ∀ f ∈ F, 0 < f)
    (energyNonnegative : ∀ g ∈ G, ∀ d ∈ D, 0 ≤ energy g d) :
    (∑ q ∈ Icc (R + 1) M, (q : ℝ)⁻¹ * conductorCost G D F energy q) ≤
      ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, (2 * (g.gcd f : ℝ) / (max R (d * g) : ℕ)) * energy g d := by
  let Q := Icc (R + 1) M
  let term (q g d f : ℕ) := if d * g ∣ q ∧ d * f ∣ q then
    ((d : ℝ) * g * f) / (q : ℝ) ^ 2 * energy g d else 0
  have reorder : (∑ q ∈ Q, ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, term q g d f) =
      ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, ∑ q ∈ Q, term q g d f := by
    rw [sum_comm]
    refine sum_congr rfl fun g _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun d _ => sum_comm
  calc
    _ = ∑ q ∈ Q, ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, term q g d f := by
      refine sum_congr rfl fun q _ => ?_
      unfold conductorCost
      simp only [mul_sum]
      refine sum_congr rfl fun g _ => sum_congr rfl fun d _ => sum_congr rfl fun f _ => ?_
      unfold term
      split_ifs <;> ring
    _ = ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, ∑ q ∈ Q, term q g d f := reorder
    _ ≤ _ := by
      refine sum_le_sum fun g gMember => sum_le_sum fun d dMember => sum_le_sum fun f fMember => ?_
      have factor : (∑ q ∈ Q, term q g d f) =
          (∑ q ∈ Q.filter (fun q => d * g ∣ q ∧ d * f ∣ q), ((d : ℝ) * g * f) / (q : ℝ) ^ 2) * energy g d := by
        rw [sum_mul, sum_filter]
      rw [factor]
      exact mul_le_mul_of_nonneg_right (conductor_modulus_tail g d f R M (gPositive g gMember)
        (dPositive d dMember) (fPositive f fMember)) (energyNonnegative g gMember d dMember)

theorem sum_weighted_moduli_le {ι : Type*} (items : Finset ι) (g : ι → ℕ) (w : ι → ℝ)
    (R M : ℕ) (MPositive : 0 < M) {W : ℝ} (WNonnegative : 0 ≤ W)
    (stepRange : ∀ i ∈ items, g i ∈ Icc 1 M)
    (weightBound : ∀ u ∈ Icc 1 M, (∑ i ∈ items.filter (fun i => g i = u), w i) ≤ W)
    (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ)
    (gPositive : ∀ g ∈ G, 0 < g) (dPositive : ∀ d ∈ D, 0 < d) (fPositive : ∀ f ∈ F, 0 < f)
    (energyNonnegative : ∀ g ∈ G, ∀ d ∈ D, 0 ≤ energy g d) :
    (∑ i ∈ items, (w i / (g i : ℝ)) * ∑ q ∈ (g i).divisors.filter (fun q => R < q),
      conductorCost G D F energy q) ≤
      (W * (1 + Real.log M)) * (∑ u ∈ G, ∑ d ∈ D, ∑ f ∈ F,
        (2 * (u.gcd f : ℝ) / (max R (d * u) : ℕ)) * energy u d) := by
  let Q := Icc (R + 1) M
  let Ψ := conductorCost G D F energy
  let logarithm := 1 + Real.log (M : ℝ)
  have logNonnegative : 0 ≤ logarithm := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast MPositive))
  have moduli (i : ι) (membership : i ∈ items) : (g i).divisors.filter (fun q => R < q) =
      Q.filter (fun q => q ∣ g i) := by
    ext q
    obtain ⟨iPositive, iBound⟩ := mem_Icc.mp (stepRange i membership)
    simp only [Q, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨divides, _⟩, above⟩
      exact ⟨⟨Nat.succ_le_of_lt above, (Nat.le_of_dvd iPositive divides).trans iBound⟩, divides⟩
    · rintro ⟨⟨above, _⟩, divides⟩
      exact ⟨⟨divides, by omega⟩, above⟩
  calc
    _ = ∑ i ∈ items, ∑ q ∈ Q, if q ∣ g i then (w i / (g i : ℝ)) * Ψ q else 0 := by
      refine sum_congr rfl fun i membership => ?_
      rw [moduli i membership, mul_sum, sum_filter]
    _ = ∑ q ∈ Q, (∑ i ∈ items, if q ∣ g i then w i / (g i : ℝ) else 0) * Ψ q := by
      rw [sum_comm]
      refine sum_congr rfl fun q _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by split_ifs <;> simp
    _ ≤ ∑ q ∈ Q, W * (q : ℝ)⁻¹ * logarithm * Ψ q := by
      refine sum_le_sum fun q qMember => ?_
      have qPositive : 0 < q := (Nat.zero_lt_succ R).trans_le (mem_Icc.mp qMember).1
      exact mul_le_mul_of_nonneg_right (step_multiple_weight_le items g w M q qPositive WNonnegative stepRange weightBound)
        (conductorCost_nonnegative G D F energy energyNonnegative q)
    _ = (W * logarithm) * ∑ q ∈ Q, (q : ℝ)⁻¹ * Ψ q := by
      rw [mul_sum]
      exact sum_congr rfl fun q _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_modulus_cost_le R M G D F energy gPositive dPositive fPositive energyNonnegative)
      (mul_nonneg WNonnegative logNonnegative)


end
end DyadicMixedB4ModulusAggregate

end

section

open Finset DyadicMixedB4ArcGeometry DyadicMixedB4BilinearBlock DyadicMixedB4BilinearEnergy
open DyadicMixedB4ModulusAggregate

namespace DyadicMixedB4BlockModulus

noncomputable section

theorem norm_primitiveBlock_le (n M B H q step lo hi U A : ℕ) (nPositive : 0 < n) (APositive : 0 < A)
    (qPositive : 0 < q) (qBound : q ≤ M) (stepBound : M ≤ n) (radiusUpper : radius M ≤ 1)
    (indices : Finset ℕ) (indexRange : indices ⊆ Ico A (2 * A)) (w : ℕ → ℂ)
    {T : ℝ} (TNonnegative : 0 ≤ T) (wBound : ∀ a ∈ indices, ‖w a‖ ≤ T)
    (divisorBound : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    ‖primitiveBlock n M B H q step lo hi U indices w‖ ≤
      (T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1)) / (step : ℝ)) *
        conductorCost (Icc 1 (2 * A)) (Icc 1 M) n.divisors (blockEnergy n A U) q := by
  let G := Icc 1 (2 * A)
  let D := Icc 1 M
  let energy := blockEnergy n A U
  let K := T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1)) / (step : ℝ)
  have KNonnegative : 0 ≤ K := by
    unfold K
    have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  let budget (g d : ℕ) :=
    ∑ f ∈ n.divisors, if d * g ∣ q ∧ d * f ∣ q then ((d : ℝ) * g * f) / (q : ℝ) * energy g d else 0
  have budgetNonnegative (g d : ℕ) : 0 ≤ budget g d := by
    unfold budget
    refine sum_nonneg fun f _ => ?_
    split_ifs
    · exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · exact le_rfl
  let fibre (g : ℕ) := indices.filter (fun a => a.gcd q = g)
  have mapsTo (a : ℕ) (member : a ∈ indices) : a.gcd q ∈ G := by
    obtain ⟨lower, upper⟩ := mem_Ico.mp (indexRange member)
    have aPositive := APositive.trans_le lower
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left q aPositive, (Nat.gcd_le_left q aPositive).trans upper.le⟩
  have boundFibre (g : ℕ) (gMember : g ∈ G) :
      ‖primitiveBlock n M B H q step lo hi U (fibre g) w‖ ≤ K * ∑ d ∈ D, budget g d := by
    have gPositive : 0 < g := (mem_Icc.mp gMember).1
    have exactGcd (a : ℕ) (member : a ∈ fibre g) : a.gcd q = g := (mem_filter.mp member).2
    by_cases gq : g ∣ q
    · have rPositive : 0 < q / g := Nat.div_pos (Nat.le_of_dvd qPositive gq) gPositive
      letI : NeZero q := ⟨qPositive.ne'⟩
      letI : NeZero (q / g) := ⟨rPositive.ne'⟩
      let r := q / g
      let qr : r ∣ q := Nat.div_dvd_of_dvd gq
      have inclusion : r.divisors ⊆ D := by
        intro d member
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors member,
          (Nat.divisor_le member).trans ((Nat.div_le_self q g).trans qBound)⟩
      rw [primitiveBlock_eq_sum_conductorBlock gq n M B H step lo hi U (fibre g) w exactGcd]
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ d ∈ r.divisors.attach, K * budget g d.1 := by
          refine sum_le_sum fun d _ => ?_
          have estimate := norm_conductorBlock_le gq n M B H step lo hi U A nPositive APositive gPositive
            radiusUpper (fibre g) (fun _ member => indexRange (mem_filter.mp member).1)
            exactGcd w TNonnegative (fun a member => wBound a (mem_filter.mp member).1)
            (divisorBound r ((Nat.div_le_self q g).trans (qBound.trans stepBound))) d
          have divides : d.1 * g ∣ q := by
            rw [Nat.mul_comm]
            exact (Nat.dvd_div_iff_mul_dvd gq).mp (Nat.dvd_of_mem_divisors d.2)
          have factor : budget g d.1 =
              (∑ f ∈ n.divisors, if d.1 * f ∣ q then ((d.1 : ℝ) * g * f) / (q : ℝ) else 0) * energy g d.1 := by
            unfold budget
            rw [sum_mul]
            refine sum_congr rfl fun f _ => ?_
            simp only [divides, true_and]
            split_ifs <;> simp
          rw [factor, ← mul_assoc]
          exact estimate
        _ = K * ∑ d ∈ r.divisors, budget g d := by
          rw [mul_sum]
          exact sum_attach r.divisors (fun d => K * budget g d)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg inclusion (fun d _ _ => budgetNonnegative g d)) KNonnegative
    · have empty : fibre g = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a member
        exact gq (exactGcd a member ▸ Nat.gcd_dvd_right a q)
      rw [empty, primitiveBlock, sum_empty, norm_zero]
      exact mul_nonneg KNonnegative (sum_nonneg fun d _ => budgetNonnegative g d)
  have split : primitiveBlock n M B H q step lo hi U indices w =
      ∑ g ∈ G, primitiveBlock n M B H q step lo hi U (fibre g) w := by
    unfold primitiveBlock
    exact (sum_fiberwise_of_maps_to mapsTo _).symm
  rw [split]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ g ∈ G, K * ∑ d ∈ D, budget g d := sum_le_sum boundFibre
    _ = _ := by rw [← mul_sum]; rfl


end
end DyadicMixedB4BlockModulus

end

section

namespace DyadicMixedB4DyadicCost

private theorem sqrt_prod_le_max {x y : ℝ} (xNonnegative : 0 ≤ x) :
    Real.sqrt x * Real.sqrt y ≤ max x y := by
  calc
    _ ≤ Real.sqrt (max x y) * Real.sqrt (max x y) :=
      mul_le_mul (Real.sqrt_le_sqrt (le_max_left _ _)) (Real.sqrt_le_sqrt (le_max_right _ _))
        (Real.sqrt_nonneg y) (Real.sqrt_nonneg _)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (xNonnegative.trans (le_max_left _ _))]

private theorem sqrt_le_of_le_sq {x y : ℝ} (yNonnegative : 0 ≤ y) (bound : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := (Real.sqrt_le_sqrt bound).trans_eq (Real.sqrt_sq yNonnegative)

theorem dyadic_cost_le (A G D Y R : ℝ) (aPositive : 0 < A) (gLower : 1 ≤ G)
    (dPositive : 0 < D) (yPositive : 0 < Y) (rPositive : 0 < R) (yLarge : A ≤ Real.sqrt Y) :
    Real.sqrt ((A / G) * D * (A / G + D) * (Y + D ^ 2) * Y) / max R (G * D) ≤
      (2 * A * Y) / (G * Real.sqrt G * Real.sqrt R) +
      (2 * Real.sqrt A * Y) / (G * Real.sqrt G) +
      (2 * Real.sqrt A * Real.sqrt Y * D) / (G * Real.sqrt G) := by
  let X := A / G
  let T := max R (G * D)
  let energy := X * D * (X + D) * (Y + D ^ 2) * Y
  let lowCost := (2 * A * Y) / (G * Real.sqrt G * Real.sqrt R)
  let midCost := (2 * Real.sqrt A * Y) / (G * Real.sqrt G)
  let highCost := (2 * Real.sqrt A * Real.sqrt Y * D) / (G * Real.sqrt G)
  have gPositive : 0 < G := zero_lt_one.trans_le gLower
  have xPositive : 0 < X := div_pos aPositive gPositive
  have tPositive : 0 < T := rPositive.trans_le (le_max_left _ _)
  have productPositive : 0 < G * D := mul_pos gPositive dPositive
  have productBound : G * D ≤ T := le_max_right _ _
  have xBound : X ≤ Real.sqrt Y := (div_le_self aPositive.le gLower).trans yLarge
  have lowNonnegative : 0 ≤ lowCost := by dsimp [lowCost]; positivity
  have midNonnegative : 0 ≤ midCost := by dsimp [midCost]; positivity
  have highNonnegative : 0 ≤ highCost := by dsimp [highCost]; positivity
  have addLow : lowCost ≤ lowCost + midCost + highCost := by linarith only [midNonnegative, highNonnegative]
  have addMid : midCost ≤ lowCost + midCost + highCost := by linarith only [lowNonnegative, highNonnegative]
  have addHigh : highCost ≤ lowCost + midCost + highCost := by linarith only [lowNonnegative, midNonnegative]
  have sqrtX : Real.sqrt X = Real.sqrt A / Real.sqrt G := Real.sqrt_div aPositive.le _
  have sqrtDPositive : 0 < Real.sqrt D := Real.sqrt_pos.mpr dPositive
  have sqrtGPositive : 0 < Real.sqrt G := Real.sqrt_pos.mpr gPositive
  have sqrtRPositive : 0 < Real.sqrt R := Real.sqrt_pos.mpr rPositive
  change Real.sqrt energy / T ≤ lowCost + midCost + highCost
  by_cases medium : D ≤ Real.sqrt Y
  · have Dsquare : D ^ 2 ≤ Y := by
      have bound := pow_le_pow_left₀ dPositive.le medium 2
      rwa [Real.sq_sqrt yPositive.le] at bound
    by_cases narrow : D ≤ X
    · have root : Real.sqrt energy ≤ 2 * X * Real.sqrt D * Y := by
        apply sqrt_le_of_le_sq (by positivity)
        calc
          _ ≤ X * D * (2 * X) * (2 * Y) * Y := by
            unfold energy
            gcongr <;> linarith only [narrow, Dsquare]
          _ = _ := by simp only [mul_pow, Real.sq_sqrt dPositive.le]; ring
      have geometric := sqrt_prod_le_max (y := G * D) rPositive.le
      rw [Real.sqrt_mul gPositive.le] at geometric
      have geometricPositive := mul_pos sqrtRPositive (mul_pos sqrtGPositive sqrtDPositive)
      refine le_trans ?_ addLow
      calc
        _ ≤ (2 * X * Real.sqrt D * Y) / T := div_le_div_of_nonneg_right root tPositive.le
        _ ≤ (2 * X * Real.sqrt D * Y) / (Real.sqrt R * (Real.sqrt G * Real.sqrt D)) :=
          div_le_div_of_nonneg_left (by positivity) geometricPositive geometric
        _ = _ := by
          unfold lowCost X
          field_simp [gPositive.ne', sqrtDPositive.ne', sqrtGPositive.ne', sqrtRPositive.ne']
    · have root : Real.sqrt energy ≤ 2 * Real.sqrt X * D * Y := by
        apply sqrt_le_of_le_sq (by positivity)
        calc
          _ ≤ X * D * (2 * D) * (2 * Y) * Y := by
            unfold energy
            gcongr <;> linarith only [lt_of_not_ge narrow, Dsquare]
          _ = _ := by simp only [mul_pow, Real.sq_sqrt xPositive.le]; ring
      refine le_trans ?_ addMid
      calc
        _ ≤ (2 * Real.sqrt X * D * Y) / T := div_le_div_of_nonneg_right root tPositive.le
        _ ≤ (2 * Real.sqrt X * D * Y) / (G * D) :=
          div_le_div_of_nonneg_left (by positivity) productPositive productBound
        _ = _ := by
          unfold midCost
          rw [sqrtX]
          field_simp [gPositive.ne', dPositive.ne', sqrtGPositive.ne']
  · have wide : X ≤ D := xBound.trans (lt_of_not_ge medium).le
    have ySquare : Y ≤ D ^ 2 := by
      have bound := pow_le_pow_left₀ (Real.sqrt_nonneg Y) (lt_of_not_ge medium).le 2
      rwa [Real.sq_sqrt yPositive.le] at bound
    have root : Real.sqrt energy ≤ 2 * Real.sqrt X * Real.sqrt Y * D ^ 2 := by
      apply sqrt_le_of_le_sq (by positivity)
      calc
        _ ≤ X * D * (2 * D) * (2 * D ^ 2) * Y := by
          unfold energy
          gcongr <;> linarith only [wide, ySquare]
        _ = _ := by simp only [mul_pow, Real.sq_sqrt xPositive.le, Real.sq_sqrt yPositive.le]; ring
    refine le_trans ?_ addHigh
    calc
      _ ≤ (2 * Real.sqrt X * Real.sqrt Y * D ^ 2) / T := div_le_div_of_nonneg_right root tPositive.le
      _ ≤ (2 * Real.sqrt X * Real.sqrt Y * D ^ 2) / (G * D) :=
        div_le_div_of_nonneg_left (by positivity) productPositive productBound
      _ = _ := by
        unfold highCost
        rw [sqrtX]
        field_simp [gPositive.ne', dPositive.ne', sqrtGPositive.ne']


end DyadicMixedB4DyadicCost

end

section

open Finset DyadicMixedB4BilinearEnergy DyadicMixedB4DyadicCost
open DyadicMixedB4MaximalSieve DyadicMixedB4PrimitiveEnergy

namespace DyadicMixedB4EnergyTail

noncomputable section

def logBudget (n : ℕ) : ℝ := 1 + Real.log ((n : ℝ) + 2)

theorem one_le_logBudget (n : ℕ) : 1 ≤ logBudget n :=
  le_add_of_nonneg_right (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))

def tailShape (n A M R : ℕ) : ℝ :=
  (n : ℝ) / Real.sqrt R + (n : ℝ) / Real.sqrt A + Real.sqrt n * (M : ℝ)

theorem tailShape_nonnegative (n A M R : ℕ) : 0 ≤ tailShape n A M R := by
  unfold tailShape
  positivity

def tailWeight (R g f d : ℕ) : ℝ := 2 * (g.gcd f : ℝ) / (max R (d * g) : ℕ)

theorem tailWeight_nonnegative (R g f d : ℕ) : 0 ≤ tailWeight R g f d := by
  unfold tailWeight
  positivity

theorem blockEnergy_nonnegative (n A U g d : ℕ) : 0 ≤ blockEnergy n A U g d := Real.sqrt_nonneg _

theorem energy_tail_in_dyad_le (n A U R M g f D : ℕ) (aPos : 0 < A) (gPos : 0 < g)
    (gUpper : g ≤ 2 * A) (dPos : 0 < D) (rPos : 0 < R) (dUpper : D ≤ M)
    (yLarge : (A : ℝ) ≤ Real.sqrt (n / A : ℕ)) :
    (∑ d ∈ Ico D (2 * D), tailWeight R g f d * blockEnergy n A U g d) ≤
      2048 * logBudget n ^ 2 * ((g.gcd f : ℝ) / ((g : ℝ) * Real.sqrt g)) * tailShape n A M R := by
  let Y := n / A
  let X := (2 * A) / g + 1
  let x := (A : ℝ) / g
  let Z := max (R : ℝ) ((g : ℝ) * D)
  let I := prefixMass Y
  let J d := integratedPrimitiveEnergy Y d (mangoldtExtension U)
  let L := Real.log ((Y : ℝ) + 2)
  let P := x * (x + D) * I
  let Q := (D : ℝ) * I * ((Y : ℝ) + (D : ℝ) ^ 2) * Y
  let V := x * D * (x + D) * ((Y : ℝ) + (D : ℝ) ^ 2) * Y
  have gReal : (0 : ℝ) < g := by exact_mod_cast gPos
  have aReal : (0 : ℝ) < A := by exact_mod_cast aPos
  have dReal : (0 : ℝ) < D := by exact_mod_cast dPos
  have rReal : (0 : ℝ) < R := by exact_mod_cast rPos
  have aSqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos_of_pos aReal
  have yPos : 0 < (Y : ℝ) := by
    by_contra! hy
    rw [Real.sqrt_eq_zero_of_nonpos hy] at yLarge
    exact aReal.not_ge yLarge
  have ZPos : 0 < Z := rReal.trans_le (le_max_left _ _)
  have xPos : 0 < x := div_pos aReal gReal
  have I0 : 0 ≤ I := prefixMass_nonnegative _
  have L0 : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  have P0 : 0 ≤ P := by unfold P; positivity
  have Q0 : 0 ≤ Q := by unfold Q; positivity
  have xBound : (X : ℝ) ≤ 4 * x := by
    have division : (((2 * A) / g : ℕ) : ℝ) * g ≤ 2 * (A : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (2 * A) g
    have oneBound : 1 ≤ 2 * x := by
      unfold x
      rw [← mul_div_assoc]
      exact (le_div_iff₀ gReal).mpr (by simpa using (show (g : ℝ) ≤ 2 * (A : ℝ) by exact_mod_cast gUpper))
    have half : (((2 * A) / g : ℕ) : ℝ) ≤ 2 * x := by
      unfold x
      rw [← mul_div_assoc]
      exact (le_div_iff₀ gReal).mpr division
    unfold X
    push_cast
    linarith only [oneBound, half]
  have weightBound (d : ℕ) (member : d ∈ Ico D (2 * D)) :
      tailWeight R g f d ≤ 2 * (g.gcd f : ℝ) / Z := by
    have dBound : (D : ℝ) ≤ d := by exact_mod_cast (mem_Ico.mp member).1
    unfold tailWeight
    push_cast
    apply div_le_div_of_nonneg_left (by positivity) ZPos
    unfold Z
    rw [mul_comm (d : ℝ)]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left dBound gReal.le)
  have energyBound (d : ℕ) (member : d ∈ Ico D (2 * D)) :
      blockEnergy n A U g d ≤ (4 * Real.sqrt P) * Real.sqrt (J d) := by
    have dBound : (d : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast (mem_Ico.mp member).2.le
    have second : (X : ℝ) + d ≤ 4 * (x + D) := by linarith only [xBound, dBound, dReal]
    have J0 : 0 ≤ J d := integratedPrimitiveEnergy_nonnegative _ _ _
    have within : (X : ℝ) * ((X : ℝ) + d) * I * J d ≤ 16 * P * J d := by
      calc
        _ ≤ ((4 * x) * (4 * (x + D))) * I * J d := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul xBound second (by positivity) (by positivity)) I0) J0
        _ = _ := by unfold P; ring
    calc
      _ ≤ Real.sqrt (16 * P * J d) := Real.sqrt_le_sqrt within
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ 16 * P), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]; norm_num
  have energySum := sum_sqrt_dyadic_energy_le Y U D dPos
  have sqrtFactor : Real.sqrt P * Real.sqrt Q = I * Real.sqrt V := by
    rw [← Real.sqrt_mul P0]
    have factor : P * Q = I ^ 2 * V := by unfold P Q V; ring
    rw [factor, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq I0]
  have cost := dyadic_cost_le (A : ℝ) (g : ℝ) (D : ℝ) (Y : ℝ) (R : ℝ) aReal
    (by exact_mod_cast gPos) dReal yPos rReal yLarge
  have nBound : (A : ℝ) * (Y : ℝ) ≤ n := by
    rw [mul_comm]
    exact_mod_cast Nat.div_mul_le_self n A
  have middle : Real.sqrt (A : ℝ) * (Y : ℝ) ≤ (n : ℝ) / Real.sqrt A := by
    apply (le_div_iff₀ aSqrt).mpr
    calc
      _ = (A : ℝ) * (Y : ℝ) := by
        calc
          _ = (Real.sqrt (A : ℝ)) ^ 2 * (Y : ℝ) := by ring
          _ = _ := by rw [Real.sq_sqrt aReal.le]
      _ ≤ _ := nBound
  have endTerm : Real.sqrt (A : ℝ) * Real.sqrt (Y : ℝ) * D ≤ Real.sqrt (n : ℝ) * M := by
    rw [← Real.sqrt_mul aReal.le]
    exact mul_le_mul (Real.sqrt_le_sqrt nBound) (by exact_mod_cast dUpper)
      (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have simplified : Real.sqrt V / Z ≤ (2 / ((g : ℝ) * Real.sqrt g)) * tailShape n A M R := by
    refine cost.trans ?_
    unfold tailShape
    have first : (A : ℝ) * (Y : ℝ) / Real.sqrt R ≤ (n : ℝ) / Real.sqrt R :=
      div_le_div_of_nonneg_right nBound (Real.sqrt_nonneg _)
    have combined := add_le_add (add_le_add first middle) endTerm
    calc
      _ = (2 / ((g : ℝ) * Real.sqrt g)) *
          ((A : ℝ) * (Y : ℝ) / Real.sqrt R + Real.sqrt (A : ℝ) * (Y : ℝ) +
            Real.sqrt (A : ℝ) * Real.sqrt (Y : ℝ) * D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left combined (by positivity)
  have logBound : L ≤ logBudget n := by
    have yBound : (Y : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n A
    exact (Real.log_le_log (by positivity) (by linarith only [yBound])).trans
      (le_add_of_nonneg_left zero_le_one)
  have massBound : I ≤ 8 * logBudget n :=
    (integral_prefixMajorant_le Y).trans (mul_le_mul_of_nonneg_left logBound (by norm_num))
  calc
    _ ≤ ∑ d ∈ Ico D (2 * D), (2 * (g.gcd f : ℝ) / Z * (4 * Real.sqrt P)) * Real.sqrt (J d) := by
      refine sum_le_sum fun d member => ?_
      rw [mul_assoc]
      exact mul_le_mul (weightBound d member) (energyBound d member)
        (blockEnergy_nonnegative n A U g d) (by positivity)
    _ ≤ (2 * (g.gcd f : ℝ) / Z * (4 * Real.sqrt P)) * (16 * L * Real.sqrt Q) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left energySum (by positivity)
    _ = 128 * L * I * (g.gcd f : ℝ) * (Real.sqrt V / Z) := by
      calc
        _ = 128 * L * (g.gcd f : ℝ) / Z * (Real.sqrt P * Real.sqrt Q) := by ring
        _ = _ := by rw [sqrtFactor]; ring
    _ ≤ 128 * logBudget n * (8 * logBudget n) * (g.gcd f : ℝ) *
        ((2 / ((g : ℝ) * Real.sqrt g)) * tailShape n A M R) := by
      have bNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left logBound (by norm_num)) massBound I0 (by positivity))
            (Nat.cast_nonneg _))
        simplified (div_nonneg (Real.sqrt_nonneg _) ZPos.le) (by positivity)
    _ = _ := by ring


end
end DyadicMixedB4EnergyTail

end

section

open Filter Topology DyadicMixedB4ArcGeometry

namespace DyadicMixedB4Scale

noncomputable section

def cutoffU (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊
def cutoffB (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
def cutoffR (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 9 : ℝ)⌋₊
def maximumStep (n : ℕ) : ℕ := cutoffU n * cutoffB n
def cutoffH (n : ℕ) : ℕ := 256 * cutoffB n * (Nat.log 2 (n + 2)) ^ 2

theorem maximumStep_le_power (n : ℕ) (nPositive : 0 < n) :
    (maximumStep n : ℝ) ≤ (n : ℝ) ^ (19 / 48 : ℝ) := by
  have u : (cutoffU n : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) := Nat.floor_le (by positivity)
  have b : (cutoffB n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  unfold maximumStep
  push_cast
  calc
    _ ≤ (n : ℝ) ^ (1 / 16 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_add (by positivity)]; norm_num

theorem floor_half_le {x : ℝ} (xLower : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases small : x ≤ 2
  · have floorLower : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.le_floor (n := 1) (by simpa using xLower))
    linarith only [small, floorLower]
  · have floorBound := Nat.lt_floor_add_one x
    linarith only [floorBound, lt_of_not_ge small]

theorem cutoffs_ordered (n : ℕ) (nPositive : 0 < n) :
    1 ≤ cutoffR n ∧ cutoffR n ≤ cutoffB n ∧ cutoffB n ≤ maximumStep n ∧ maximumStep n ≤ n := by
  have nReal : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have Upositive : 1 ≤ cutoffU n := Nat.le_floor (Real.one_le_rpow nReal (by norm_num))
  refine ⟨Nat.le_floor (Real.one_le_rpow nReal (by norm_num)), ?_, ?_, ?_⟩
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nReal (by norm_num))
  · exact Nat.le_mul_of_pos_left (cutoffB n) Upositive
  · exact_mod_cast (maximumStep_le_power n nPositive).trans ((Real.rpow_le_rpow_of_exponent_le nReal
      (by norm_num : (19 / 48 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))

/-- The logarithm comparison adapts the corresponding estimate in
goldbach-proofs PR #2468, revision 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem log2_le_four_log (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  have hb := Real.natLog_le_logb (n + 2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have square : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logarithm := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) square
  rw [Real.log_pow] at logarithm
  norm_num at logarithm
  have divided := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
  have multiplied := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n + 2)) : (0 : ℝ) ≤ _)
  linarith only [logarithm, divided, multiplied]

theorem cutoffR_covered (n : ℕ) (nPositive : 0 < n) :
    (cutoffR n : ℝ) * n * radius (maximumStep n) ≤ cutoffH n := by
  have nReal : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have uLower : (n : ℝ) ^ (1 / 16 : ℝ) / 2 ≤ cutoffU n := floor_half_le (Real.one_le_rpow nReal (by norm_num))
  have bLower : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ cutoffB n := floor_half_le (Real.one_le_rpow nReal (by norm_num))
  have logLower : (1 : ℝ) ≤ Nat.log 2 (n + 2) := by
    exact_mod_cast Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)
  have rUpper : (cutoffR n : ℝ) ≤ (n : ℝ) ^ (1 / 9 : ℝ) := Nat.floor_le (by positivity)
  have MPositive : 0 < maximumStep n := by have := cutoffs_ordered n nPositive; omega
  have coverLower : (64 : ℝ) * (n : ℝ) ^ (9 / 8 : ℝ) ≤ 8 * (maximumStep n : ℝ) ^ 2 * (cutoffH n : ℝ) := by
    have uPower : ((n : ℝ) ^ (1 / 16 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul nRealPositive.le]
      norm_num
    have bPower : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul nRealPositive.le]
      norm_num
    calc
      _ = 2048 * ((n : ℝ) ^ (1 / 16 : ℝ) / 2) ^ 2 * ((n : ℝ) ^ (1 / 3 : ℝ) / 2) ^ 3 := by
        rw [div_pow, div_pow, uPower, bPower]
        have exponent : (n : ℝ) ^ (9 / 8 : ℝ) = (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) := by
          calc
            _ = (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add nRealPositive]; norm_num
            _ = _ := by rw [Real.rpow_one]
        rw [exponent]
        ring
      _ ≤ 2048 * (cutoffU n : ℝ) ^ 2 * (cutoffB n : ℝ) ^ 3 := by gcongr
      _ ≤ 2048 * (cutoffU n : ℝ) ^ 2 * (cutoffB n : ℝ) ^ 3 * (Nat.log 2 (n + 2) : ℝ) ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ logLower)
      _ = _ := by unfold maximumStep cutoffH; push_cast; ring
  have coverUpper : (cutoffR n : ℝ) * n ≤ (n : ℝ) ^ (9 / 8 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 9 : ℝ) * n := mul_le_mul_of_nonneg_right rUpper nRealPositive.le
      _ = (n : ℝ) ^ (10 / 9 : ℝ) := by
        calc
          _ = (n : ℝ) ^ (1 / 9 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add nRealPositive]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le nReal (by norm_num)
  unfold radius
  rw [mul_one_div]
  apply (div_le_iff₀ (show 0 < 8 * (maximumStep n : ℝ) ^ 2 by positivity)).mpr
  exact coverUpper.trans ((le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 64)).trans
    (by simpa only [mul_comm (cutoffH n : ℝ)] using coverLower))

theorem eventually_small_width : ∀ᶠ n : ℕ in atTop, 4 * cutoffH n * maximumStep n ≤ n := by
  have limit : Tendsto (fun n : ℕ => (Real.log n) ^ 2 / (n : ℝ) ^ (13 / 48 : ℝ)) atTop (𝓝 0) := by
    have asymptotic := (isLittleO_log_rpow_rpow_atTop (2 : ℕ) (show (0 : ℝ) < 13 / 48 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Function.comp_def] using asymptotic.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, limit.eventually_lt_const (show (0 : ℝ) < 1 / 16384 by norm_num)] with n hn small
  have nPositive : 0 < n := by omega
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have bUpper : (cutoffB n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  have stepUpper := maximumStep_le_power n nPositive
  have logUpper := log2_le_four_log n hn
  have asReal : (4 : ℝ) * (cutoffH n : ℝ) * maximumStep n ≤ n := by
    calc
      _ = 1024 * (cutoffB n : ℝ) * (Nat.log 2 (n + 2) : ℝ) ^ 2 * (maximumStep n : ℝ) := by
        unfold cutoffH
        push_cast
        ring
      _ ≤ 1024 * ((n : ℝ) ^ (1 / 3 : ℝ)) * (4 * Real.log n) ^ 2 * ((n : ℝ) ^ (19 / 48 : ℝ)) := by gcongr
      _ = (n : ℝ) ^ (35 / 48 : ℝ) * (16384 * (Real.log n) ^ 2) := by
        have exponent : (n : ℝ) ^ (35 / 48 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (19 / 48 : ℝ) := by
          rw [← Real.rpow_add nRealPositive]
          norm_num
        rw [exponent]
        ring
      _ ≤ (n : ℝ) ^ (35 / 48 : ℝ) * (n : ℝ) ^ (13 / 48 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have absorbed := (div_lt_iff₀ (show 0 < (n : ℝ) ^ (13 / 48 : ℝ) by positivity)).mp small
        linarith only [absorbed]
      _ = _ := by rw [← Real.rpow_add nRealPositive]; norm_num
  exact_mod_cast asReal


end
end DyadicMixedB4Scale

end

section

open DyadicMixedB4EnergyTail DyadicMixedB4Scale

namespace DyadicMixedB4TailScale

noncomputable section

theorem log_le_logBudget {m n : ℕ} (mPositive : 0 < m) (upper : m ≤ n) :
    Real.log m ≤ logBudget n := by
  have mReal : (0 : ℝ) < m := by exact_mod_cast mPositive
  have mUpper : (m : ℝ) ≤ n := by exact_mod_cast upper
  exact (Real.log_le_log mReal (by linarith)).trans (le_add_of_nonneg_left zero_le_one)

theorem natLog_succ_le {m n : ℕ} (nLower : 2 ≤ n) (mBound : m ≤ n) :
    (Nat.log 2 m : ℝ) + 1 ≤ 5 * logBudget n := by
  have hlog := log2_le_four_log n nLower
  have hmono : (Nat.log 2 m : ℝ) ≤ Nat.log 2 (n + 2) := by
    exact_mod_cast Nat.log_mono_right (mBound.trans (Nat.le_add_right n 2))
  have hle := log_le_logBudget (by omega : 0 < n) (le_refl n)
  linarith only [hlog, hmono, hle, one_le_logBudget n]

theorem one_add_log_step_le (n : ℕ) (nPositive : 0 < n) :
    1 + Real.log (maximumStep n : ℝ) ≤ logBudget n := by
  obtain ⟨rPositive, rBound, bBound, mBound⟩ := cutoffs_ordered n nPositive
  have mPositive := rPositive.trans (rBound.trans bBound)
  have positive : (0 : ℝ) < maximumStep n := by exact_mod_cast mPositive
  have upper : (maximumStep n : ℝ) ≤ n := by exact_mod_cast mBound
  exact add_le_add_right (Real.log_le_log positive (by linarith only [upper])) 1

theorem maximumStep_divisor_lower (n : ℕ) (nPositive : 0 < n) :
    (n : ℝ) ^ (19 / 48 : ℝ) / 4 ≤ (maximumStep n : ℝ) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have u : (n : ℝ) ^ (1 / 16 : ℝ) / 2 ≤ cutoffU n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  have b : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ cutoffB n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  calc
    _ = ((n : ℝ) ^ (1 / 16 : ℝ) / 2) * ((n : ℝ) ^ (1 / 3 : ℝ) / 2) := by
      rw [div_mul_div_comm, ← Real.rpow_add nReal]; norm_num
    _ ≤ _ := by unfold maximumStep; push_cast; gcongr

theorem sqrt_mul_maximumStep_le (n : ℕ) (nPositive : 0 < n) :
    Real.sqrt (n : ℝ) * (maximumStep n : ℝ) ≤ (n : ℝ) ^ (31 / 32 : ℝ) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  calc
    _ ≤ Real.sqrt (n : ℝ) * (n : ℝ) ^ (19 / 48 : ℝ) :=
      mul_le_mul_of_nonneg_left (maximumStep_le_power n nPositive) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add nReal]
      exact Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)

theorem short_dyad_yLarge {n A : ℕ} (aPositive : 0 < A)
    (aUpper : A ≤ ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊) :
    (A : ℝ) ≤ Real.sqrt (n / A : ℕ) := by
  have aLower : (1 : ℝ) ≤ A := by exact_mod_cast aPositive
  have aRealUpper := (show (A : ℝ) ≤ (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) by exact_mod_cast aUpper).trans
    (Nat.floor_le (by positivity))
  have fourth : (A : ℝ) ^ 4 ≤ (n : ℝ) := by
    refine (pow_le_pow_left₀ (Nat.cast_nonneg _) aRealUpper 4).trans_eq ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have cube : (A : ℝ) ^ 3 ≤ (n : ℝ) := (pow_le_pow_right₀ aLower (by decide : 3 ≤ 4)).trans fourth
  have div : A ^ 2 ≤ n / A := by
    apply (Nat.le_div_iff_mul_le aPositive).mpr
    rw [← pow_succ]
    exact_mod_cast cube
  have rdiv : (A : ℝ) ^ 2 ≤ (n / A : ℕ) := by exact_mod_cast div
  exact (Real.sqrt_sq (Nat.cast_nonneg _)).symm.trans_le (Real.sqrt_le_sqrt rdiv)

private theorem div_sqrt_le_power (n b : ℕ) (nPositive : 0 < n) (bPositive : 0 < b)
    (a : ℝ) (lower : (n : ℝ) ^ (2 * a) / 4 ≤ b) :
    (n : ℝ) / Real.sqrt b ≤ 2 * (n : ℝ) ^ (1 - a) := by
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have bReal : (0 : ℝ) < b := by exact_mod_cast bPositive
  have rootLower : (n : ℝ) ^ a / 2 ≤ Real.sqrt b := by
    calc
      _ = Real.sqrt (((n : ℝ) ^ a / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := by
        apply Real.sqrt_le_sqrt
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul nReal.le, mul_comm a, show (↑(2 : ℕ) : ℝ) = 2 by norm_cast]
        norm_num
        exact lower
  apply (div_le_iff₀ (Real.sqrt_pos_of_pos bReal)).mpr
  calc
    _ = 2 * (n : ℝ) ^ (1 - a) * ((n : ℝ) ^ a / 2) := by
      have product := (Real.rpow_add nReal (1 - a) a).symm
      rw [sub_add_cancel, Real.rpow_one] at product
      calc
        _ = (n : ℝ) ^ (1 - a) * (n : ℝ) ^ a := product.symm
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left rootLower (by positivity)

theorem tailShape_scale_le {n A : ℕ} (nPositive : 0 < n) (aPositive : 0 < A)
    (uLower : cutoffU n < 2 * A) :
    tailShape n A (maximumStep n) (cutoffR n) ≤ 5 * (n : ℝ) ^ (31 / 32 : ℝ) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have uReal : (cutoffU n : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast uLower.le
  have lowerU : (n : ℝ) ^ (1 / 16 : ℝ) / 2 ≤ cutoffU n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  have lowerR : (n : ℝ) ^ (1 / 9 : ℝ) / 2 ≤ cutoffR n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  have rPos := (cutoffs_ordered n nPositive).1
  have first : (n : ℝ) / Real.sqrt (cutoffR n) ≤ 2 * (n : ℝ) ^ (31 / 32 : ℝ) := by
    refine (div_sqrt_le_power n (cutoffR n) nPositive rPos (1 / 18) ?_).trans ?_
    · rw [show (2 : ℝ) * (1 / 18) = 1 / 9 by norm_num]
      linarith only [lowerR, Real.rpow_nonneg nReal.le (1 / 9 : ℝ)]
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)) (by norm_num)
  have second : (n : ℝ) / Real.sqrt (A : ℝ) ≤ 2 * (n : ℝ) ^ (31 / 32 : ℝ) := by
    simpa only [show (1 : ℝ) - 1 / 32 = 31 / 32 by norm_num] using
      (div_sqrt_le_power n A nPositive aPositive (1 / 32) (by
        rw [show (2 : ℝ) * (1 / 32) = 1 / 16 by norm_num]
        linarith only [uReal, lowerU]))
  have third : Real.sqrt (n : ℝ) * (maximumStep n : ℝ) ≤ (n : ℝ) ^ (31 / 32 : ℝ) := by
    calc
      _ ≤ Real.sqrt (n : ℝ) * (n : ℝ) ^ (19 / 48 : ℝ) :=
        mul_le_mul_of_nonneg_left (maximumStep_le_power n nPositive) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add nReal]
        exact Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)
  unfold tailShape
  linarith only [first, second, third]


end
end DyadicMixedB4TailScale

end

section

open Finset

namespace DyadicMixedB4GcdSeries

noncomputable section

def gcdSeriesConstant : ℝ := ∑' j : ℕ, (j : ℝ) ^ (-3 / 2 : ℝ)

theorem gcdSeriesConstant_nonnegative : 0 ≤ gcdSeriesConstant :=
  tsum_nonneg (fun j => Real.rpow_nonneg (Nat.cast_nonneg j) _)

theorem inverse_sqrt_product_eq_rpow {g : ℕ} (gPositive : 0 < g) :
    ((g : ℝ) * Real.sqrt g)⁻¹ = (g : ℝ) ^ (-3 / 2 : ℝ) := by
  have nonnegative : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have positive : (0 : ℝ) < g := by exact_mod_cast gPositive
  rw [Real.sqrt_eq_rpow]
  nth_rw 1 [← Real.rpow_one (g : ℝ)]
  rw [← Real.rpow_add positive, ← Real.rpow_neg nonnegative]
  norm_num

theorem sum_rpow_multiples (h G : ℕ) (hPositive : 0 < h) :
    (∑ g ∈ (Icc 1 G).filter (fun g => h ∣ g), (g : ℝ) ^ (-3 / 2 : ℝ)) =
      (h : ℝ) ^ (-3 / 2 : ℝ) * ∑ k ∈ Icc 1 (G / h), (k : ℝ) ^ (-3 / 2 : ℝ) := by
  rw [mul_sum]
  symm
  apply sum_bij (fun k _ => h * k)
  · intro k member
    obtain ⟨lower, upper⟩ := mem_Icc.mp member
    have productUpper : k * h ≤ G := (Nat.le_div_iff_mul_le hPositive).mp upper
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hPositive lower, by simpa [mul_comm] using productUpper⟩,
      dvd_mul_right h k⟩
  · intro k _ k' _ same
    exact Nat.eq_of_mul_eq_mul_left hPositive same
  · intro g member
    obtain ⟨inIcc, k, identity⟩ := mem_filter.mp member
    obtain ⟨lower, upper⟩ := mem_Icc.mp inIcc
    have productLower : 0 < h * k := identity ▸ lower
    have productUpper : k * h ≤ G := by simpa [identity, Nat.mul_comm] using upper
    exact ⟨k, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left productLower,
      (Nat.le_div_iff_mul_le hPositive).mpr productUpper⟩, identity.symm⟩
  · intro k _
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

theorem gcd_sqrt_reciprocal_sum_le (f G : ℕ) (fPositive : 0 < f) :
    (∑ g ∈ Icc 1 G, (g.gcd f : ℝ) / ((g : ℝ) * Real.sqrt g)) ≤
      gcdSeriesConstant * (f.divisors.card : ℝ) := by
  let series (g : ℕ) := (g : ℝ) ^ (-3 / 2 : ℝ)
  have sNonnegative (g : ℕ) : 0 ≤ series g := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have summable : Summable series := Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ g ∈ Icc 1 G, ∑ h ∈ f.divisors, if h ∣ g then (h : ℝ) * series g else 0 := by
      refine sum_le_sum fun g member => ?_
      have gPositive := (mem_Icc.mp member).1
      have gcdMember : g.gcd f ∈ f.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right g f, fPositive.ne'⟩
      rw [div_eq_mul_inv, inverse_sqrt_product_eq_rpow gPositive]
      have term := single_le_sum (s := f.divisors)
        (f := fun h => if h ∣ g then (h : ℝ) * series g else 0)
        (fun h _ => by
          split_ifs
          · exact mul_nonneg (Nat.cast_nonneg _) (sNonnegative g)
          · exact le_rfl) gcdMember
      simpa only [if_pos (Nat.gcd_dvd_left g f), series] using term
    _ = ∑ h ∈ f.divisors, (h : ℝ) * ∑ g ∈ (Icc 1 G).filter (fun g => h ∣ g), series g := by
      rw [sum_comm]
      refine sum_congr rfl fun h _ => ?_
      rw [mul_sum, sum_filter]
    _ ≤ ∑ _ ∈ f.divisors, gcdSeriesConstant := by
      refine sum_le_sum fun h member => ?_
      have hPositive := Nat.pos_of_mem_divisors member
      have hReal : (1 : ℝ) ≤ h := by exact_mod_cast hPositive
      have coeff : (h : ℝ) * (h : ℝ) ^ (-3 / 2 : ℝ) ≤ 1 := by
        have positive : (0 : ℝ) < h := by positivity
        nth_rw 1 [← Real.rpow_one (h : ℝ)]
        rw [← Real.rpow_add positive]
        exact (Real.rpow_le_rpow_of_exponent_le hReal (by norm_num : (1 + -3 / 2 : ℝ) ≤ 0)).trans_eq
          (Real.rpow_zero _)
      unfold series
      rw [sum_rpow_multiples h G hPositive, ← mul_assoc]
      exact (mul_le_of_le_one_left (sum_nonneg fun k _ => sNonnegative k) coeff).trans
        (summable.sum_le_tsum _ fun k _ => sNonnegative k)
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]


end
end DyadicMixedB4GcdSeries

end

section

open Finset

namespace DyadicMixedB4DyadicPartition

def dyadicIndices (N : ℕ) : Finset ℕ := range (Nat.log 2 N + 1)

def dyadicBase (k : ℕ) : ℕ := 2 ^ k

theorem dyadicBase_positive (k : ℕ) : 0 < dyadicBase k :=
  Nat.pow_pos (by decide)

theorem dyadicBase_le {k N : ℕ} (nPositive : 0 < N) (membership : k ∈ dyadicIndices N) :
    dyadicBase k ≤ N := by
  have exponent : k ≤ Nat.log 2 N := Nat.le_of_lt_succ (mem_range.mp membership)
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) exponent).trans (Nat.pow_log_le_self 2 nPositive.ne')

theorem mem_dyadicInterval {a k : ℕ} (aPositive : 0 < a) (logExact : Nat.log 2 a = k) :
    a ∈ Ico (dyadicBase k) (2 * dyadicBase k) := by
  subst k
  refine mem_Ico.mpr ⟨Nat.pow_log_le_self 2 aPositive.ne', ?_⟩
  unfold dyadicBase
  rw [← Nat.pow_succ']
  exact Nat.lt_pow_succ_log_self (by decide) _

theorem dyadic_sum_partition {R : Type*} [AddCommMonoid R] (s : Finset ℕ) (N : ℕ)
    (upper : ∀ a ∈ s, a ≤ N) (term : ℕ → R) :
    (∑ a ∈ s, term a) = ∑ k ∈ dyadicIndices N, ∑ a ∈ s.filter (fun a => Nat.log 2 a = k), term a :=
  (sum_fiberwise_of_maps_to (fun a member => mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right (upper a member)))) term).symm


end DyadicMixedB4DyadicPartition

end

section

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4DyadicPartition DyadicMixedB4GcdSeries DyadicMixedB4BilinearEnergy

namespace DyadicMixedB4TailAggregate

noncomputable section

theorem sum_energy_tails_le {n A : ℕ} (nLower : 2 ≤ n) (aPositive : 0 < A)
    (aUpper : A ≤ ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊) (uLower : cutoffU n < 2 * A)
    {T : ℝ} (TNonnegative : 0 ≤ T) (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∑ g ∈ Icc 1 (2 * A), ∑ d ∈ Icc 1 (maximumStep n), ∑ f ∈ n.divisors,
      tailWeight (cutoffR n) g f d * blockEnergy n A (cutoffU n) g d) ≤
      51200 * gcdSeriesConstant * T ^ 2 * logBudget n ^ 3 * (n : ℝ) ^ (31 / 32 : ℝ) := by
  let M := maximumStep n
  let R := cutoffR n
  let term (g f d : ℕ) := tailWeight R g f d * blockEnergy n A (cutoffU n) g d
  let C := 2048 * logBudget n ^ 2
  let F (g f : ℕ) := (g.gcd f : ℝ) / ((g : ℝ) * Real.sqrt g)
  let H := tailShape n A M R
  let C' := C * (5 * logBudget n) * H
  have nPositive : 0 < n := by omega
  have MBound : M ≤ n := (cutoffs_ordered n nPositive).2.2.2
  have RPositive : 0 < R := (cutoffs_ordered n nPositive).1
  have MPositive : 0 < M := RPositive.trans_le
    ((cutoffs_ordered n nPositive).2.1.trans (cutoffs_ordered n nPositive).2.2.1)
  have C0 : 0 ≤ C := by unfold C; positivity
  have B0 : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have H0 : 0 ≤ H := tailShape_nonnegative _ _ _ _
  have C'0 : 0 ≤ C' := by unfold C'; positivity
  have F0 (g f : ℕ) : 0 ≤ F g f := by unfold F; positivity
  have term0 (g f d : ℕ) : 0 ≤ term g f d :=
    mul_nonneg (tailWeight_nonnegative _ _ _ _) (blockEnergy_nonnegative _ _ _ _ _)
  have row (g f : ℕ) (gMem : g ∈ Icc 1 (2 * A)) :
      (∑ d ∈ Icc 1 M, term g f d) ≤ C' * F g f := by
    have each (k : ℕ) (kMem : k ∈ dyadicIndices M) :
        (∑ d ∈ (Icc 1 M).filter (fun d => Nat.log 2 d = k), term g f d) ≤ C * F g f * H := by
      let D := dyadicBase k
      have anyMem : (Icc 1 M).filter (fun d => Nat.log 2 d = k) ⊆ Ico D (2 * D) := by
        intro d member
        obtain ⟨dRange, logExact⟩ := mem_filter.mp member
        exact mem_dyadicInterval (mem_Icc.mp dRange).1 logExact
      exact (sum_le_sum_of_subset_of_nonneg anyMem (fun d _ _ => term0 g f d)).trans
        (energy_tail_in_dyad_le n A (cutoffU n) R M g f D aPositive (mem_Icc.mp gMem).1
          (mem_Icc.mp gMem).2 (dyadicBase_positive k) RPositive (dyadicBase_le MPositive kMem)
          (short_dyad_yLarge aPositive aUpper))
    rw [dyadic_sum_partition _ M (fun d member => (mem_Icc.mp member).2)]
    calc
      _ ≤ ∑ _ ∈ dyadicIndices M, C * F g f * H := sum_le_sum each
      _ = ((Nat.log 2 M : ℝ) + 1) * (C * F g f * H) := by
        simp [dyadicIndices, nsmul_eq_mul]
      _ ≤ (5 * logBudget n) * (C * F g f * H) :=
        mul_le_mul_of_nonneg_right (natLog_succ_le nLower MBound) (by positivity)
      _ = _ := by unfold C'; ring
  have divSum : (∑ f ∈ n.divisors, ∑ g ∈ Icc 1 (2 * A), F g f) ≤ gcdSeriesConstant * T ^ 2 := by
    calc
      _ ≤ ∑ f ∈ n.divisors, gcdSeriesConstant * (f.divisors.card : ℝ) :=
        sum_le_sum fun f member => gcd_sqrt_reciprocal_sum_le f (2 * A) (Nat.pos_of_mem_divisors member)
      _ ≤ ∑ _ ∈ n.divisors, gcdSeriesConstant * T :=
        sum_le_sum fun f member => mul_le_mul_of_nonneg_left (tBound _ (Nat.divisor_le member))
          gcdSeriesConstant_nonnegative
      _ ≤ T * (gcdSeriesConstant * T) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (tBound n le_rfl) (mul_nonneg gcdSeriesConstant_nonnegative TNonnegative)
      _ = _ := by ring
  change (∑ g ∈ Icc 1 (2 * A), ∑ d ∈ Icc 1 M, ∑ f ∈ n.divisors, term g f d) ≤ _
  calc
    _ = ∑ g ∈ Icc 1 (2 * A), ∑ f ∈ n.divisors, ∑ d ∈ Icc 1 M, term g f d :=
      sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ g ∈ Icc 1 (2 * A), ∑ f ∈ n.divisors, C' * F g f :=
      sum_le_sum fun g member => sum_le_sum fun f _ => row g f member
    _ = C' * ∑ f ∈ n.divisors, ∑ g ∈ Icc 1 (2 * A), F g f := by
      simp only [mul_sum]
      exact sum_comm
    _ ≤ C' * (gcdSeriesConstant * T ^ 2) := mul_le_mul_of_nonneg_left divSum C'0
    _ = (C * (5 * logBudget n) * (gcdSeriesConstant * T ^ 2)) * H := by unfold C'; ring
    _ ≤ (C * (5 * logBudget n) * (gcdSeriesConstant * T ^ 2)) * (5 * (n : ℝ) ^ (31 / 32 : ℝ)) :=
      mul_le_mul_of_nonneg_left (tailShape_scale_le nPositive aPositive uLower)
        (mul_nonneg (by positivity) (mul_nonneg gcdSeriesConstant_nonnegative (sq_nonneg _)))
    _ = _ := by unfold C; ring


end
end DyadicMixedB4TailAggregate

end

section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4Arithmetic

theorem finite_divisor_hyperbola {R : Type*} [AddCommMonoid R] (limit : ℕ)
    (term : ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors, term a (m / a)) =
      ∑ a ∈ Icc 1 limit, ∑ b ∈ Icc 1 (limit / a), term a b := by
  classical
  have divisorFilter (m : ℕ) (membership : m ∈ Icc 1 limit) :
      m.divisors = (Icc 1 limit).filter (fun a => a ∣ m) := by
    obtain ⟨positive, bounded⟩ := mem_Icc.mp membership
    ext a
    rw [mem_filter, mem_Icc]
    constructor
    · intro divisor
      have divides := Nat.dvd_of_mem_divisors divisor
      exact ⟨⟨Nat.pos_of_mem_divisors divisor, (Nat.le_of_dvd positive divides).trans bounded⟩,
        divides⟩
    · rintro ⟨_, divides⟩
      exact Nat.mem_divisors.mpr ⟨divides, (show 0 < m from positive).ne'⟩
  calc
    _ = ∑ m ∈ Icc 1 limit, ∑ a ∈ Icc 1 limit, if a ∣ m then term a (m / a) else 0 := by
      refine sum_congr rfl fun m membership => ?_
      rw [divisorFilter m membership, sum_filter]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun a membership => ?_
      have aPositive : 0 < a := (mem_Icc.mp membership).1
      let multiply : ℕ ↪ ℕ := ⟨fun b => a * b,
        fun _ _ equal => mul_left_cancel₀ aPositive.ne' equal⟩
      have multiples : (Icc 1 limit).filter (fun m => a ∣ m) =
          (Icc 1 (limit / a)).map multiply := by
        ext m
        simp only [mem_filter, mem_map]
        constructor
        · rintro ⟨inInterval, divides⟩
          obtain ⟨b, rfl⟩ := divides
          obtain ⟨mPositive, mBounded⟩ := mem_Icc.mp inInterval
          have bPositive : 0 < b := by
            by_contra! bZero
            have bEqualsZero : b = 0 := Nat.eq_zero_of_le_zero bZero
            simp [bEqualsZero] at mPositive
          have bBounded : b ≤ limit / a :=
            (Nat.le_div_iff_mul_le aPositive).mpr (by simpa only [mul_comm] using mBounded)
          exact ⟨b, mem_Icc.mpr ⟨bPositive, bBounded⟩, rfl⟩
        · rintro ⟨b, bInInterval, rfl⟩
          obtain ⟨bPositive, bBounded⟩ := mem_Icc.mp bInInterval
          change a * b ∈ Icc 1 limit ∧ a ∣ a * b
          have mBounded : a * b ≤ limit := by
            simpa only [mul_comm] using (Nat.le_div_iff_mul_le aPositive).mp bBounded
          exact ⟨mem_Icc.mpr ⟨Nat.mul_pos aPositive bPositive, mBounded⟩, dvd_mul_right a b⟩
      rw [← sum_filter, multiples, sum_map]
      refine sum_congr rfl fun b _ => ?_
      change term a ((a * b) / a) = term a b
      rw [Nat.mul_div_cancel_left _ aPositive]

theorem long_moebius_eq_negative_short {a cutoff : ℕ} (nonunit : a ≠ 1) :
    (∑ d ∈ a.divisors.filter (fun d => cutoff < d), (μ d : ℝ)) =
      -(∑ d ∈ a.divisors.filter (fun d => d ≤ cutoff), (μ d : ℝ)) := by
  have integerSum : (∑ d ∈ a.divisors, μ d) = 0 := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta, one_apply_ne nonunit]
  have realSum : (∑ d ∈ a.divisors, (μ d : ℝ)) = 0 := by
    exact_mod_cast integerSum
  have partition :
      (∑ d ∈ a.divisors.filter (fun d => cutoff < d), (μ d : ℝ)) +
      (∑ d ∈ a.divisors.filter (fun d => d ≤ cutoff), (μ d : ℝ)) = 0 := by
    rw [← realSum]
    simpa only [not_lt] using
      (sum_filter_add_sum_filter_not a.divisors (fun d => cutoff < d) (fun d => (μ d : ℝ)))
  exact (eq_neg_iff_add_eq_zero).mpr partition

theorem finite_divisor_triples {R : Type*} [AddCommMonoid R]
    (limit cutoff lower cofactorCap : ℕ) (cofactorCapLe : cofactorCap ≤ limit)
    (cofactorBound : ∀ a b : ℕ, lower < a → a * b ≤ limit → b ≤ cofactorCap)
    (term : ℕ → ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors,
      if lower < a ∧ cutoff < m / a then
        ∑ d ∈ a.divisors, if d ≤ cutoff then term d (m / a) (a / d) else 0
      else 0) =
      ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (limit / b)),
        ∑ k ∈ Ioc (lower / d) (limit / (d * b)), term d b k := by
  classical
  let summand (b a : ℕ) : R :=
    if lower < a ∧ cutoff < b then
      ∑ d ∈ a.divisors, if d ≤ cutoff then term d b (a / d) else 0
    else 0
  have cofactorSubset : Ioc cutoff cofactorCap ⊆ Icc 1 limit := by
    intro b member
    obtain ⟨above, bounded⟩ := mem_Ioc.mp member
    exact mem_Icc.mpr ⟨(Nat.zero_le cutoff).trans_lt above, bounded.trans cofactorCapLe⟩
  have cofactorRestrict :
      (∑ b ∈ Icc 1 limit, ∑ a ∈ Icc 1 (limit / b), summand b a) =
        ∑ b ∈ Ioc cutoff cofactorCap, ∑ a ∈ Icc 1 (limit / b), summand b a := by
    symm
    refine sum_subset cofactorSubset fun b inOriginal outside => ?_
    refine sum_eq_zero fun a inRange => ?_
    apply ite_eq_right
    rintro ⟨above, bAbove⟩
    have bPositive : 0 < b := (mem_Icc.mp inOriginal).1
    have productBound := (Nat.le_div_iff_mul_le bPositive).mp (mem_Icc.mp inRange).2
    exact outside (mem_Ioc.mpr ⟨bAbove, cofactorBound a b above productBound⟩)
  calc
    _ = ∑ m ∈ Icc 1 limit, ∑ b ∈ m.divisors, summand b (m / b) := by
      refine sum_congr rfl fun m _ => ?_
      change (∑ a ∈ m.divisors, summand (m / a) a) = _
      rw [← Nat.sum_divisorsAntidiagonal (fun a b => summand b a),
        Nat.sum_divisorsAntidiagonal' (fun a b => summand b a)]
    _ = ∑ b ∈ Icc 1 limit, ∑ a ∈ Icc 1 (limit / b), summand b a :=
      finite_divisor_hyperbola limit summand
    _ = ∑ b ∈ Ioc cutoff cofactorCap, ∑ a ∈ Icc 1 (limit / b), summand b a := cofactorRestrict
    _ = _ := by
      refine sum_congr rfl fun b bMember => ?_
      have bAbove := (mem_Ioc.mp bMember).1
      let expanded (d k : ℕ) : R :=
        if d ≤ cutoff ∧ lower < d * k then term d b k else 0
      have row (a : ℕ) : summand b a = ∑ d ∈ a.divisors, expanded d (a / d) := by
        by_cases above : lower < a
        · simp only [summand, above, bAbove, and_self, ite_true]
          refine sum_congr rfl fun d divisor => ?_
          simp [expanded, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors divisor), above]
        · simp only [summand, above, false_and, ite_false]
          symm
          refine sum_eq_zero fun d divisor => ?_
          simp [expanded, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors divisor), above]
      have dFilter : (Icc 1 (limit / b)).filter (fun d => d ≤ cutoff) =
          Icc 1 (min cutoff (limit / b)) := by
        ext d
        simp only [mem_filter, mem_Icc, le_min_iff]
        tauto
      calc
        _ = ∑ a ∈ Icc 1 (limit / b), ∑ d ∈ a.divisors, expanded d (a / d) :=
          sum_congr rfl fun a _ => row a
        _ = ∑ d ∈ Icc 1 (limit / b), ∑ k ∈ Icc 1 ((limit / b) / d), expanded d k :=
          finite_divisor_hyperbola (limit / b) expanded
        _ = ∑ d ∈ Icc 1 (min cutoff (limit / b)),
            ∑ k ∈ Icc 1 ((limit / b) / d), if lower < d * k then term d b k else 0 := by
          rw [← dFilter, sum_filter]
          refine sum_congr rfl fun d _ => ?_
          by_cases small : d ≤ cutoff <;> simp [expanded, small]
        _ = _ := by
          refine sum_congr rfl fun d dMember => ?_
          have dPositive : 0 < d := (mem_Icc.mp dMember).1
          have kFilter : (Icc 1 ((limit / b) / d)).filter (fun k => lower < d * k) =
              Ioc (lower / d) (limit / (d * b)) := by
            ext k
            simp only [mem_filter, mem_Icc, mem_Ioc]
            rw [Nat.div_div_eq_div_mul, mul_comm b d]
            have lowerIff : lower < d * k ↔ lower / d < k := by
              rw [Nat.div_lt_iff_lt_mul dPositive, mul_comm k d]
            constructor
            · rintro ⟨⟨_, upper⟩, lowerBound⟩
              exact ⟨lowerIff.mp lowerBound, upper⟩
            · rintro ⟨lowerBound, upper⟩
              exact ⟨⟨(Nat.zero_le (lower / d)).trans_lt lowerBound, upper⟩,
                lowerIff.mpr lowerBound⟩
          rw [← sum_filter, kFilter]

def upperBandWeight {R : Type*} [Ring R] (cutoff lower : ℕ)
    (divisorWeight cofactorWeight : ℕ → R) (m : ℕ) : R :=
  ∑ a ∈ m.divisors.filter (fun a => lower < a ∧ cutoff < m / a),
    (∑ d ∈ a.divisors.filter (fun d => cutoff < d), divisorWeight d) * cofactorWeight (m / a)

theorem upper_band_progressions {R : Type*} [CommRing R]
    (limit cutoff lower cofactorCap : ℕ) (cofactorCapLe : cofactorCap ≤ limit)
    (cofactorBound : ∀ a b : ℕ, lower < a → a * b ≤ limit → b ≤ cofactorCap)
    (divisorWeight cofactorWeight phase : ℕ → R)
    (cancellation : ∀ a : ℕ, lower < a → (∑ d ∈ a.divisors, divisorWeight d) = 0) :
    (∑ m ∈ range (limit + 1), upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m) =
      ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (limit / b)),
        (-divisorWeight d) * cofactorWeight b *
          ∑ k ∈ Ioc (lower / d) (limit / (d * b)), phase (d * b * k) := by
  classical
  let term (d b k : ℕ) : R := (-divisorWeight d) * cofactorWeight b * phase (d * b * k)
  have removeZero :
      (∑ m ∈ range (limit + 1), upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m) =
        ∑ m ∈ Icc 1 limit, upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m := by
    symm
    refine sum_subset (fun m member => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp member).2)) ?_
    intro m member outside
    have upper := Nat.lt_succ_iff.mp (mem_range.mp member)
    have zero : m = 0 := by
      by_contra nonzero
      exact outside (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr nonzero, upper⟩)
    simp [zero, upperBandWeight]
  calc
    _ = ∑ m ∈ Icc 1 limit, upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m :=
      removeZero
    _ = ∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors,
        if lower < a ∧ cutoff < m / a then
          ∑ d ∈ a.divisors, if d ≤ cutoff then term d (m / a) (a / d) else 0
        else 0 := by
      refine sum_congr rfl fun m _ => ?_
      rw [upperBandWeight, sum_filter, sum_mul]
      refine sum_congr rfl fun a divisor => ?_
      by_cases inBand : lower < a ∧ cutoff < m / a
      · have split :
            (∑ d ∈ a.divisors.filter (fun d => cutoff < d), divisorWeight d) =
              -(∑ d ∈ a.divisors.filter (fun d => d ≤ cutoff), divisorWeight d) := by
          apply eq_neg_iff_add_eq_zero.mpr
          rw [← cancellation a inBand.1]
          simpa only [not_lt] using
            sum_filter_add_sum_filter_not a.divisors (fun d => cutoff < d) divisorWeight
        simp only [inBand, and_self, ite_true]
        rw [split, ← sum_neg_distrib, sum_mul, sum_mul, sum_filter]
        refine sum_congr rfl fun d dDivisor => ?_
        by_cases small : d ≤ cutoff
        · have product : d * (m / a) * (a / d) = m := by
            calc
              _ = (d * (a / d)) * (m / a) := by ac_rfl
              _ = _ := by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors dDivisor),
                Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors divisor)]
          simp only [small, ite_true, term, product]
        · simp [small]
      · simp [inBand]
    _ = ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (limit / b)),
        ∑ k ∈ Ioc (lower / d) (limit / (d * b)), term d b k :=
      finite_divisor_triples limit cutoff lower cofactorCap cofactorCapLe cofactorBound term
    _ = _ := by
      refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
      rw [mul_sum]

theorem cube_root_cofactor_of_high_divisor {n a b : ℕ} (nPositive : 0 < n)
    (aLarge : ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ < a) (product : a * b ≤ n) :
    b ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  have realPositive : 0 < (n : ℝ) := Nat.cast_pos.mpr nPositive
  have aAbove : (n : ℝ) ^ (2 / 3 : ℝ) < (a : ℝ) := Nat.lt_of_floor_lt aLarge
  have aPositive : 0 < (a : ℝ) := (Real.rpow_pos_of_pos realPositive _).trans aAbove
  have productLe : (a : ℝ) * (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast product
  apply Nat.le_floor
  by_contra! bAbove
  have productLt : (n : ℝ) < (a : ℝ) * (b : ℝ) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add realPositive]
        norm_num
      _ < (a : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right aAbove (Real.rpow_pos_of_pos realPositive _)
      _ < _ := mul_lt_mul_of_pos_left bAbove aPositive
  exact (not_lt_of_ge productLe) productLt

theorem vaughan_high_factor_expansion (n : ℕ) (nPositive : 0 < n) (phase : ℕ → ℂ) :
    let cutoff := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊
    let lower := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊
    let cofactorCap := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    (∑ m ∈ range (n + 1),
      (upperBandWeight cutoff lower (fun d => (μ d : ℝ)) (fun b => Λ b) m : ℂ) * phase m) =
      ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (n / b)),
        (-(μ d : ℂ)) * (Λ b : ℂ) *
          ∑ k ∈ Ioc (lower / d) (n / (d * b)), phase (d * b * k) := by
  dsimp only
  have oneLe : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr nPositive.ne')
  have capBound : ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ≤ n :=
    Nat.floor_le_of_le (Real.rpow_le_self_of_one_le oneLe (by norm_num))
  have lowerPositive : 1 ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow oneLe (by norm_num : 0 ≤ (2 / 3 : ℝ))
  have cancellation (a : ℕ) (large : ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ < a) :
      (∑ d ∈ a.divisors, (μ d : ℂ)) = 0 := by
    have nonunit : a ≠ 1 := by omega
    have integerSum : (∑ d ∈ a.divisors, μ d) = 0 := by
      rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta, one_apply_ne nonunit]
    exact_mod_cast integerSum
  have castWeight (cutoff lower m : ℕ) :
      (upperBandWeight cutoff lower (fun d => (μ d : ℝ)) (fun b => Λ b) m : ℂ) =
        upperBandWeight cutoff lower (fun d => (μ d : ℂ)) (fun b => (Λ b : ℂ)) m := by
    unfold upperBandWeight
    push_cast
    rfl
  simp only [castWeight]
  exact upper_band_progressions n _ _ _ capBound
    (fun _ _ => cube_root_cofactor_of_high_divisor nPositive)
    (fun d => (μ d : ℂ)) (fun b => (Λ b : ℂ)) phase cancellation


end DyadicMixedB4Arithmetic

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters

namespace DyadicMixedB4ArcDecomposition

noncomputable section

/-- Adapted from the major-arc measurability proof in goldbach-proofs PR #2468,
revision 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem wide_measurable (n B H : ℕ) : MeasurableSet (wide n B H) := by
  unfold wide
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases condition : 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q
  · obtain ⟨qPositive, qBound, aBound, coprime⟩ := condition
    simp only [qPositive, qBound, aBound, true_and]
    have equality : {x : ℝ | a.Coprime q ∧ |x - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} =
        {x : ℝ | |x - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} := by
      ext x
      exact ⟨And.right, And.intro coprime⟩
    rw [equality]
    exact measurableSet_le (f := fun t : ℝ => |t - (a : ℝ) / q|)
      (g := fun _ : ℝ => (H : ℝ) / ((q : ℝ) * n)) (by fun_prop) measurable_const
  · have empty : {t : ℝ | 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} = ∅ := by
      ext t
      simp
      tauto
    rw [empty]
    exact MeasurableSet.empty

theorem indicator_intervalIntegrable {f : ℝ → ℂ} {s : Set ℝ} (continuous : Continuous f)
    (measurable : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (continuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator measurable

def plainPolynomial (n : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ range (n + 1), a m * phase ((m : ℝ) * t)

def shiftedPolynomial (n : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ range (n + 1), a m * phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)

theorem shiftedPolynomial_eq (n : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    shiftedPolynomial n a t = plainPolynomial n a t * phase (-(n : ℝ) * t) := by
  rw [shiftedPolynomial, plainPolynomial, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_assoc, ← phase_add, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  congr 2
  ring

theorem shiftedPolynomial_continuous (n : ℕ) (a : ℕ → ℂ) : Continuous (shiftedPolynomial n a) := by
  unfold shiftedPolynomial phase
  fun_prop

theorem norm_shiftedPolynomial_eq (n : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖shiftedPolynomial n a t‖ = ‖plainPolynomial n a t‖ := by
  rw [shiftedPolynomial_eq, norm_mul, norm_phase', mul_one]

theorem shiftedPolynomial_parseval (n : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖shiftedPolynomial n a t‖ ^ 2) = ∑ m ∈ range (n + 1), ‖a m‖ ^ 2 := by
  have exactMode (m : ℕ) (t : ℝ) : phase ((m : ℝ) * t) = DyadicMixedB4Fourier.mode (m : ℤ) t := by
    rw [BombieriVinogradov.LargeSieve.mode_nat_additivePhase]
    simp only [phase, BombieriVinogradov.LargeSieve.additivePhase, circleMap_zero, Complex.ofReal_one, one_mul]
  simp only [norm_shiftedPolynomial_eq, plainPolynomial, exactMode]
  exact DyadicMixedB4Fourier.parseval_real (n + 1) a

theorem split_shifted_wave (n M B H R g l r : ℕ) (a : ℕ → ℂ)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator (fun x => shiftedPolynomial n a x * wave g l r x) t) =
      (∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator
        (fun x => shiftedPolynomial n a x * offWave (radius M) g l r x) t) +
      ∑ q ∈ g.divisors.filter (fun q => R < q), ∑ m ∈ range (n + 1), a m * ramanujan q ((m : ℤ) - n) *
        ∫ t in window n M B H q, phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave g l r t := by
  classical
  let near := gridNear (radius M) g
  let outside := (wide n B H)ᶜ
  let f (t : ℝ) := shiftedPolynomial n a t * wave g l r t
  let off (t : ℝ) := shiftedPolynomial n a t * offWave (radius M) g l r t
  let v (m : ℕ) (t : ℝ) := phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave g l r t
  have waveContinuous : Continuous (wave g l r) := by unfold wave phase; fun_prop
  have fContinuous : Continuous f := (shiftedPolynomial_continuous n a).mul waveContinuous
  have nearMeasurable : MeasurableSet near := gridNear_measurable (radius M) g
  have outsideMeasurable : MeasurableSet outside := (wide_measurable n B H).compl
  have offEqual : outside.indicator off = (outside ∩ nearᶜ).indicator f := by
    funext t
    by_cases nearMem : t ∈ near <;> by_cases outsideMem : t ∈ outside <;>
      simp_all only [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, Set.mem_compl_iff,
        not_true_eq_false, not_false_eq_true, and_true, and_false, false_and, true_and, mul_zero, off, near, offWave, f]
  have offInt : IntervalIntegrable (outside.indicator off) volume 0 1 := by
    rw [offEqual]
    exact indicator_intervalIntegrable fContinuous (outsideMeasurable.inter nearMeasurable.compl)
  have nearInt : IntervalIntegrable ((near ∩ outside).indicator f) volume 0 1 :=
    indicator_intervalIntegrable fContinuous (nearMeasurable.inter outsideMeasurable)
  have split (t : ℝ) : outside.indicator f t = outside.indicator off t + (near ∩ outside).indicator f t := by
    rw [offEqual]
    by_cases nearMem : t ∈ near <;> by_cases outsideMem : t ∈ outside <;> simp [nearMem, outsideMem]
  have expandNear (t : ℝ) : (near ∩ outside).indicator f t =
      ∑ m ∈ range (n + 1), a m * (near ∩ outside).indicator (v m) t := by
    by_cases membership : t ∈ near ∩ outside
    · simp only [Set.indicator_of_mem membership, f, shiftedPolynomial, sum_mul, v, mul_assoc]
    · simp [membership]
  have termInt (m : ℕ) : IntervalIntegrable (fun t => a m * (near ∩ outside).indicator (v m) t) volume 0 1 := by
    have continuousMode : Continuous (fun t : ℝ => phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) := by
      unfold phase
      fun_prop
    exact (indicator_intervalIntegrable (continuousMode.mul waveContinuous)
      (nearMeasurable.inter outsideMeasurable)).const_mul (a m)
  change (∫ t in (0 : ℝ)..1, outside.indicator f t) = (∫ t in (0 : ℝ)..1, outside.indicator off t) + _
  calc
    _ = ∫ t in (0 : ℝ)..1, outside.indicator off t + (near ∩ outside).indicator f t :=
      intervalIntegral.integral_congr fun t _ => split t
    _ = (∫ t in (0 : ℝ)..1, outside.indicator off t) + ∫ t in (0 : ℝ)..1, (near ∩ outside).indicator f t :=
      intervalIntegral.integral_add offInt nearInt
    _ = _ := by
      congr 1
      simp_rw [expandNear]
      rw [intervalIntegral.integral_finsetSum (fun m _ => termInt m)]
      simp_rw [intervalIntegral.integral_const_mul]
      have identify (m : ℕ) : (∫ t in (0 : ℝ)..1, (near ∩ outside).indicator (v m) t) =
          ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q ((m : ℤ) - n) *
            ∫ t in window n M B H q, v m t :=
        centered_deep_wave_integral n M B H R g l r ((m : ℤ) - n)
          nPositive gPositive gBound Bbound width Rpositive Rbound cover
      simp_rw [identify, mul_sum]
      rw [sum_comm]
      simp only [v, mul_assoc]


end
end DyadicMixedB4ArcDecomposition

end

section

open Finset ArithmeticFunction DyadicMixedB4Arithmetic DyadicMixedB4Scale
open DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric DyadicMixedB4MoebiusGauss
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4HighAtoms

noncomputable section

def highCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊

def highBandCoefficient (n m : ℕ) : ℝ := upperBandWeight (cutoffU n) (highCut n)
  (fun d => (μ d : ℝ)) (fun b => Λ b) m

def highAtoms (n : ℕ) : Finset (ℕ × ℕ) := Icc 1 (cutoffU n) ×ˢ Ioc (cutoffU n) (cutoffB n)

def atomStep (atom : ℕ × ℕ) : ℕ := atom.1 * atom.2
def atomLower (n : ℕ) (atom : ℕ × ℕ) : ℕ := highCut n / atom.1
def atomUpper (n : ℕ) (atom : ℕ × ℕ) : ℕ := n / atomStep atom
def atomWeight (atom : ℕ × ℕ) : ℂ := (-(μ atom.1 : ℂ)) * (Λ atom.2 : ℂ)

theorem atomStep_range {n : ℕ} {atom : ℕ × ℕ} (membership : atom ∈ highAtoms n) :
    0 < atomStep atom ∧ atomStep atom ≤ maximumStep n := by
  obtain ⟨d, b⟩ := mem_product.mp membership
  obtain ⟨dPositive, dBound⟩ := mem_Icc.mp d
  obtain ⟨bLower, bBound⟩ := mem_Ioc.mp b
  exact ⟨Nat.mul_pos dPositive ((Nat.zero_le _).trans_lt bLower), Nat.mul_le_mul dBound bBound⟩

theorem highBandPolynomial_eq_atoms (n : ℕ) (nPositive : 0 < n) (t : ℝ) :
    plainPolynomial n (fun m => (highBandCoefficient n m : ℂ)) t =
      ∑ i ∈ highAtoms n, atomWeight i * wave (atomStep i) (atomLower n i) (atomUpper n i) t := by
  unfold plainPolynomial highAtoms
  have castWeight (m : ℕ) : (highBandCoefficient n m : ℂ) =
      upperBandWeight (R := ℂ) (cutoffU n) (highCut n)
        (fun d => ((μ d : ℝ) : ℂ)) (fun b => (Λ b : ℂ)) m := by
    unfold highBandCoefficient upperBandWeight
    push_cast
    rfl
  simp_rw [castWeight]
  have expansion := vaughan_high_factor_expansion n nPositive (fun j => phase ((j : ℝ) * t))
  dsimp only at expansion
  change (∑ m ∈ range (n + 1), upperBandWeight (R := ℂ) (cutoffU n) (highCut n)
      (fun d => ((μ d : ℝ) : ℂ)) (fun b => (Λ b : ℂ)) m * phase ((m : ℝ) * t)) =
    (∑ b ∈ Ioc (cutoffU n) (cutoffB n), ∑ d ∈ Icc 1 (min (cutoffU n) (n / b)),
      (-(μ d : ℂ)) * (Λ b : ℂ) * ∑ k ∈ Ioc (highCut n / d) (n / (d * b)),
        phase (((d * b * k : ℕ) : ℝ) * t)) at expansion
  rw [expansion]
  rw [Finset.sum_product, Finset.sum_comm]
  refine sum_congr rfl fun b bMember => ?_
  have bInterval : b ∈ Ioc (cutoffU n) (cutoffB n) := bMember
  have bPositive : 0 < b := (Nat.zero_le _).trans_lt (mem_Ioc.mp bInterval).1
  have full : cutoffU n ≤ n / b := by
    apply (Nat.le_div_iff_mul_le bPositive).mpr
    calc
      cutoffU n * b ≤ maximumStep n := Nat.mul_le_mul_left _ (mem_Ioc.mp bInterval).2
      _ ≤ n := (cutoffs_ordered n nPositive).2.2.2
  have minExact : min (cutoffU n) (n / b) = cutoffU n := min_eq_left full
  rw [minExact]
  rfl

theorem norm_atomWeight_le_log {n : ℕ} {i : ℕ × ℕ} (nPositive : 0 < n) (membership : i ∈ highAtoms n) :
    ‖atomWeight i‖ ≤ Real.log n := by
  obtain ⟨_, bMember⟩ := mem_product.mp membership
  obtain ⟨bLower, bUpper⟩ := mem_Ioc.mp bMember
  have bPositive : 0 < i.2 := (Nat.zero_le _).trans_lt bLower
  have nBound := (cutoffs_ordered n nPositive).2.2
  have bBound := bUpper.trans (nBound.1.trans nBound.2)
  have logBound : Λ i.2 ≤ Real.log n := vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast bPositive) (by exact_mod_cast bBound))
  unfold atomWeight
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left vonMangoldt_nonneg (norm_moebiusComplex_le_one i.1)).trans logBound

theorem sum_atomWeight_fibre_le {n u : ℕ} (nPositive : 0 < n) (uPositive : 0 < u) :
    (∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖) ≤
      (u.divisors.card : ℝ) * Real.log n := by
  classical
  let fibre := (highAtoms n).filter (fun i => atomStep i = u)
  have mapsTo : fibre.image Prod.fst ⊆ u.divisors := by
    intro d member
    obtain ⟨i, iMember, rfl⟩ := mem_image.mp member
    have same := (mem_filter.mp iMember).2
    exact Nat.mem_divisors.mpr ⟨⟨i.2, same.symm⟩, uPositive.ne'⟩
  have injOn : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) (fibre : Set (ℕ × ℕ)) := by
    intro i iMember j jMember equal
    have hi := (mem_filter.mp iMember).2
    have hj := (mem_filter.mp jMember).2
    have hiPos : 0 < i.1 := (mem_Icc.mp (mem_product.mp (mem_filter.mp iMember).1).1).1
    have productEqual : i.1 * i.2 = i.1 * j.2 := hi.trans (by simpa only [atomStep, equal] using hj.symm)
    exact Prod.ext equal (Nat.eq_of_mul_eq_mul_left hiPos productEqual)
  have fibreBound : fibre.card ≤ u.divisors.card := (card_image_of_injOn injOn).symm.trans_le (card_le_card mapsTo)
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast nPositive)
  change (∑ i ∈ fibre, ‖atomWeight i‖) ≤ _
  calc
    _ ≤ ∑ _ ∈ fibre, Real.log n := sum_le_sum fun i membership => norm_atomWeight_le_log nPositive (mem_filter.mp membership).1
    _ = (fibre.card : ℝ) * Real.log n := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast fibreBound) logNonnegative


end
end DyadicMixedB4HighAtoms

end

section

open Finset ArithmeticFunction DyadicMixedB4Arithmetic
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4LowBand

noncomputable section

def lowMoebiusWeight (U a : ℕ) : ℝ := ∑ d ∈ a.divisors.filter (fun d => U < d), (μ d : ℝ)

def lowBandCoefficient (U B m : ℕ) : ℝ :=
  ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), lowMoebiusWeight U a * Λ (m / a)

theorem abs_lowMoebiusWeight_le (U a : ℕ) : |lowMoebiusWeight U a| ≤ (a.divisors.card : ℝ) := by
  have bound : ‖lowMoebiusWeight U a‖ ≤ (a.divisors.card : ℝ) := by
    unfold lowMoebiusWeight
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ d ∈ a.divisors.filter (fun d => U < d), (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        rw [Real.norm_eq_abs]
        exact_mod_cast (abs_moebius_le_one (n := d))
      _ ≤ ∑ d ∈ a.divisors, (1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => zero_le_one)
      _ = _ := by simp
  simpa only [Real.norm_eq_abs] using bound

theorem abs_lowBandCoefficient_le (U B m n : ℕ) (mBound : m ≤ n) (nPositive : 0 < n) :
    |lowBandCoefficient U B m| ≤ (m.divisors.card : ℝ) ^ 2 * Real.log n := by
  have nRealLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg nRealLower
  have logLambda (a : ℕ) (member : a ∈ m.divisors) : Λ (m / a) ≤ Real.log n := by
    have aDivides := Nat.dvd_of_mem_divisors member
    have mPositive : 0 < m := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors member)
    have aPositive := Nat.pos_of_mem_divisors member
    have quotientPositive := Nat.div_pos (Nat.le_of_dvd mPositive aDivides) aPositive
    refine vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast quotientPositive) ?_)
    exact_mod_cast (Nat.div_le_self m a).trans mBound
  have tau (a : ℕ) (member : a ∈ m.divisors) : (a.divisors.card : ℝ) ≤ m.divisors.card := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro d dMember
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors dMember).trans (Nat.dvd_of_mem_divisors member),
      Nat.ne_zero_of_mem_divisors member⟩
  rw [← Real.norm_eq_abs, lowBandCoefficient]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), (m.divisors.card : ℝ) * Real.log n := by
      refine sum_le_sum fun a membership => ?_
      have divisor := (mem_filter.mp membership).1
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul ((abs_lowMoebiusWeight_le U a).trans (tau a divisor)) (logLambda a divisor)
        vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ ≤ ∑ _ ∈ m.divisors, (m.divisors.card : ℝ) * Real.log n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) logNonnegative)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem low_band_hyperbola (n U B : ℕ) (Bbound : B ≤ n) (f : ℕ → ℂ) :
    (∑ m ∈ range (n + 1), (lowBandCoefficient U B m : ℂ) * f m) =
      ∑ a ∈ Ioc U B, (lowMoebiusWeight U a : ℂ) *
        ∑ b ∈ Ioc U (n / a), (Λ b : ℂ) * f (a * b) := by
  let term (a b : ℕ) : ℂ := (lowMoebiusWeight U a : ℂ) * ((Λ b : ℂ) * f (a * b))
  let supported (a b : ℕ) : ℂ := if U < a ∧ a ≤ B ∧ U < b then term a b else 0
  have partition : range (n + 1) = insert 0 (Icc 1 n) := by ext m; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [partition, sum_insert (by simp)]
  simp only [lowBandCoefficient, Nat.divisors_zero, filter_empty, sum_empty, Complex.ofReal_zero, zero_mul, zero_add]
  calc
    _ = ∑ m ∈ Icc 1 n, ∑ a ∈ m.divisors, supported a (m / a) := by
      refine sum_congr rfl fun m _ => ?_
      rw [Complex.ofReal_sum, sum_mul, sum_filter]
      refine sum_congr rfl fun a aMember => ?_
      by_cases cond : U < a ∧ a ≤ B ∧ U < m / a
      · simp only [supported, term, if_pos cond, Complex.ofReal_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors aMember)]
        ring
      · simp [supported, cond]
    _ = ∑ a ∈ Icc 1 n, ∑ b ∈ Icc 1 (n / a), supported a b := finite_divisor_hyperbola n supported
    _ = ∑ a ∈ (Icc 1 n).filter (fun a => U < a ∧ a ≤ B),
        ∑ b ∈ (Icc 1 (n / a)).filter (fun b => U < b), term a b := by
      rw [sum_filter]
      refine sum_congr rfl fun a _ => ?_
      by_cases cond : U < a ∧ a ≤ B
      · rw [if_pos cond, sum_filter]
        exact sum_congr rfl fun b _ => by simp [supported, cond.1, cond.2]
      · rw [if_neg cond]
        exact sum_eq_zero fun b _ => if_neg (fun h => cond ⟨h.1, h.2.1⟩)
    _ = _ := by
      have intervalA : (Icc 1 n).filter (fun a => U < a ∧ a ≤ B) = Ioc U B := by
        ext a
        simp only [mem_filter, mem_Icc, mem_Ioc]
        omega
      have intervalB (a : ℕ) : (Icc 1 (n / a)).filter (fun b => U < b) = Ioc U (n / a) := by
        ext b
        simp only [mem_filter, mem_Icc, mem_Ioc]
        omega
      simp_rw [intervalA, intervalB, term, ← mul_sum]


end
end DyadicMixedB4LowBand

end

section

open Finset MeasureTheory DyadicMixedB4Geometric

namespace DyadicMixedB4OffWaveMoment

noncomputable section

theorem wave_continuous (g l r : ℕ) : Continuous (wave g l r) := by unfold wave phase; fun_prop

theorem offWave_measurable (b : ℝ) (g l r : ℕ) : Measurable (offWave b g l r) :=
  (wave_continuous g l r).measurable.indicator (gridNear_measurable b g).compl

theorem norm_offWave_le (b : ℝ) (g l r : ℕ) (t : ℝ) : ‖offWave b g l r t‖ ≤ r := by
  unfold offWave
  by_cases outside : t ∈ (gridNear b g)ᶜ
  · rw [Set.indicator_of_mem outside]
    exact wave_cap g l r t
  · rw [Set.indicator_of_notMem outside, norm_zero]
    exact Nat.cast_nonneg _

theorem intervalIntegrable_offWave_norm_sq {ι : Type*} (items : Finset ι) (b : ℝ)
    (g l r : ι → ℕ) (c : ι → ℂ) :
    IntervalIntegrable (fun t => ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have measurable : Measurable (fun t => ∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (offWave_measurable b (g i) (l i) (r i)))
  apply Integrable.of_bound (measurable.norm.pow_const 2).aestronglyMeasurable
    ((∑ i ∈ items, ‖c i‖ * (r i : ℝ)) ^ 2)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  refine (norm_sum_le _ _).trans (sum_le_sum (fun i _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_offWave_le b (g i) (l i) (r i) t) (norm_nonneg _)

theorem offWave_mass_le_pairwise {ι : Type*} (items : Finset ι) (n : ℕ) (b : ℝ)
    (bPositive : 0 < b) (g l r : ι → ℕ) (c : ι → ℂ)
    (gRange : ∀ i ∈ items, 0 < g i ∧ g i ≤ n) (rRange : ∀ i ∈ items, r i ≤ n / g i) :
    (∫ t in (0 : ℝ)..1, ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2) ≤
      ∑ i ∈ items, ∑ j ∈ items, (‖c i‖ * ‖c j‖) * (128 * ((1 + Real.log ((n : ℝ) + 2)) ^ 2 +
        ((g i).gcd (g j) : ℝ) / ((g i : ℝ) * (g j : ℝ) * b))) := by
  let H (i j : ι) : ℝ → ℝ := (gridNear b ((g i).gcd (g j)))ᶜ.indicator
    (fun t => ‖wave (g i) (l i) (r i) t * wave (g j) (l j) (r j) t‖)
  let P (i j : ι) (t : ℝ) : ℝ := (‖c i‖ * ‖c j‖) * H i j t
  let f (t : ℝ) : ℝ := ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2
  have fIntegrable : IntervalIntegrable f volume 0 1 := intervalIntegrable_offWave_norm_sq items b g l r c
  have HIntegrable (i j : ι) : IntervalIntegrable (H i j) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have continuous : Continuous (fun t => ‖wave (g i) (l i) (r i) t * wave (g j) (l j) (r j) t‖) :=
      ((wave_continuous _ _ _).mul (wave_continuous _ _ _)).norm
    exact (continuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (gridNear_measurable b ((g i).gcd (g j))).compl
  have pairIntegrable (i j : ι) : IntervalIntegrable (P i j) volume 0 1 :=
    (HIntegrable i j).const_mul (‖c i‖ * ‖c j‖)
  have rowIntegrable (i : ι) : IntervalIntegrable (fun t => ∑ j ∈ items, P i j t) volume 0 1 := by
    have integrated := IntervalIntegrable.sum items (fun j _ => pairIntegrable i j)
    convert integrated using 1
    funext t
    simp only [Finset.sum_apply]
  have sumIntegrable : IntervalIntegrable (fun t => ∑ i ∈ items, ∑ j ∈ items, P i j t) volume 0 1 := by
    have integrated := IntervalIntegrable.sum items (fun i _ => rowIntegrable i)
    convert integrated using 1
    funext t
    simp only [Finset.sum_apply]
  have pointwise (t : ℝ) : f t ≤ ∑ i ∈ items, ∑ j ∈ items, P i j t := by
    calc
      _ ≤ (∑ i ∈ items, ‖c i * offWave b (g i) (l i) (r i) t‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = ∑ i ∈ items, ∑ j ∈ items, (‖c i‖ * ‖c j‖) *
          ‖offWave b (g i) (l i) (r i) t * offWave b (g j) (l j) (r j) t‖ := by
        rw [pow_two, sum_mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        simp only [norm_mul]
        ring
      _ ≤ _ := by
        refine sum_le_sum fun i iMember => sum_le_sum fun j jMember => ?_
        exact mul_le_mul_of_nonneg_left
          (norm_offWave_mul_le b (gRange i iMember).1 (gRange j jMember).1 _ _ _ _ t)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  change (∫ t in (0 : ℝ)..1, f t) ≤ _
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ∑ i ∈ items, ∑ j ∈ items, P i j t :=
      intervalIntegral.integral_mono_on zero_le_one fIntegrable sumIntegrable (fun t _ => pointwise t)
    _ = ∑ i ∈ items, ∑ j ∈ items, (‖c i‖ * ‖c j‖) * ∫ t in (0 : ℝ)..1, H i j t := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => rowIntegrable i)]
      refine sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun j _ => pairIntegrable i j)]
      exact sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      refine sum_le_sum fun i iMember => sum_le_sum fun j jMember => ?_
      exact mul_le_mul_of_nonneg_left (awayBound n (g i) (g j) (l i) (r i) (l j) (r j) b bPositive
        (gRange i iMember).1 (gRange j jMember).1 (gRange i iMember).2 (gRange j jMember).2
        (rRange i iMember) (rRange j jMember)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem sum_step_pairs {ι : Type*} (items : Finset ι) (steps : Finset ℕ)
    (g : ι → ℕ) (weight : ι → ℝ) (F : ℕ → ℕ → ℝ) (mapsInto : ∀ i ∈ items, g i ∈ steps) :
    (∑ i ∈ items, ∑ j ∈ items, weight i * weight j * F (g i) (g j)) =
      ∑ u ∈ steps, ∑ v ∈ steps, (∑ i ∈ items.filter (fun i => g i = u), weight i) *
        (∑ j ∈ items.filter (fun j => g j = v), weight j) * F u v := by
  calc
    _ = ∑ u ∈ steps, ∑ i ∈ items.filter (fun i => g i = u), ∑ j ∈ items, weight i * weight j * F (g i) (g j) :=
      (sum_fiberwise_of_maps_to mapsInto _).symm
    _ = ∑ u ∈ steps, ∑ v ∈ steps, ∑ i ∈ items.filter (fun i => g i = u),
        ∑ j ∈ items.filter (fun j => g j = v), weight i * weight j * F (g i) (g j) := by
      refine sum_congr rfl fun u _ => ?_
      have inner (i : ι) : (∑ j ∈ items, weight i * weight j * F (g i) (g j)) =
          ∑ v ∈ steps, ∑ j ∈ items.filter (fun j => g j = v), weight i * weight j * F (g i) (g j) :=
        (sum_fiberwise_of_maps_to mapsInto _).symm
      simp_rw [inner]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
      rw [sum_mul_sum, sum_mul]
      refine sum_congr rfl fun i iMember => ?_
      rw [sum_mul]
      refine sum_congr rfl fun j jMember => ?_
      rw [(mem_filter.mp iMember).2, (mem_filter.mp jMember).2]

theorem offWave_mass_le_weighted {ι : Type*} (items : Finset ι) (n M : ℕ) (b W : ℝ)
    (MPositive : 0 < M) (MBound : M ≤ n) (bPositive : 0 < b) (WNonnegative : 0 ≤ W)
    (g l r : ι → ℕ) (c : ι → ℂ) (gRange : ∀ i ∈ items, 0 < g i ∧ g i ≤ M)
    (rRange : ∀ i ∈ items, r i ≤ n / g i)
    (weightBound : ∀ u ∈ Icc 1 M, (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) ≤ W) :
    (∫ t in (0 : ℝ)..1, ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2) ≤
      128 * W ^ 2 * ((M : ℝ) ^ 2 * (1 + Real.log ((n : ℝ) + 2)) ^ 2 +
        b⁻¹ * (1 + Real.log (M : ℝ)) ^ 3) := by
  let J := (1 + Real.log ((n : ℝ) + 2)) ^ 2
  let F (u v : ℕ) : ℝ := 128 * (J + (u.gcd v : ℝ) / ((u : ℝ) * (v : ℝ) * b))
  have mapsInto (i : ι) (member : i ∈ items) : g i ∈ Icc 1 M := mem_Icc.mpr (gRange i member)
  have first := offWave_mass_le_pairwise items n b bPositive g l r c
    (fun i member => ⟨(gRange i member).1, (gRange i member).2.trans MBound⟩) rRange
  change _ ≤ ∑ i ∈ items, ∑ j ∈ items, ‖c i‖ * ‖c j‖ * F (g i) (g j) at first
  rw [sum_step_pairs items (Icc 1 M) g (fun i => ‖c i‖) F mapsInto] at first
  have positiveF (u v : ℕ) : 0 ≤ F u v := by unfold F J; positivity
  have pairBound : (∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 M,
      (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) *
        (∑ j ∈ items.filter (fun j => g j = v), ‖c j‖) * F u v) ≤
      ∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 M, W ^ 2 * F u v := by
    refine sum_le_sum fun u uMember => sum_le_sum fun v vMember => ?_
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (weightBound u uMember) (weightBound v vMember)
        (sum_nonneg (fun _ _ => norm_nonneg _)) WNonnegative) (positiveF u v)
  refine (first.trans pairBound).trans ?_
  have expand (u v : ℕ) : W ^ 2 * F u v =
      128 * W ^ 2 * (J + b⁻¹ * ((u.gcd v : ℝ) / ((u : ℝ) * (v : ℝ)))) := by
    unfold F
    ring
  simp_rw [expand, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have cardinality : (Icc 1 M).card = M := by simp
  simp only [sum_add_distrib, sum_const, cardinality, nsmul_eq_mul, ← mul_sum]
  have gcdBound := DyadicMixedB4GcdHarmonic.gcd_reciprocal_sum_le M MPositive
  have constantTerm : (M : ℝ) * ((M : ℝ) * J) = (M : ℝ) ^ 2 * J := by ring
  rw [constantTerm]
  exact add_le_add_right (mul_le_mul_of_nonneg_left gcdBound (by positivity)) _


end
end DyadicMixedB4OffWaveMoment

end

section

open MeasureTheory

namespace DyadicMixedB4YoungIntegral

theorem scaled_young {s x y : ℝ} (sPositive : 0 < s) :
    x * y ≤ (1 / 2) * (s * x ^ 2 + s⁻¹ * y ^ 2) := by
  have multiplied : (2 * x * y - s * x ^ 2) * s ≤ y ^ 2 := by
    nlinarith only [sq_nonneg (s * x - y)]
  have divided := (le_div_iff₀ sPositive).mpr multiplied
  rw [inv_mul_eq_div]
  linarith only [divided]

theorem norm_indicator_product_le {f g : ℝ → ℂ} {s : Set ℝ} {scale : ℝ}
    (scalePositive : 0 < scale) (sMeasurable : MeasurableSet s) (fMeasurable : Measurable f)
    (gMeasurable : Measurable g)
    (fSquareIntegrable : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1)
    (gSquareIntegrable : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 1) :
    ‖∫ t in (0 : ℝ)..1, s.indicator (fun x => f x * g x) t‖ ≤
      (1 / 2) * (scale * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) +
        scale⁻¹ * (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2)) := by
  let product := s.indicator (fun t => f t * g t)
  let bound (t : ℝ) := (1 / 2) * (scale * ‖f t‖ ^ 2 + scale⁻¹ * ‖g t‖ ^ 2)
  have productMeasurable : Measurable product := (fMeasurable.mul gMeasurable).indicator sMeasurable
  have firstIntegrable : IntervalIntegrable (fun t => scale * ‖f t‖ ^ 2) volume 0 1 :=
    fSquareIntegrable.const_mul scale
  have secondIntegrable : IntervalIntegrable (fun t => scale⁻¹ * ‖g t‖ ^ 2) volume 0 1 :=
    gSquareIntegrable.const_mul scale⁻¹
  have sumIntegrable : IntervalIntegrable (fun t => scale * ‖f t‖ ^ 2 + scale⁻¹ * ‖g t‖ ^ 2) volume 0 1 :=
    firstIntegrable.add secondIntegrable
  have boundIntegrable : IntervalIntegrable bound volume 0 1 := sumIntegrable.const_mul (1 / 2)
  have pointwise (t : ℝ) : ‖product t‖ ≤ bound t := by
    unfold product bound
    by_cases member : t ∈ s
    · rw [Set.indicator_of_mem member, norm_mul]
      exact scaled_young scalePositive
    · rw [Set.indicator_of_notMem member, norm_zero]
      positivity
  have productIntegrable : IntervalIntegrable product volume 0 1 := boundIntegrable.mono_fun'
    productMeasurable.aestronglyMeasurable (Filter.Eventually.of_forall pointwise)
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖product t‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, bound t := intervalIntegral.integral_mono_on zero_le_one productIntegrable.norm
      boundIntegrable (fun t _ => pointwise t)
    _ = _ := by
      unfold bound
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add firstIntegrable secondIntegrable,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]


end DyadicMixedB4YoungIntegral

end

section

open Finset MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4ArcDecomposition

namespace DyadicMixedB4PairIntegral

noncomputable section

def lowCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

def lowCoefficients (n m : ℕ) : ℂ := (lowBandCoefficient (cutoffU n) (lowCut n) m : ℂ)

def deepPairIntegral (n : ℕ) : ℂ := ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
  (fun x => plainPolynomial n (lowCoefficients n) x *
    plainPolynomial n (fun m => (highBandCoefficient n m : ℂ)) x * phase (-(n : ℝ) * x)) t

def outsidePolynomial (n : ℕ) (t : ℝ) : ℂ := ∑ i ∈ highAtoms n,
  atomWeight i * offWave (radius (maximumStep n)) (atomStep i) (atomLower n i) (atomUpper n i) t

def outsidePairIntegral (n : ℕ) : ℂ := ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
  (fun x => shiftedPolynomial n (lowCoefficients n) x * outsidePolynomial n x) t

def exactNearAtom (n : ℕ) (i : ℕ × ℕ) (q : ℕ) : ℂ :=
  ∑ m ∈ range (n + 1), lowCoefficients n m * ramanujan q ((m : ℤ) - n) *
    ∫ t in window n (maximumStep n) (cutoffB n) (cutoffH n) q,
      phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave (atomStep i) (atomLower n i) (atomUpper n i) t

def exactNearPair (n : ℕ) : ℂ := ∑ i ∈ highAtoms n, atomWeight i *
  ∑ q ∈ (atomStep i).divisors.filter (fun q => cutoffR n < q), exactNearAtom n i q

theorem deepPairIntegral_split (n : ℕ) (nPositive : 0 < n) (width : 4 * cutoffH n * maximumStep n ≤ n) :
    deepPairIntegral n = outsidePairIntegral n + exactNearPair n := by
  classical
  let outside := (wide n (cutoffB n) (cutoffH n))ᶜ
  let F := shiftedPolynomial n (lowCoefficients n)
  let W (i : ℕ × ℕ) := wave (atomStep i) (atomLower n i) (atomUpper n i)
  let O (i : ℕ × ℕ) := offWave (radius (maximumStep n)) (atomStep i) (atomLower n i) (atomUpper n i)
  have FContinuous : Continuous F := shiftedPolynomial_continuous n _
  have WContinuous (i : ℕ × ℕ) : Continuous (W i) := by unfold W wave phase; fun_prop
  have sMeasurable : MeasurableSet outside := (wide_measurable n (cutoffB n) (cutoffH n)).compl
  have usualIntegral (i : ℕ × ℕ) : IntervalIntegrable (outside.indicator (fun t => F t * W i t)) volume 0 1 :=
    indicator_intervalIntegrable (FContinuous.mul (WContinuous i)) sMeasurable
  have outsideIntegral (i : ℕ × ℕ) : IntervalIntegrable (outside.indicator (fun t => F t * O i t)) volume 0 1 := by
    let grid := gridNear (radius (maximumStep n)) (atomStep i)
    have equivalent : outside.indicator (fun t => F t * O i t) =
        (outside ∩ gridᶜ).indicator (fun t => F t * W i t) := by
      funext t
      by_cases onGrid : t ∈ grid <;> by_cases onOutside : t ∈ outside <;>
        simp_all only [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, Set.mem_compl_iff,
          not_true_eq_false, not_false_eq_true, and_true, and_false, mul_zero, O, W, grid, offWave]
    rw [equivalent]
    exact indicator_intervalIntegrable (FContinuous.mul (WContinuous i))
      (sMeasurable.inter (gridNear_measurable (radius (maximumStep n)) (atomStep i)).compl)
  have originalPointwise (t : ℝ) : outside.indicator (fun x => plainPolynomial n (lowCoefficients n) x *
        plainPolynomial n (fun m => (highBandCoefficient n m : ℂ)) x * phase (-(n : ℝ) * x)) t =
      ∑ i ∈ highAtoms n, atomWeight i * outside.indicator (fun x => F x * W i x) t := by
    by_cases membership : t ∈ outside
    · simp only [Set.indicator_of_mem membership, highBandPolynomial_eq_atoms n nPositive, F, shiftedPolynomial_eq,
        mul_sum, sum_mul]
      refine sum_congr rfl fun i _ => ?_
      unfold W
      ring
    · simp [membership]
  have outsidePointwise (t : ℝ) : outside.indicator (fun x => F x * outsidePolynomial n x) t =
      ∑ i ∈ highAtoms n, atomWeight i * outside.indicator (fun x => F x * O i x) t := by
    by_cases membership : t ∈ outside
    · simp only [Set.indicator_of_mem membership, outsidePolynomial, mul_sum, O]
      exact sum_congr rfl fun _ _ => by ring
    · simp [membership]
  have cutoffs := cutoffs_ordered n nPositive
  have each (i : ℕ × ℕ) (iMember : i ∈ highAtoms n) :
      (∫ t in (0 : ℝ)..1, outside.indicator (fun x => F x * W i x) t) =
        (∫ t in (0 : ℝ)..1, outside.indicator (fun x => F x * O i x) t) +
          ∑ q ∈ (atomStep i).divisors.filter (fun q => cutoffR n < q), exactNearAtom n i q :=
    split_shifted_wave n (maximumStep n) (cutoffB n) (cutoffH n) (cutoffR n)
      (atomStep i) (atomLower n i) (atomUpper n i) (lowCoefficients n) nPositive
      (atomStep_range iMember).1 (atomStep_range iMember).2 cutoffs.2.2.1
      width cutoffs.1 cutoffs.2.1 (cutoffR_covered n nPositive)
  unfold deepPairIntegral outsidePairIntegral exactNearPair
  change (∫ t in (0 : ℝ)..1, outside.indicator (fun x => plainPolynomial n (lowCoefficients n) x *
      plainPolynomial n (fun m => (highBandCoefficient n m : ℂ)) x * phase (-(n : ℝ) * x)) t) =
    (∫ t in (0 : ℝ)..1, outside.indicator (fun x => F x * outsidePolynomial n x) t) + _
  simp_rw [originalPointwise, outsidePointwise]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (usualIntegral i).const_mul (atomWeight i)),
    intervalIntegral.integral_finsetSum (fun i _ => (outsideIntegral i).const_mul (atomWeight i))]
  simp_rw [intervalIntegral.integral_const_mul, ← sum_add_distrib, ← mul_add]
  exact sum_congr rfl (fun i iMember => congrArg (fun z : ℂ => atomWeight i * z) (each i iMember))

theorem norm_outsidePairIntegral_le (n : ℕ) (nPositive : 0 < n) {S A W : ℝ} (SPositive : 0 < S)
    (ANonnegative : 0 ≤ A) (WNonnegative : 0 ≤ W)
    (aBound : ∀ m ∈ range (n + 1), ‖lowCoefficients n m‖ ≤ A)
    (wBound : ∀ u ∈ Icc 1 (maximumStep n),
      (∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖) ≤ W) :
    ‖outsidePairIntegral n‖ ≤ (1 / 2) * (S * (((n : ℝ) + 1) * A ^ 2) +
      S⁻¹ * (128 * W ^ 2 * ((maximumStep n : ℝ) ^ 2 * (1 + Real.log ((n : ℝ) + 2)) ^ 2 +
        (radius (maximumStep n))⁻¹ * (1 + Real.log (maximumStep n : ℝ)) ^ 3))) := by
  let F := shiftedPolynomial n (lowCoefficients n)
  let G := outsidePolynomial n
  have cutoffs := cutoffs_ordered n nPositive
  have MPositive : 0 < maximumStep n := cutoffs.1.trans (cutoffs.2.1.trans cutoffs.2.2.1)
  have bPositive : 0 < radius (maximumStep n) := by unfold radius; positivity
  have FContinuous : Continuous F := shiftedPolynomial_continuous n _
  have GMeasurable : Measurable G :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (DyadicMixedB4OffWaveMoment.offWave_measurable _ _ _ _))
  have Fint : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume 0 1 := (FContinuous.norm.pow 2).intervalIntegrable 0 1
  have Gint : IntervalIntegrable (fun t => ‖G t‖ ^ 2) volume 0 1 :=
    DyadicMixedB4OffWaveMoment.intervalIntegrable_offWave_norm_sq (highAtoms n) _ atomStep (atomLower n) (atomUpper n) atomWeight
  have Fbound : (∫ t in (0 : ℝ)..1, ‖F t‖ ^ 2) ≤ ((n : ℝ) + 1) * A ^ 2 := by
    rw [shiftedPolynomial_parseval]
    calc
      _ ≤ ∑ _ ∈ range (n + 1), A ^ 2 := sum_le_sum fun m member => pow_le_pow_left₀ (norm_nonneg _) (aBound m member) 2
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_range, Nat.cast_add, Nat.cast_one]
  have Gbound := DyadicMixedB4OffWaveMoment.offWave_mass_le_weighted (highAtoms n) n (maximumStep n)
    (radius (maximumStep n)) W MPositive cutoffs.2.2.2 bPositive WNonnegative atomStep (atomLower n) (atomUpper n)
    atomWeight (fun _ member => atomStep_range member) (fun _ _ => le_rfl) wBound
  have productBound := DyadicMixedB4YoungIntegral.norm_indicator_product_le SPositive
    (wide_measurable n (cutoffB n) (cutoffH n)).compl FContinuous.measurable GMeasurable Fint Gint
  refine productBound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left Fbound SPositive.le)
      (mul_le_mul_of_nonneg_left Gbound (inv_nonneg.mpr SPositive.le))) (by norm_num)


end
end DyadicMixedB4PairIntegral

end

section

open Finset MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4ProgressionApprox DyadicMixedB4WindowKernel DyadicMixedB4KernelControl DyadicMixedB4Ramanujan

namespace DyadicMixedB4NearReplacement

noncomputable section

theorem norm_windowKernel_difference_le (n M B H q g l r : ℕ) (s : ℝ)
    (gPositive : 0 < g) (radiusBound : (g : ℝ) * radius M ≤ 1 / 2) :
    ‖(∫ t in window n M B H q, phase (s * t) * wave g l r t) -
      (windowKernel n M B H q g l r s : ℂ)‖ ≤ 2 * Real.pi * (2 * radius M) := by
  have phaseContinuous : Continuous (fun t => phase (s * t)) := by unfold phase; fun_prop
  have waveContinuous : Continuous (wave g l r) := by unfold wave phase; fun_prop
  have waveIntegrable : IntegrableOn (fun t => phase (s * t) * wave g l r t) (window n M B H q) :=
    ((phaseContinuous.mul waveContinuous).continuousOn.integrableOn_Icc).mono_set (window_subset_interval n M B H q)
  have averageIntegrable : IntegrableOn (fun t => phase (s * t) * progressionAverage g l r t) (window n M B H q) :=
    ((phaseContinuous.mul (progressionAverage_continuous g l r)).continuousOn.integrableOn_Icc).mono_set
      (window_subset_interval n M B H q)
  change ‖(∫ t in window n M B H q, phase (s * t) * wave g l r t) -
    Complex.ofReal (scalarKernel g l r (radius M) s -
      if q ≤ B then scalarKernel g l r (innerRadius n M H q) s else 0)‖ ≤ _
  rw [← integral_progression_window, ← integral_sub waveIntegrable averageIntegrable]
  simp only [← mul_sub]
  exact norm_window_replacement_le n M B H q g l r s gPositive radiusBound

theorem norm_sum_windowKernel_difference_le (n M B H q g l r : ℕ) [NeZero q] (a : ℕ → ℂ)
    (qLower : 1 < q) (gPositive : 0 < g) (radiusBound : (g : ℝ) * radius M ≤ 1 / 2)
    {A : ℝ} (aBound : ∀ m ∈ range (n + 1), ‖a m‖ ≤ A) (ANonnegative : 0 ≤ A) :
    ‖(∑ m ∈ range (n + 1), a m * ramanujan q ((m : ℤ) - n) *
        ∫ t in window n M B H q, phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave g l r t) -
      ∑ m ∈ range (n + 1), a m * ramanujan q ((m : ℤ) - n) *
        (windowKernel n M B H q g l r (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℂ)‖ ≤
      (A * (2 * Real.pi * (2 * radius M))) * ((q.divisors.card : ℝ) * ((n : ℝ) + q)) := by
  let C := 2 * Real.pi * (2 * radius M)
  rw [← sum_sub_distrib]
  simp only [← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ m ∈ range (n + 1), (A * C) * ‖ramanujan q ((m : ℤ) - n)‖ := by
      refine sum_le_sum fun m membership => ?_
      simp only [norm_mul]
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (aBound m membership)
          (norm_windowKernel_difference_le n M B H q g l r (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) gPositive radiusBound)
          (norm_nonneg _) ANonnegative) (norm_nonneg _)
    _ = (A * C) * ∑ m ∈ range (n + 1), ‖ramanujan q ((m : ℤ) - n)‖ := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_norm_shifted_ramanujan_le qLower n)
      (mul_nonneg ANonnegative (by dsimp [C]; exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (radius_nonnegative M))))


end
end DyadicMixedB4NearReplacement

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4KernelControl DyadicMixedB4NearReplacement

namespace DyadicMixedB4NearPair

noncomputable section

def smoothKernelFactor (n : ℕ) (i : ℕ × ℕ) (q m : ℕ) : ℂ :=
  ramanujan q ((m : ℤ) - n) *
    (windowKernel n (maximumStep n) (cutoffB n) (cutoffH n) q (atomStep i) (atomLower n i) (atomUpper n i)
      (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℂ)

def smoothedNearAtom (n : ℕ) (i : ℕ × ℕ) (q : ℕ) : ℂ :=
  ∑ m ∈ range (n + 1), lowCoefficients n m * smoothKernelFactor n i q m

def smoothedNearPair (n : ℕ) : ℂ := ∑ i ∈ highAtoms n, atomWeight i *
  ∑ q ∈ (atomStep i).divisors.filter (fun q => cutoffR n < q), smoothedNearAtom n i q

theorem smoothedNearAtom_hyperbola (n : ℕ) (i : ℕ × ℕ) (q : ℕ) (nPositive : 0 < n) :
    smoothedNearAtom n i q = ∑ a ∈ Ioc (cutoffU n) (lowCut n), (lowMoebiusWeight (cutoffU n) a : ℂ) *
      ∑ b ∈ Ioc (cutoffU n) (n / a), (Λ b : ℂ) * smoothKernelFactor n i q (a * b) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have Bbound : lowCut n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nLower (by norm_num))
  exact low_band_hyperbola n (cutoffU n) (lowCut n) Bbound (smoothKernelFactor n i q)

theorem sum_atomWeight_le (n : ℕ) {W : ℝ}
    (wBound : ∀ u ∈ Icc 1 (maximumStep n),
      (∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖) ≤ W) :
    (∑ i ∈ highAtoms n, ‖atomWeight i‖) ≤ (maximumStep n : ℝ) * W := by
  have mapsInto (i : ℕ × ℕ) (member : i ∈ highAtoms n) : atomStep i ∈ Icc 1 (maximumStep n) :=
    mem_Icc.mpr (atomStep_range member)
  calc
    _ = ∑ u ∈ Icc 1 (maximumStep n), ∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖ :=
      (sum_fiberwise_of_maps_to mapsInto _).symm
    _ ≤ ∑ _ ∈ Icc 1 (maximumStep n), W := sum_le_sum wBound
    _ = _ := by simp [nsmul_eq_mul]

theorem norm_nearPair_replacement_le (n : ℕ) (nPositive : 0 < n) {A T W : ℝ}
    (ANonnegative : 0 ≤ A) (TNonnegative : 0 ≤ T)
    (aBound : ∀ m ∈ range (n + 1), ‖lowCoefficients n m‖ ≤ A)
    (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : ∀ u ∈ Icc 1 (maximumStep n),
      (∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖) ≤ W) :
    ‖exactNearPair n - smoothedNearPair n‖ ≤
      (A * (2 * Real.pi * (2 * radius (maximumStep n))) * T ^ 2 * (2 * (n : ℝ))) *
        ((maximumStep n : ℝ) * W) := by
  let radiusError := 2 * Real.pi * (2 * radius (maximumStep n))
  let C := A * radiusError * T * (2 * (n : ℝ))
  let moduli (i : ℕ × ℕ) := (atomStep i).divisors.filter (fun q => cutoffR n < q)
  have radiusNonnegative : 0 ≤ radiusError := by
    unfold radiusError
    exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (DyadicMixedB4WindowKernel.radius_nonnegative _))
  have CNonnegative : 0 ≤ C := by unfold C; positivity
  have cuts := cutoffs_ordered n nPositive
  have MPositive : 0 < maximumStep n := cuts.1.trans (cuts.2.1.trans cuts.2.2.1)
  have individual (i : ℕ × ℕ) (iMember : i ∈ highAtoms n) (q : ℕ) (qMember : q ∈ moduli i) :
      ‖exactNearAtom n i q - smoothedNearAtom n i q‖ ≤ C := by
    obtain ⟨gPositive, gBound⟩ := atomStep_range iMember
    obtain ⟨divisor, qAbove⟩ := mem_filter.mp qMember
    have qLower := cuts.1.trans_lt qAbove
    letI : NeZero q := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors divisor)⟩
    have qBound := (Nat.le_of_dvd gPositive (Nat.dvd_of_mem_divisors divisor)).trans (gBound.trans cuts.2.2.2)
    have radiusBound : (atomStep i : ℝ) * radius (maximumStep n) ≤ 1 / 2 := by
      have upper := radius_le_product (q := atomStep i) (r := 1) gPositive (by decide) gBound MPositive
      have gRealPositive : (0 : ℝ) < atomStep i := by exact_mod_cast gPositive
      calc
        _ ≤ (atomStep i : ℝ) * (1 / (4 * (atomStep i : ℝ) * (1 : ℕ))) :=
          mul_le_mul_of_nonneg_left upper gRealPositive.le
        _ = (1 : ℝ) / 4 := by simp only [Nat.cast_one, mul_one]; field_simp
        _ ≤ _ := by norm_num
    have actual := norm_sum_windowKernel_difference_le n (maximumStep n) (cutoffB n) (cutoffH n) q
      (atomStep i) (atomLower n i) (atomUpper n i) (lowCoefficients n) qLower gPositive radiusBound aBound ANonnegative
    have normalized : ‖exactNearAtom n i q - smoothedNearAtom n i q‖ ≤
        (A * radiusError) * ((q.divisors.card : ℝ) * ((n : ℝ) + q)) := by
      unfold exactNearAtom smoothedNearAtom smoothKernelFactor radiusError
      simpa only [mul_assoc] using actual
    refine normalized.trans ?_
    unfold C
    rw [mul_assoc (A * radiusError) T (2 * (n : ℝ))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg ANonnegative radiusNonnegative)
    refine mul_le_mul (tBound q qBound) ?_ (by positivity) TNonnegative
    have qReal : (q : ℝ) ≤ n := by exact_mod_cast qBound
    linarith only [qReal]
  have inner (i : ℕ × ℕ) (iMember : i ∈ highAtoms n) :
      ‖∑ q ∈ moduli i, (exactNearAtom n i q - smoothedNearAtom n i q)‖ ≤ T * C := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ moduli i, C := sum_le_sum (individual i iMember)
      _ ≤ ∑ _ ∈ (atomStep i).divisors, C :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => CNonnegative)
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (tBound _ ((atomStep_range iMember).2.trans cuts.2.2.2)) CNonnegative
  unfold exactNearPair smoothedNearPair
  rw [← sum_sub_distrib]
  simp only [← mul_sub, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ highAtoms n, ‖atomWeight i‖ * (T * C) := by
      refine sum_le_sum fun i membership => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (inner i membership) (norm_nonneg _)
    _ = (∑ i ∈ highAtoms n, ‖atomWeight i‖) * (T * C) := (sum_mul _ _ _).symm
    _ ≤ ((maximumStep n : ℝ) * W) * (T * C) :=
      mul_le_mul_of_nonneg_right (sum_atomWeight_le n wBound) (mul_nonneg TNonnegative CNonnegative)
    _ = _ := by unfold C radiusError; ring


end
end DyadicMixedB4NearPair

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4KernelControl DyadicMixedB4NearPair DyadicMixedB4PrimitiveAt

namespace DyadicMixedB4PrimitiveNearPair

noncomputable section

def primitiveNearAtom (n : ℕ) (i : ℕ × ℕ) (q : ℕ) : ℂ := ∑ a ∈ Ioc (cutoffU n) (lowCut n),
  (lowMoebiusWeight (cutoffU n) a : ℂ) *
    ∑ b ∈ Ioc (cutoffU n) (n / a), (Λ b : ℂ) * (primitiveAt q n a b *
      (windowKernel n (maximumStep n) (cutoffB n) (cutoffH n) q (atomStep i) (atomLower n i) (atomUpper n i)
        (((((a * b : ℕ) : ℤ) - (n : ℤ)) : ℝ)) : ℂ))

def primitiveNearPair (n : ℕ) : ℂ := ∑ i ∈ highAtoms n, atomWeight i *
  ∑ q ∈ (atomStep i).divisors.filter (fun q => cutoffR n < q), primitiveNearAtom n i q

set_option maxHeartbeats 800000 in
theorem norm_smoothedNearAtom_sub_primitive_le (n : ℕ) (i : ℕ × ℕ) (q : ℕ) (nPositive : 0 < n)
    (qLower : 1 < q) (qBound : q ≤ n) {T : ℝ} (TNonnegative : 0 ≤ T)
    (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖smoothedNearAtom n i q - primitiveNearAtom n i q‖ ≤
      (16 * (lowCut n : ℝ) * T ^ 2 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n) / (atomStep i : ℝ) * q := by
  let V : ℝ := 16 / (atomStep i : ℝ)
  let E : ℝ := (V * ((q : ℝ) * (1 + T))) * (T * (Nat.log 2 n : ℝ) * Real.log n)
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast nPositive)
  have VNonnegative : 0 ≤ V := by unfold V; positivity
  have ENonnegative : 0 ≤ E := by unfold E; positivity
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have lowBound : lowCut n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nLower (by norm_num))
  let K (a b : ℕ) := (windowKernel n (maximumStep n) (cutoffB n) (cutoffH n) q
    (atomStep i) (atomLower n i) (atomUpper n i) (((((a * b : ℕ) : ℤ) - (n : ℤ)) : ℝ)) : ℂ)
  have boundAt (a : ℕ) : ‖∑ b ∈ Ioc (cutoffU n) (n / a), (Λ b : ℂ) *
      ((ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b) * K a b)‖ ≤ E := by
    have within : Ioc (cutoffU n) (n / a) ⊆ Icc 1 n := by
      intro b member
      obtain ⟨lower, upper⟩ := mem_Ioc.mp member
      exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt lower, upper.trans (Nat.div_le_self n a)⟩
    have kernelBound (b : ℕ) (_ : b ∈ Ioc (cutoffU n) (n / a)) : ‖K a b‖ ≤ V := by
      unfold K V
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_windowKernel_le _ _ _ _ _ _ _ _ _
    have estimate := norm_mangoldt_replacement_le qLower nPositive a _ within (K a) VNonnegative kernelBound
    refine estimate.trans ?_
    unfold E
    have rBound : reducedModulus q a ≤ n := (Nat.div_le_self q (a.gcd q)).trans qBound
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add_right (tBound n le_rfl) 1) (Nat.cast_nonneg _)) VNonnegative
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (tBound _ rBound) (Nat.cast_nonneg _)) logNonnegative
    · positivity
    · positivity
  rw [smoothedNearAtom_hyperbola n i q nPositive]
  unfold primitiveNearAtom smoothKernelFactor
  rw [← sum_sub_distrib]
  simp only [← mul_sub, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ Ioc (cutoffU n) (lowCut n), T * E := by
      refine sum_le_sum fun a member => ?_
      have within := (mem_Ioc.mp member).2.trans lowBound
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((abs_lowMoebiusWeight_le (cutoffU n) a).trans (tBound a within))
        (by simpa only [Int.cast_sub, sub_mul, K] using boundAt a) (norm_nonneg _) TNonnegative
    _ ≤ ∑ _ ∈ Icc 1 (lowCut n), T * E := by
      refine sum_le_sum_of_subset_of_nonneg (fun a member => ?_) (fun _ _ _ => mul_nonneg TNonnegative ENonnegative)
      obtain ⟨lower, upper⟩ := mem_Ioc.mp member
      exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt lower, upper⟩
    _ = _ := by unfold E V; rw [sum_const, nsmul_eq_mul]; simp; ring

theorem norm_smoothedNearPair_sub_primitive_le (n : ℕ) (nPositive : 0 < n) {T W : ℝ}
    (TNonnegative : 0 ≤ T) (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : ∀ u ∈ Icc 1 (maximumStep n),
      (∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖) ≤ W) :
    ‖smoothedNearPair n - primitiveNearPair n‖ ≤
      (16 * (lowCut n : ℝ) * T ^ 3 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n) *
        ((maximumStep n : ℝ) * W) := by
  let C : ℝ := 16 * (lowCut n : ℝ) * T ^ 2 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n
  let moduli (i : ℕ × ℕ) := (atomStep i).divisors.filter (fun q => cutoffR n < q)
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast nPositive)
  have CNonnegative : 0 ≤ C := by unfold C; positivity
  have cutoffs := cutoffs_ordered n nPositive
  have inner (i : ℕ × ℕ) (membership : i ∈ highAtoms n) :
      ‖∑ q ∈ moduli i, (smoothedNearAtom n i q - primitiveNearAtom n i q)‖ ≤ C * T := by
    obtain ⟨positive, upper⟩ := atomStep_range membership
    have within : atomStep i ≤ n := upper.trans cutoffs.2.2.2
    have stepPositive : (0 : ℝ) < atomStep i := by exact_mod_cast positive
    have qBound (q : ℕ) (member : q ∈ moduli i) : q ≤ atomStep i :=
      Nat.le_of_dvd positive (Nat.dvd_of_mem_divisors (mem_filter.mp member).1)
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ q ∈ moduli i, C / (atomStep i : ℝ) * (q : ℝ) := by
        exact sum_le_sum fun q member => norm_smoothedNearAtom_sub_primitive_le n i q nPositive
          (cutoffs.1.trans_lt (mem_filter.mp member).2) ((qBound q member).trans within) TNonnegative tBound
      _ ≤ ∑ _ ∈ moduli i, C := by
        refine sum_le_sum fun q member => ?_
        calc
          _ ≤ C / (atomStep i : ℝ) * (atomStep i : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast qBound q member) (by positivity)
          _ = _ := div_mul_cancel₀ _ stepPositive.ne'
      _ ≤ ∑ _ ∈ (atomStep i).divisors, C :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => CNonnegative)
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_right (tBound _ within) CNonnegative
  unfold smoothedNearPair primitiveNearPair
  rw [← sum_sub_distrib]
  simp only [← mul_sub, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ highAtoms n, ‖atomWeight i‖ * (C * T) := by
      refine sum_le_sum fun i member => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (inner i member) (norm_nonneg _)
    _ = (∑ i ∈ highAtoms n, ‖atomWeight i‖) * (C * T) := (sum_mul _ _ _).symm
    _ ≤ ((maximumStep n : ℝ) * W) * (C * T) :=
      mul_le_mul_of_nonneg_right (sum_atomWeight_le n wBound) (mul_nonneg CNonnegative TNonnegative)
    _ = _ := by unfold C; ring


end
end DyadicMixedB4PrimitiveNearPair

end

section

open Finset DyadicMixedB4Scale DyadicMixedB4ArcGeometry
open DyadicMixedB4BilinearEnergy DyadicMixedB4BilinearBlock DyadicMixedB4BlockModulus
open DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral DyadicMixedB4PrimitiveNearPair
open DyadicMixedB4ModulusAggregate DyadicMixedB4DyadicPartition DyadicMixedB4GcdSeries
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4TailAggregate

namespace DyadicMixedB4NearMain

noncomputable section

def shortIndices (n k : ℕ) : Finset ℕ :=
  (Ioc (cutoffU n) (lowCut n)).filter (fun a => Nat.log 2 a = k)

def primitiveDyadPair (n k : ℕ) : ℂ :=
  ∑ i ∈ highAtoms n, atomWeight i * ∑ q ∈ (atomStep i).divisors.filter (fun q => cutoffR n < q),
    primitiveBlock n (maximumStep n) (cutoffB n) (cutoffH n) q (atomStep i) (atomLower n i) (atomUpper n i)
      (cutoffU n) (shortIndices n k) (fun a => (lowMoebiusWeight (cutoffU n) a : ℂ))

theorem lowCut_le (n : ℕ) (nPositive : 0 < n) : lowCut n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast nPositive) (by norm_num))

theorem primitiveNearPair_eq_sum_dyads (n : ℕ) (nPositive : 0 < n) :
    primitiveNearPair n = ∑ k ∈ dyadicIndices n, primitiveDyadPair n k := by
  let Q (i : ℕ × ℕ) := (atomStep i).divisors.filter (fun q => cutoffR n < q)
  let F (i : ℕ × ℕ) (q k : ℕ) := primitiveBlock n (maximumStep n) (cutoffB n) (cutoffH n) q
    (atomStep i) (atomLower n i) (atomUpper n i) (cutoffU n) (shortIndices n k)
    (fun a => (lowMoebiusWeight (cutoffU n) a : ℂ))
  have each (i : ℕ × ℕ) (q : ℕ) : primitiveNearAtom n i q = ∑ k ∈ dyadicIndices n, F i q k := by
    unfold primitiveNearAtom F shortIndices primitiveBlock
    exact dyadic_sum_partition _ n (fun a member => (mem_Ioc.mp member).2.trans (lowCut_le n nPositive)) _
  calc
    _ = ∑ i ∈ highAtoms n, atomWeight i * ∑ q ∈ Q i, ∑ k ∈ dyadicIndices n, F i q k := by
      unfold primitiveNearPair
      simp only [each, Q]
    _ = ∑ i ∈ highAtoms n, ∑ k ∈ dyadicIndices n, atomWeight i * ∑ q ∈ Q i, F i q k := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm, mul_sum]
    _ = _ := sum_comm

theorem atomWeight_bound (n : ℕ) (nPositive : 0 < n) {T : ℝ} (TNonnegative : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ∀ u ∈ Icc 1 (maximumStep n),
      (∑ i ∈ (highAtoms n).filter (fun i => atomStep i = u), ‖atomWeight i‖) ≤ T * logBudget n := by
  intro u member
  have nonnegativeLog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast nPositive)
  have uWithin : u ≤ n := (mem_Icc.mp member).2.trans (cutoffs_ordered n nPositive).2.2.2
  exact (sum_atomWeight_fibre_le nPositive (mem_Icc.mp member).1).trans
    (mul_le_mul (divisorBound u uWithin) (log_le_logBudget nPositive le_rfl) nonnegativeLog TNonnegative)

set_option maxHeartbeats 900000 in
theorem norm_primitiveDyadPair_le (n k : ℕ) (nLower : 2 ≤ n) {T : ℝ} (TNonnegative : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖primitiveDyadPair n k‖ ≤
      2048000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 6 * (n : ℝ) ^ (31 / 32 : ℝ) := by
  have BNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have constantNonnegative : 0 ≤ 2048000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 6 *
      (n : ℝ) ^ (31 / 32 : ℝ) := by
    have := gcdSeriesConstant_nonnegative
    positivity
  by_cases nonempty : (shortIndices n k).Nonempty
  · let A := dyadicBase k
    let U := cutoffU n
    let M := maximumStep n
    let R := cutoffR n
    let G := Icc 1 (2 * A)
    let D := Icc 1 M
    let energy := blockEnergy n A U
    let w (a : ℕ) := (lowMoebiusWeight U a : ℂ)
    let C := T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1))
    let Q (i : ℕ × ℕ) := (atomStep i).divisors.filter (fun q => R < q)
    let cost := conductorCost G D n.divisors energy
    let W := T * logBudget n
    have nPositive : 0 < n := by omega
    have aPositive := dyadicBase_positive k
    have CNonnegative : 0 ≤ C := by
      unfold C
      have := Real.log_nonneg (show 1 ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
      positivity
    have indicesRange : shortIndices n k ⊆ Ico A (2 * A) := by
      intro a member
      obtain ⟨within, equality⟩ := mem_filter.mp member
      exact mem_dyadicInterval ((Nat.zero_le _).trans_lt (mem_Ioc.mp within).1) equality
    have aUpper : A ≤ lowCut n := by
      obtain ⟨a, member⟩ := nonempty
      exact (mem_Ico.mp (indicesRange member)).1.trans (mem_Ioc.mp (mem_filter.mp member).1).2
    have uLower : U < 2 * A := by
      obtain ⟨a, member⟩ := nonempty
      exact (mem_Ioc.mp (mem_filter.mp member).1).1.trans (mem_Ico.mp (indicesRange member)).2
    obtain ⟨rPositive, rB, bM, mN⟩ := cutoffs_ordered n nPositive
    have mPositive : 0 < M := rPositive.trans (rB.trans bM)
    have radiusUpper : radius M ≤ 1 := by
      have mReal : (1 : ℝ) ≤ M := by exact_mod_cast mPositive
      unfold radius
      apply (div_le_one (by positivity)).mpr
      exact (one_le_pow₀ mReal).trans (le_mul_of_one_le_left (by positivity) (by norm_num))
    have wBound (a : ℕ) (member : a ∈ shortIndices n k) : ‖w a‖ ≤ T := by
      unfold w
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_lowMoebiusWeight_le U a).trans
        (divisorBound a ((mem_Ioc.mp (mem_filter.mp member).1).2.trans (lowCut_le n nPositive)))
    have each (i : ℕ × ℕ) (iMember : i ∈ highAtoms n) (q : ℕ) (qMember : q ∈ Q i) :
        ‖primitiveBlock n M (cutoffB n) (cutoffH n) q (atomStep i) (atomLower n i) (atomUpper n i)
          U (shortIndices n k) w‖ ≤ C / (atomStep i : ℝ) * cost q := by
      obtain ⟨divisor, _⟩ := mem_filter.mp qMember
      obtain ⟨positive, bound⟩ := atomStep_range iMember
      exact norm_primitiveBlock_le n M (cutoffB n) (cutoffH n) q (atomStep i) (atomLower n i) (atomUpper n i)
        U A nPositive aPositive (Nat.pos_of_mem_divisors divisor)
        ((Nat.le_of_dvd positive (Nat.dvd_of_mem_divisors divisor)).trans bound) mN
        radiusUpper (shortIndices n k) indicesRange w TNonnegative wBound divisorBound
    have WNonnegative : 0 ≤ W := mul_nonneg TNonnegative BNonnegative
    have weightBound := atomWeight_bound n nPositive TNonnegative divisorBound
    have mainBound := sum_weighted_moduli_le (highAtoms n) atomStep (fun i => ‖atomWeight i‖)
      R M mPositive WNonnegative (fun _ member => mem_Icc.mpr (atomStep_range member)) weightBound
      G D n.divisors energy (fun _ member => (mem_Icc.mp member).1) (fun _ member => (mem_Icc.mp member).1)
      (fun _ member => Nat.pos_of_mem_divisors member) (fun g _ d _ => blockEnergy_nonnegative n A U g d)
    have tailBound := sum_energy_tails_le nLower aPositive aUpper uLower TNonnegative divisorBound
    let tail := ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ n.divisors, tailWeight R g f d * energy g d
    have logPlus : Real.log ((n : ℝ) + 1) ≤ logBudget n :=
      (Real.log_le_log (by positivity) (by linarith)).trans (le_add_of_nonneg_left zero_le_one)
    have CBound : C ≤ 40 * T ^ 2 * logBudget n := by
      unfold C
      calc
        _ ≤ T ^ 2 * (40 * logBudget n) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          linarith only [logPlus, one_le_logBudget n]
        _ = _ := by ring
    have mLogNonnegative : 0 ≤ 1 + Real.log (M : ℝ) :=
      (add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast mPositive)))
    have tailNonnegative : 0 ≤ tail :=
      sum_nonneg fun g _ => sum_nonneg fun d _ => sum_nonneg fun f _ =>
        mul_nonneg (tailWeight_nonnegative _ _ _ _) (blockEnergy_nonnegative _ _ _ _ _)
    unfold primitiveDyadPair
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i ∈ highAtoms n, ‖atomWeight i‖ * ∑ q ∈ Q i, C / (atomStep i : ℝ) * cost q := by
        refine sum_le_sum fun i member => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum (each i member))) (norm_nonneg _)
      _ = C * (∑ i ∈ highAtoms n, (‖atomWeight i‖ / (atomStep i : ℝ)) * ∑ q ∈ Q i, cost q) := by
        conv_rhs => rw [mul_sum]
        refine sum_congr rfl fun _ _ => ?_
        rw [← mul_sum]
        ring
      _ ≤ C * ((W * (1 + Real.log (M : ℝ))) * tail) :=
        mul_le_mul_of_nonneg_left mainBound CNonnegative
      _ ≤ (40 * T ^ 2 * logBudget n) * ((W * logBudget n) *
          (51200 * gcdSeriesConstant * T ^ 2 * logBudget n ^ 3 * (n : ℝ) ^ (31 / 32 : ℝ))) := by
        apply mul_le_mul CBound _ (mul_nonneg (mul_nonneg WNonnegative mLogNonnegative) tailNonnegative)
          (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (one_add_log_step_le n nPositive) WNonnegative)
          tailBound tailNonnegative (mul_nonneg WNonnegative BNonnegative)
      _ = _ := by unfold W; ring
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [primitiveDyadPair, empty, primitiveBlock, constantNonnegative]

theorem norm_primitiveNearPair_le (n : ℕ) (nLower : 2 ≤ n) {T : ℝ} (TNonnegative : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖primitiveNearPair n‖ ≤
      10240000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 7 * (n : ℝ) ^ (31 / 32 : ℝ) := by
  let C := 2048000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 6 * (n : ℝ) ^ (31 / 32 : ℝ)
  have logNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have CNonnegative : 0 ≤ C := by unfold C; have := gcdSeriesConstant_nonnegative; positivity
  rw [primitiveNearPair_eq_sum_dyads n (by omega)]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ dyadicIndices n, C :=
      sum_le_sum fun k _ => norm_primitiveDyadPair_le n k nLower TNonnegative divisorBound
    _ = ((Nat.log 2 n : ℝ) + 1) * C := by simp [dyadicIndices, nsmul_eq_mul]
    _ ≤ (5 * logBudget n) * C := mul_le_mul_of_nonneg_right (natLog_succ_le nLower le_rfl) CNonnegative
    _ = _ := by unfold C; ring


end
end DyadicMixedB4NearMain

end

section

open DyadicMixedB4Scale DyadicMixedB4ArcGeometry DyadicMixedB4EnergyTail
open DyadicMixedB4PairIntegral DyadicMixedB4TailScale

namespace DyadicMixedB4NumericBudgets

noncomputable section

def finalScale (n : ℕ) (T : ℝ) : ℝ :=
  T ^ 5 * logBudget n ^ 7 * (n : ℝ) ^ (31 / 32 : ℝ)

def outsideScale (n : ℕ) : ℝ := (maximumStep n : ℝ) / Real.sqrt n

theorem maximumStep_real_positive (n : ℕ) (nPositive : 0 < n) : (0 : ℝ) < maximumStep n := by
  obtain ⟨rPositive, rB, bM, _⟩ := cutoffs_ordered n nPositive
  exact_mod_cast rPositive.trans (rB.trans bM)

theorem outsideScale_positive (n : ℕ) (nPositive : 0 < n) : 0 < outsideScale n :=
  div_pos (maximumStep_real_positive n nPositive) (Real.sqrt_pos_of_pos (by exact_mod_cast nPositive))

theorem outside_budget_le (n : ℕ) (nPositive : 0 < n) {T : ℝ} (TLower : 1 ≤ T) :
    let A := T ^ 2 * logBudget n
    let W := T * logBudget n
    (1 / 2) * (outsideScale n * (((n : ℝ) + 1) * A ^ 2) +
      (outsideScale n)⁻¹ * (128 * W ^ 2 * ((maximumStep n : ℝ) ^ 2 * logBudget n ^ 2 +
        (radius (maximumStep n))⁻¹ * (1 + Real.log (maximumStep n : ℝ)) ^ 3))) ≤ 600 * finalScale n T := by
  dsimp only
  let A := T ^ 2 * logBudget n
  let W := T * logBudget n
  let B := logBudget n
  let M := (maximumStep n : ℝ)
  let S := outsideScale n
  have mPositive : 0 < M := maximumStep_real_positive n nPositive
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have root : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos nReal
  have SPositive : 0 < S := outsideScale_positive n nPositive
  have BLower : 1 ≤ B := one_le_logBudget n
  have BNonnegative : 0 ≤ B := zero_le_one.trans BLower
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have HNonnegative : 0 ≤ 1 + Real.log M := add_nonneg zero_le_one (Real.log_nonneg (by
    obtain ⟨rPositive, rB, bM, _⟩ := cutoffs_ordered n nPositive
    unfold M
    exact_mod_cast rPositive.trans (rB.trans bM)))
  have radiusInv : (radius (maximumStep n))⁻¹ = 8 * M ^ 2 := by unfold radius M; rw [one_div, inv_inv]
  have nDivSqrt : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
    apply (div_eq_iff root.ne').mpr
    rw [← pow_two, Real.sq_sqrt nReal.le]
  have first : S * (((n : ℝ) + 1) * A ^ 2) ≤ 2 * Real.sqrt n * M * A ^ 2 := by
    calc
      _ ≤ S * ((2 * (n : ℝ)) * A ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith only [nLower]) (sq_nonneg _)) SPositive.le
      _ = _ := by
        change (M / Real.sqrt n) * ((2 * (n : ℝ)) * A ^ 2) = _
        calc
          _ = 2 * ((n : ℝ) / Real.sqrt n) * M * A ^ 2 := by ring
          _ = _ := by rw [nDivSqrt]
  have inner : M ^ 2 * B ^ 2 + (radius (maximumStep n))⁻¹ * (1 + Real.log M) ^ 3 ≤ 9 * M ^ 2 * B ^ 3 := by
    rw [radiusInv]
    calc
      _ ≤ M ^ 2 * B ^ 3 + (8 * M ^ 2) * B ^ 3 :=
        (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ BLower (by decide : 2 ≤ 3)) (sq_nonneg _))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ HNonnegative (one_add_log_step_le n nPositive) 3) (by positivity)))
      _ = _ := by ring
  have second : S⁻¹ * (128 * W ^ 2 * (M ^ 2 * B ^ 2 + (radius (maximumStep n))⁻¹ * (1 + Real.log M) ^ 3)) ≤
      1152 * Real.sqrt n * M * (W ^ 2 * B ^ 3) := by
    calc
      _ ≤ S⁻¹ * (128 * W ^ 2 * (9 * M ^ 2 * B ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left inner (by positivity)) (by positivity)
      _ = _ := by
        change (M / Real.sqrt n)⁻¹ * _ = _
        rw [inv_div]
        field_simp
        ring
  have aBound : A ^ 2 ≤ T ^ 5 * B ^ 7 := by
    unfold A
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul (pow_le_pow_right₀ TLower (by decide : 2 * 2 ≤ 5))
      (pow_le_pow_right₀ BLower (by decide : 2 ≤ 7)) (sq_nonneg _) (by positivity)
  have wBound : W ^ 2 * B ^ 3 ≤ T ^ 5 * B ^ 7 := by
    unfold W
    rw [mul_pow, mul_assoc, ← pow_add]
    exact mul_le_mul (pow_le_pow_right₀ TLower (by decide : 2 ≤ 5))
      (pow_le_pow_right₀ BLower (by decide : 2 + 3 ≤ 7)) (by positivity) (by positivity)
  change (1 / 2) * (S * (((n : ℝ) + 1) * A ^ 2) +
    S⁻¹ * (128 * W ^ 2 * (M ^ 2 * B ^ 2 + (radius (maximumStep n))⁻¹ * (1 + Real.log M) ^ 3))) ≤ _
  calc
    _ ≤ (1 / 2) * (2 * Real.sqrt n * M * A ^ 2 + 1152 * Real.sqrt n * M * (W ^ 2 * B ^ 3)) :=
      mul_le_mul_of_nonneg_left (add_le_add first second) (by norm_num)
    _ = (Real.sqrt n * M) * (A ^ 2 + 576 * (W ^ 2 * B ^ 3)) := by ring
    _ ≤ (n : ℝ) ^ (31 / 32 : ℝ) * (T ^ 5 * B ^ 7 + 576 * (T ^ 5 * B ^ 7)) :=
      mul_le_mul (sqrt_mul_maximumStep_le n nPositive)
        (add_le_add aBound (mul_le_mul_of_nonneg_left wBound (by norm_num))) (by positivity) (by positivity)
    _ = 577 * finalScale n T := by unfold finalScale B; ring
    _ ≤ _ := by apply mul_le_mul_of_nonneg_right (by norm_num); unfold finalScale; positivity

theorem smoothing_budget_le (n : ℕ) (nPositive : 0 < n) {T : ℝ} (TLower : 1 ≤ T) :
    ((T ^ 2 * logBudget n) * (2 * Real.pi * (2 * radius (maximumStep n))) * T ^ 2 * (2 * (n : ℝ))) *
      ((maximumStep n : ℝ) * (T * logBudget n)) ≤ 16 * finalScale n T := by
  let M := (maximumStep n : ℝ)
  let B := logBudget n
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have mPositive : 0 < M := maximumStep_real_positive n nPositive
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have BLower : 1 ≤ B := one_le_logBudget n
  have BNonnegative : 0 ≤ B := zero_le_one.trans BLower
  have nDiv : (n : ℝ) / M ≤ 4 * (n : ℝ) ^ (31 / 32 : ℝ) := by
    have smaller : (n : ℝ) / M ≤ 4 * (n : ℝ) ^ (29 / 48 : ℝ) := by
      apply (div_le_iff₀ mPositive).mpr
      calc
        _ = (4 * (n : ℝ) ^ (29 / 48 : ℝ)) * ((n : ℝ) ^ (19 / 48 : ℝ) / 4) := by
          calc
            _ = (n : ℝ) ^ (29 / 48 : ℝ) * (n : ℝ) ^ (19 / 48 : ℝ) := by
              rw [← Real.rpow_add nReal]
              norm_num
            _ = _ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (maximumStep_divisor_lower n nPositive) (by positivity)
    exact smaller.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)) (by norm_num))
  calc
    _ = Real.pi * T ^ 5 * B ^ 2 * ((n : ℝ) / M) := by
      unfold radius
      change (T ^ 2 * B * (2 * Real.pi * (2 * (1 / (8 * M ^ 2)))) * T ^ 2 * (2 * (n : ℝ))) *
        (M * (T * B)) = _
      field_simp
      <;> ring
    _ ≤ (4 * T ^ 5 * B ^ 7) * (4 * (n : ℝ) ^ (31 / 32 : ℝ)) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity))
        (pow_le_pow_right₀ BLower (by decide : 2 ≤ 7)) (by positivity) (by positivity)) nDiv (by positivity) (by positivity)
    _ = _ := by unfold finalScale B; ring

theorem primitive_replacement_budget_le (n : ℕ) (nLower : 2 ≤ n) {T : ℝ} (TLower : 1 ≤ T) :
    (16 * (lowCut n : ℝ) * T ^ 3 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n) *
      ((maximumStep n : ℝ) * (T * logBudget n)) ≤ 160 * finalScale n T := by
  let B := logBudget n
  have nPositive : 0 < n := by omega
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have nRealLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have BLower : 1 ≤ B := one_le_logBudget n
  have BNonnegative : 0 ≤ B := zero_le_one.trans BLower
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg nRealLower
  have length : (lowCut n : ℝ) * (maximumStep n : ℝ) ≤ (n : ℝ) ^ (31 / 32 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (19 / 48 : ℝ) :=
        mul_le_mul (Nat.floor_le (by positivity)) (maximumStep_le_power n nPositive) (Nat.cast_nonneg _) (by positivity)
      _ ≤ _ := by
        rw [← Real.rpow_add nReal]
        exact Real.rpow_le_rpow_of_exponent_le nRealLower (by norm_num)
  have tPow : T ^ 4 * (1 + T) ≤ 2 * T ^ 5 := by
    calc
      _ ≤ T ^ 4 * (2 * T) := mul_le_mul_of_nonneg_left (by linarith only [TLower]) (by positivity)
      _ = _ := by ring
  have lPow : (Nat.log 2 n : ℝ) * Real.log n * B ≤ 5 * B ^ 7 := by
    have h : (Nat.log 2 n : ℝ) ≤ 5 * B := by linarith only [natLog_succ_le nLower (le_refl n)]
    calc
      _ ≤ (5 * B) * B * B := mul_le_mul_of_nonneg_right
        (mul_le_mul h (log_le_logBudget nPositive le_rfl) logNonnegative (by positivity)) BNonnegative
      _ = 5 * B ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ BLower (by decide : 3 ≤ 7)) (by norm_num)
  calc
    _ = 16 * ((lowCut n : ℝ) * (maximumStep n : ℝ)) * (T ^ 4 * (1 + T)) *
        ((Nat.log 2 n : ℝ) * Real.log n * B) := by unfold B; ring
    _ ≤ 16 * (n : ℝ) ^ (31 / 32 : ℝ) * (2 * T ^ 5) * (5 * B ^ 7) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left length (by norm_num)) tPow
        (by positivity) (by positivity)) lPow (by positivity) (by positivity)
    _ = _ := by unfold finalScale B; ring


end
end DyadicMixedB4NumericBudgets

end

section

open Finset Filter

namespace DyadicMixedB4DivisorGrowth

noncomputable section

/-- Adapted from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem divisorPower (K : ℕ) (hK : 0<K) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ, 0<n → (n.divisors.card:ℝ)^K ≤ C*n := by
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) K (by norm_num : (1:ℝ)<2)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨E,hE⟩ := eventually_atTop.mp hl
  let c : ℝ := (2:ℝ)^K*((E:ℝ)+1)^K
  have hc : 1≤c := by
    dsimp [c]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E]))
  have small (e : ℕ) : ((e:ℝ)+1)^K ≤ c*(2:ℝ)^e := by
    by_cases he : e<E
    · have hle : ((e:ℝ)+1)^K ≤ ((E:ℝ)+1)^K := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show e+1≤E+1 by omega)) _
      have h2 : (1:ℝ)≤2^K := one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ)≤2^e := one_le_pow₀ (by norm_num)
      exact hle.trans ((le_mul_of_one_le_left (by positivity) h2).trans (le_mul_of_one_le_right (by positivity) h3))
    · have hs := hE (e+1) (by omega)
      simp only [Function.comp_apply,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one,abs_of_nonneg (pow_nonneg (by positivity : 0≤(e:ℝ)+1) K),abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (e+1)),one_mul,pow_succ] at hs
      rw [abs_of_nonneg (by positivity)] at hs
      have hK1 : (2:ℝ)≤2^K := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hK)
      have hE1 : (1:ℝ)≤((E:ℝ)+1)^K := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E])
      have hc2 : (2:ℝ)≤c := hK1.trans (le_mul_of_one_le_right (by positivity) hE1)
      exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤(2:ℝ)^e)])
  let P : ℕ := 2^K
  refine ⟨c^P,one_le_pow₀ hc,?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors,(p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast (by simpa [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn.ne' :
      (∏ p ∈ n.primeFactors,p^(n.factorization p))=n)
  have hlocal (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p:ℝ)+1)^K ≤ (if p<P then c else 1)*(p:ℝ)^(n.factorization p) := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact (small _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by linarith))
    · rw [one_mul]
      have he : ∀ e : ℕ,(e:ℝ)+1 ≤ (2:ℝ)^e := by
        intro e; induction e with
        | zero => norm_num
        | succ e ih => push_cast; rw [pow_succ]; linarith [show (0:ℝ)≤e by positivity]
      calc
        _ ≤ ((2:ℝ)^n.factorization p)^K := pow_le_pow_left₀ (by positivity) (he _) _
        _ = ((2:ℝ)^K)^n.factorization p := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show 2^K≤p by omega)) _
  have hcount : ((n.primeFactors.filter (·<P)).card)≤P := by
    have : n.primeFactors.filter (·<P)⊆range P := fun _ h => mem_range.mpr (mem_filter.mp h).2
    simpa using card_le_card this
  have hfactor : (∏ p ∈ n.primeFactors, if p<P then c else 1)≤c^P := by
    rw [←prod_filter,prod_const]; exact pow_le_pow_right₀ hc hcount
  rw [Nat.card_divisors hn.ne',Nat.cast_prod,←prod_pow]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<P then c else 1)*(p:ℝ)^(n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ ≤ _ := by rw [prod_mul_distrib,hprod]; exact mul_le_mul_of_nonneg_right hfactor (by positivity)


end
end DyadicMixedB4DivisorGrowth

end

section

open Filter Topology DyadicMixedB4NumericBudgets DyadicMixedB4DivisorGrowth DyadicMixedB4EnergyTail

namespace DyadicMixedB4FinalGrowth

noncomputable section

private theorem divisor_envelope : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 1024 : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower 1024 (by decide)
  let p : ℝ := 1 / 1024
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by norm_num [p]), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) 1024) standard
      (show 0 ≤ p by norm_num [p])
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    norm_num [p] at powered ⊢
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity

private theorem eventually_log_budget_le :
    ∀ᶠ n : ℕ in atTop, logBudget n ≤ (n : ℝ) ^ (1 / 1024 : ℝ) := by
  have limit : Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ (1 / 1024 : ℝ)) atTop (𝓝 0) := by
    have realLimit := (isLittleO_log_rpow_rpow_atTop (1 : ℕ)
      (show (0 : ℝ) < 1 / 1024 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one, Nat.cast_one, Function.comp_def] using
      realLimit.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, limit.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)] with n hn small
  have nLower : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have nPositive : (0 : ℝ) < n := by linarith only [nLower]
  have logTwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) nLower
  have big : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith only [nLower])
      (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logSquare := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) big
  rw [Real.log_pow] at logSquare
  norm_num at logSquare
  have logBound : logBudget n ≤ 4 * Real.log n := by
    unfold logBudget
    linarith only [logSquare, logTwo, Real.log_two_gt_d9]
  have divided := (div_lt_iff₀ (Real.rpow_pos_of_pos nPositive _)).mp small
  exact logBound.trans (by linarith only [divided])

theorem eventually_finalScale_le {C e : ℝ} (CNonnegative : 0 ≤ C) (ePositive : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ T : ℝ, 1 ≤ T ∧ (∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) ∧
      C * finalScale n T ≤ e * (n : ℝ) := by
  obtain ⟨D, DLower, estimate⟩ := divisor_envelope
  let P := C * D ^ 5
  have DNonnegative : 0 ≤ D := zero_le_one.trans DLower
  have limit : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(5 / 256) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 256)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaledLimit : Tendsto (fun n : ℕ => P * (n : ℝ) ^ (-(5 / 256) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le, scaledLimit.eventually_lt_const ePositive]
    with n nLower logBound small
  let X := (n : ℝ) ^ (1 / 1024 : ℝ)
  let T := D * X
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast nLower
  have nPositive : (0 : ℝ) < n := zero_lt_one.trans_le nOne
  have XLower : 1 ≤ X := Real.one_le_rpow nOne (by norm_num)
  have TLower : 1 ≤ T := one_le_mul_of_one_le_of_one_le DLower XLower
  refine ⟨T, TLower, fun m upper => estimate n m upper, ?_⟩
  calc
    _ ≤ C * (T ^ 5 * X ^ 7 * (n : ℝ) ^ (31 / 32 : ℝ)) := by
      unfold finalScale
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_logBudget n)) logBound 7)
          (by positivity)) (by positivity)) CNonnegative
    _ = P * (X ^ 12 * (n : ℝ) ^ (31 / 32 : ℝ)) := by unfold T P; ring
    _ = P * (n : ℝ) ^ (251 / 256 : ℝ) := by
      unfold X
      rw [← Real.rpow_natCast, ← Real.rpow_mul nPositive.le, ← Real.rpow_add nPositive]
      norm_num
    _ = (P * (n : ℝ) ^ (-(5 / 256) : ℝ)) * (n : ℝ) := by
      calc
        _ = P * ((n : ℝ) ^ (-(5 / 256) : ℝ) * (n : ℝ) ^ (1 : ℝ)) := by
          rw [← Real.rpow_add nPositive]
          norm_num
        _ = _ := by rw [Real.rpow_one]; unfold P; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right small.le nPositive.le


end
end DyadicMixedB4FinalGrowth

end

section

open Filter Finset DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand
open DyadicMixedB4PairIntegral DyadicMixedB4NearPair DyadicMixedB4PrimitiveNearPair DyadicMixedB4NearMain
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4GcdSeries
open DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

namespace DyadicMixedB4Finish

noncomputable section

def totalConstant : ℝ := 776 + 10240000 * gcdSeriesConstant

theorem totalConstant_nonnegative : 0 ≤ totalConstant :=
  (add_nonneg (by norm_num) (mul_nonneg (by norm_num) gcdSeriesConstant_nonnegative))

theorem norm_deepPairIntegral_le (n : ℕ) (nLower : 2 ≤ n) (width : 4 * cutoffH n * maximumStep n ≤ n)
    {T : ℝ} (TLower : 1 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖deepPairIntegral n‖ ≤ totalConstant * finalScale n T := by
  let A := T ^ 2 * logBudget n
  let W := T * logBudget n
  have nPositive : 0 < n := by omega
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have BNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have ANonnegative : 0 ≤ A := mul_nonneg (sq_nonneg _) BNonnegative
  have WNonnegative : 0 ≤ W := mul_nonneg TNonnegative BNonnegative
  have aBound (m : ℕ) (membership : m ∈ range (n + 1)) : ‖lowCoefficients n m‖ ≤ A := by
    have mBound : m ≤ n := Nat.le_of_lt_succ (mem_range.mp membership)
    unfold lowCoefficients A
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_lowBandCoefficient_le (cutoffU n) (lowCut n) m n mBound nPositive).trans
      (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (divisorBound m mBound) 2)
        (log_le_logBudget nPositive le_rfl) (Real.log_nonneg (by exact_mod_cast nPositive)) (sq_nonneg _))
  have wBound := atomWeight_bound n nPositive TNonnegative divisorBound
  have far := (norm_outsidePairIntegral_le n nPositive (outsideScale_positive n nPositive)
    ANonnegative WNonnegative aBound wBound).trans (outside_budget_le n nPositive TLower)
  have smooth := (norm_nearPair_replacement_le n nPositive ANonnegative TNonnegative aBound divisorBound wBound).trans
    (smoothing_budget_le n nPositive TLower)
  have primitive := (norm_smoothedNearPair_sub_primitive_le n nPositive TNonnegative divisorBound wBound).trans
    (primitive_replacement_budget_le n nLower TLower)
  have main : ‖primitiveNearPair n‖ ≤ (10240000 * gcdSeriesConstant) * finalScale n T :=
    (norm_primitiveNearPair_le n nLower TNonnegative divisorBound).trans_eq (by unfold finalScale; ring)
  have approxNorm (x y : ℂ) : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  rw [deepPairIntegral_split n nPositive width]
  have triangle := norm_add_le (outsidePairIntegral n) (exactNearPair n)
  have first := approxNorm (exactNearPair n) (smoothedNearPair n)
  have second := approxNorm (smoothedNearPair n) (primitiveNearPair n)
  unfold totalConstant
  linarith only [triangle, first, second, far, smooth, primitive, main]

theorem deepPairIntegral_eventually (e : ℝ) (ePositive : 0 < e) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖deepPairIntegral n‖ ≤ e * (n : ℝ) := by
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 2, eventually_small_width, eventually_finalScale_le totalConstant_nonnegative ePositive]
    with n nLower width envelope
  obtain ⟨T, TLower, divisorBound, bound⟩ := envelope
  exact (norm_deepPairIntegral_le n nLower width TLower divisorBound).trans bound


end
end DyadicMixedB4Finish

end

namespace PEqualNP.Outside

theorem L_goldbach_frontier_type2_b1_b4 :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₄ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₃ n < a ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₄ n)‖ ≤ e * (n : ℝ) := by
  dsimp only
  intro e ePositive
  obtain ⟨N, estimate⟩ := DyadicMixedB4Finish.deepPairIntegral_eventually e ePositive
  exact ⟨N, fun n bound _ => estimate n bound⟩

end PEqualNP.Outside
