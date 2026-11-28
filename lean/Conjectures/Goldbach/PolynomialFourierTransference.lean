import Mathlib

/-! Polynomial transference by testing against the bad sums.
The quadratic majorant of the contribution of f uses the squared norm of a
truncated residual for the reflected average of g. All frequencies outside
the truncation are paid for using the two restriction bounds and the second
moment of the normalized indicator of the bad sums.

Alsetri and Shao, Density versions of the binary Goldbach problem, Proposition
3.1, supplies the qualitative comparison and the Fourier normalization.
The elementary character conjugation and orthogonality follow the project
calculation of skayla2007 in PR 3068 at 45b40f5be8a9fdd821a399336a52cc75343903fd,
under Apache-2.0, with a negative phase and normalized average here. -/


namespace PolynomialTransfer
open Finset
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]
abbrev G (N : ℕ) := ZMod N
def E (f : G N → ℝ) : ℝ := (∑ x, f x) / N
def C (f : G N → ℂ) : ℂ := (∑ x, f x) / N
def ch (r x : G N) : ℂ := ZMod.stdAddChar (-(r*x))
def F (f : G N → ℝ) (r : G N) : ℂ := C (fun x => (f x : ℂ) * ch r x)
def P (a : G N → ℂ) (x : G N) : ℂ := ∑ r, a r * ch r x
theorem Enonneg {f : G N → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ E f :=
  div_nonneg (sum_nonneg fun x _ => h x) (Nat.cast_nonneg _)
theorem Emono {f g : G N → ℝ} (h : ∀ x, f x ≤ g x) : E f ≤ E g :=
  div_le_div_of_nonneg_right (sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)
theorem Eadd (f g : G N → ℝ) : E (fun x => f x+g x)=E f+E g := by simp [E,sum_add_distrib,add_div]
theorem Esub (f g : G N → ℝ) : E (fun x => f x-g x)=E f-E g := by simp [E,sum_sub_distrib,sub_div]
theorem Emul (a : ℝ) (f : G N → ℝ) : E (fun x => a*f x)=a*E f := by simp [E,←mul_sum]; ring
theorem Econst (a : ℝ) : E (fun _ : G N => a)=a := by simp [E,ZMod.card,NeZero.ne (N:ℝ)]
theorem Cof (f : G N → ℝ) : C (fun x => (f x : ℂ)) = (E f : ℂ) := by simp [C,E]
theorem Cre (f : G N → ℂ) : (C f).re = E (fun x => (f x).re) := by
  unfold C E; rw [←Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum]
theorem Csum {ι : Type*} (s : Finset ι) (f : ι → G N → ℂ) :
    C (fun x => ∑ i ∈ s, f i x)=∑ i ∈ s, C (f i) := by
  simp only [C,←sum_div]; rw [sum_comm]
theorem Cmul (a : ℂ) (f : G N → ℂ) : C (fun x => a*f x)=a*C f := by simp [C,←mul_sum]; ring
theorem Csub (f g : G N → ℂ) : C (fun x => f x-g x)=C f-C g := by simp [C,sum_sub_distrib,sub_div]
theorem cn (r x : G N) : ‖ch r x‖=1 := by simp [ch,ZMod.stdAddChar_apply]
theorem cconj (r x : G N) : conj (ch r x)=ch (-r) x := by
  unfold ch; rw [show -(-r*x) = -(-(r*x)) by ring, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]; simp
theorem csub (r s x : G N) : ch r x*conj (ch s x)= ch (r-s) x := by
  rw [cconj]; unfold ch; rw [←AddChar.map_add_eq_mul]; congr 1; ring
theorem carg (r n x : G N) : ch r (-(n-x)) = ch r (-n)*ch r x := by
  unfold ch; rw [←AddChar.map_add_eq_mul]; congr 1; ring
theorem Fzero (f : G N → ℝ) : F f 0=(E f : ℂ) := by simp [F,ch,C,E]
theorem Fone (r : G N) : F (fun _ => 1) r = if r=0 then 1 else 0 := by
  classical
  by_cases h : r=0
  · subst r; simp [Fzero,Econst]
  · simp only [F,C,ch,Complex.ofReal_one,one_mul,if_neg h,←neg_mul]
    have z := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N (neg_ne_zero.mpr h))
    simp only [AddChar.mulShift_apply] at z
    rw [z,zero_div]
theorem Fsub (f g : G N → ℝ) (r : G N) : F (fun x=> f x-g x) r=F f r-F g r := by
  simp only [F,Complex.ofReal_sub,sub_mul]; apply Csub
theorem cflip (r x : G N) : ch r (-x)=conj (ch r x) := by rw [cconj]; simp [ch]
theorem inversion (f : G N → ℝ) (x : G N) : P (F f) (-x) = (f x : ℂ) := by
  have hf (r : G N) : F f r = ZMod.dft (fun j => (f j:ℂ)) r / N := by
    simp only [F,C,ch,ZMod.dft_apply,smul_eq_mul]; congr 1; apply sum_congr rfl
    intro j _; rw [mul_comm r j,mul_comm]
  simp only [P,hf,div_mul_eq_mul_div,←sum_div]
  have e := congrFun (ZMod.dft_dft (fun j => (f j:ℂ))) (-x)
  rw [ZMod.dft_apply] at e
  simpa only [smul_eq_mul,neg_neg] using
    (show (∑ r, ZMod.dft (fun j => (f j:ℂ)) r * ch r (-x))/N = (f x:ℂ) by
      apply (div_eq_iff (NeZero.ne (N:ℂ))).2
      simpa only [ch,smul_eq_mul,neg_neg,mul_comm] using e)
theorem pair (w : G N → ℝ) (a : G N → ℂ) :
    C (fun x => (w x : ℂ)*P a x) = ∑ r, a r*F w r := by
  simp only [P,mul_sum]; calc
    _ = C (fun x => ∑ r, a r*((w x:ℂ)*ch r x)) := by congr 1; funext x; apply sum_congr rfl; intros; ring
    _ = _ := by rw [Csum]; simp only [Cmul,F]
set_option maxHeartbeats 1600000 in
theorem gram (w : G N → ℝ) (a : G N → ℂ) :
    (E (fun x => w x*‖P a x‖^2):ℂ)=∑ r, ∑ s, a r*conj (a s)*F w (r-s) := by
  rw [←Cof]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,←Complex.mul_conj',P,map_sum,map_mul]
  simp only [sum_mul_sum]
  simp only [mul_sum]
  calc
    _ = C (fun x => ∑ r, ∑ s, (a r*conj (a s))*((w x:ℂ)*ch (r-s) x)) := by
      congr 1; funext x; apply sum_congr rfl; intro r _; apply sum_congr rfl; intro s _
      rw [←csub]; ring
    _ = _ := by rw [Csum]; apply sum_congr rfl; intro r _; rw [Csum]; simp only [Cmul,F]
theorem parseP (a : G N → ℂ) : E (fun x=> ‖P a x‖^2)=∑ r, ‖a r‖^2 := by
  classical
  have h := gram (fun _ : G N => 1) a
  simp only [one_mul,Fone,sub_eq_zero,mul_ite,mul_one,mul_zero,sum_ite_eq,mem_univ,ite_true,Complex.mul_conj'] at h
  exact_mod_cast h
theorem parseF (f : G N → ℝ) : (∑ r, ‖F f r‖^2)=E (fun x=> (f x)^2) := by
  rw [←parseP]; unfold E; congr 1
  rw [←Equiv.sum_comp (Equiv.neg (G N)) (fun x=> ‖P (F f) x‖^2)]
  simp [inversion,Real.norm_eq_abs]
theorem boundF (f : G N → ℝ) (hf : ∀ x,0≤f x) (r : G N) : ‖F f r‖≤ E f := by
  unfold F C E
  rw [norm_div]; simp only [Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (norm_sum_le _ _).trans (sum_le_sum (fun x _ => by simp [norm_mul,cn,Real.norm_eq_abs,abs_of_nonneg (hf x)]))
end
end PolynomialTransfer

namespace PolynomialTransfer
open Finset
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]
def coeff (b g : G N → ℝ) (r : G N) : ℂ := F g r*conj (F b r)
def corr (b g : G N → ℝ) (x : G N) : ℝ := E (fun n => b n*g (n-x))
def conv (f g : G N → ℝ) (n : G N) : ℝ := E (fun x=> f x*g (n-x))
theorem CorrP (b g : G N → ℝ) (x : G N) : P (coeff b g) x = (corr b g x:ℂ) := by
  rw [corr,←Cof]
  simp only [Complex.ofReal_mul, ←inversion g, P,carg,mul_sum]
  have z (r : G N) : C (fun n => (b n:ℂ)*ch r (-n))=conj (F b r) := by
    simp [F,C,cflip]
  calc
    _ = ∑ r, (F g r*ch r x)*C (fun n=> (b n:ℂ)*ch r (-n)) := by simp only [z,coeff]; apply sum_congr rfl; intros; ring
    _ = _ := by simp_rw [←Cmul]; rw [←Csum]; apply congrArg C; funext n; apply sum_congr rfl; intro r _; ring
      <;> try rfl
theorem Eshift (g : G N → ℝ) (n : G N) : E (fun x=>g (n-x))=E g := by
  unfold E
  congr 1
  exact Fintype.sum_equiv ((Equiv.neg (G N)).trans (Equiv.addLeft n)) _ _ (fun x=> by simp [sub_eq_add_neg])
theorem Ecorr (b g : G N → ℝ) : E (corr b g)=E b*E g := by
  unfold corr E
  simp only [←sum_div]
  rw [sum_comm]; simp only [←mul_sum]
  have sh (n : G N) : (∑ x, g (n-x))=∑ x,g x := by
    exact Fintype.sum_equiv ((Equiv.neg (G N)).trans (Equiv.addLeft n)) _ _ (fun x=>by simp [sub_eq_add_neg])
  simp only [sh,←sum_mul]; ring
theorem corrPair (b f g : G N → ℝ) : E (fun x=>f x*corr b g x)=E (fun n=>b n*conv f g n) := by
  unfold corr conv E
  simp only [←mul_div_assoc, mul_sum,←sum_div]
  rw [sum_comm]; congr 2
  apply sum_congr rfl; intro n _; apply sum_congr rfl; intro x _; ring
theorem gramBound (u : G N → ℝ) (a : G N → ℂ) {ε : ℝ}
    (he : ∀ r, ‖F (fun x=>u x-1) r‖ ≤ ε) :
    E (fun x=>u x*‖P a x‖^2) ≤ E (fun x=>‖P a x‖^2)+ε*(∑ r, ‖a r‖)^2 := by
  have eq : E (fun x=>u x*‖P a x‖^2)-E (fun x=>‖P a x‖^2) =
      E (fun x=>(u x-1)*‖P a x‖^2) := by rw [←Esub]; congr 1; funext x; ring
  apply (sub_le_iff_le_add').mp
  rw [eq]
  let v := fun x=>u x-1
  calc
    _ ≤ ‖(E (fun x=>v x*‖P a x‖^2):ℂ)‖ := by simpa [v,Real.norm_eq_abs] using le_abs_self (E (fun x=>(u x-1)*‖P a x‖^2))
    _ = _ := congrArg norm (gram v a)
    _ ≤ ∑ r, ∑ s, ‖a r‖*‖a s‖*ε := by
      apply (norm_sum_le _ _).trans; apply sum_le_sum; intro r _
      apply (norm_sum_le _ _).trans; apply sum_le_sum; intro s _
      simp only [norm_mul,Complex.norm_conj]; gcongr; exact he _
    _ = _ := by simp only [←sum_mul,←mul_sum]; ring
theorem constantP (x : G N) : P (fun r=> if r=0 then 1 else 0) x=1 := by
  classical
  simp [P,ite_mul,ch]
theorem Psub (a b : G N → ℂ) (x : G N) : P (fun r=>a r-b r) x=P a x-P b x := by simp [P,sub_mul,sum_sub_distrib]
theorem absmean (f : G N → ℝ) {s : ℝ} (hs : 0 ≤ s) (h : E (fun x=>f x^2) ≤ s^2) :
    E (fun x=>|f x|) ≤ s := by
  have cs := sum_mul_sq_le_sq_mul_sq (R:=ℝ) (univ : Finset (G N)) (fun _=>1) (fun x=>|f x|)
  simp only [one_mul,one_pow,sq_abs,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one] at cs
  have pos := NeZero.pos N
  have nr : 0<(N:ℝ) := by exact_mod_cast pos
  unfold E at h ⊢
  rw [div_le_iff₀ nr] at h ⊢
  have := mul_le_mul_of_nonneg_left h nr.le
  apply le_of_sq_le_sq _ (mul_nonneg hs nr.le)
  nlinarith only [cs,this]
end
end PolynomialTransfer

namespace PolynomialTransfer
open Finset
noncomputable section
variable {ι : Type*} [Fintype ι]
theorem momentProduct (a b : ι → ℝ) (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i)
    {p D : ℝ} (hma : ∑ i, a i^p ≤ D) (hmb : ∑ i,b i^p ≤ D) :
    ∑ i, (a i*b i)^(p/2) ≤ D := by
  have term (i : ι) : (a i*b i)^(p/2) ≤ (a i^p+b i^p)/2 := by
    rw [Real.mul_rpow (ha i) (hb i)]
    have sq (x : ℝ) (hx : 0 ≤ x) : (x^(p/2))^2=x^p := by
      rw [←Real.rpow_mul_natCast hx]; congr 1 <;> push_cast <;> ring
    nlinarith [sq_nonneg (a i^(p/2)-b i^(p/2)),sq (a i) (ha i),sq (b i) (hb i)]
  have h := sum_le_sum (s:=univ) (fun i _ => term i)
  simp only [←sum_div,sum_add_distrib] at h; linarith
theorem weakMoment (X : ι → ℝ) (nn : ∀ i,0 ≤ X i) {q D s : ℝ} {k : ℕ}
    (hq : 0<q) (hq' : q<2) (hs : 0<s) (hs' : s ≤ 1) (hk : 4 ≤ (k:ℝ)*(2-q))
    (hm : ∑ i,X i^q ≤ D) :
    ∑ i, (if X i ≤ s^k then X i^2 else 0) ≤ s^4*D := by
  calc
    _ ≤ ∑ i, s^4*(X i)^q := by
      apply sum_le_sum; intro i _
      split_ifs with h
      · have xb : X i^(2-q) ≤ s^4 := calc
          _ ≤ (s^k)^(2-q) := Real.rpow_le_rpow (nn i) h (by linarith)
          _ = s^((k:ℝ)*(2-q)) := by rw [←Real.rpow_natCast_mul hs.le]
          _ ≤ _ := by rw [←Real.rpow_natCast s 4]; exact Real.rpow_le_rpow_of_exponent_ge hs hs' (by exact_mod_cast hk)
        calc
          _ = X i^(2-q)*X i^q := by rw [←Real.rpow_add' (nn i) (by linarith),sub_add_cancel]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_right xb (Real.rpow_nonneg (nn i) _)
      · exact mul_nonneg (by positivity) (Real.rpow_nonneg (nn i) _)
    _ ≤ _ := by rw [←mul_sum]; gcongr
theorem strongCount (X : ι → ℝ) (nn : ∀ i,0 ≤ X i) {q D t : ℝ}
    (hq : 0<q) (hq' : q ≤ 2) (ht : 0<t) (ht' : t ≤ 1) (hm : ∑ i,X i^q ≤ D) :
    ((univ.filter fun i=> t<X i).card : ℝ)*t^2 ≤ D := by
  let S := univ.filter fun i=>t<X i
  calc
    _ = ∑ _i ∈ S, t^2 := by simp [S]
    _ ≤ ∑ i ∈ S, X i^q := by
      apply sum_le_sum; intro i hi
      have gt := (mem_filter.mp hi).2
      calc
        _ ≤ t^q := by rw [←Real.rpow_natCast t 2]; apply Real.rpow_le_rpow_of_exponent_ge ht ht'; exact_mod_cast hq'
        _ ≤ _ := Real.rpow_le_rpow ht.le gt.le hq.le
    _ ≤ ∑ i, X i^q := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>Real.rpow_nonneg (nn i) _
    _ ≤ _ := hm
end
end PolynomialTransfer

namespace PolynomialTransfer
open Finset
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]
theorem corrError (b v : G N → ℝ) (mass : E b=1) {ε s : ℝ} (hs : 0<s)
    (fv : ∀ r, ‖F (fun x=>v x-1) r‖ ≤ ε) (e0 : 0 ≤ ε) (small : ε ≤ s^2)
    (b2 : (∑ r, ‖F b r‖^2) ≤ 1/s^2) :
    E (fun x=>(corr b v x-1)^2) ≤ s^2 := by
  let d := fun x=>v x-1
  have sub (x : G N) : corr b d x=corr b v x-1 := by
    simp only [corr,d,mul_sub,mul_one,Esub,mass]
  have v2 : E (fun x=>(corr b v x-1)^2) = ∑ r, ‖coeff b d r‖^2 := by
    rw [←parseP]; congr 1; funext x; rw [CorrP,sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [v2]
  calc
    _ ≤ ∑ r, ε^2*‖F b r‖^2 := by
      apply sum_le_sum; intro r _; simp only [coeff,norm_mul,Complex.norm_conj,mul_pow]; gcongr; exact fv _
    _ ≤ ε^2*(1/s^2) := by rw [←mul_sum]; gcongr
    _ ≤ s^2 := by rw [←mul_div_assoc,mul_one,div_le_iff₀ (by positivity),←sq]; exact pow_le_pow_left₀ e0 small 2
theorem corrBarrier (b g v : G N → ℝ) (mass : E b=1) (bn : ∀ x,0 ≤ b x)
    (hg : ∀ x,0 ≤ g x ∧ g x ≤ v x) {s : ℝ} (hs : 0 ≤ s)
    (energy : E (fun x=>(corr b v x-1)^2) ≤ s^2) :
    E (fun x=>(1-corr b g x)^2) ≤ 1-E g+s+s^2 := by
  let l := corr b v
  let k := corr b g
  have pt (x : G N) : (1-k x)^2 ≤ (1-k x)+|l x-1|+(l x-1)^2 := by
    have kn : 0 ≤ k x := Enonneg fun n=>mul_nonneg (bn n) (hg _).1
    have kl : k x ≤ l x := Emono fun n=>mul_le_mul_of_nonneg_left (hg _).2 (bn n)
    by_cases small : k x ≤ 1
    · nlinarith [mul_nonneg kn (sub_nonneg.mpr small),abs_nonneg (l x-1),sq_nonneg (l x-1)]
    · rw [abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr kl) (show 0 ≤ l x+k x-1 by linarith)]
  have h := Emono pt
  simp only [Eadd,Esub,Econst,k,Ecorr,mass,one_mul] at h
  have ah := absmean (fun x=>l x-1) hs energy
  dsimp [k,l] at *; linarith
theorem truncated (b f g u : G N → ℝ) (S : Finset (G N)) (h0 : 0∈S)
    (hf : ∀ x,0 ≤ f x ∧ f x ≤ u x) {ε W T : ℝ}
    (hu : ∀ r, ‖F (fun x=>u x-1) r‖ ≤ ε)
    (lone : (∑ r, ‖if r∈S then (if r=0 then (1:ℂ) else 0)-coeff b g r else 0‖) ≤ W)
    (e0 : 0 ≤ ε)
    (tail : ∑ r, (if r∈S then 0 else ‖F f r‖*‖F g r‖*‖F b r‖) ≤ T) :
    E f ≤ E (fun x=>(1-corr b g x)^2)+ε*W^2+2*(E (fun x=>f x*corr b g x)+T) := by
  classical
  let h := coeff b g
  let full := fun r : G N => (if r=0 then (1:ℂ) else 0)-h r
  let a := fun r=>if r∈S then full r else 0
  have pf (x : G N) : P full x=1-(corr b g x:ℂ) := by rw [show P full x = _ from Psub _ _ x, constantP,CorrP]
  have l2 : E (fun x=>‖P a x‖^2) ≤ E (fun x=>(1-corr b g x)^2) := by
    calc
      _ = _ := parseP a
      _ ≤ ∑ r, ‖full r‖^2 := by apply sum_le_sum; intro r _; by_cases hr : r∈S <;> simp [a,hr]
      _ = _ := by rw [←parseP]; congr 1; funext x; rw [pf,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have gm := gramBound u a hu
  have aw : (∑ r, ‖a r‖) ≤ W := lone
  have en := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _=>norm_nonneg _) aw 2) e0
  let d := fun r=>full r-a r
  have dx (x : G N) : P d x=1-(corr b g x:ℂ)-P a x := by rw [show P d x = _ from Psub _ _ x,pf]
  have dt : (C (fun x=>(f x:ℂ)*P d x)).re ≤ T := calc
    _ ≤ _ := Complex.re_le_norm _
    _ = _ := congrArg norm (pair f d)
    _ ≤ ∑ r, if r∈S then 0 else ‖F f r‖*‖F g r‖*‖F b r‖ := by
      apply (norm_sum_le _ _).trans; apply sum_le_sum; intro r _
      by_cases hr : r∈S
      · simp [d,a,hr]
      · have nz : r≠0 := fun eq=>hr (eq ▸ h0)
        simp [d,a,full,h,coeff,hr,nz,mul_comm,mul_left_comm]
    _ ≤ _ := tail
  have re (x : G N) : ((f x:ℂ)*P d x).re = f x*(1-(P a x).re)-f x*corr b g x := by rw [dx]; simp; ring
  rw [Cre] at dt
  simp_rw [re] at dt
  rw [Esub] at dt
  have point (x : G N) : f x ≤ u x*‖P a x‖^2+2*(f x*(1-(P a x).re)) := by
    have n := Complex.abs_re_le_norm (P a x)
    have a1 := sq_le_sq' (abs_le.mp n).1 (abs_le.mp n).2
    have h1 : 0 ≤ ‖P a x‖^2+1-2*(P a x).re := by nlinarith [sq_nonneg ((P a x).re-1)]
    nlinarith [mul_nonneg (hf x).1 h1,mul_le_mul_of_nonneg_right (hf x).2 (sq_nonneg ‖P a x‖)]
  have up := Emono point
  rw [Eadd,Emul] at up
  linarith
end
end PolynomialTransfer

namespace PolynomialTransfer
open Finset
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]
theorem spectrumBudgets (b f g : G N → ℝ) (bn : ∀ x,0 ≤ b x) (mass : E b=1)
    (gn : ∀ x,0 ≤ g x) (gm : E g ≤ 2)
    {q D s : ℝ} {k : ℕ} (hq : 0<q) (hq' : q<2) (d1 : 1 ≤ D)
    (hs : 0<s) (hs' : s ≤ 1) (hk : 4 ≤ (k:ℝ)*(2-q))
    (hm : ∑ r, (‖F f r‖*‖F g r‖)^q ≤ D)
    (b2 : (∑ r, ‖F b r‖^2) ≤ 1/s^2) :
    ∃ S : Finset (G N), 0 ∈ S ∧
      (∑ r, ‖if r∈S then (if r=0 then (1:ℂ) else 0)-coeff b g r else 0‖) ≤ 3+2*D/(s^k)^2 ∧
      (∑ r, if r∈S then 0 else ‖F f r‖*‖F g r‖*‖F b r‖) ≤ D*s := by
  classical
  let X := fun r=> ‖F f r‖*‖F g r‖
  let t := s^k
  have tp : 0<t := pow_pos hs _
  have t1 : t ≤ 1 := pow_le_one₀ hs.le hs'
  let U := univ.filter fun r=>t<X r
  let S := insert 0 U
  have nn (r) : 0 ≤ X r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have co := strongCount X nn hq hq'.le tp t1 hm
  have cs : (U.card:ℝ) ≤ D/t^2 := (le_div_iff₀ (sq_pos_of_pos tp)).2 co
  have cb (r) : ‖coeff b g r‖ ≤ 2 := by
    simp only [coeff,norm_mul,Complex.norm_conj]
    have h := (boundF b bn r).trans_eq mass
    nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (F g r)), (boundF g gn r).trans gm]
  refine ⟨S,mem_insert_self ..,?_,?_⟩
  · have pt (r : G N) :
        ‖if r∈S then (if r=0 then (1:ℂ) else 0)-coeff b g r else 0‖ ≤
        (if r=0 then (3:ℝ) else 0)+(if r∈U then 2 else 0) := by
      by_cases rz : r=0
      · subst r; simp only [S,mem_insert, true_or,ite_true]
        have := norm_sub_le (1:ℂ) (coeff b g 0)
        simp only [norm_one] at this
        split_ifs <;> linarith [cb 0]
      · by_cases hr : r∈U <;> simp [S,rz,hr,cb]
    have h := sum_le_sum (s:=univ) fun r _=>pt r
    simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at h
    have su : (∑ r : G N, if r∈U then (2:ℝ) else 0) = U.card*2 := by simp
    rw [su] at h
    rw [mul_div_assoc]; dsimp [t] at cs; linarith
  · let Y := fun r=> if r∈S then 0 else X r
    have yp (r) : Y r^2 ≤ (if X r ≤ t then X r^2 else 0) := by
      by_cases hr : r∈S
      · by_cases hh : X r ≤ t <;> simp [Y,hr,hh,sq_nonneg]
      · have sm : X r ≤ t := by
          by_contra! bad; apply hr; exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,bad⟩)
        simp [Y,hr,sm]
    have yy := (sum_le_sum (s:=univ) fun r _=>yp r).trans (weakMoment X nn hq hq' hs hs' hk hm)
    have sq := sum_mul_sq_le_sq_mul_sq (R:=ℝ) univ Y (fun r=>‖F b r‖)
    have prod := mul_le_mul yy b2 (sum_nonneg fun _ _=>sq_nonneg _) (mul_nonneg (by positivity) (by linarith))
    have e : s^4*D*(1/s^2)=D*s^2 := by field_simp <;> ring
    rw [e] at prod
    have aux : (∑ r, Y r*‖F b r‖) ≤ D*s := by
      apply le_of_sq_le_sq _ (mul_nonneg (by linarith) hs.le)
      nlinarith [mul_nonneg (show 0 ≤ D*(D-1) by nlinarith) (sq_nonneg s)]
    simpa only [Y,X,ite_mul,zero_mul] using aux
end
end PolynomialTransfer

namespace PolynomialTransfer
open Finset
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]
set_option maxHeartbeats 1400000 in
theorem expForm (f : G N → ℝ) (r : G N) : F f r =
    (∑ x : ZMod N, (f x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ) := by
  unfold F C; apply congrArg (fun z : ℂ => z/(N:ℂ)); apply sum_congr rfl; intro x _; apply congrArg (fun z : ℂ => (f x:ℂ)*z)
  calc
    _ = ZMod.stdAddChar ((-((r*x).val:ℤ) : ℤ) : ZMod N) := by simp [ch]
    _ = _ := by rw [ZMod.stdAddChar_coe]; push_cast; congr 1; ring
theorem badWeights (f g : G N → ℝ) {δ η s : ℝ} (hs : 0<s) (sη : s^2 ≤ η)
    (bad : η*N < ((univ.filter fun n=> conv f g n < δ^3/1000).card:ℝ)) :
    ∃ b : G N → ℝ, (∀ x,0 ≤ b x) ∧ E b=1 ∧ (∑ r, ‖F b r‖^2) ≤ 1/s^2 ∧
      E (fun x=> f x*corr b g x) ≤ δ^3/1000 := by
  classical
  let B := univ.filter fun n=> conv f g n < δ^3/1000
  have nr : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have card : 0<(B.card:ℝ) := lt_of_le_of_lt (mul_nonneg ((sq_nonneg s).trans sη) nr.le) bad
  let b := fun x=>if x∈B then (N:ℝ)/B.card else 0
  have bn (x) : 0 ≤ b x := by dsimp [b]; split_ifs <;> positivity
  have mass : E b=1 := by simp [E,b,NeZero.ne (N:ℝ),ne_of_gt card]; field_simp
  have cap (x) : b x ≤ 1/s^2 := by
    dsimp [b]; split_ifs
    · apply (div_le_div_iff₀ card (sq_pos_of_pos hs)).2
      nlinarith [mul_le_mul_of_nonneg_right sη nr.le,show η*N < (B.card:ℝ) from bad]
    · positivity
  refine ⟨b,bn,mass,?_,?_⟩
  · rw [parseF]
    have h := Emono (f:=fun x=>b x^2) (g:=fun x=>(1/s^2)*b x) (fun x=> by rw [sq]; exact mul_le_mul_of_nonneg_right (cap x) (bn x))
    simpa only [Emul,mass,mul_one] using h
  · rw [corrPair]
    have pt (n : G N) : b n*conv f g n ≤ (δ^3/1000)*b n := by
      by_cases h : n∈B
      · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (mem_filter.mp h).2.le (bn n)
      · simp [b,h]
    simpa only [Emul,mass,mul_one] using Emono pt
set_option maxHeartbeats 2000000 in
theorem mainBound {p M : ℝ} (p2 : 2<p) (p4 : p<4) (m1 : 1 ≤ M) :
    ∃ c K : ℝ, 0<c ∧ 0<K ∧ ∀ δ η : ℝ, 0<δ → δ ≤ 1 → 0<η → η ≤ 1 →
    ∀ (N : ℕ) [NeZero N] (f g u v : G N → ℝ),
    (∀ x,0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ E f+E g →
    (∑ r, ‖F f r‖^p) ≤ M^p → (∑ r, ‖F g r‖^p) ≤ M^p →
    (∀ r, ‖F (fun x=>u x-1) r‖ ≤ c*(δ*η)^K ∧ ‖F (fun x=>v x-1) r‖ ≤ c*(δ*η)^K) →
    ((univ.filter (fun n=> conv f g n < δ^3/1000)).card:ℝ) ≤ η*N := by
  classical
  let D := 10+M^p
  have mp : 0 ≤ M^p := Real.rpow_nonneg (by linarith) _
  have d10 : 10 ≤ D := by dsimp [D]; linarith
  have dpos : 0<D := by linarith
  have qlt : 0<2-p/2 := by linarith
  obtain ⟨k,kk⟩ := exists_nat_ge (4/(2-p/2))
  have gain : 4 ≤ (k:ℝ)*(2-p/2) := (div_le_iff₀ qlt).mp kk
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
  have hm := momentProduct (fun r=>‖F f r‖) (fun r=>‖F g r‖) (fun _=>norm_nonneg _) (fun _=>norm_nonneg _) ff fg
  obtain ⟨S,h0,lone,tail⟩ := spectrumBudgets b f g bn mass (fun x=>(dom x).2.2.1) gm
    (q:=p/2) (D:=D) (by linarith) (by linarith) (by linarith) sp s1 gain
    (hm.trans (by dsimp [D]; linarith)) b2
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
end PolynomialTransfer

theorem Conjectures.Goldbach.PolynomialFourierTransference :
by
  classical
  exact ∀ p M : ℝ, 2 < p → p < 4 → 1 ≤ M → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ δ η : ℝ, 0 < δ → δ ≤ 1 → 0 < η → η ≤ 1 →
    ∀ (N : ℕ) [NeZero N], ∀ f g u v : ZMod N → ℝ,
    let avg := fun h : ZMod N → ℝ => (∑ x, h x)/(N : ℝ)
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ avg f + avg g →
    (∑ r : ZMod N, ‖ft f r‖^p) ≤ M^p → (∑ r : ZMod N, ‖ft g r‖^p) ≤ M^p →
    (∀ r, ‖ft (fun x => u x-1) r‖ ≤ c*(δ*η)^K ∧ ‖ft (fun x => v x-1) r‖ ≤ c*(δ*η)^K) →
    ((Finset.univ.filter (fun n : ZMod N => avg (fun x => f x*g (n-x)) < δ^3/1000)).card : ℝ) ≤ η*(N : ℝ) := by
  classical
  intro p M hp hP hM
  obtain ⟨c,K,hc,hK,h⟩ := PolynomialTransfer.mainBound hp hP hM
  refine ⟨c,K,hc,hK,?_⟩
  intro δ η hd hD he hE N inst f g u v
  dsimp only
  simpa only [PolynomialTransfer.expForm,PolynomialTransfer.conv,PolynomialTransfer.E] using
    h δ η hd hD he hE N f g u v
