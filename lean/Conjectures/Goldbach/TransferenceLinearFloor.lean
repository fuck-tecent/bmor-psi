import Mathlib
import Conjectures.Goldbach.PolynomialFourierTransference

/-! The bad-set test from PolynomialFourierTransference, with a scaled residual.
Taking ρ = 1 - δ/4 creates a quadratic surplus, which pays for all spectral
truncation errors while retaining the requested linear convolution floor.
The badWeights proof and the parameter-selection structure adapt the Apache-2.0
proof in https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4281. -/
namespace LinearFloorTransfer
open PolynomialTransfer Finset
open scoped ComplexConjugate BigOperators
noncomputable section
variable {N : ℕ} [NeZero N]

theorem Fmul (a : ℝ) (g : G N → ℝ) (r : G N) :
    F (fun x => a*g x) r = (a:ℂ)*F g r := by
  simp only [F, Complex.ofReal_mul, mul_assoc]
  exact Cmul _ _

theorem corrMul (a : ℝ) (b g : G N → ℝ) (x : G N) :
    corr b (fun y => a*g y) x = a*corr b g x := by
  unfold corr
  simp_rw [show ∀ n, b n*(a*g (n-x)) = a*(b n*g (n-x)) by intro n; ring]
  exact Emul _ _

theorem badWeights (f g : G N → ℝ) {θ η s : ℝ} (hs : 0<s) (sη : s^2 ≤ η)
    (bad : η*N < ((univ.filter fun n => conv f g n < θ).card:ℝ)) :
    ∃ b : G N → ℝ, (∀ x,0 ≤ b x) ∧ E b=1 ∧ (∑ r, ‖F b r‖^2) ≤ 1/s^2 ∧
      E (fun x => f x*corr b g x) ≤ θ := by
  classical
  let B := univ.filter fun n => conv f g n < θ
  have nr : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have card : 0<(B.card:ℝ) := lt_of_le_of_lt (mul_nonneg ((sq_nonneg s).trans sη) nr.le) bad
  let b := fun x => if x∈B then (N:ℝ)/B.card else 0
  have bn (x) : 0 ≤ b x := by dsimp [b]; split_ifs <;> positivity
  have mass : E b=1 := by simp [E,b,NeZero.ne (N:ℝ),ne_of_gt card]; field_simp
  have cap (x) : b x ≤ 1/s^2 := by
    dsimp [b]; split_ifs
    · apply (div_le_div_iff₀ card (sq_pos_of_pos hs)).2
      nlinarith [mul_le_mul_of_nonneg_right sη nr.le,show η*N < (B.card:ℝ) from bad]
    · positivity
  refine ⟨b,bn,mass,?_,?_⟩
  · rw [parseF]
    have h := Emono (f:=fun x => b x^2) (g:=fun x => (1/s^2)*b x)
      (fun x => by rw [sq]; exact mul_le_mul_of_nonneg_right (cap x) (bn x))
    simpa only [Emul,mass,mul_one] using h
  · rw [corrPair]
    have pt (n : G N) : b n*conv f g n ≤ θ*b n := by
      by_cases h : n∈B
      · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (mem_filter.mp h).2.le (bn n)
      · simp [b,h]
    simpa only [Emul,mass,mul_one] using Emono pt

theorem scaledBarrier (b g v : G N → ℝ) (mass : E b=1) (bn : ∀ x,0 ≤ b x)
    (hg : ∀ x,0 ≤ g x ∧ g x ≤ v x) {s : ℝ} (hs : 0 ≤ s)
    (energy : E (fun x => (corr b v x-1)^2) ≤ s^2) (ρ : ℝ) :
    E (fun x => (1-corr b (fun y => ρ*g y) x)^2) ≤
      1-(2*ρ-ρ^2)*E g+ρ^2*(s+s^2) := by
  have h := mul_le_mul_of_nonneg_left (corrBarrier b g v mass bn hg hs energy) (sq_nonneg ρ)
  have eq : E (fun x => (1-corr b (fun y => ρ*g y) x)^2) =
      ρ^2*E (fun x => (1-corr b g x)^2)+(1-ρ^2)-2*ρ*(1-ρ)*E g := by
    calc
      _ = E (fun x => ρ^2*(1-corr b g x)^2+(1-ρ^2)-2*ρ*(1-ρ)*corr b g x) := by
        congr 1; funext x; rw [corrMul]; ring
      _ = _ := by rw [Esub,Eadd,Emul,Econst,Emul,Ecorr,mass,one_mul]
  rw [eq]
  nlinarith only [h]

set_option maxHeartbeats 2400000 in
 theorem mainBound {p M : ℝ} (p2 : 2<p) (p4 : p<4) (m1 : 1 ≤ M) :
    ∃ c K : ℝ, 0<c ∧ 0<K ∧ ∀ δ η : ℝ, 0<δ → δ ≤ 1 → 0<η → η ≤ 1 →
    ∀ (N : ℕ) [NeZero N] (f g u v : G N → ℝ),
    (∀ x,0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ E f+E g →
    (∑ r, ‖F f r‖^p) ≤ M^p → (∑ r, ‖F g r‖^p) ≤ M^p →
    (∀ r, ‖F (fun x => u x-1) r‖ ≤ c*(δ*η)^K ∧ ‖F (fun x => v x-1) r‖ ≤ c*(δ*η)^K) →
    ((univ.filter (fun n => conv f g n < δ/2)).card:ℝ) ≤ η*N := by
  classical
  let D := 10+M^p
  have mp : 0 ≤ M^p := Real.rpow_nonneg (by linarith) _
  have d10 : 10 ≤ D := by dsimp [D]; linarith
  have dpos : 0<D := by linarith
  have qlt : 0<2-p/2 := by linarith
  obtain ⟨k,kk⟩ := exists_nat_ge (4/(2-p/2))
  have gain : 4 ≤ (k:ℝ)*(2-p/2) := (div_le_iff₀ qlt).mp kk
  let L := 4*k+4
  let a : ℝ := 1/(1000*D)
  have ap : 0<a := by dsimp [a]; positivity
  refine ⟨a^L,((2*L:ℕ):ℝ),pow_pos ap _,by dsimp [L]; positivity,?_⟩
  intro δ η dp d1 ep e1 n inst f g u v dom size ff fg dec
  let s := a*(δ*η)^2
  let t := s^k
  let ε := s^L
  let ρ := 1-δ/4
  let g' := fun x => ρ*g x
  have lp : 0<ρ := by dsimp [ρ]; linarith
  have l1 : ρ ≤ 1 := by dsimp [ρ]; linarith
  have sp : 0<s := mul_pos ap (sq_pos_of_pos (mul_pos dp ep))
  have ds : 1000*D*s=(δ*η)^2 := by dsimp [s,a]; field_simp
  have dsle : 1000*D*s ≤ δ^2 := by
    rw [ds,mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg δ) (pow_le_one₀ ep.le e1)
  have sη : s ≤ η := calc
    s ≤ 1000*D*s := by nlinarith [mul_nonneg (show 0 ≤ 1000*D-1 by linarith) sp.le]
    _ = (δ*η)^2 := ds
    _ ≤ δ*η := by
      have h : δ*η ≤ 1 := (mul_le_of_le_one_right dp.le e1).trans d1
      nlinarith [mul_nonneg (mul_nonneg dp.le ep.le) (sub_nonneg.mpr h)]
    _ ≤ η := mul_le_of_le_one_left ep.le d1
  have s1 : s ≤ 1 := sη.trans e1
  have tp : 0<t := pow_pos sp k
  have t1 : t ≤ 1 := pow_le_one₀ sp.le s1
  have ee : ε=t^4*s^4 := by simp only [ε,L,t,pow_add,pow_mul]; ring_nf
  have εpos : 0 ≤ ε := (pow_pos sp _).le
  have es : ε ≤ s^2 := by
    rw [ee]; calc
      _ ≤ 1*s^4 := mul_le_mul_of_nonneg_right (pow_le_one₀ tp.le t1) (by positivity)
      _ ≤ _ := by rw [one_mul]; exact pow_le_pow_of_le_one sp.le s1 (by omega)
  have ε1 : ε ≤ 1 := es.trans (pow_le_one₀ sp.le s1)
  have eh : a^L*(δ*η)^((2*L:ℕ):ℝ)=ε := by
    rw [Real.rpow_natCast,pow_mul,←mul_pow]
  simp only [eh] at dec
  have gm : E g ≤ 2 := by
    have h := (dec 0).2
    rw [Fzero,Complex.norm_real,Real.norm_eq_abs,Esub,Econst] at h
    have vv := (abs_le.mp h).2
    have gv := Emono (fun x => (dom x).2.2.2)
    linarith
  have gn : 0 ≤ E g := Enonneg fun x => (dom x).2.2.1
  have gm' : E g' ≤ 2 := by
    change E (fun x => ρ*g x) ≤ 2
    rw [Emul]
    exact (mul_le_of_le_one_left gn l1).trans gm
  by_contra! too
  obtain ⟨b,bn,mass,b2,low⟩ := badWeights f g sp
    ((show s^2 ≤ s by nlinarith only [mul_nonneg sp.le (sub_nonneg.mpr s1)]).trans sη) too
  have hm := momentProduct (fun r => ‖F f r‖) (fun r => ‖F g r‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ff fg
  have hmg : ∑ r, (‖F f r‖*‖F g' r‖)^(p/2) ≤ D := by
    refine (sum_le_sum (fun r _ => ?_)).trans (hm.trans (by dsimp [D]; linarith))
    apply Real.rpow_le_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ (by linarith)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    change ‖F (fun x => ρ*g x) r‖ ≤ ‖F g r‖
    rw [Fmul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos lp]
    exact mul_le_of_le_one_left (norm_nonneg _) l1
  obtain ⟨S,h0,lone,tail⟩ := spectrumBudgets b f g' bn mass
    (fun x => mul_nonneg lp.le (dom x).2.2.1) gm'
    (q:=p/2) (D:=D) (by linarith) (by linarith) (by linarith) sp s1 gain hmg b2
  have cr := corrError b v mass sp (fun r => (dec r).2) εpos es b2
  have bar := scaledBarrier b g v mass bn (fun x => (dom x).2.2) sp.le cr ρ
  have cut := truncated b f g' u S h0 (fun x => ⟨(dom x).1,(dom x).2.1⟩)
    (fun r => (dec r).1) lone εpos tail
  have low' : E (fun x => f x*corr b g' x) ≤ ρ*(δ/2) := by
    have eq : E (fun x => f x*corr b g' x) = ρ*E (fun x => f x*corr b g x) := by
      change E (fun x => f x*corr b (fun y => ρ*g y) x) = _
      simp_rw [corrMul]
      rw [show (fun x => f x*(ρ*corr b g x)) = (fun x => ρ*(f x*corr b g x)) by funext x; ring, Emul]
    rw [eq]
    exact mul_le_mul_of_nonneg_left low lp.le
  have cost : ε*(3+2*D/t^2)^2 ≤ δ^2/100 := by
    have id : ε*(3+2*D/t^2)^2=(s^2*(3*t^2+2*D))^2 := by rw [ee]; field_simp <;> ring
    rw [id]
    have l : s^2*(3*t^2+2*D) ≤ s*(5*D) := by
      apply mul_le_mul _ _ (by positivity) sp.le
      · nlinarith only [mul_nonneg sp.le (sub_nonneg.mpr s1)]
      · nlinarith [show t^2 ≤ 1 from pow_le_one₀ tp.le t1]
    have l' : s^2*(3*t^2+2*D) ≤ δ^2/100 := by nlinarith only [l,dsle]
    have nn : 0 ≤ s^2*(3*t^2+2*D) := by positivity
    have dd : δ^2 ≤ 1 := pow_le_one₀ dp.le d1
    nlinarith only [l', mul_nonneg nn (show 0 ≤ 1-s^2*(3*t^2+2*D) by linarith only [l', dd])]
  have sδ : s ≤ δ^2/1000 := by
    nlinarith only [dsle, mul_nonneg (show 0 ≤ D-1 by linarith only [d10]) sp.le]
  have Ds : D*s ≤ δ^2/1000 := by nlinarith only [dsle]
  have err : ρ^2*(s+s^2) ≤ 2*s := calc
    _ ≤ 1*(s+s^2) := mul_le_mul_of_nonneg_right (pow_le_one₀ lp.le l1) (by positivity)
    _ ≤ _ := by nlinarith only [mul_nonneg sp.le (sub_nonneg.mpr s1)]
  change E f ≤ _ + ε*(3+2*D/t^2)^2+2*(_+D*s) at cut
  change E (fun x => (1-corr b g' x)^2) ≤ _ at bar
  have combined : δ ≤ (1-ρ)^2*E g+ρ*δ+2*s+δ^2/100+2*D*s := by
    nlinarith only [size,cut,bar,low',cost,err]
  have gap : (1-ρ)^2*E g ≤ δ^2/8 := by
    have h := mul_le_mul_of_nonneg_left gm (sq_nonneg (1-ρ))
    dsimp [ρ] at h ⊢
    nlinarith only [h]
  have ld : ρ*δ=δ-δ^2/4 := by dsimp [ρ]; ring
  rw [ld] at combined
  nlinarith only [combined,gap,sδ,Ds,sq_pos_of_pos dp]
end
end LinearFloorTransfer

 theorem Conjectures.Goldbach.TransferenceLinearFloor :
by
  classical
  exact ∀ p M : ℝ, 2 < p → p < 4 → 1 ≤ M → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ δ η : ℝ, 0 < δ → δ ≤ 1 → 0 < η → η ≤ 1 →
    ∀ (N : ℕ) [NeZero N], ∀ f g u v : ZMod N → ℝ,
    let avg := fun h : ZMod N → ℝ => (∑ x, h x)/(N : ℝ)
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ avg f + avg g →
    (∑ r : ZMod N, ‖ft f r‖^p) ≤ M^p → (∑ r : ZMod N, ‖ft g r‖^p) ≤ M^p →
    (∀ r, ‖ft (fun x => u x-1) r‖ ≤ c*(δ*η)^K ∧ ‖ft (fun x => v x-1) r‖ ≤ c*(δ*η)^K) →
    ((Finset.univ.filter (fun n : ZMod N => avg (fun x => f x*g (n-x)) < δ/2)).card : ℝ) ≤ η*(N : ℝ) := by
  classical
  intro p M hp hP hM
  obtain ⟨c,K,hc,hK,h⟩ := LinearFloorTransfer.mainBound hp hP hM
  refine ⟨c,K,hc,hK,?_⟩
  intro δ η hd hD he hE N inst f g u v
  dsimp only
  simpa only [PolynomialTransfer.expForm,PolynomialTransfer.conv,PolynomialTransfer.E] using
    h δ η hd hD he hE N f g u v
