import Mathlib

/- Background sources are credited in the sections that use them. The Vaughan
hyperbola change of variables and the geometric estimates adapt openai/math
at revision 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
The Ramanujan-sum identities adapt DFQDZZ's goldbach-proofs PR #316
at e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). -/

section

open Filter Topology

namespace CornerFour

private theorem hpLog (n : ℕ) (hn : 2≤n) :
    (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
  have hb := Real.natLog_le_logb (n+2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2:ℝ)≤n := by exact_mod_cast hn
  have hh : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤(n:ℝ)-2 by linarith) (show 0≤(n:ℝ)+1 by linarith)]
  have hl := Real.log_le_log (by positivity : 0<(n:ℝ)+2) hh
  rw [Real.log_pow] at hl
  norm_num at hl
  have hx' := (le_div_iff₀ (by linarith : 0<Real.log 2)).mp hb
  have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_)
  linarith only [hl,hx',hm]

noncomputable section
def cutU (n : ℕ) := ⌊(n:ℝ)^(1/16:ℝ)⌋₊
def cutT (n : ℕ) := ⌊(n:ℝ)^(2/3:ℝ)⌋₊
def cutM (n : ℕ) := ⌊(n:ℝ)^(2/5:ℝ)⌋₊
def cutB (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def cutH (n : ℕ) := 256 * cutB n * (Nat.log 2 (n+2))^2

theorem scaleAvailable : ∀ᶠ n : ℕ in atTop,
    0<n ∧ 1≤cutT n ∧ 1≤cutB n ∧ 0<cutH n ∧ cutB n≤cutM n ∧ cutM n≤n ∧
    n/(cutT n+1)*cutU n≤cutM n ∧ 4*cutH n*cutM n≤n := by
  have hlim : Tendsto (fun n : ℕ=>(Real.log n)^2/(n:ℝ)^(4/15:ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2:ℕ) (show (0:ℝ)<4/15 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast,Function.comp_def] using h.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop 2,hlim.eventually_lt_const (show (0:ℝ)<1/16384 by norm_num)] with n hn hlog
  have hn' : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hB : 1≤cutB n := Nat.le_floor (Real.one_le_rpow hn' (by norm_num))
  have hlog2 : 1≤Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hH : 0<cutH n := Nat.mul_pos (Nat.mul_pos (by decide) hB) (pow_pos hlog2 _)
  have hbc : (cutB n:ℝ)≤(n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hmc : (cutM n:ℝ)≤(n:ℝ)^(2/5:ℝ) := Nat.floor_le (by positivity)
  have hUc : (cutU n:ℝ)≤(n:ℝ)^(1/16:ℝ) := Nat.floor_le (by positivity)
  refine ⟨by omega,Nat.le_floor (Real.one_le_rpow hn' (by norm_num)),hB,hH,
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/3:ℝ)≤2/5)),?_,?_,?_⟩
  · apply Nat.floor_le_of_le
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (show (2/5:ℝ)≤1 by norm_num)
  · apply Nat.le_floor
    push_cast
    have ht := Nat.lt_floor_add_one ((n:ℝ)^(2/3:ℝ))
    change (n:ℝ)^(2/3:ℝ) < (cutT n:ℝ)+1 at ht
    have hd : (n/(cutT n+1):ℕ)*(cutT n+1)≤n := Nat.div_mul_le_self ..
    have hd' : ((n/(cutT n+1):ℕ):ℝ)*((cutT n:ℝ)+1)≤n := by exact_mod_cast hd
    have hw : ((n/(cutT n+1):ℕ):ℝ)≤(n:ℝ)^(1/3:ℝ) := by
      apply (le_of_mul_le_mul_right (a:=(n:ℝ)^(2/3:ℝ)) · (by positivity))
      calc
        _ ≤ ((n/(cutT n+1):ℕ):ℝ)*((cutT n:ℝ)+1) := by gcongr
        _ ≤ _ := hd'
        _ = _ := by rw [← Real.rpow_add hn0]; norm_num
    calc
      _ ≤ (n:ℝ)^(1/3:ℝ)*(n:ℝ)^(1/16:ℝ) := mul_le_mul hw hUc (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)
      _ ≤ _ := by rw [← Real.rpow_add hn0]; exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  · have hs : (Nat.log 2 (n+2):ℝ)^2 ≤ (4*Real.log n)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hpLog n hn) _
    have hz := (div_lt_iff₀ (Real.rpow_pos_of_pos hn0 (4/15:ℝ))).mp hlog
    have h16384 : (16384:ℝ)*(Real.log n)^2≤(n:ℝ)^(4/15:ℝ) := by linarith
    have bound : 4*(256*(cutB n:ℝ)*(Nat.log 2 (n+2):ℝ)^2)*(cutM n:ℝ)≤n := calc
      _ ≤ 4*(256*((n:ℝ)^(1/3:ℝ))*(4*Real.log n)^2)*((n:ℝ)^(2/5:ℝ)) := by gcongr
      _ = (16384*(Real.log n)^2)*((n:ℝ)^(1/3:ℝ)*(n:ℝ)^(2/5:ℝ)) := by ring
      _ ≤ ((n:ℝ)^(4/15:ℝ))*((n:ℝ)^(1/3:ℝ)*(n:ℝ)^(2/5:ℝ)) := by gcongr
      _ = n := by rw [← Real.rpow_add hn0,← Real.rpow_add hn0]; norm_num
    exact_mod_cast bound

end
end CornerFour

end

section

namespace CornerFour
open Finset
noncomputable section

def harmonicBox (M : ℕ) : ℝ := ∑ d ∈ Icc 1 M,(d:ℝ)⁻¹
def invHit (q u : ℕ) : ℝ := if q∣u then (u:ℝ)⁻¹ else 0

theorem invHit_nonneg (q u : ℕ) : 0≤ invHit q u := by unfold invHit; split_ifs <;> positivity
theorem harmonicBox_nonneg (M : ℕ) : 0≤harmonicBox M := sum_nonneg fun _ _ => by positivity

theorem hitHarmonic (M q : ℕ) (hq : 0<q) :
    (∑ u ∈ Icc 1 M,invHit q u) ≤ (q:ℝ)⁻¹*harmonicBox M := by
  let S := Icc 1 (M/q)
  have hs : (Icc 1 M).filter (q∣·) = S.image (fun k => q*k) := by
    ext u
    constructor
    · intro h
      obtain ⟨huk,huq⟩ := mem_filter.mp h
      obtain ⟨k,rfl⟩ := huq
      obtain ⟨h1,h2⟩ := mem_Icc.mp huk
      exact mem_image.mpr ⟨k,mem_Icc.mpr ⟨by cases k <;> simp_all,
        (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using h2)⟩,rfl⟩
    · intro h
      obtain ⟨k,hk,rfl⟩ := mem_image.mp h
      obtain ⟨hk1,hk2⟩ := mem_Icc.mp hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq hk1,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hk2⟩,dvd_mul_right _ _⟩
  unfold invHit
  rw [←sum_filter,hs,sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  simp only [Nat.cast_mul,mul_inv,←mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self _ _)) (fun _ _ _ => by positivity)

theorem gcdHarmonic (M n : ℕ) (hn : 0<n) :
    (∑ q ∈ Icc 1 M, (q.gcd n:ℝ)*(q:ℝ)⁻¹) ≤ n.divisors.card*harmonicBox M := by
  have hb (q : ℕ) (hq : 0<q) :
      (q.gcd n:ℝ)*(q:ℝ)⁻¹ ≤ ∑ d ∈ n.divisors,(d:ℝ)*invHit d q := by
    have hg : q.gcd n ∈ n.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hn.ne'⟩
    have hsingle := single_le_sum (f:=fun d : ℕ => (d:ℝ)*invHit d q)
      (fun d hd => mul_nonneg (Nat.cast_nonneg _) (invHit_nonneg _ _)) hg
    simpa [invHit,Nat.gcd_dvd_left] using hsingle
  calc
    _ ≤ ∑ q ∈ Icc 1 M, ∑ d ∈ n.divisors,(d:ℝ)*invHit d q := sum_le_sum fun _ h => hb _ (mem_Icc.mp h).1
    _ = ∑ d ∈ n.divisors,(d:ℝ)*∑ q ∈ Icc 1 M,invHit d q := by rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ _ ∈ n.divisors,harmonicBox M := by
      apply sum_le_sum; intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdR : (d:ℝ)≠0 := by exact_mod_cast hd0.ne'
      calc
        _ ≤ (d:ℝ)*((d:ℝ)⁻¹*harmonicBox M) := mul_le_mul_of_nonneg_left (hitHarmonic M d hd0) (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp

theorem doubleDivisorBound (M : ℕ) (T : ℕ→ℝ) (hT : ∀ q,0≤T q) :
    (∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 M, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤
      (∑ q ∈ Icc 1 M,T q*(q:ℝ)⁻¹^2)*(harmonicBox M)^2 := by
  let S := Icc 1 M
  have he (u v : ℕ) (hu : u∈S) (hv : v∈S) :
      (∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹ =
        ∑ q ∈ S,T q*invHit q u*invHit q v := by
    have hu0 := (mem_Icc.mp hu).1
    have hg0 : 0<u.gcd v := Nat.gcd_pos_of_pos_left _ hu0
    have hdiv : (u.gcd v).divisors = S.filter (fun q => q∣u ∧ q∣v) := by
      ext q
      simp only [S,Nat.mem_divisors,mem_filter,mem_Icc,Nat.dvd_gcd_iff,ne_eq, Nat.ne_of_gt hg0,not_false_eq_true,and_true]
      constructor
      · intro h; exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hu0,(Nat.le_of_dvd hu0 h.1).trans (mem_Icc.mp hu).2⟩,h⟩
      · exact And.right
    rw [hdiv,sum_filter,sum_mul,sum_mul]
    apply sum_congr rfl
    intro q hq
    by_cases ha : q∣u <;> by_cases hb : q∣v <;> simp [invHit,ha,hb]
  calc
    _ = ∑ u ∈ S,∑ v ∈ S,∑ q ∈ S,T q*invHit q u*invHit q v := by
      exact sum_congr rfl fun u hu => sum_congr rfl fun v hv => he u v hu hv
    _ = ∑ q ∈ S,T q*(∑ u ∈ S,invHit q u)^2 := by
      trans ∑ u ∈ S, ∑ q ∈ S,∑ v ∈ S,T q*invHit q u*invHit q v
      · exact sum_congr rfl fun _ _ => sum_comm
      · rw [sum_comm]
        apply sum_congr rfl; intro q hq
        simp only [sq,←mul_sum,←sum_mul]
        ring
    _ ≤ ∑ q ∈ S, T q*((q:ℝ)⁻¹*harmonicBox M)^2 := by
      apply sum_le_sum; intro q hq
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun u _ => invHit_nonneg q u)
        (hitHarmonic M q (mem_Icc.mp hq).1) 2) (hT q)
    _ = _ := by rw [sum_mul]; apply sum_congr rfl; intro q _; ring

end
end CornerFour

end

section

namespace CornerFour
open Finset
noncomputable section

def cornerLog (n : ℕ) : ℝ := 1+Real.log ((n:ℝ)+2)
def cornerCost (n M B H u v : ℕ) : ℝ :=
  (cornerLog n)^2 + (M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) +
  (n:ℝ)/((u:ℝ)*v) *
    ((∑ q ∈ (u.gcd v).divisors.filter (·≤B),(q.gcd n:ℝ)*q/H) +
     ∑ q ∈ (u.gcd v).divisors.filter (B<·),(q.gcd n:ℝ))
theorem cornerCost_nonneg (n M B H u v : ℕ) : 0≤cornerCost n M B H u v := by
  unfold cornerCost; positivity

set_option maxHeartbeats 1000000 in
theorem cornerCost_sum (n M B H : ℕ) (hn : 0<n) (hB : 0<B) (hH : B≤H) :
    (∑ u ∈ Icc 1 M,∑ v ∈ Icc 1 M,cornerCost n M B H u v) ≤
     (M:ℝ)^2*(cornerLog n)^2 + (M:ℝ)^2*(harmonicBox M)^2 +
      ((n:ℝ)/B)*n.divisors.card*(harmonicBox M)^3 := by
  let X := Icc 1 M
  let D := fun (f : ℕ→ℝ) (u v : ℕ) => (∑ q ∈ (u.gcd v).divisors,f q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹
  let f := fun q : ℕ => (q:ℝ)^2
  let t := fun q : ℕ => (q.gcd n:ℝ)*q
  have hbR : 0<(B:ℝ) := by exact_mod_cast hB
  have hHH : (B:ℝ)≤H := by exact_mod_cast hH
  have HA (u v : ℕ) (hu : u∈X) :
      cornerCost n M B H u v ≤ (cornerLog n)^2+(M:ℝ)*D f u v + ((n:ℝ)/B)*D t u v := by
    have hg : 0<u.gcd v := Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hu).1
    let s := (u.gcd v).divisors
    have hl : (u.gcd v:ℝ)^2 ≤ ∑ q ∈ s,f q := by
      exact single_le_sum (f:=f) (fun _ _ => sq_nonneg _) (Nat.mem_divisors.mpr ⟨dvd_rfl,hg.ne'⟩)
    have hk : (∑ q ∈ s.filter (·≤B),(q.gcd n:ℝ)*q/H)+(∑ q ∈ s.filter (B<·),(q.gcd n:ℝ)) ≤
        (∑ q ∈ s,t q)/B := by
      rw [sum_filter,sum_filter,←sum_add_distrib,sum_div]
      apply sum_le_sum
      intro q hq
      by_cases hqB : q≤B
      · simp only [hqB,not_lt.mpr hqB,ite_true,ite_false,add_zero,t]
        exact div_le_div_of_nonneg_left (by positivity) hbR hHH
      · simp only [hqB,lt_of_not_ge hqB,ite_true,ite_false,zero_add,t]
        apply (le_div_iff₀ hbR).mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show B≤q by omega)) (by positivity)
    unfold cornerCost
    change (cornerLog n)^2+_+((n:ℝ)/_)* _ ≤ _
    have hl' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl
      (inv_nonneg.mpr (Nat.cast_nonneg u))) (inv_nonneg.mpr (Nat.cast_nonneg v))) (Nat.cast_nonneg M)
    have hk' := mul_le_mul_of_nonneg_left hk (by positivity : 0≤(n:ℝ)/((u:ℝ)*v))
    have hmiddle : (M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) ≤ (M:ℝ)*D f u v := by
      simpa only [D,s,div_eq_mul_inv,mul_inv,mul_assoc] using hl'
    calc
      _ ≤ (cornerLog n)^2+(M:ℝ)*D f u v + ((n:ℝ)/((u:ℝ)*v))*((∑ q ∈ s,t q)/B) :=
        by exact add_le_add (add_le_add le_rfl hmiddle) hk'
      _ = _ := by simp only [D,s,div_eq_mul_inv,mul_inv]; ring
  have hf := doubleDivisorBound M f (fun q => sq_nonneg _)
  have ht := doubleDivisorBound M t (fun q => by dsimp only [t]; positivity)
  have hF : (∑ q ∈ X,f q * (q:ℝ)⁻¹^2)=(M:ℝ) := by
    calc
      _ = ∑ _ ∈ X,(1:ℝ) := by
        apply sum_congr rfl; intro q hq; dsimp only [f]
        have hx : (q:ℝ)≠0 := by exact_mod_cast (show 0<q from (mem_Icc.mp hq).1).ne'
        field_simp
      _ = _ := by simp [X]
  have hT : (∑ q ∈ X,t q * (q:ℝ)⁻¹^2)≤n.divisors.card*harmonicBox M := by
    apply le_trans _ (gcdHarmonic M n hn)
    apply sum_le_sum; intro q hq; dsimp only [t]
    have hx : (q:ℝ)≠0 := by exact_mod_cast (show 0<q from (mem_Icc.mp hq).1).ne'
    exact le_of_eq (by field_simp)
  change _ ≤ (∑ q ∈ X,f q*_) * _ at hf
  rw [hF] at hf
  change _ ≤ (∑ q ∈ X,t q*_) * _ at ht
  have hτ := ht.trans (mul_le_mul_of_nonneg_right hT (sq_nonneg _))
  calc
    _ ≤ ∑ u ∈ X,∑ v ∈ X,((cornerLog n)^2+(M:ℝ)*D f u v+((n:ℝ)/B)*D t u v) :=
      sum_le_sum fun u hu => sum_le_sum fun v _ => HA u v hu
    _ = (M:ℝ)^2*(cornerLog n)^2+(M:ℝ)*(∑ u ∈ X,∑ v ∈ X,D f u v)+
          ((n:ℝ)/B)*(∑ u ∈ X,∑ v ∈ X,D t u v) := by
      simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,X,Nat.card_Icc,Nat.add_sub_cancel]
      ring
    _ ≤ _ := by
      have ha := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg M)
      have hb := mul_le_mul_of_nonneg_left hτ (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg B))
      change (M:ℝ)*(∑ u ∈ X,∑ v ∈ X,D f u v) ≤ _ at ha
      change ((n:ℝ)/B)*(∑ u ∈ X,∑ v ∈ X,D t u v) ≤ _ at hb
      linarith

end
end CornerFour

end

section

namespace CornerFour
open Finset Filter
noncomputable section

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
end CornerFour

end

section

namespace CornerFour
open Finset Filter
noncomputable section

def cornerBudget (n M B H : ℕ) : ℝ :=
  ∑ u ∈ Icc 1 M,∑ v ∈ Icc 1 M,
    (u.divisors.card:ℝ)*v.divisors.card*(cornerLog n)^2*cornerCost n M B H u v

theorem cornerBudget_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ M B H : ℕ,
      (M:ℝ) ≤ (n:ℝ)^(2/5:ℝ) → ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ≤ B → B≤H →
      cornerBudget n M B H ≤ ε*n := by
  obtain ⟨C,hC,htau⟩ := divisorPower 240 (by decide)
  have hc : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hy := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/120)).comp hc
  have hl := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/120)).comp_tendsto hc).bound (by norm_num : (0:ℝ)<1/4)
  filter_upwards [eventually_ge_atTop (2:ℕ),hc.eventually_ge_atTop C,hy.eventually_ge_atTop 2,
    hy.eventually_ge_atTop (3/ε),hl] with n hn hCn hy2 hyε hl
  intro M B H hM hB hH
  let y := (n:ℝ)^(1/120:ℝ)
  change 2≤y at hy2
  change 3/ε≤y at hyε
  have hy1 : 1≤y := by linarith
  have hy0 : 0≤y := by linarith
  have hn0 : 0<n := by omega
  have hnr : (2:ℝ)≤n := by exact_mod_cast hn
  have hypow (a : ℕ) : y^a=(n:ℝ)^((1/120:ℝ)*a) := by
    dsimp only [y]; rw [Real.rpow_mul (Nat.cast_nonneg n),Real.rpow_natCast]
  have h120 : y^120=(n:ℝ) := by rw [hypow]; norm_num
  have h40 : y^40=(n:ℝ)^(1/3:ℝ) := by rw [hypow]; norm_num
  have h48 : y^48=(n:ℝ)^(2/5:ℝ) := by rw [hypow]; norm_num
  have hm48 : (M:ℝ)≤y^48 := h48 ▸ hM
  have hmn : M≤n := by
    exact_mod_cast hm48.trans ((pow_le_pow_right₀ hy1 (by decide : 48≤120)).trans_eq h120)
  have hfloor := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
  have hb' : (⌊(n:ℝ)^(1/3:ℝ)⌋₊:ℝ)≤B := by exact_mod_cast hB
  have hb39 : y^39≤(B:ℝ) := by
    rw [←h40] at hfloor hb'
    have h39 : 1≤y^39 := one_le_pow₀ hy1
    have hh := mul_le_mul_of_nonneg_left hy2 (pow_nonneg hy0 39)
    nlinarith only [hfloor,hb',h39,hh]
  have hbpos : 0<B := by
    have h1 := (one_le_pow₀ hy1 (n:=39)).trans hb39
    exact_mod_cast h1
  have hτ (k : ℕ) (hk : 0<k) (hkn : k≤n) : (k.divisors.card:ℝ)≤y := by
    apply le_of_pow_le_pow_left₀ (n:=240) (by decide) hy0
    calc
      _ ≤ C*k := htau k hk
      _ ≤ (n:ℝ)*n := mul_le_mul hCn (by exact_mod_cast hkn) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = y^240 := by rw [←h120]; ring
  have hyLog : 0≤cornerLog n ∧ cornerLog n≤y := by
    have hlog : 0≤Real.log (n:ℝ) := Real.log_nonneg (by linarith)
    change ‖(Real.log (n:ℝ))^(1:ℝ)‖≤(1/4:ℝ)*‖y‖ at hl
    rw [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg hlog,Real.norm_eq_abs,abs_of_nonneg hy0] at hl
    have hln : Real.log ((n:ℝ)+2) ≤ 2*Real.log (n:ℝ) := by
      rw [show (2:ℝ)*Real.log (n:ℝ)=Real.log ((n:ℝ)^2) by simp [Real.log_pow]]
      exact Real.log_le_log (by positivity) (by nlinarith only [mul_nonneg (show 0≤(n:ℝ)-2 by linarith only [hnr]) (show 0≤(n:ℝ)+1 by linarith only [hnr])])
    unfold cornerLog
    exact ⟨by linarith [Real.log_nonneg (show 1≤(n:ℝ)+2 by linarith)],by linarith⟩
  have hyH : harmonicBox M≤y := by
    have h := harmonic_le_one_add_log M
    have hbox : harmonicBox M≤1+Real.log (M:ℝ) := by
      simpa only [harmonicBox,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using h
    by_cases hm0 : M=0
    · simp [harmonicBox,hm0,hy0]
    · apply hbox.trans
      have hlog := Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hm0) : 0<(M:ℝ)) (by linarith [show (M:ℝ)≤n by exact_mod_cast hmn] : (M:ℝ)≤(n:ℝ)+2)
      exact (add_le_add le_rfl hlog).trans hyLog.2
  have hex : (n:ℝ)/B≤y^81 := by
    apply (div_le_iff₀ (by exact_mod_cast hbpos)).mpr
    rw [←h120]
    calc
      y^120 = y^81*y^39 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb39 (pow_nonneg hy0 _)
  have htotal : (∑ u ∈ Icc 1 M,∑ v ∈ Icc 1 M,cornerCost n M B H u v)≤3*y^98 := by
    apply (cornerCost_sum n M B H hn0 hbpos hH).trans
    have hm2 := pow_le_pow_left₀ (Nat.cast_nonneg M) hm48 2
    have hl2 := pow_le_pow_left₀ hyLog.1 hyLog.2 2
    have hh2 := pow_le_pow_left₀ (harmonicBox_nonneg M) hyH 2
    have hh3 := pow_le_pow_left₀ (harmonicBox_nonneg M) hyH 3
    have h1 := mul_le_mul hm2 hl2 (sq_nonneg _) (sq_nonneg _)
    have h2 := mul_le_mul hm2 hh2 (sq_nonneg _) (sq_nonneg _)
    have h3 := mul_le_mul (mul_le_mul hex (hτ n hn0 le_rfl) (Nat.cast_nonneg _) (pow_nonneg hy0 81)) hh3 (pow_nonneg (harmonicBox_nonneg M) _) (by positivity)
    have hsmall : y^85 ≤ y^98 := pow_le_pow_right₀ hy1 (by decide)
    nlinarith only [h1,h2,h3,hsmall]
  have hweighted : cornerBudget n M B H ≤ y^4*(∑ u ∈ Icc 1 M,∑ v ∈ Icc 1 M,cornerCost n M B H u v) := by
    unfold cornerBudget
    simp_rw [mul_sum]
    apply sum_le_sum; intro u hu
    apply sum_le_sum; intro v hv
    apply mul_le_mul_of_nonneg_right _ (cornerCost_nonneg ..)
    have hmul := mul_le_mul (hτ u (mem_Icc.mp hu).1 ((mem_Icc.mp hu).2.trans hmn)) (hτ v (mem_Icc.mp hv).1 ((mem_Icc.mp hv).2.trans hmn)) (Nat.cast_nonneg _) hy0
    exact (mul_le_mul hmul (pow_le_pow_left₀ hyLog.1 hyLog.2 2) (sq_nonneg _) (mul_nonneg hy0 hy0)).trans_eq (by ring)
  have hε' := (div_le_iff₀ hε).mp hyε
  calc
    _ ≤ y^4*(3*y^98) := hweighted.trans (mul_le_mul_of_nonneg_left htotal (pow_nonneg hy0 4))
    _ ≤ ε*y^103 := by nlinarith only [mul_le_mul_of_nonneg_right hε' (pow_nonneg hy0 102)]
    _ ≤ ε*n := mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hy1 (by decide : 103≤120)).trans_eq h120) hε.le

end
end CornerFour

end

section

namespace CornerFour
open Finset MeasureTheory
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
def wave (u l r : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Ioc l r, phase ((u*h:ℕ)*t)
def near (M g : ℕ) : Set ℝ :=
  {t | ∃ j : ℕ, j ≤ g ∧ |t-(j:ℝ)/g| ≤ 1/(4*(M:ℝ)*g)}
def wide (n B H : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1≤q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}
def osc (n u v l r k s : ℕ) (t : ℝ) : ℂ :=
  wave u l r t * wave v k s t * phase (-(n:ℝ)*t)
def annulus (n M g B H q : ℕ) (x : ℝ) : Prop :=
  |x| ≤ 1/(4*(M:ℝ)*g) ∧ (B < q ∨ (H:ℝ)/(q*n) < |x|)

end
end CornerFour

end

section

/-!
The Vaughan estimate and its supporting development are adapted from OpenAI,
openai/math, revision 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/NumberTheory/EgyptianFractions (Apache License 2.0).
This version selects the declarations supporting the final estimate and adapts them
to version 4.36.0 of the proof assistant and its pinned Mathlib. Section comments identify upstream files.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions
-/

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanIdentity

namespace OAI
/-!
# Vaughan's identity with finite cutoffs

This file supplies an unconditional algebraic input to the analytic three-prime
route. Multiplication of arithmetic functions below is Dirichlet convolution.
No estimate for exponential sums over primes is assumed or asserted here.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- The part of an arithmetic function supported on integers at most `U`. -/
def shortPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The complementary part, supported on integers strictly above `U`. -/
def longPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma shortPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    shortPart U f n = if n ≤ U then f n else 0 := rfl

@[simp] lemma longPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    longPart U f n = if U < n then f n else 0 := rfl

lemma shortPart_add_longPart {R : Type*} [AddMonoid R]
    (U : ℕ) (f : ArithmeticFunction R) : shortPart U f + longPart U f = f := by
  ext n
  by_cases hn : n ≤ U <;> simp [hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]

lemma longPart_eq_sub_shortPart {R : Type*} [AddCommGroup R]
    (U : ℕ) (f : ArithmeticFunction R) : longPart U f = f - shortPart U f := by
  have h := shortPart_add_longPart U f
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

/-- Vaughan's four-term identity, valid also at zero and for zero cutoffs.
The first convolution is Type I; the second has a coefficient supported on
`[1,U*V]`; the last is the long-long Type II convolution. -/
theorem vonMangoldt_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      shortPart V ArithmeticFunction.vonMangoldt +
      shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
      (shortPart U (μ : ArithmeticFunction ℝ) *
        shortPart V ArithmeticFunction.vonMangoldt) * (ζ : ArithmeticFunction ℝ) +
      (longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
        longPart V ArithmeticFunction.vonMangoldt := by
  rw [longPart_eq_sub_shortPart, longPart_eq_sub_shortPart]
  have hμ : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hΛ : (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt =
      ArithmeticFunction.log := ArithmeticFunction.zeta_mul_vonMangoldt
  calc
    ArithmeticFunction.vonMangoldt =
        ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
    _ = _ := by
      rw [← hΛ]
      have hshort : ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          shortPart V ArithmeticFunction.vonMangoldt =
          shortPart V ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
      linear_combination hshort

/-- A convolution of two short parts has the expected product support. -/
lemma shortPart_mul_eq_zero_of_lt {R : Type*} [Semiring R]
    (U V n : ℕ) (f g : ArithmeticFunction R) (hn : U * V < n) :
    (shortPart U f * shortPart V g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have habn := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ U
  · have hb : ¬ ab.2 ≤ V := by
      intro hb
      have hm := Nat.mul_le_mul ha hb
      rw [habn] at hm
      omega
    simp [ha, hb]
  · simp [ha]

/-- Convolving a long part cannot create a smaller positive index. -/
lemma longPart_mul_eq_zero_of_le {R : Type*} [Semiring R]
    (U n : ℕ) (f g : ArithmeticFunction R) (hn : n ≤ U) :
    (longPart U f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.2, hprod.symm⟩
  have hnot : ¬ U < ab.1 := by omega
  simp [hnot]

lemma abs_shortPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |shortPart U f n| ≤ |f n| := by
  by_cases hn : n ≤ U <;> simp [hn, abs_nonneg]

lemma abs_longPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |longPart U f n| ≤ |f n| := by
  by_cases hn : U < n <;> simp [hn, abs_nonneg]

lemma abs_real_moebius_le_one (n : ℕ) :
    |(μ : ArithmeticFunction ℝ) n| ≤ 1 := by
  change |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The short convolution coefficient appearing in Type I sums. -/
def typeICoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  shortPart U (μ : ArithmeticFunction ℝ) * shortPart V ArithmeticFunction.vonMangoldt

/-- The coefficient appearing in the long-long Type II sum. -/
def typeIICoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)

lemma typeICoefficient_eq_zero (U V n : ℕ) (hn : U * V < n) :
    typeICoefficient U V n = 0 := shortPart_mul_eq_zero_of_lt U V n _ _ hn

lemma typeIICoefficient_eq_zero (U n : ℕ) (hn : n ≤ U) :
    typeIICoefficient U n = 0 := longPart_mul_eq_zero_of_le U n _ _ hn

/-- The Type I coefficient costs only a logarithm, not a divisor function. -/
lemma abs_typeICoefficient_le_log (U V n : ℕ) :
    |typeICoefficient U V n| ≤ Real.log n := by
  unfold typeICoefficient
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal,
        |shortPart U (μ : ArithmeticFunction ℝ) ab.1 *
          shortPart V ArithmeticFunction.vonMangoldt ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt ab.2 := by
      apply Finset.sum_le_sum
      intro ab hab
      rw [abs_mul]
      have hμ := (abs_shortPart_le U (μ : ArithmeticFunction ℝ) ab.1).trans
        (abs_real_moebius_le_one ab.1)
      have hΛ := abs_shortPart_le V ArithmeticFunction.vonMangoldt ab.2
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hΛ
      calc
        _ ≤ 1 * ArithmeticFunction.vonMangoldt ab.2 :=
          mul_le_mul hμ hΛ (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => ArithmeticFunction.vonMangoldt b)]
      exact ArithmeticFunction.vonMangoldt_sum

/-- A uniform elementary coefficient bound for the Type II sum. -/
lemma abs_typeIICoefficient_le_divisors_card (U n : ℕ) :
    |typeIICoefficient U n| ≤ (n.divisors.card : ℝ) := by
  rw [typeIICoefficient, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, |longPart U (μ : ArithmeticFunction ℝ) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (abs_longPart_le U (μ : ArithmeticFunction ℝ) d).trans
        (abs_real_moebius_le_one d)
    _ = _ := by simp

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanHyperbola

namespace OAI
/-!
# Finite hyperbola reindexing for Vaughan sums

An exact finite change of variables from `n = a*b` to pairs of positive
integers below a hyperbola. The arbitrary weight version is suitable for
both rational additive characters and real-frequency exponential sums.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.Vaughan

/-- Positive lattice points below the multiplicative hyperbola `a*b ≤ N`. -/
def hyperbola (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter (fun ab => ab.1 * ab.2 ≤ N)

@[simp] lemma mem_hyperbola {N a b : ℕ} :
    (a, b) ∈ hyperbola N ↔ 1 ≤ a ∧ 1 ≤ b ∧ a * b ≤ N := by
  change ((a, b) ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun ab => ab.1 * ab.2 ≤ N)) ↔ _
  rw [Finset.mem_filter]
  have hm : (a, b) ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N) ↔
      a ∈ Finset.Icc 1 N ∧ b ∈ Finset.Icc 1 N := Finset.mem_product
  rw [hm]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hp⟩
    exact ⟨ha, hb, hp⟩
  · rintro ⟨ha, hb, hp⟩
    have haN : a ≤ N := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp
    have hbN : b ≤ N := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans hp
    exact ⟨⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, hp⟩

/-- The divisor-antidiagonal fibers partition the positive hyperbola exactly.
The summand may also depend on the product index `n`. -/
theorem sum_divisor_fibers {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → ℕ → A) :
    (∑ n ∈ Finset.Icc 1 N, ∑ ab ∈ n.divisorsAntidiagonal, F n ab.1 ab.2) =
      ∑ ab ∈ hyperbola N, F (ab.1 * ab.2) ab.1 ab.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun x : Sigma (fun _n : ℕ => ℕ × ℕ) => x.2)
    (fun ab : ℕ × ℕ => (⟨ab.1 * ab.2, ab⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)))
  · rintro ⟨n, a, b⟩ hx
    obtain ⟨hn, hab⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    apply mem_hyperbola.mpr
    change a * b = n at hprod
    change n ≠ 0 at hn0
    have hab0 : a * b ≠ 0 := by rw [hprod]; exact hn0
    exact ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0),
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0), by rw [hprod]; exact hnN⟩
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hb, hp⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change (⟨a * b, (a, b)⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)) = ⟨n, (a, b)⟩
    rw [hprod]
  · intro ab hab
    rfl
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change F n a b = F (a * b) a b
    rw [hprod]

/-- The hyperbola sum as ordinary nested integer intervals. The inner endpoint
is the natural-number quotient `N / a`; the outer interval excludes zero. -/
theorem sum_hyperbola_eq_nested {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → A) :
    (∑ ab ∈ hyperbola N, F ab.1 ab.2) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ab : ℕ × ℕ => (⟨ab.1, ab.2⟩ : Sigma (fun _a : ℕ => ℕ)))
    (fun x : Sigma (fun _a : ℕ => ℕ) => (x.1, x.2))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨ha,
        (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp⟩
    · apply Finset.mem_Icc.mpr
      exact ⟨hb, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by simpa [mul_comm] using hp)⟩
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hx
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hb
    change 1 ≤ a at ha1
    change 1 ≤ b at hb1
    change b ≤ N / a at hbN
    apply mem_hyperbola.mpr
    refine ⟨ha1, hb1, ?_⟩
    have hp := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hbN
    simpa [mul_comm] using hp
  · intro ab hab
    rfl
  · intro x hx
    rfl
  · intro ab hab
    rfl

/-- Real arithmetic coefficients with complex weights, the combination used
for the von-Mangoldt exponential sum. -/
theorem sum_real_convolution_hyperbola
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ ab ∈ hyperbola N, ((f ab.1 * g ab.2 : ℝ) : ℂ) * w (ab.1 * ab.2) := by
  simp_rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
  exact sum_divisor_fibers N (fun n a b => ((f a * g b : ℝ) : ℂ) * w n)

/-- The traditional nested-interval form of the finite convolution identity. -/
theorem sum_real_convolution_eq_nested
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a),
        ((f a * g b : ℝ) : ℂ) * w (a * b) := by
  rw [sum_real_convolution_hyperbola]
  exact sum_hyperbola_eq_nested (A := ℂ) N
    (fun a b => ((f a * g b : ℝ) : ℂ) * w (a * b))

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GeometricCharacterBound

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The elementary peak bound for a geometric kernel. -/
theorem norm_geometric_sum_le_card {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ (N : ℝ) := by
  calc
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ ∑ j ∈ Finset.range N, ‖z ^ j‖ := norm_sum_le _ _
    _ = (N : ℝ) := by simp [norm_pow, hz]

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

/-- Uniform lower bound for the sine away from both ends of a period. -/
theorem sin_pi_mul_lower_on_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hδ.le hleft
  have hx1 : 0 ≤ 1 - x := by linarith
  by_cases hx : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x)
      (mul_nonneg Real.pi_pos.le hx0) (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at hs
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - x))
      (mul_nonneg Real.pi_pos.le hx1)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    linarith

end Problem337

end

end OAI

end

section

namespace CornerFour
open Finset MeasureTheory
noncomputable section

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
  exact OAI.Problem337.norm_geometric_phase_sum_le hs _

theorem wave_local (u l r : ℕ) (x : ℝ) (hu : 0<u) (hx : x≠0)
    (hs : (u:ℝ)*|x|≤1/2) : ‖wave u l r x‖ ≤ 1/((u:ℝ)*|x|) := by
  have hpos : 0<(u:ℝ)*|x| := mul_pos (by exact_mod_cast hu) (abs_pos.mpr hx)
  have hsin := OAI.Problem337.sin_pi_mul_lower_on_middle hpos (le_refl _) (by linarith)
  have heq : |Real.sin (Real.pi*((u:ℝ)*x))| = Real.sin (Real.pi*((u:ℝ)*|x|)) := by
    rcases le_or_gt 0 x with h|h
    · rw [abs_of_nonneg h]
      rw [abs_of_nonneg]
      rw [abs_of_nonneg h] at hsin hpos
      linarith
    · rw [abs_of_neg h] at hsin hpos ⊢
      simp only [mul_neg,Real.sin_neg] at hsin ⊢
      rw [abs_of_nonpos (by linarith)]
  have hsin' : (u:ℝ)*|x| ≤ |Real.sin (Real.pi*((u:ℝ)*x))| := by rw [heq]; linarith
  exact (wave_sin u l r x (abs_pos.mp (hpos.trans_le hsin'))).trans
    (one_div_le_one_div_of_le hpos hsin')

private theorem norm_osc_mul (n u v l r k s : ℕ) (x : ℝ) :
    ‖osc n u v l r k s x‖ = ‖wave u l r x‖*‖wave v k s x‖ := by simp [osc]

theorem annulus_budget (n M g B H q u v l r k s : ℕ)
    (hn : 0<n) (hH : 0<H) (hq : 0<q) (hg : 0<g) (hu : 0<u) (hv : 0<v)
    (huM : u≤M) (hvM : v≤M) (hru : r≤n/u) (hsv : s≤n/v) :
    ‖∫ x in (-(1:ℝ)/(4*(M:ℝ)*g))..(1/(4*(M:ℝ)*g)),
      {x:ℝ|annulus n M g B H q x}.indicator (osc n u v l r k s) x‖ ≤
      (2*Real.pi)*((n:ℝ)/((u:ℝ)*v))*(if q≤B then (q:ℝ)/H else 1) := by
  let W : ℝ := 1/(4*(M:ℝ)*g)
  let c : ℝ := if q≤B then (H:ℝ)/(q*n) else 1/n
  have hcp : 0<c := by dsimp [c]; split <;> positivity
  have hMp : 0<M := hu.trans_le huM
  have hWp : 0<W := by dsimp [W]; positivity
  have hu' : (0:ℝ)<u := by exact_mod_cast hu
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hr' : (r:ℝ) ≤ (n:ℝ)/u := (le_div_iff₀ hu').mpr (by exact_mod_cast (Nat.le_div_iff_mul_le hu).mp hru)
  have hs' : (s:ℝ) ≤ (n:ℝ)/v := (le_div_iff₀ hv').mpr (by exact_mod_cast (Nat.le_div_iff_mul_le hv).mp hsv)
  let D : ℝ := 2/((u:ℝ)*v)
  have hD : 0<D := by dsimp [D]; positivity
  have point (x : ℝ) : ‖{x:ℝ|annulus n M g B H q x}.indicator (osc n u v l r k s) x‖ ≤ D*(c^2+x^2)⁻¹ := by
    by_cases hx : annulus n M g B H q x
    · rw [Set.indicator_of_mem (show x∈{x:ℝ|annulus n M g B H q x} from hx),norm_osc_mul]
      obtain ⟨hW,hax⟩ := hx
      change |x|≤W at hW
      have hscale (a : ℕ) (ha : a≤M) : (a:ℝ)*|x|≤1/2 := by
        have hh := (le_div_iff₀ (show 0<4*(M:ℝ)*g by positivity)).mp hW
        have hg' : (1:ℝ)≤g := by exact_mod_cast hg
        have ha' : (a:ℝ)≤M := by exact_mod_cast ha
        have hm : |x| *a ≤ |x| *M := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left hg' (mul_nonneg (abs_nonneg x) (Nat.cast_nonneg M))]
      have hcx : c≤|x| ∨ (q>B ∧ |x|≤c) := by
        by_cases hqB : q≤B
        · exact Or.inl (by simpa [c,hqB] using (hax.resolve_left (by omega)).le)
        · exact (le_total c |x|).imp_right fun h=>⟨by omega,h⟩
      have hden : 0 < c^2+x^2 := by positivity
      rw [← div_eq_mul_inv,le_div_iff₀ hden]
      rcases hcx with hcx|⟨hbig,hxc⟩
      · have hx0 := abs_pos.mp (hcp.trans_le hcx)
        have hu1 := wave_local u l r x hu hx0 (hscale u huM)
        have hv1 := wave_local v k s x hv hx0 (hscale v hvM)
        have h2 : c^2+x^2 ≤ 2*|x| ^2 := by nlinarith [sq_le_sq' (by linarith : -|x|≤c) hcx,sq_abs x]
        calc
          _ ≤ (1/((u:ℝ)*|x|))*(1/((v:ℝ)*|x|))*(2*|x| ^2) := by gcongr
          _ = D := by dsimp [D]; field_simp
      · have hc : c=1/(n:ℝ) := by simp [c,show ¬q≤B by omega]
        have hu1 := (wave_cap u l r x).trans hr'
        have hv1 := (wave_cap v k s x).trans hs'
        have h2 : c^2+x^2 ≤ 2*c^2 := by nlinarith [sq_le_sq' (by linarith [abs_nonneg x] : -c≤|x|) hxc,sq_abs x]
        calc
          _ ≤ ((n:ℝ)/u)*(n/v)*(2*c^2) := by gcongr
          _ = D := by rw [hc]; dsimp [D]; field_simp
    · rw [Set.indicator_of_notMem (show x∉{x:ℝ|annulus n M g B H q x} from hx),norm_zero]
      positivity
  have ic : Continuous (fun x:ℝ=>D*(c^2+x^2)⁻¹) := by fun_prop (disch:=intro x; positivity)
  rw [neg_div]
  apply (intervalIntegral.norm_integral_le_of_norm_le (show -W≤W by linarith)
    (Filter.Eventually.of_forall (fun x _ => point x)) (ic.intervalIntegrable _ _)).trans
  rw [intervalIntegral.integral_const_mul,integral_inv_sq_add_sq hcp.ne']
  have ht : Real.arctan (W/c)-Real.arctan (-W/c) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two (W/c),Real.neg_pi_div_two_lt_arctan (-W/c)]
  calc
    _ ≤ D*(c⁻¹*Real.pi) := by gcongr
    _ = _ := by dsimp [D,c]; split <;> field_simp <;> ring
end
end CornerFour

end

section

namespace CornerFour
open Finset OAI.Problem337.Vaughan ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section

def muR (d : ℕ) : ℝ := (ArithmeticFunction.moebius d:ℝ)

def tau4 (U B m : ℕ) : ℝ :=
  ∑ a ∈ m.divisors.filter (fun a => B<a ∧ U < m / a),
    (∑ d ∈ a.divisors.filter (fun d => U<d), muR d)*vonMangoldt (m/a)

private theorem mu_complement (U a : ℕ) (ha : 1<a) :
    (∑ d∈a.divisors.filter (fun d=>U<d),muR d) =
    -(∑ d∈a.divisors.filter (fun d=>d≤U),muR d) := by
  have hz : (∑ d∈a.divisors,muR d)=0 := by
    change (∑ d∈a.divisors, (μ : ArithmeticFunction ℝ) d)=0
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply_ne (by omega)]
  have h := sum_filter_add_sum_filter_not a.divisors (fun d=>U<d) muR
  simpa only [not_lt, hz, add_eq_zero_iff_eq_neg] using h

private theorem nested {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ→ℕ→A) :
    (∑ n∈Icc 1 N, ∑ a∈n.divisors, f a (n/a)) =
    ∑ a∈Icc 1 N, ∑ b∈Icc 1 (N/a),f a b := by
  calc
    _ = ∑ n∈Icc 1 N, ∑ ab∈n.divisorsAntidiagonal, f ab.1 ab.2 :=
      sum_congr rfl (fun n _=> (Nat.sum_divisorsAntidiagonal f).symm)
    _ = _ := (sum_divisor_fibers N (fun _ a b=> f a b)).trans (sum_hyperbola_eq_nested N f)

private theorem nestedR {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ→ℕ→A) :
    (∑ n∈Icc 1 N, ∑ a∈n.divisors, f a (n/a)) =
    ∑ b∈Icc 1 N, ∑ a∈Icc 1 (N/b),f a b := by
  calc
    _ = ∑ n∈Icc 1 N, ∑ ab∈n.divisorsAntidiagonal, f ab.1 ab.2 :=
      sum_congr rfl (fun n _=> (Nat.sum_divisorsAntidiagonal f).symm)
    _ = ∑ n∈Icc 1 N, ∑ b∈n.divisors, f (n/b) b :=
      sum_congr rfl (fun n _=> Nat.sum_divisorsAntidiagonal' f)
    _ = _ := nested N (fun b a=>f a b)

theorem expansion (n U B : ℕ) (hB : 1≤B) (w : ℕ→ℂ) :
    (∑ m∈range (n+1),(tau4 U B m:ℂ)*w m) =
    -(∑ b∈Ioc U (n/(B+1)), ∑ d∈Icc 1 U,
        ((muR d*vonMangoldt b:ℝ):ℂ)*∑ h∈Ioc (B/d) (n/(b*d)), w (b*d*h)) := by
  classical
  have hs : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
  rw [hs,sum_insert (by simp)]
  simp only [tau4,Nat.divisors_zero,Finset.filter_empty,Finset.sum_empty,Complex.ofReal_zero,zero_mul,zero_add]
  let f (a b : ℕ) : ℂ := if B<a ∧ U<b then
    ((∑ d∈a.divisors.filter (fun d=>d≤U), (muR d*vonMangoldt b:ℝ)):ℝ)*w (a*b) else 0
  have h1 : ∀ m∈Icc 1 n,
      ((∑ a∈m.divisors.filter (fun a=>B<a ∧ U < m / a),
      (∑ d∈a.divisors.filter (fun d=>U<d),muR d)*vonMangoldt (m/a):ℝ):ℂ)*w m =
      -(∑ a∈m.divisors,f a (m/a)) := by
    intro m hm
    rw [Complex.ofReal_sum,sum_mul,← sum_neg_distrib,sum_filter]
    apply sum_congr rfl
    intro a ha
    by_cases h : B<a ∧ U < m / a
    · simp only [h,f,mu_complement U a (by omega),sum_mul,neg_mul,Complex.ofReal_neg]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)]
      simp
    · simp [f,h]
  rw [sum_congr rfl h1,sum_neg_distrib,nestedR]
  congr 1
  have hsub : Ioc U (n/(B+1)) ⊆ Icc 1 n := by
    intro b hb
    obtain ⟨hl,hr⟩ := mem_Ioc.mp hb
    exact mem_Icc.mpr ⟨by omega,hr.trans (Nat.div_le_self ..)⟩
  rw [← sum_subset hsub (f:=fun b=> ∑ a∈Icc 1 (n/b),f a b) (by
    intro b hb hno
    apply sum_eq_zero
    intro a ha
    obtain ⟨hb1,_⟩ := mem_Icc.mp hb
    obtain ⟨_,ha2⟩ := mem_Icc.mp ha
    have hab := (Nat.le_div_iff_mul_le hb1).mp ha2
    have hm : ¬(B<a ∧ U<b) := by
      rintro ⟨ha,hu⟩
      exact hno (mem_Ioc.mpr ⟨hu,(Nat.le_div_iff_mul_le (by omega)).mpr
        (by simpa [mul_comm] using (Nat.mul_le_mul_right b ha).trans hab)⟩)
    simp [f,hm])]
  apply sum_congr rfl
  intro b hb
  obtain ⟨hUb,hBn⟩ := mem_Ioc.mp hb
  have hb1 : 0<b := by omega
  let term (d h : ℕ) : ℂ := if B<d*h ∧ d≤U then
    ((muR d*vonMangoldt b:ℝ):ℂ)*w (b*d*h) else 0
  have inner (a : ℕ) : f a b = ∑ d∈a.divisors,term d (a/d) := by
    dsimp [f]
    by_cases hBa : B<a
    · simp only [hUb,hBa,and_self,ite_true,Complex.ofReal_sum,sum_mul,sum_filter]
      apply sum_congr rfl
      intro d hd
      have had := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd))
      dsimp [term]
      rw [had]
      by_cases hdU : d≤U
      · simp [hBa,hdU, mul_comm a b, mul_assoc b,had]
      · simp [hBa,hdU]
    · simp only [hBa,false_and,ite_false]
      apply Eq.symm
      apply sum_eq_zero
      intro d hd
      simp [term,Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd),hBa]
  simp_rw [inner]
  rw [nested]
  have dterm (d : ℕ) (hd : 0<d) :
      (∑ h∈Icc 1 (n/b/d),term d h) =
        if d≤U then ((muR d*vonMangoldt b:ℝ):ℂ)*∑ h∈Ioc (B/d) (n/(b*d)), w (b*d*h)
        else 0 := by
    by_cases hU : d≤U
    · simp only [hU,ite_true,mul_sum]
      have eqs : Ioc (B/d) (n/(b*d)) = (Icc 1 (n/b/d)).filter (fun h=>B<d*h) := by
        ext h
        simp only [mem_Ioc,mem_filter,mem_Icc,Nat.div_div_eq_div_mul,Nat.div_lt_iff_lt_mul hd]
        constructor
        · rintro ⟨h1,h2⟩
          exact ⟨⟨by by_contra!; simp_all,h2⟩,by simpa [mul_comm] using h1⟩
        · rintro ⟨⟨_,h2⟩,h1⟩
          exact ⟨by simpa [mul_comm] using h1,h2⟩
      simp [eqs,sum_filter,term,hU]
    · simp [hU,term]
  rw [sum_congr rfl (fun d hd=>dterm d (mem_Icc.mp hd).1)]
  rw [← sum_filter]
  apply sum_subset_zero_on_sdiff
  · intro d hd
    obtain ⟨hmem,hle⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hmem).1,hle⟩
  · intro d hmem
    obtain ⟨hd,hno⟩ := mem_sdiff.mp hmem
    obtain ⟨hd1,hdU⟩ := mem_Icc.mp hd
    have hlarge : n / b < d := by
      by_contra! hh
      exact hno (mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1,hh⟩,hdU⟩)
    have he : n/(b*d)=0 := by rw [← Nat.div_div_eq_div_mul]; exact Nat.div_eq_of_lt hlarge
    simp [he]
  · intro d hd
    rfl
end
end CornerFour

end

section

namespace CornerFour
open Finset OAI.Problem337.Vaughan MeasureTheory
noncomputable section

theorem wideMeas' (n B H : ℕ) : MeasurableSet (wide n B H) := by
  unfold wide
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1≤q ∧ q≤B ∧ a≤q ∧ a.Coprime q
  · rcases h with ⟨h1,h2,h3,h4⟩
    simp only [h1,h2,h3,true_and]
    have he : {x : ℝ | a.Coprime q ∧ |x-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} =
        {x : ℝ | |x-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} := by
      ext x; exact ⟨And.right,And.intro h4⟩
    rw [he]
    exact measurableSet_le (f:=fun t : ℝ => |t-(a:ℝ)/q|) (g:=fun _ : ℝ => (H:ℝ)/((q:ℝ)*n)) (by fun_prop) measurable_const
  · have he : {t : ℝ | 1≤q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} = ∅ := by
      ext t; simp; tauto
    rw [he]; exact MeasurableSet.empty

def freq4 (n U T : ℕ) (t : ℝ) : ℂ :=
  ∑ m∈range (n+1), (tau4 U T m:ℂ)*phase ((m:ℝ)*t)
def J4 (n U T B H : ℕ) : ℂ := ∫ t in (0:ℝ)..1, (wide n B H)ᶜ.indicator
  (fun x=>freq4 n U T x * freq4 n U T x * phase (-(n:ℝ)*x)) t
def atom (n B H u v l r k s : ℕ) : ℂ := ∫ t in (0:ℝ)..1,
  (wide n B H)ᶜ.indicator (osc n u v l r k s) t
def pairs (n U T : ℕ) := (Ioc U (n/(T+1))) ×ˢ (Icc 1 U)
def step (i : ℕ×ℕ) := i.1*i.2
def cf (i : ℕ×ℕ) : ℂ := ((muR i.2*ArithmeticFunction.vonMangoldt i.1:ℝ):ℂ)

theorem atom_sum (n U T B H : ℕ) (hT : 1≤T) :
    J4 n U T B H = ∑ ij∈(pairs n U T) ×ˢ (pairs n U T),
      (cf ij.1*cf ij.2)*atom n B H (step ij.1) (step ij.2)
        (T/ij.1.2) (n/step ij.1) (T/ij.2.2) (n/step ij.2) := by
  classical
  let S := pairs n U T
  let W (i : ℕ×ℕ) := wave (step i) (T/i.2) (n/step i)
  let F (ij : (ℕ×ℕ)×(ℕ×ℕ)) := osc n (step ij.1) (step ij.2)
    (T/ij.1.2) (n/step ij.1) (T/ij.2.2) (n/step ij.2)
  let c (ij : (ℕ×ℕ)×(ℕ×ℕ)) := cf ij.1*cf ij.2
  let D := (wide n B H)ᶜ
  have hS (t : ℝ) : freq4 n U T t = -(∑ i∈S,cf i*W i t) := by
    rw [freq4,expansion n U T hT]
    unfold S pairs
    rw [sum_product]
    rfl
  have hid (t : ℝ) : D.indicator (fun x=>freq4 n U T x*freq4 n U T x*phase (-(n:ℝ)*x)) t =
      ∑ ij∈S×ˢS,c ij*D.indicator (F ij) t := by
    by_cases ht : t∈D
    · simp only [Set.indicator_of_mem ht,hS,neg_mul_neg,sum_product,sum_mul,mul_sum]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      unfold F c W osc
      ring
    · simp [Set.indicator_of_notMem ht]
  have hI (ij : (ℕ×ℕ)×(ℕ×ℕ)) : IntervalIntegrable (fun t=>c ij*D.indicator (F ij) t) volume 0 1 := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hc : Continuous (F ij) := by unfold F osc wave phase; fun_prop
    exact (hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator (wideMeas' ..).compl
  unfold J4
  change (∫ t in (0:ℝ)..1,D.indicator _ t)=_
  simp_rw [hid]
  rw [intervalIntegral.integral_finsetSum (fun ij _=>hI ij)]
  apply sum_congr rfl
  intro ij _
  exact intervalIntegral.integral_const_mul ..

theorem pairs_le_fibers (n U T M : ℕ) (hm : n/(T+1)*U ≤ M)
    (f : ℕ→ℝ) (hf : ∀ m, 0≤f m) :
    ∑ i∈pairs n U T,f (step i) ≤ ∑ m∈Icc 1 M, (m.divisors.card:ℝ)*f m := by
  have hsub : pairs n U T ⊆ hyperbola M := by
    rintro ⟨b,d⟩ hi
    obtain ⟨hb,hd⟩ := mem_product.mp hi
    obtain ⟨hu,hbn⟩ := mem_Ioc.mp hb
    obtain ⟨hd1,hdU⟩ := mem_Icc.mp hd
    exact mem_hyperbola.mpr ⟨by omega,hd1,(Nat.mul_le_mul hbn hdU).trans hm⟩
  apply (sum_le_sum_of_subset_of_nonneg (f:=fun i=>f (step i)) hsub (fun i _ _=>hf _)).trans_eq
  change (∑ ab∈hyperbola M,f (ab.1*ab.2))=_
  rw [←sum_divisor_fibers M (fun m _ _=>f m)]
  apply sum_congr rfl
  intro m _
  rw [Nat.sum_divisorsAntidiagonal (fun _ _=>f m)]
  simp

theorem cf_bound (n U T : ℕ) {i : ℕ×ℕ} (hi : i∈pairs n U T) :
    ‖cf i‖ ≤ 1+Real.log ((n:ℝ)+2) := by
  have hb := mem_Ioc.mp (mem_product.mp hi).1
  have hbn := hb.2.trans (Nat.div_le_self ..)
  have hlog := Real.log_le_log (show 0<(i.1:ℝ) by exact_mod_cast (show 0 < i.1 by omega))
    (show (i.1:ℝ)≤(n:ℝ)+2 by exact_mod_cast (by omega : i.1≤n+2))
  have hm : |muR i.2|≤1 := abs_real_moebius_le_one _
  rw [cf,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ 1*ArithmeticFunction.vonMangoldt i.1 := by gcongr
    _ ≤ _ := by linarith [ArithmeticFunction.vonMangoldt_le_log (n:=i.1)]

theorem sum_budget (n U T B H M : ℕ) (hT : 1≤T) (hm : n/(T+1)*U≤M)
    (C : ℝ) (hC : 0≤C) (F : ℕ→ℕ→ℝ) (hF : ∀ u v,0≤F u v)
    (bound : ∀ i∈pairs n U T, ∀ j∈pairs n U T,
      ‖atom n B H (step i) (step j) (T/i.2) (n/step i) (T/j.2) (n/step j)‖ ≤ C*F (step i) (step j)) :
    ‖J4 n U T B H‖ ≤ C * ∑ u∈Icc 1 M, ∑ v∈Icc 1 M,
      (u.divisors.card:ℝ)*v.divisors.card*(1+Real.log ((n:ℝ)+2))^2 * F u v := by
  classical
  let L := 1+Real.log ((n:ℝ)+2)
  let S := pairs n U T
  have hL : 0≤L := by dsimp [L]; have := Real.log_nonneg (show 1≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n]); linarith
  rw [atom_sum n U T B H hT]
  apply (norm_sum_le ..).trans
  rw [sum_product]
  calc
    _ ≤ ∑ i∈S,∑ j∈S,C*(L^2*F (step i) (step j)) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [norm_mul,norm_mul]
      calc
        _ ≤ (L*L)*(C*F (step i) (step j)) := by
          have := cf_bound n U T hi; have := cf_bound n U T hj
          exact mul_le_mul (mul_le_mul (cf_bound n U T hi) (cf_bound n U T hj) (norm_nonneg _) hL)
            (bound i hi j hj) (norm_nonneg _) (mul_nonneg hL hL)
        _ = _ := by ring
    _ = C*∑ i∈S,∑ j∈S,L^2*F (step i) (step j) := by simp [mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        _ ≤ ∑ i∈S,∑ v∈Icc 1 M, (v.divisors.card:ℝ)*(L^2*F (step i) v) :=
          sum_le_sum fun i _=>pairs_le_fibers n U T M hm _ (fun v=>mul_nonneg (sq_nonneg L) (hF _ _))
        _ ≤ ∑ u∈Icc 1 M,(u.divisors.card:ℝ)*∑ v∈Icc 1 M,(v.divisors.card:ℝ)*(L^2*F u v) :=
          pairs_le_fibers n U T M hm _ (fun u=>sum_nonneg (fun v _=>
            mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg L) (hF u v))))
        _ = _ := by simp [L,mul_sum,mul_assoc]
end
end CornerFour

end

section

namespace CornerFour
open Filter Finset MeasureTheory
noncomputable section

theorem of_atoms
    (C : ℝ) (hC : 0<C)
    (atomBound : ∀ n M B H u v l r k s : ℕ, 0<n → 0<H → 1≤B → B≤M → M≤n →
      0<u → 0<v → u≤M → v≤M → r≤n/u → s≤n/v → 4*H*(u.gcd v)≤n →
      ‖atom n B H u v l r k s‖≤C*cornerCost n M B H u v) :
    ∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n →
        ‖J4 n (cutU n) (cutT n) (cutB n) (cutH n)‖≤e*n := by
  intro e he
  have hε : 0<e/C := div_pos he hC
  have hevs : ∀ᶠ n : ℕ in atTop,
      ‖J4 n (cutU n) (cutT n) (cutB n) (cutH n)‖≤e*n := by
    filter_upwards [scaleAvailable,cornerBudget_eventually (e/C) hε] with n hs hbudget
    obtain ⟨hn,ht,hb,hh,hbm,hmn,hm,hscale⟩:= hs
    have hBH : cutB n≤cutH n := by
      have hL : 1≤Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
      have hL2 : 1≤(Nat.log 2 (n+2))^2 := one_le_pow₀ hL
      unfold cutH
      nlinarith [Nat.mul_le_mul_left (256*cutB n) hL2]
    have bounds (i : ℕ×ℕ) (hi : i∈pairs n (cutU n) (cutT n)) :
        0<step i ∧ step i≤cutM n := by
      obtain ⟨hb,hd⟩ := mem_product.mp hi
      obtain ⟨hlo,hup⟩ := mem_Ioc.mp hb
      obtain ⟨hd1,hd2⟩ := mem_Icc.mp hd
      exact ⟨Nat.mul_pos (by omega) hd1,(Nat.mul_le_mul hup hd2).trans hm⟩
    have hstep := sum_budget n (cutU n) (cutT n) (cutB n) (cutH n) (cutM n) ht hm C hC.le
      (cornerCost n (cutM n) (cutB n) (cutH n)) (fun u v=>cornerCost_nonneg ..) (by
        intro i hi j hj
        obtain ⟨hi',hiM⟩:=bounds i hi
        obtain ⟨hj',hjM⟩:=bounds j hj
        apply atomBound n (cutM n) (cutB n) (cutH n) _ _ _ _ _ _ hn hh hb hbm hmn hi' hj' hiM hjM le_rfl le_rfl
        exact (Nat.mul_le_mul_left _ ((Nat.gcd_le_left _ hi').trans hiM)).trans hscale)
    change _ ≤ C*cornerBudget n (cutM n) (cutB n) (cutH n) at hstep
    have ha := hbudget (cutM n) (cutB n) (cutH n) (Nat.floor_le (by positivity)) le_rfl hBH
    apply hstep.trans
    calc
      _ ≤ C*((e/C)*n) := mul_le_mul_of_nonneg_left ha hC.le
      _ = _ := by field_simp
  obtain ⟨N,h⟩ := (eventually_atTop.1 hevs)
  exact ⟨N,fun n hn _=>h n hn⟩

end
end CornerFour

end

section

/-!
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT
namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor

open Finset

noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]


end
end GoldbachExplicitModeledMajor

end

section

namespace CornerFour
open Finset GoldbachExplicitModeledMajor
open scoped ComplexConjugate
noncomputable section

def peakRam (n q : ℕ) : ℂ := ∑ a∈(range q).filter (fun a => a.Coprime q),
  CornerFour.phase (-(n:ℝ)*((a:ℝ)/q))

private theorem peakRam_conj (n q : ℕ) : peakRam n q = conj (GoldbachExplicitModeledMajor.ram q n) := by
  unfold peakRam ram
  rw [map_sum]
  apply sum_congr rfl
  intro a _
  unfold CornerFour.phase GoldbachExplicitModeledMajor.phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem peakRam_le (n q : ℕ) : ‖peakRam n q‖ ≤ (q.gcd n:ℝ) := by
  rw [peakRam_conj,Complex.norm_conj]
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ j =>
      rw [ram_primePower _ _ _ hp]
      by_cases h : p^(j+1) ∣ n
      · have hd : p^j ∣ n := (pow_dvd_pow p (by omega : j≤j+1)).trans h
        rw [if_pos h,if_pos hd,Nat.gcd_eq_left h]
        have hle : p^j ≤ p^(j+1) := Nat.pow_le_pow_right hp.pos (by omega)
        rw [← Nat.cast_sub hle,Complex.norm_natCast]
        exact_mod_cast Nat.sub_le _ _
      · rw [if_neg h,zero_sub,norm_neg]
        by_cases hd : p^j∣n
        · rw [if_pos hd,Complex.norm_natCast]
          exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_left n (pow_pos hp.pos _))
            (Nat.dvd_gcd (pow_dvd_pow p (by omega : j≤j+1)) hd)
        · simp [hd]
  | coprime q r hq hr hc iq ir =>
    rw [ram_mul (by omega) (by omega) hc, norm_mul, Nat.gcd_comm (q*r) n,
      Nat.Coprime.gcd_mul n hc,Nat.cast_mul,Nat.gcd_comm n q,Nat.gcd_comm n r]
    exact mul_le_mul iq ir (norm_nonneg _) (by positivity)

end
end CornerFour

end

section

namespace CornerFour
open Finset MeasureTheory
noncomputable section

theorem nearMeas' (M g : ℕ) : MeasurableSet (near M g) := by
  unfold near
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases hj : j≤g
  · simp only [hj,true_and]
    exact measurableSet_le (f:=fun t:ℝ=>|t-(j:ℝ)/g|) (g:=fun _=>1/(4*(M:ℝ)*g)) (by fun_prop) measurable_const
  · simp [hj]

theorem assemble_atom (n M B H u v l r k s : ℕ) (hn : 0<n) (hH : 0<H) (hu : 0<u)
    (hv : 0<v) (huM : u≤M) (hvM : v≤M) (hru : r≤n/u) (hsv : s≤n/v)
    (C : ℝ) (hC : 0≤C)
    (away : (∫ t in (0:ℝ)..1, (near M (u.gcd v))ᶜ.indicator
          (fun x=>‖wave u l r x*wave v k s x‖) t) ≤
          C*((cornerLog n)^2+(M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v)))
    (peak : (∫ t in (0:ℝ)..1, (near M (u.gcd v) ∩ (wide n B H)ᶜ).indicator
          (osc n u v l r k s) t) = ∑ q∈(u.gcd v).divisors, peakRam n q*
          ∫ x in (-(1:ℝ)/(4*(M:ℝ)*(u.gcd v)))..(1/(4*(M:ℝ)*(u.gcd v))),
            {x:ℝ|annulus n M (u.gcd v) B H q x}.indicator (osc n u v l r k s) x) :
    ‖atom n B H u v l r k s‖ ≤ (C+2*Real.pi)*cornerCost n M B H u v := by
  classical
  let g := u.gcd v
  let N := near M g
  let D := (wide n B H)ᶜ
  let P := osc n u v l r k s
  let W := 1/(4*(M:ℝ)*g)
  let E (q : ℕ) := ∫ x in (-W)..W, {x:ℝ|annulus n M g B H q x}.indicator P x
  let f (q : ℕ) := if q≤B then (q.gcd n:ℝ)*q/H else (q.gcd n:ℝ)
  let R := (n:ℝ)/((u:ℝ)*v)
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ hu
  have hN : MeasurableSet N := nearMeas' ..
  have hD : MeasurableSet D := (wideMeas' ..).compl
  have contP : Continuous P := by unfold P osc wave phase; fun_prop
  have hint (S : Set ℝ) (hs : MeasurableSet S) : IntervalIntegrable (S.indicator P) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (contP.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hs
  have splitP : atom n B H u v l r k s = (∫ t in (0:ℝ)..1, (N∩D).indicator P t)+
        ∫ t in (0:ℝ)..1,(Nᶜ∩D).indicator P t := by
    rw [←intervalIntegral.integral_add (hint _ (hN.inter hD)) (hint _ (hN.compl.inter hD))]
    apply intervalIntegral.integral_congr; intro x _
    change D.indicator P x = _
    by_cases ha:x∈N <;> by_cases hb:x∈D <;> simp [ha,hb]
  have far : ‖∫ t in (0:ℝ)..1,(Nᶜ∩D).indicator P t‖ ≤
      C*((cornerLog n)^2+(M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v)) := by
    apply LE.le.trans _ away
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · apply Filter.Eventually.of_forall
      intro x _
      change ‖(Nᶜ∩D).indicator P x‖ ≤ Nᶜ.indicator _ x
      by_cases ha:x∈N <;> by_cases hb:x∈D <;> simp [ha,hb,P,osc] <;> positivity
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      have hc : Continuous (fun x=>‖wave u l r x*wave v k s x‖) := by unfold wave phase; fun_prop
      exact (hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hN.compl
  have area (q : ℕ) (hq : q∈g.divisors) : ‖peakRam n q*E q‖ ≤ (2*Real.pi*R)*f q := by
    have ha := annulus_budget n M g B H q u v l r k s hn hH (Nat.pos_of_mem_divisors hq) hg hu hv huM hvM hru hsv
    rw [neg_div] at ha
    change ‖E q‖≤_*R*_ at ha
    rw [norm_mul]
    apply (mul_le_mul (peakRam_le n q) ha (norm_nonneg _) (Nat.cast_nonneg _)).trans_eq
    dsimp [f]
    split <;> ring
  have sumnear : ‖∫ t in (0:ℝ)..1,(N∩D).indicator P t‖≤(2*Real.pi*R)*∑ q∈g.divisors,f q := by
    change (∫ t in (0:ℝ)..1,(N∩D).indicator P t)=_ at peak
    rw [neg_div] at peak
    rw [peak,mul_sum]
    exact (norm_sum_le ..).trans (sum_le_sum area)
  have hadd : ∑ q∈g.divisors, f q =
      (∑ q∈g.divisors.filter (·≤B),(q.gcd n:ℝ)*q/H) +
        ∑ q∈g.divisors.filter (B<·),(q.gcd n:ℝ) := by
    simp only [sum_filter,←sum_add_distrib]
    apply sum_congr rfl; intro q _
    by_cases h:q≤B <;> simp [f,h,show B<q ↔ ¬q≤B by omega]
  have hsum : 0≤∑ q∈g.divisors,f q := by
    apply sum_nonneg; intro q _; dsimp [f]; split <;> positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hbase : 0≤(cornerLog n)^2+(M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) := by positivity
  rw [splitP]
  apply (norm_add_le ..).trans
  apply (add_le_add sumnear far).trans
  unfold cornerCost
  change _ ≤ (C+2*Real.pi)*(_+R*_)
  rw [← hadd]
  nlinarith only [mul_nonneg hC (mul_nonneg hR hsum),mul_nonneg Real.pi_pos.le hbase]

end
end CornerFour

end

section

/- The elementary rational separation and reduced-fraction uniqueness arguments adapt
ChiyodaMomo01 (PR #1923, b0820ebb68754bebd52ee5512cbdf2ebd85677dd) and wzhxzkk
(93d33090fdfc93fb272dde08cb463f3bff3c64ce), goldbach-proofs, Apache-2.0. -/
namespace CornerFour
open Finset MeasureTheory
noncomputable section

def peakR (M g : ℕ) : ℝ := 1/(4*(M:ℝ)*g)
def nearCell (n M g B H q a : ℕ) : Set ℝ :=
  {t | annulus n M g B H q (t-(a:ℝ)/q)}
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

private theorem twoCenters {a b q r g M : ℕ} {t W : ℝ}
    (hq : 0<q) (hr : 0<r) (hqg : q≤g) (hrM : r≤M)
    (hrW : W ≤ 1/(4*(r:ℝ)*g)) (h₁ : |t-(a:ℝ)/q| ≤ peakR M g)
    (h₂ : |t-(b:ℝ)/r| ≤ W) : a*r=b*q := by
  by_contra h
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  have hr' : 0<(r:ℝ) := by exact_mod_cast hr
  have hs : 1/(4*(r:ℝ)*g) ≤ 1/(4*(r:ℝ)*q) := by
    apply one_div_le_one_div_of_le (by positivity); gcongr
  have hs' : peakR M g ≤ 1/(4*(r:ℝ)*q) := by
    apply one_div_le_one_div_of_le (by positivity); gcongr <;> assumption_mod_cast
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have he : 1/((q:ℝ)*r) = 4*(1/(4*(r:ℝ)*q)) := by field_simp
  have hh := centerSep hq hr h
  rw [he] at hh
  linarith [show 0 < 1/(4*(r:ℝ)*q) by positivity]

private theorem wide_at_peak {a q n M g B H : ℕ} {t : ℝ} (hn : 0<n) (hg : 0<g)
    (hq : q ∈ g.divisors) (ha : a∈numSet q) (hBM : B≤M) (hH : 4*H*g≤n)
    (ht : |t-(a:ℝ)/q|≤peakR M g) :
    t ∈ wide n B H ↔ q≤B ∧ |t-(a:ℝ)/q| ≤ (H:ℝ)/(q*n) := by
  have hqp := Nat.pos_of_mem_divisors hq
  obtain ⟨har,hac⟩ := mem_filter.mp ha
  constructor
  · rintro ⟨r,b,hr,hrB,hbr,hbc,hx⟩
    have hr' : 0<(r:ℝ) := by exact_mod_cast hr
    have hw : (H:ℝ)/(r*n) ≤ 1/(4*(r:ℝ)*g) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh : 4*(H:ℝ)*g≤n := by exact_mod_cast hH
      nlinarith [mul_le_mul_of_nonneg_left hh hr'.le]
    obtain ⟨rfl,rfl⟩ := centerEq hqp hr hac hbc
      (twoCenters hqp hr (Nat.le_of_dvd hg (Nat.mem_divisors.mp hq).1) (hrB.trans hBM) hw ht hx)
    exact ⟨hrB,hx⟩
  · rintro ⟨hqB,hx⟩
    exact ⟨q,a,hqp,hqB,by have := mem_range.mp har; omega,hac,hx⟩

private theorem mem_peak (n M g B H : ℕ) (hn : 0<n) (hg : 0<g)
    (hBM : B≤M) (hH : 4*H*g≤n) (t : ℝ) :
    t ∈ near M g ∩ (wide n B H)ᶜ ↔
       ∃ q ∈ g.divisors, ∃ a∈numSet q, t ∈ nearCell n M g B H q a := by
  constructor
  · rintro ⟨⟨j,hj,ht⟩,hw⟩
    obtain ⟨q,hq,a,ha,hc⟩ := centerOfGrid j g hg hj
    rw [hc] at ht
    refine ⟨q,hq,a,ha,ht,?_⟩
    have hh := (wide_at_peak hn hg hq ha hBM hH ht).not.mp hw
    simpa only [not_and_or,not_le] using hh
  · rintro ⟨q,hq,a,ha,ht⟩
    obtain ⟨j,hj,hc⟩ := gridOfCenter hq ha
    refine ⟨⟨j,hj,hc.symm ▸ ht.1⟩,?_⟩
    apply (wide_at_peak hn hg hq ha hBM hH ht.1).not.mpr
    simpa only [not_and_or,not_le] using ht.2

private theorem unique_peak {n M g B H q r a b : ℕ} {t : ℝ} (hg : 0<g) (hgM : g≤M)
    (hq : q ∈ g.divisors) (hr : r ∈ g.divisors)
    (ha : a∈numSet q) (hb : b∈numSet r) (hx : t∈ nearCell n M g B H q a)
    (hy : t∈nearCell n M g B H r b) : q=r ∧ a=b := by
  have hrM := (Nat.le_of_dvd hg (Nat.mem_divisors.mp hr).1).trans hgM
  have hrp := Nat.pos_of_mem_divisors hr
  apply centerEq (Nat.pos_of_mem_divisors hq) hrp (mem_filter.mp ha).2 (mem_filter.mp hb).2
  apply twoCenters (Nat.pos_of_mem_divisors hq) hrp (Nat.le_of_dvd hg (Nat.mem_divisors.mp hq).1)
    hrM (W:=peakR M g) _ hx.1 hy.1
  apply one_div_le_one_div_of_le (by positivity); gcongr

theorem peak_indicator (f : ℝ→ℂ) (n M g B H : ℕ) (hn : 0<n) (hg : 0<g) (hgM : g≤M)
    (hBM : B≤M) (hH : 4*H*g≤n) (t : ℝ) :
    (near M g ∩ (wide n B H)ᶜ).indicator f t =
    ∑ q ∈ g.divisors, ∑ a∈numSet q, (nearCell n M g B H q a).indicator f t := by
  classical
  by_cases ht : t ∈ near M g ∩ (wide n B H)ᶜ
  · obtain ⟨q,hq,a,ha,hm⟩ := (mem_peak n M g B H hn hg hBM hH t).mp ht
    rw [Set.indicator_of_mem ht, sum_eq_single_of_mem q hq]
    · rw [sum_eq_single_of_mem a ha,Set.indicator_of_mem hm]
      intro b hb hba
      exact Set.indicator_of_notMem (fun h => hba (unique_peak hg hgM hq hq hb ha h hm).2) _
    · intro r hr hrq
      apply sum_eq_zero
      intro b hb
      exact Set.indicator_of_notMem (fun h => hrq (unique_peak hg hgM hr hq hb ha h hm).1) _
  · rw [Set.indicator_of_notMem ht]
    symm; apply sum_eq_zero; intro q hq; apply sum_eq_zero; intro a ha
    apply Set.indicator_of_notMem; intro h
    exact ht ((mem_peak n M g B H hn hg hBM hH t).mpr ⟨q,hq,a,ha,h⟩)

end
end CornerFour

end

section

namespace CornerFour
open Finset MeasureTheory
noncomputable section

private theorem phase_addC (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast; congr 1; ring

private theorem phase_intC (m : ℤ) : phase m = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I m using 2
  push_cast; ring

private theorem wave_center {q u : ℕ} (hq : 0<q) (hd : q∣u) (l r a : ℕ) (x : ℝ) :
    wave u l r ((a:ℝ)/q+x) = wave u l r x := by
  obtain ⟨k,rfl⟩ := hd
  unfold wave
  apply sum_congr rfl
  intro h _
  rw [mul_add,phase_addC, show ((q*k*h:ℕ):ℝ)*((a:ℝ)/q) = ((k*h*a:ℕ):ℝ) by
    push_cast; field_simp]
  rw [show phase ((k*h*a:ℕ):ℝ)=1 by exact_mod_cast phase_intC ((k*h*a:ℕ):ℤ)]
  simp

private theorem osc_center {q u v : ℕ} (hq : 0<q) (hu : q∣u) (hv : q∣v)
    (n l r k s a : ℕ) (x : ℝ) : osc n u v l r k s ((a:ℝ)/q+x) =
    phase (-(n:ℝ)*((a:ℝ)/q)) * osc n u v l r k s x := by
  unfold osc
  rw [wave_center hq hu,wave_center hq hv,mul_add,phase_addC]
  ring

def peakWindow (n M g B H q : ℕ) : Set ℝ := {x | annulus n M g B H q x}

theorem window_meas (n M g B H q : ℕ) : MeasurableSet (peakWindow n M g B H q) := by
  change MeasurableSet ({x : ℝ | |x|≤peakR M g} ∩ ({_x : ℝ | B < q} ∪ {x : ℝ | (H:ℝ)/(q*n) < |x|}))
  exact (isClosed_le (f:=fun x:ℝ => |x|) (g:=fun _ => peakR M g) continuous_abs continuous_const).measurableSet.inter
    ((MeasurableSet.const (B<q)).union (isOpen_lt (f:=fun _:ℝ => (H:ℝ)/(q*n)) (g:=fun x:ℝ => |x|) continuous_const continuous_abs).measurableSet)

private theorem cell_meas (n M g B H q a : ℕ) : MeasurableSet (nearCell n M g B H q a) := by
  exact (window_meas n M g B H q).preimage (measurable_id.sub measurable_const)

private theorem osc_cont (n u v l r k s : ℕ) : Continuous (osc n u v l r k s) := by
  unfold osc wave phase
  fun_prop

set_option maxHeartbeats 850000 in
theorem peak_integral_cells (n M g B H : ℕ) (hn : 0<n) (hg : 0<g) (hgM : g≤M)
    (hBM : B≤M) (hH : 4*H*g≤n) (f : ℝ→ℂ) (hc : Continuous f) :
    (∫ t in (0:ℝ)..1, (near M g ∩ (wide n B H)ᶜ).indicator f t) =
    ∑ q ∈ g.divisors, ∑ a∈numSet q, ∫ t in (0:ℝ)..1, (nearCell n M g B H q a).indicator f t := by
  have hi (q a : ℕ) : IntervalIntegrable ((nearCell n M g B H q a).indicator f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (hc.integrableOn_Icc.indicator (cell_meas n M g B H q a))
  let F (q a : ℕ) := (nearCell n M g B H q a).indicator f
  calc
    _ = ∫ t in (0:ℝ)..1, ∑ q∈g.divisors, ∑ a∈numSet q,F q a t :=
      intervalIntegral.integral_congr (fun t _ => peak_indicator f n M g B H hn hg hgM hBM hH t)
    _ = ∑ q∈g.divisors, ∫ t in (0:ℝ)..1, ∑ a∈numSet q,F q a t :=
      intervalIntegral.integral_finsetSum (fun q _ => by
        simpa only [F, ← Finset.sum_apply] using IntervalIntegrable.sum (numSet q) (fun a _ => hi q a))
    _ = _ := sum_congr rfl fun q _ => intervalIntegral.integral_finsetSum (fun a _ => hi q a)

theorem centered_cell {q u v : ℕ} (hq : 0<q) (hu : q∣u) (hv : q∣v)
    (n M g B H l r k s a : ℕ) :
    (∫ t in (0:ℝ)..1, (nearCell n M g B H q a).indicator (osc n u v l r k s) t) =
    phase (-(n:ℝ)*((a:ℝ)/q)) * ∫ x in (-(a:ℝ)/q)..(1-(a:ℝ)/q),
      (peakWindow n M g B H q).indicator (osc n u v l r k s) x := by
  let c : ℝ := (a:ℝ)/q
  have ht (t : ℝ) :
      (nearCell n M g B H q a).indicator (osc n u v l r k s) t =
      phase (-(n:ℝ)*c) * (peakWindow n M g B H q).indicator (osc n u v l r k s) (t-c) := by
    by_cases hh : t-c∈peakWindow n M g B H q
    · rw [Set.indicator_of_mem (show t∈nearCell n M g B H q a from hh),Set.indicator_of_mem hh]
      simpa [c] using osc_center hq hu hv n l r k s a (t-c)
    · rw [Set.indicator_of_notMem (show t∉nearCell n M g B H q a from hh),Set.indicator_of_notMem hh,mul_zero]
  simp_rw [ht]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right]
  simp only [c,zero_sub,neg_div]

private theorem support_bounds {f : ℝ→ℂ} {D : Set ℝ} (hm : MeasurableSet D)
    {a b c d : ℝ} (hab : a≤b) (hcd : c≤d)
    (he : ∀ x∈D, (a≤x ∧ x≤b) ↔ (c≤x ∧ x≤d)) :
    (∫ t in a..b,D.indicator f t) = ∫ t in c..d,D.indicator f t := by
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc,← integral_Icc_eq_integral_Ioc,setIntegral_indicator hm,
    setIntegral_indicator hm]
  have hset : Set.Icc a b ∩ D = Set.Icc c d ∩ D := by
    ext x
    exact ⟨fun h => ⟨(he x h.2).mp h.1,h.2⟩,fun h => ⟨(he x h.2).mpr h.1,h.2⟩⟩
  rw [hset]

private theorem peakR_le {M g q : ℕ} (hg : 0<g) (hM : 0<M) (hq : q∈g.divisors) :
    peakR M g ≤ 1/(q:ℝ) := by
  apply one_div_le_one_div_of_le (by exact_mod_cast Nat.pos_of_mem_divisors hq)
  have hgq : (q:ℝ) ≤ g := by exact_mod_cast Nat.le_of_dvd hg (Nat.mem_divisors.mp hq).1
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [mul_le_mul_of_nonneg_right hM' (show (0:ℝ) ≤ g by positivity)]

private theorem sum_centered {q u v : ℕ} (hu : 0<u) (hv : 0<v)
    (n M B H l r k s : ℕ) (hM : 0<M) (hq : q∈(u.gcd v).divisors) :
    (∑ a∈numSet q, ∫ t in (0:ℝ)..1,
      (nearCell n M (u.gcd v) B H q a).indicator (osc n u v l r k s) t) =
    peakRam n q * ∫ x in (-peakR M (u.gcd v))..(peakR M (u.gcd v)),
      (peakWindow n M (u.gcd v) B H q).indicator (osc n u v l r k s) x := by
  let g := u.gcd v
  let R := peakR M g
  let D := peakWindow n M g B H q
  let f := osc n u v l r k s
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hq' := Nat.pos_of_mem_divisors hq
  have hqu := (Nat.mem_divisors.mp hq).1.trans (Nat.gcd_dvd_left u v)
  have hqv := (Nat.mem_divisors.mp hq).1.trans (Nat.gcd_dvd_right u v)
  have hm : MeasurableSet D := window_meas ..
  have hr0 : 0≤R := by dsimp [R,peakR]; positivity
  have hrq : R≤1/(q:ℝ) := peakR_le hg hM hq
  have bound (x : ℝ) (hx : x∈D) : -R≤x ∧ x≤R := abs_le.mp hx.1
  simp_rw [centered_cell hq' hqu hqv]
  change (∑ a∈numSet q, phase (-(n:ℝ)*((a:ℝ)/q)) *
    ∫ x in (-(a:ℝ)/q)..(1-(a:ℝ)/q),D.indicator f x) =
    peakRam n q * ∫ x in -R..R,D.indicator f x
  by_cases h1 : q=1
  · subst q
    have hR : R≤1 := by simpa using hrq
    have hzero : (∫ t in (0:ℝ)..1,D.indicator f t) = ∫ t in (0:ℝ)..R,D.indicator f t := by
      apply support_bounds hm (by norm_num) hr0
      intro x hx; have hh := bound x hx; grind
    have hone : (∫ t in (-1:ℝ)..0,D.indicator f t) = ∫ t in -R..0,D.indicator f t := by
      apply support_bounds hm (by norm_num) (by linarith)
      intro x hx; have hh := bound x hx; grind
    have hint (a b : ℝ) (hab : a≤b) : IntervalIntegrable (D.indicator f) volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
        ((osc_cont n u v l r k s).integrableOn_Icc.indicator hm)
    have hp : phase (-(n:ℝ))=1 := by simpa using phase_intC (-(n:ℤ))
    have hp0 : phase 0 = 1 := by simp [phase]
    have hnum : numSet 1={0,1} := by decide
    have hr1 : peakRam n 1=1 := by simp [peakRam,phase]
    rw [hr1,hnum]
    simp only [Finset.sum_insert (show (0:ℕ) ∉ ({1}:Finset ℕ) by decide),Finset.sum_singleton,
      Nat.cast_one,Nat.cast_zero,div_one,mul_zero,neg_zero,sub_zero,hp0,mul_one,hp,one_mul,
      sub_self,hzero,hone]
    rw [add_comm,intervalIntegral.integral_add_adjacent_intervals (hint _ _ (by linarith)) (hint _ _ hr0)]
  · have har (a : ℕ) (ha : a∈numSet q) : 0<a ∧ a<q := by
      obtain ⟨har,hac⟩ := mem_filter.mp ha
      have har' := mem_range.mp har
      constructor
      · by_contra! hz; have he : a=0 := by omega
        simpa [he,h1] using hac
      · by_contra! h; have he : a=q := by omega
        simpa [he,Nat.Coprime,h1] using hac
    have hnum : numSet q = (range q).filter (fun a=>a.Coprime q) := by
      ext a
      constructor
      · intro h
        exact mem_filter.mpr ⟨mem_range.mpr (har a h).2,(mem_filter.mp h).2⟩
      · intro h
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp h).1;omega),(mem_filter.mp h).2⟩
    rw [peakRam,← hnum,sum_mul]
    apply sum_congr rfl
    intro a ha
    congr 1
    obtain ⟨ha0,haq⟩ := har a ha
    have hqR : (0:ℝ)<q := by exact_mod_cast hq'
    have hlow : R ≤ (a:ℝ)/q := hrq.trans ((div_le_div_iff_of_pos_right hqR).mpr (by exact_mod_cast ha0))
    have hhigh : R ≤ 1-(a:ℝ)/q := by
      apply hrq.trans
      rw [le_sub_iff_add_le,← add_div,div_le_iff₀ hqR,one_mul]
      exact_mod_cast (by omega : 1+a≤q)
    simp only [neg_div]
    apply support_bounds hm (by linarith) (by linarith)
    intro x hx
    have hh := bound x hx
    constructor <;> intro _ <;> constructor <;> linarith

theorem common_peak (n M B H u v l r k s : ℕ) (hn : 0<n) (hu : 0<u) (hv : 0<v)
    (huM : u≤M) (hBM : B≤M) (hH : 4*H*(u.gcd v)≤n) :
    (∫ t in (0:ℝ)..1, (near M (u.gcd v) ∩ (wide n B H)ᶜ).indicator (osc n u v l r k s) t) =
    ∑ q∈(u.gcd v).divisors,peakRam n q *
      (∫ x in (-(1:ℝ)/(4*(M:ℝ)*(u.gcd v)))..(1/(4*(M:ℝ)*(u.gcd v))),
       {x : ℝ | annulus n M (u.gcd v) B H q x}.indicator (osc n u v l r k s) x) := by
  have hg := Nat.gcd_pos_of_pos_left v hu
  rw [peak_integral_cells n M (u.gcd v) B H hn hg ((Nat.gcd_le_left v hu).trans huM)
    hBM hH _ (osc_cont ..)]
  apply sum_congr rfl
  intro q hq
  simpa only [peakR,neg_div,peakWindow] using sum_centered hu hv n M B H l r k s (hu.trans_le huM) hq

end
end CornerFour

end

section

namespace CornerFour
open Finset
noncomputable section

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
end
end CornerFour

end

section

namespace CornerFour
open Finset
noncomputable section

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
end
end CornerFour

end

section

namespace CornerFour
open MeasureTheory Set
noncomputable section
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
        rw [integral_zpow (Or.inr ⟨by norm_num,notMem_uIcc_of_lt ha (by positivity)⟩)]
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
end
end CornerFour

end

section

namespace CornerFour
open Finset
noncomputable section

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
end
end CornerFour

end

section

namespace CornerFour
open Finset MeasureTheory
noncomputable section

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

theorem awayPoint (n M u v l r k s : ℕ) (hu : 0<u) (hv : 0<v) (hM : 0<M)
    (hr : r≤n/u) (hs : s≤n/v) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    (near M (u.gcd v))ᶜ.indicator (fun x=>‖wave u l r x * wave v k s x‖) t ≤
      ∑ z ∈ centers u v, pairEnv (1/((n:ℝ)+1)) (1/(4*(M:ℝ)*(u.gcd v:ℝ))) u v z t := by
  classical
  let a : ℝ := 1/((n:ℝ)+1)
  let b : ℝ := 1/(4*(M:ℝ)*(u.gcd v:ℝ))
  have ha : 0<a := by dsimp [a]; positivity
  have hg : 0<u.gcd v := Nat.gcd_pos_of_pos_left v hu
  have hb : 0<b := by dsimp [b]; positivity
  by_cases hm : t∈(near M (u.gcd v))ᶜ
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

end
end CornerFour

end

section

namespace CornerFour
open Finset MeasureTheory
noncomputable section

theorem nearMeasAway (M g : ℕ) : MeasurableSet (near M g) := by
  unfold near
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases h : j≤g
  · simp only [h,true_and]
    exact measurableSet_le (f:= fun t:ℝ => |t-(j:ℝ)/g|) (g:=fun _=>1/(4*(M:ℝ)*g)) (by fun_prop) measurable_const
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

theorem awayBound : ∃ C : ℝ, 0<C ∧ ∀ (n M u v l r k s : ℕ), 1≤u → 1≤v → u≤M → v≤M → M≤n →
    r≤n/u → s≤n/v →
    (∫ t in (0:ℝ)..1, (near M (u.gcd v))ᶜ.indicator (fun x=>‖wave u l r x * wave v k s x‖) t) ≤
      C * ((1+Real.log ((n:ℝ)+2))^2 + (M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v)) := by
  refine ⟨512,by norm_num,?_⟩
  intro n M u v l r k s hu hv hum hvm hmn hr hs
  let g := u.gcd v
  let a : ℝ := 1/((n:ℝ)+1)
  let b : ℝ := 1/(4*(M:ℝ)*g)
  let W : ℝ := Real.log ((n:ℝ)+2)
  have hm : 0<M := hu.trans hum
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have ha : 0<a := by dsimp [a];positivity
  have hb : 0<b := by dsimp [b];positivity
  have hw : 0≤W := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hI : IntervalIntegrable ((near M g)ᶜ.indicator (fun x=>‖wave u l r x * wave v k s x‖)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hc : Continuous (fun x=>‖wave u l r x * wave v k s x‖) := by unfold wave phase;fun_prop
    exact (hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator (nearMeasAway M g).compl
  have hJ (z : ℕ×ℕ) := (pair_cont a b ha hb u v z).intervalIntegrable (μ:=volume) 0 1
  have hbound := intervalIntegral.integral_mono_on zero_le_one hI (IntervalIntegrable.sum (centers u v) (fun z _ => hJ z))
    (fun t ht => by simpa only [Finset.sum_apply] using awayPoint n M u v l r k s hu hv hm hr hs t ht)
  simp only [Finset.sum_apply] at hbound
  rw [intervalIntegral.integral_finsetSum (fun z _ => hJ z)] at hbound
  have hx := hbound.trans (sum_le_sum (s:=centers u v) (fun z hz => pair_integral n b hb u v hu hv z hz))
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hx
  have hco : 0≤16*W/((u:ℝ)*v) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (coincidentCount u v hu hv) (show 0≤32/((u:ℝ)*v*b) by positivity)
  have h2 := mul_le_mul_of_nonneg_left (spacingSum n u v hu hv (hum.trans hmn) (hvm.trans hmn)) hco
  have hc : (32/((u:ℝ)*v*b))*(4*(u.gcd v:ℝ))=512*((M:ℝ)*g^2/((u:ℝ)*v)) := by
    dsimp [b,g];field_simp;ring
  rw [hc] at h1
  have hd : (16*W/((u:ℝ)*v))*(8*((u:ℝ)*v)*(1+W))=128*W*(1+W) := by field_simp;ring
  change _ ≤ (16*W/((u:ℝ)*v))*(8*((u:ℝ)*v)*(1+W)) at h2
  rw [hd] at h2
  change _ ≤ 512*((1+W)^2+(M:ℝ)*g^2/((u:ℝ)*v))
  have hlin : 128*W*(1+W) ≤ 512*(1+W)^2 := by nlinarith [sq_nonneg W]
  exact hx.trans (by linarith only [h1,h2,hlin])
end
end CornerFour

end

section

namespace CornerFour

theorem main : ∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n →
    ‖J4 n (cutU n) (cutT n) (cutB n) (cutH n)‖≤e*n := by
  obtain ⟨C,hC,away⟩ := awayBound
  apply of_atoms (C+2*Real.pi) (by positivity)
  intro n M B H u v l r k s hn hH _ hBM hMn hu hv huM hvM hru hsv hg
  exact assemble_atom n M B H u v l r k s hn hH hu hv huM hvM hru hsv C hC.le
    (away n M u v l r k s hu hv huM hvM hMn hru hsv)
    (common_peak n M B H u v l r k s hn hu hv huM hBM hg)

end CornerFour

end

theorem PEqualNP.Outside.L_goldbach_frontier_type2_b4_b4 : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₄ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₃ n < a ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₄ n) (τ₄ n)‖ ≤ e * (n : ℝ) := by exact CornerFour.main
