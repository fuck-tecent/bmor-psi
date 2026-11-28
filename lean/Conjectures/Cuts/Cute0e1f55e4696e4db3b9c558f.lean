import Mathlib

/- The dyadic translation argument follows muoshuosha, goldbach-proofs #3793,
04429e06c04c3c87e0f24438aa6860a152d42f9d. The fixed-row middle band uses
the cube-root height and a denominator cutoff of 5/24. See also HymnOfLight,
goldbach-proofs #3883, b3e8a9fec6067484ff44957e93f85e23697040a5, for signed
middle-arc tails on a different range of rows. The sources are Apache-2.0. -/

-- child 1 zh: 在固定行 N=2X，统计中间弧系数实部至少为 −X/32 的无素数对偶频率，证明其数目至多为常数乘 X^(191/240)。
-- child 1 en: On the fixed row N=2X, bound missed even frequencies with middle coefficient real part at least -X/32 by a constant times X^(191/240).
-- child 2 zh: 在同一固定行及分母范围内，证明中间弧系数实部低于 −X/32 的偶频率数为 O(X^α)，其中 α<4/5。
-- child 2 en: On the same fixed row and rational windows, show that the number of even frequencies with middle real part below -X/32 is O(X^alpha) for some alpha below 4/5.

open Finset Filter
open scoped Topology

theorem Conjectures.Cuts.Cute0e1f55e4696e4db3b9c558f
    (h₁ :
  let e := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0
  let S := fun (N : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (N+1), (w k:ℂ)*e ((k:ℝ)*t)
  let B := fun N : ℕ => {t : ℝ | ∃ q a : ℕ, (Nat.log 2 (N+2))^2 < q ∧
    q ≤ ⌊(N:ℝ)^(5/24:ℝ)⌋₊ ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (⌊(N:ℝ)^(1/3:ℝ)⌋₊ : ℕ)/((q:ℝ)*N)}
  let J := fun (X m : ℕ) => (intervalIntegral (fun t => (B (2*X)).indicator
    (fun u => (S (2*X) u)^2*e (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re
  let I := fun X : ℕ => (Finset.Icc (X/2) (2*X)).filter (fun m => 4 ≤ m ∧ Even m)
  let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card
  ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    (((I X).filter (fun m => G m=0 ∧ -(X:ℝ)/32 ≤ J X m)).card:ℝ) ≤ C*(X:ℝ)^(191/240:ℝ))
    (h₂ :
  let e := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0
  let S := fun (N : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (N+1), (w k:ℂ)*e ((k:ℝ)*t)
  let B := fun N : ℕ => {t : ℝ | ∃ q a : ℕ, (Nat.log 2 (N+2))^2 < q ∧
    q ≤ ⌊(N:ℝ)^(5/24:ℝ)⌋₊ ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (⌊(N:ℝ)^(1/3:ℝ)⌋₊ : ℕ)/((q:ℝ)*N)}
  let J := fun (X m : ℕ) => (intervalIntegral (fun t => (B (2*X)).indicator
    (fun u => (S (2*X) u)^2*e (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re
  let I := fun X : ℕ => (Finset.Icc (X/2) (2*X)).filter (fun m => 4 ≤ m ∧ Even m)
  ∃ α C : ℝ, α<4/5 ∧ 0<C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    (((I X).filter (fun m => J X m < -(X:ℝ)/32)).card:ℝ) ≤ C*(X:ℝ)^α) :
    (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4) := by
  classical
  let e := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0
  let S := fun (N : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (N+1), (w k:ℂ)*e ((k:ℝ)*t)
  let B := fun N : ℕ => {t : ℝ | ∃ q a : ℕ, (Nat.log 2 (N+2))^2 < q ∧
    q ≤ ⌊(N:ℝ)^(5/24:ℝ)⌋₊ ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (⌊(N:ℝ)^(1/3:ℝ)⌋₊ : ℕ)/((q:ℝ)*N)}
  let J := fun (X m : ℕ) => (intervalIntegral (fun t => (B (2*X)).indicator
    (fun u => (S (2*X) u)^2*e (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re
  let I := fun X : ℕ => (Finset.Icc (X/2) (2*X)).filter (fun m => 4 ≤ m ∧ Even m)
  let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card
  let H := fun X : ℕ => (I X).filter (fun m => G m=0 ∧ -(X:ℝ)/32 ≤ J X m)
  let T := fun X : ℕ => (I X).filter (fun m => J X m < -(X:ℝ)/32)
  let U := fun X : ℕ => (Ico X (2*X)).filter (fun n => Even n ∧
    0 < ((Icc 1 (Nat.log 2 X/2)).filter (fun j => G (n-2^j)=0)).card)
  change ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ((H X).card:ℝ) ≤ C*(X:ℝ)^(191/240:ℝ) at h₁
  change ∃ α C : ℝ, α<4/5 ∧ 0<C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ((T X).card:ℝ) ≤ C*(X:ℝ)^α at h₂
  change ∃ X₀ : ℕ, ∀ X ≥ X₀, (U X).card^5 ≤ X^4
  have cover (X : ℕ) (hX : 8≤X) : (U X).card ≤ (Nat.log 2 X/2)*((H X).card+(T X).card) := by
    let P := (Icc 1 (Nat.log 2 X/2)).product (H X ∪ T X)
    let shift (z : ℕ × ℕ) := z.2+2^z.1
    have hsub : U X ⊆ P.image shift := by
      intro n hn
      obtain ⟨hi,heven,hmiss⟩ := mem_filter.mp hn
      obtain ⟨hl,hu⟩ := mem_Ico.mp hi
      obtain ⟨j,hj⟩ := card_pos.mp hmiss
      obtain ⟨hjI,hzero⟩ := mem_filter.mp hj
      obtain ⟨hj1,hjL⟩ := mem_Icc.mp hjI
      have hpow : 2^(j+1) ≤ X :=
        (Nat.pow_le_pow_right (by decide) (show j+1≤Nat.log 2 X by omega)).trans
          (Nat.pow_log_le_self 2 (by omega))
      rw [pow_succ] at hpow
      have hEven := even_iff_two_dvd.mpr (Nat.dvd_sub (even_iff_two_dvd.mp heven)
        (dvd_pow_self 2 (show j≠0 by omega)))
      let m := n-2^j
      have hm : m∈I X := mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp [m];omega,by dsimp [m];omega⟩,
        by dsimp [m];omega,hEven⟩
      have hpart : m∈H X ∪ T X := by
        by_cases h : J X m < -(X:ℝ)/32
        · exact mem_union_right _ (mem_filter.mpr ⟨hm,h⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨hm,hzero,le_of_not_gt h⟩)
      exact mem_image.mpr ⟨(j,m),mem_product.mpr ⟨hjI,hpart⟩,by dsimp [shift,m];omega⟩
    calc
      _ ≤ (P.image shift).card := card_le_card hsub
      _ ≤ P.card := card_image_le
      _ = (Nat.log 2 X/2)*(H X ∪ T X).card := by
        have hI : (Icc 1 (Nat.log 2 X/2)).card = Nat.log 2 X/2 := by simp [Nat.card_Icc]
        exact (card_product (Icc 1 (Nat.log 2 X/2)) (H X ∪ T X)).trans (congrArg (fun j : ℕ => j*(H X ∪ T X).card) hI)
      _ ≤ _ := Nat.mul_le_mul_left _ (card_union_le ..)
  obtain ⟨C,hC,A,hA⟩ := h₁
  obtain ⟨α,D,hα,hD,B₀,hB⟩ := h₂
  let b := max (191/240:ℝ) α
  let s := (4/5-b)/2
  have hb : b<4/5 := max_lt (by norm_num) hα
  have hs : 0<s := by dsimp [s];linarith
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K := (C+D)/(s*Real.log 2)
  have hlim := (tendsto_rpow_atTop hs).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 8,eventually_ge_atTop A,eventually_ge_atTop B₀,hlim.eventually_ge_atTop K]
    with X h8 hXA hXB hK
  change K≤(X:ℝ)^s at hK
  have hx : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  have hp := zero_lt_one.trans_le hx
  have h₁' := (hA X hXA).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx (le_max_left (191/240:ℝ) α)) hC.le)
  have h₂' := (hB X hXB).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx (le_max_right (191/240:ℝ) α)) hD.le)
  have hadd : ((H X).card:ℝ)+((T X).card:ℝ) ≤ (C+D)*(X:ℝ)^b :=
    (add_le_add h₁' h₂').trans_eq (by ring)
  have hL : ((Nat.log 2 X/2:ℕ):ℝ) ≤ (X:ℝ)^s/(s*Real.log 2) := calc
    _ ≤ Real.log (X:ℝ)/Real.log 2 :=
      (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
    _ ≤ ((X:ℝ)^s/s)/Real.log 2 := div_le_div_of_nonneg_right (Real.log_le_rpow_div hp.le hs) hlog.le
    _ = _ := div_div ..
  have hc : ((U X).card:ℝ) ≤ (X:ℝ)^(4/5:ℝ) := calc
    _ ≤ ((Nat.log 2 X/2:ℕ):ℝ)*(((H X).card:ℝ)+((T X).card:ℝ)) := by exact_mod_cast cover X h8
    _ ≤ ((X:ℝ)^s/(s*Real.log 2))*((C+D)*(X:ℝ)^b) :=
      mul_le_mul hL hadd (by positivity) (by positivity)
    _ = K*((X:ℝ)^s*(X:ℝ)^b) := by dsimp [K];ring
    _ ≤ (X:ℝ)^s*((X:ℝ)^s*(X:ℝ)^b) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by rw [←Real.rpow_add hp,←Real.rpow_add hp,show s+(s+b)=4/5 by dsimp [s];ring]
  have hfinal : ((U X).card:ℝ)^5 ≤ (X:ℝ)^4 := calc
    _ ≤ ((X:ℝ)^(4/5:ℝ))^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
    _ = _ := by rw [←Real.rpow_mul_natCast hp.le,show (4/5:ℝ)*(5:ℕ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast]
  exact_mod_cast hfinal
