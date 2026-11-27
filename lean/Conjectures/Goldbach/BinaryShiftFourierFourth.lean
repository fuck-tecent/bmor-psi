import Mathlib

open Finset

namespace Goldbach.DyadicPairs

/-- The sum determines its largest exponent, as it lies in (2^b,2^(b+1)]. -/
theorem ordered {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : (2:ℕ)^a + 2^b = 2^c + 2^d) : a = c ∧ b = d := by
  have bound {i j k l : ℕ} (hij : i ≤ j) (hjk : j < k) :
      (2:ℕ)^i + 2^j < 2^l + 2^k := by
    have hi : (2:ℕ)^i ≤ 2^j := Nat.pow_le_pow_right (by decide) hij
    have hk : (2:ℕ)^(j+1) ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have hl : 0 < (2:ℕ)^l := by positivity
    rw [pow_succ] at hk
    omega
  have he : b = d := by
    rcases lt_trichotomy b d with hb | hb | hb
    · exact False.elim ((ne_of_lt (bound (l:=c) hab hb)) h)
    · exact hb
    · exact False.elim ((ne_of_lt (bound (l:=a) hcd hb)) h.symm)
  subst d
  exact ⟨(Nat.pow_right_injective (by decide : 2 ≤ 2)) (Nat.add_right_cancel h), rfl⟩

theorem pair_eq {a b c d : ℕ} (h : (2:ℕ)^a + 2^b = 2^c + 2^d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · exact Or.inl (ordered hab hcd h)
  · exact Or.inr (ordered hab hdc (by simpa only [Nat.add_comm (2^d)] using h))
  · exact Or.inr ((ordered hba hcd (by simpa only [Nat.add_comm (2^b)] using h)).symm)
  · exact Or.inl ((ordered hba hdc (by simpa only [Nat.add_comm (2^b),Nat.add_comm (2^d)] using h)).symm)

end Goldbach.DyadicPairs

open MeasureTheory
open scoped ComplexConjugate
namespace Goldbach.DyadicFourth

/- The character and its integral are reused from FourSevenths.Coefficient in
   ExceptionFourSeventhsCountingBridge, adapted there from L_goldbach_arc_coefficient_sum. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]


theorem eneg (x : ℝ) : conj (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
  ring

def freq (u : ℕ × ℕ) : ℕ := 2^(u.1+1) + 2^(u.2+1)

theorem same_freq (u v : ℕ × ℕ) : freq u = freq v ↔ v=u ∨ v=u.swap := by
  obtain ⟨i,j⟩ := u
  obtain ⟨a,b⟩ := v
  constructor
  · intro h
    rcases Goldbach.DyadicPairs.pair_eq h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
      simp only [Nat.add_right_cancel_iff] at h₁ h₂ <;> subst a <;> subst b <;> simp
  · rintro (h | h)
    · exact congrArg freq h.symm
    · rw [h]
      exact Nat.add_comm ..

theorem row (L : ℕ) (u : ℕ × ℕ) (hu : u ∈ range L ×ˢ range L) :
    (∑ v ∈ range L ×ˢ range L, if freq u = freq v then (1:ℂ) else 0) =
      2 - (if u.1=u.2 then 1 else 0) := by
  obtain ⟨i,j⟩ := u
  have hswap : (j,i) ∈ range L ×ˢ range L := mem_product.mpr ⟨(mem_product.mp hu).2,(mem_product.mp hu).1⟩
  have hx (v : ℕ × ℕ) : (if freq (i,j) = freq v then (1:ℂ) else 0) =
      (if v=(i,j) then 1 else 0) + (if v=(j,i) then 1 else 0) -
        (if i=j then (if v=(i,j) then 1 else 0) else 0) := by
    simp only [same_freq,Prod.swap_prod_mk]
    by_cases h : i=j
    · subst j
      by_cases hv : v=(i,i) <;> simp [hv]
    · have hne : (i,j) ≠ (j,i) := by simp [h]
      by_cases hv : v=(i,j)
      · subst v
        simp [h,hne]
      · by_cases hw : v=(j,i) <;> simp [hv,hw,h]
  simp_rw [hx]
  rw [sum_sub_distrib,sum_add_distrib]
  have hj : j<L := mem_range.mp (mem_product.mp hu).2
  by_cases h : i=j <;> simp [h,hu,hswap,hj] <;> norm_num

theorem fourth (L : ℕ) :
    (∫ t in (0:ℝ)..1, ‖∑ j ∈ range L, E ((2:ℝ)^(j+1)*t)‖^4) = 2*(L:ℝ)^2-L := by
  let s := range L
  let d := s ×ˢ s
  let F := fun (u v : ℕ × ℕ) (t : ℝ) => E ((((freq u : ℤ) - freq v : ℤ):ℝ)*t)
  have hc (u v : ℕ × ℕ) : Continuous (F u v) := by dsimp [F,E]; fun_prop
  have square (t : ℝ) : (∑ j ∈ s, E ((2:ℝ)^(j+1)*t))^2 =
      ∑ u ∈ d, E ((freq u:ℝ)*t) := by
    rw [sq,sum_mul,show d=s ×ˢ s by rfl,sum_product]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← phase_add]
    dsimp [freq]
    push_cast
    ring_nf
  have pt (t : ℝ) : ((‖∑ j ∈ s, E ((2:ℝ)^(j+1)*t)‖^4 : ℝ):ℂ) =
      ∑ u ∈ d, ∑ v ∈ d, F u v t := by
    let z := ∑ j ∈ s, E ((2:ℝ)^(j+1)*t)
    have hz : ((‖z‖^4 : ℝ):ℂ) = z^2*conj (z^2) := by
      rw [Complex.mul_conj',norm_pow]
      push_cast
      ring
    rw [hz,show z^2 = _ from square t, map_sum,sum_mul]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    rw [eneg, ← phase_add]
    dsimp [F]
    push_cast
    ring_nf
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [show ∀ t : ℝ, ((‖∑ j ∈ range L, E ((2:ℝ)^(j+1)*t)‖^4:ℝ):ℂ) = _ from pt]
  rw [intervalIntegral.integral_finsetSum (fun u _ =>
    (continuous_finsetSum d (fun v _ => hc u v)).intervalIntegrable ..)]
  have vals (u : ℕ × ℕ) (hu : u ∈ d) :
      (∫ t in (0:ℝ)..1, ∑ v ∈ d, F u v t) = 2 - (if u.1=u.2 then 1 else 0) := by
    rw [intervalIntegral.integral_finsetSum (fun v _ => (hc u v).intervalIntegrable ..)]
    simp only [F,fourier_mode,sub_eq_zero,Int.natCast_inj]
    exact row L u hu
  rw [sum_congr rfl vals, sum_sub_distrib]
  have diag : (∑ u ∈ d, if u.1=u.2 then (1:ℂ) else 0) = (L:ℂ) := by
    dsimp [d]
    rw [sum_product]
    have hfilter : (range L).filter (fun x => x < L) = range L :=
      filter_true_of_mem (fun _ h => mem_range.mp h)
    simpa [s] using congrArg card hfilter
  rw [diag]
  simp [d,s]
  ring

end Goldbach.DyadicFourth

open Goldbach.DyadicFourth in
theorem Conjectures.Goldbach.BinaryShiftFourierFourth :
    let T := fun (L : ℕ) (t : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2*Real.pi*(2:ℝ)^(j+1)*t:ℝ):ℂ)*Complex.I); ∀ L : ℕ, intervalIntegral (fun t => ‖T L t‖^4) (0:ℝ) 1 MeasureTheory.volume = 2*(L:ℝ)^2-(L:ℝ) := by
  intro T L
  have ht (t : ℝ) : T L t = ∑ j ∈ range L, E ((2:ℝ)^(j+1)*t) := by
    apply sum_congr rfl
    intro j _
    unfold E
    rw [mul_assoc (2*Real.pi)]
  simpa only [ht] using fourth L
