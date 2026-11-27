import Mathlib
import Conjectures.Goldbach.PacketBinaryOrbitSecondMoment

namespace Conjectures.Goldbach.PacketLongFactorCenters_aux

private abbrev frequency (j : ℕ) := (2 : ℕ) ^ (j + 1)

private theorem spacing {q d H i j : ℕ} (hd : Odd d) (hdq : d ∣ q)
    (period : ∀ h : ℕ, 1 ≤ h → h ≤ H → ¬ d ∣ 2 ^ h - 1)
    (hij : i < j) (eqv : frequency i ≡ frequency j [MOD q]) : H < j - i := by
  by_contra! short
  have hj : j + 1 = (i + 1) + (j - i) := by omega
  have hmod := Nat.ModEq.of_dvd hdq eqv
  change 2^(i+1) ≡ 2^(j+1) [MOD d] at hmod
  rw [hj, pow_add (2 : ℕ) (i+1) (j-i)] at hmod
  have hone : 1 ≡ 2^(j-i) [MOD d] :=
    Nat.ModEq.cancel_left_of_coprime (hd.coprime_two_right.pow_right (i+1))
      (by simpa only [mul_one] using hmod)
  exact period (j-i) (by omega) short hone.dvd'

private theorem same_block {H i j : ℕ} (h : i / (H+1) = j / (H+1)) :
    j - i ≤ H := by
  have lo := Nat.div_mul_le_self i (H+1)
  have hi := Nat.lt_mul_div_succ j (Nat.succ_pos H)
  rw [← h, Nat.mul_comm (H+1), Nat.add_mul, one_mul] at hi
  omega

private theorem collision_bound {q d H m : ℕ} (hd : Odd d) (hdq : d ∣ q)
    (period : ∀ h : ℕ, 1 ≤ h → h ≤ H → ¬ d ∣ 2 ^ h - 1) :
    (((Finset.range m ×ˢ Finset.range m).filter (fun p =>
      frequency p.1 % q = frequency p.2 % q)).card) ≤ m * ((m-1)/(H+1) + 1) := by
  let hits := (Finset.range m ×ˢ Finset.range m).filter
    (fun p => frequency p.1 % q = frequency p.2 % q)
  let buckets := Finset.range m ×ˢ Finset.range ((m-1)/(H+1)+1)
  have inj : hits.card ≤ buckets.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1, p.2 / (H+1)))
    · intro p hp
      obtain ⟨hpair, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨hi,hj⟩ := Finset.mem_product.mp hpair
      have hj' := Finset.mem_range.mp hj
      exact Finset.mem_product.mpr ⟨hi, Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.div_le_div_right (show p.2 ≤ m-1 by omega)))⟩
    · rintro ⟨i,j⟩ h₁ ⟨k,l⟩ h₂ eqv
      have he := congrArg Prod.fst eqv
      change i = k at he
      subst k
      have hb := congrArg Prod.snd eqv
      change j / (H+1) = l / (H+1) at hb
      have hj : frequency i ≡ frequency j [MOD q] := (Finset.mem_filter.mp h₁).2
      have hl : frequency i ≡ frequency l [MOD q] := (Finset.mem_filter.mp h₂).2
      have h := hj.symm.trans hl
      rcases lt_trichotomy j l with hlt | heq | hgt
      · exact False.elim ((not_lt_of_ge (same_block hb)) (spacing hd hdq period hlt h))
      · simp [heq]
      · exact False.elim ((not_lt_of_ge (same_block hb.symm)) (spacing hd hdq period hgt h.symm))
  simpa [buckets, hits] using inj

end Conjectures.Goldbach.PacketLongFactorCenters_aux

open Conjectures.Goldbach.PacketLongFactorCenters_aux in
theorem Conjectures.Goldbach.PacketLongFactorCenters :
    ∀ (q d H m : ℕ) (u : ℝ), 1 < q → 0 < m → 0 < u → Odd d → d ∣ q →
    (∀ h : ℕ, 1 ≤ h → h ≤ H → ¬ d ∣ 2 ^ h - 1) →
    let K := fun t : ℝ => (∑ j ∈ Finset.range m,
      Real.cos (2 * Real.pi * (2 : ℝ)^(j+1) * t)) / (m : ℝ)
    (m : ℝ) * u^2 * (((Finset.range (q+1)).filter
      (fun a => Nat.Coprime a q ∧ u < K ((a:ℝ)/(q:ℝ)))).card : ℝ)
      ≤ (q : ℝ) * (((m-1)/(H+1) + 1 : ℕ) : ℝ) := by
  intro q d H m u hq hm hu hd hdq period K
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let z (a : ℕ) := ∑ j ∈ Finset.range m, E ((frequency j : ℝ)*(a : ℝ)/(q : ℝ))
  let A := (Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ u < K ((a:ℝ)/(q:ℝ)))
  have hsub : A ⊆ Finset.range q := by
    intro a ha
    obtain ⟨hr, hc, _⟩ := Finset.mem_filter.mp ha
    have har := Finset.mem_range.mp hr
    apply Finset.mem_range.mpr
    by_contra! h
    have : a = q := by omega
    subst a
    simp at hc
    omega
  have mpos : (0:ℝ) < m := by exact_mod_cast hm
  have phase (a : ℕ) : (z a).re = K ((a:ℝ)/(q:ℝ)) * m := by
    simp only [z, Complex.re_sum, E, Complex.exp_ofReal_mul_I_re, K,
      div_mul_cancel₀ _ mpos.ne']
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [frequency, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have energy := Conjectures.Goldbach.PacketBinaryOrbitSecondMoment q m (by omega : 0<q)
  change (∑ a ∈ Finset.range q, ‖z a‖^2) = _ at energy
  have cnt := collision_bound (m:=m) hd hdq period
  have cap : (∑ a ∈ Finset.range q, ‖z a‖^2) ≤
      (q:ℝ)*((m:ℝ)*(((m-1)/(H+1)+1:ℕ):ℝ)) := by
    rw [energy]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact_mod_cast cnt
  have tail : (∑ _a ∈ A, (u * m)^2) ≤ ∑ a ∈ Finset.range q, ‖z a‖^2 := by
    apply le_trans (Finset.sum_le_sum (g:=fun a => ‖z a‖^2) ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => sq_nonneg _))
    intro a ha
    have h := ((Finset.mem_filter.mp ha).2.2.le : u ≤ K ((a:ℝ)/(q:ℝ)))
    have h' := mul_le_mul_of_nonneg_right h mpos.le
    rw [← phase] at h'
    exact pow_le_pow_left₀ (mul_nonneg hu.le mpos.le) (h'.trans (Complex.re_le_norm _)) 2
  have tot := tail.trans cap
  simp only [Finset.sum_const, nsmul_eq_mul] at tot
  change (m:ℝ)*u^2*(A.card:ℝ) ≤ _
  apply (le_of_mul_le_mul_left (a:=(m:ℝ)) _ mpos)
  linarith only [show (A.card:ℝ)*(u*m)^2 ≤ _ from tot]
