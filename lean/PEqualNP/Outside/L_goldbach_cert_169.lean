import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset
open scoped Real

namespace GoldbachCert169

private noncomputable def term (m a b : ℕ) : ℂ :=
  Complex.exp (((2 * π * (a : ℝ) * b / m : ℝ) : ℂ) * Complex.I)

private theorem full_sum_zero (m a : ℕ) (hm : 0 < m) (ha : ¬ m ∣ a) :
    ∑ b ∈ range m, term m a b = 0 := by
  let z : ℂ := Complex.exp (2 * π * Complex.I * a / m)
  have hz : z ≠ 1 :=
    fun h => ha ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne').mp h)
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hzpow : z ^ m = 1 := by
    rw [← Complex.exp_nat_mul,
      show (m : ℂ) * (2 * π * Complex.I * a / m) = a * (2 * π * Complex.I) by field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I a
  have hterm (b : ℕ) : term m a b = z^b := by
    rw [← Complex.exp_nat_mul]
    unfold term
    push_cast
    congr 1
    ring
  simp_rw [hterm]
  have h := geom_sum_mul z m
  rw [hzpow, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz)

private theorem multiples_sum (a : ℕ) :
    ∑ b ∈ (range 169).filter (fun b => 13 ∣ b), term 169 a b =
      ∑ j ∈ range 13, term 13 a j := by
  symm
  apply sum_nbij' (13 * ·) (· / 13)
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hj; omega), dvd_mul_right ..⟩
  · intro b hb
    have := mem_range.mp (mem_filter.mp hb).1
    apply mem_range.mpr
    omega
  · intro j _
    exact Nat.mul_div_cancel_left j (by decide)
  · intro b hb
    exact Nat.mul_div_cancel' (mem_filter.mp hb).2
  · intro j _
    unfold term
    congr 2
    push_cast
    ring

private theorem unit_iff (b : ℕ) : b.Coprime 169 ↔ ¬ 13 ∣ b := by
  rw [show (169:ℕ) = 13^2 by decide, Nat.coprime_pow_right_iff (by decide),
    Nat.coprime_comm]
  exact (show Nat.Prime 13 by decide).coprime_iff_not_dvd

end GoldbachCert169

open GoldbachCert169 in
theorem PEqualNP.Outside.L_goldbach_cert_169 :
    ∀ a:ℕ, Nat.Coprime a 169 → (∑ b ∈ (Finset.range 169).filter (fun b => Nat.Coprime b 169),
      Complex.exp (((2*Real.pi*(a:ℝ)*b/169:ℝ):ℂ)*Complex.I))/(156:ℂ)=(0:ℂ)/156 := by
  intro a ha
  have hp := (unit_iff a).mp ha
  have hfull := full_sum_zero 169 a (by decide) (fun h => hp (dvd_trans (by decide : 13 ∣ 169) h))
  have hnonunit := (multiples_sum a).trans (full_sum_zero 13 a (by decide) hp)
  have hsplit := sum_filter_add_sum_filter_not (range 169) (fun b => 13 ∣ b) (term 169 a)
  rw [hnonunit, zero_add, hfull] at hsplit
  change (∑ b ∈ (range 169).filter (fun b => b.Coprime 169), term 169 a b)/(156:ℂ) = 0/156
  simp only [unit_iff, hsplit]
