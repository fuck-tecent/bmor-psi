import Mathlib

namespace GoldbachPacketStability
open Finset Real

private def length (n : ℕ) := max 1 (Nat.log 2 n / 2)
private def cutoff (n : ℕ) := (Nat.log 2 (n+2))^2
private noncomputable def term (j : ℕ) (x : ℝ) :=
  Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * x)

/-- The factor of 48 allows for the derivative and the threshold gap. -/
private lemma quartic (k : ℕ) (hk : 64 ≤ k) : 48*(2*k+2)^4 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hstep : (2*(k+1)+2)^4 ≤ 2*(2*k+2)^4 := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
      ring_nf
      omega
    calc
      48*(2*(k+1)+2)^4 ≤ 48*(2*(2*k+2)^4) := Nat.mul_le_mul_left _ hstep
      _ = 2*(48*(2*k+2)^4) := by ring
      _ ≤ 2*2^k := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

private lemma scaling {n j : ℕ} (hn : 2^128 ≤ n) (hj : j < length n) :
    48*2^(j+1)*(cutoff n)^2 ≤ n := by
  let m := Nat.log 2 n
  let k := m/2
  have hm : 128 ≤ m := Nat.le_log_of_pow_le (by decide) hn
  have hk : 64 ≤ k := by dsimp [k]; omega
  have hn2 : 2 ≤ n := (by decide : 2 ≤ 2^128).trans hn
  have hn0 : n ≠ 0 := by omega
  have hL : length n = k := max_eq_right (by omega : 1 ≤ k)
  rw [hL] at hj
  have hlog : Nat.log 2 (n+2) ≤ 2*k+2 := by
    have h := Nat.log_mono_right (b:=2) (show n+2 ≤ n*2 by omega)
    rw [Nat.log_mul_base (by decide) hn0] at h
    change _ ≤ m+1 at h
    dsimp [k]; omega
  have hcut : (cutoff n)^2 ≤ (2*k+2)^4 := by
    unfold cutoff
    rw [← pow_mul]
    exact Nat.pow_le_pow_left hlog 4
  have hpow : 2^(j+1) ≤ 2^k := Nat.pow_le_pow_right (by decide) hj
  calc
    _ = 2^(j+1)*(48*(cutoff n)^2) := by ring
    _ ≤ 2^k*2^k := Nat.mul_le_mul hpow ((Nat.mul_le_mul_left 48 hcut).trans (quartic k hk))
    _ = 2^(k+k) := (pow_add _ _ _).symm
    _ ≤ 2^m := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
    _ ≤ n := Nat.pow_log_le_self _ hn0

private lemma variation {n j : ℕ} (hn : 2^128 ≤ n) (hj : j < length n)
    {x y : ℝ} (hxy : |x-y| ≤ (cutoff n : ℝ)^2/n) :
    |term j x - term j y| ≤ 1/6 := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2^128) hn)
  have hs : 48*(2:ℝ)^(j+1)*(cutoff n:ℝ)^2 ≤ n := by exact_mod_cast scaling hn hj
  have hder : 2*Real.pi*(2:ℝ)^(j+1) ≤ 8*(2:ℝ)^(j+1) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)
  calc
    _ ≤ |2*Real.pi*(2:ℝ)^(j+1)*x - 2*Real.pi*(2:ℝ)^(j+1)*y| := abs_cos_sub_cos_le _ _
    _ = (2*Real.pi*(2:ℝ)^(j+1))*|x-y| := by rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    _ ≤ (8*(2:ℝ)^(j+1))*((cutoff n:ℝ)^2/n) := mul_le_mul hder hxy (abs_nonneg _) (by positivity)
    _ ≤ _ := by rw [← mul_div_assoc,div_le_iff₀ hn0]; linarith only [hs]

theorem stability :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ, |x-y| ≤ (cutoff n:ℝ)^2/n →
      (1:ℝ)/2 < (∑ j ∈ range (length n), term j x)/(length n:ℝ) →
      (1:ℝ)/3 < (∑ j ∈ range (length n), term j y)/(length n:ℝ) := by
  refine ⟨2^128, ?_⟩
  intro n hn x y hxy hx
  have hL : 0 < (length n:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 (Nat.log 2 n/2)))
  apply (lt_div_iff₀ hL).mpr
  have hpeak := (lt_div_iff₀ hL).mp hx
  have hsum : (∑ j ∈ range (length n), term j x) ≤
      ∑ j ∈ range (length n), (term j y+1/6) := by
    apply sum_le_sum
    intro j hj
    linarith only [(abs_le.mp (variation hn (mem_range.mp hj) hxy)).2]
  rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hsum
  linarith

end GoldbachPacketStability

theorem Conjectures.Goldbach.PacketRationalCenterStability :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
    let L := fun n : ℕ => max 1 (Nat.log 2 n / 2)
    let K := fun (n : ℕ) (t : ℝ) =>
      (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ)
    ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ, |x-y| ≤ (Q n:ℝ)^2/(n:ℝ) →
      (1:ℝ)/2 < K n x → (1:ℝ)/3 < K n y :=
  GoldbachPacketStability.stability
