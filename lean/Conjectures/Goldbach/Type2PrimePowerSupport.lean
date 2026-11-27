import Mathlib

namespace Conjectures.Goldbach.Type2PrimePowerSupport_aux

open Finset

private noncomputable def wgt : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0

private def cof (U B : ℕ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
    (∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * v (m / a)

private lemma pp_of_ne (q : ℕ) (h : ArithmeticFunction.vonMangoldt q ≠ wgt q) :
    ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ q = p ^ k := by
  by_cases hpp : IsPrimePow q
  · obtain ⟨p, k, hp, hk, hq⟩ := (isPrimePow_nat_iff q).mp hpp
    by_cases hk2 : 2 ≤ k
    · exact ⟨p, k, hp, hk2, hq.symm⟩
    · exfalso
      have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hq
      subst hq
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at h
      exact h (by simp only [wgt, if_pos hp])
  · have hnp : ¬ Nat.Prime q := fun hp => hpp hp.isPrimePow
    have hz : ArithmeticFunction.vonMangoldt q = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    rw [hz] at h
    exfalso
    exact h (by simp only [wgt, if_neg hnp])

private lemma witness (U B m : ℕ)
    (hm : cof U B ArithmeticFunction.vonMangoldt m ≠ cof U B wgt m) :
    ∃ a p k : ℕ, a ∈ m.divisors ∧ U < a ∧ a ≤ B ∧ 2 ≤ k ∧ Nat.Prime p ∧ m / a = p ^ k := by
  have h1 : ∃ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
      ArithmeticFunction.vonMangoldt (m / a) ≠ wgt (m / a) := by
    by_contra hc
    apply hm
    unfold cof
    refine Finset.sum_congr rfl (fun a ha => ?_)
    by_cases heq : ArithmeticFunction.vonMangoldt (m / a) = wgt (m / a)
    · rw [heq]
    · exact absurd ⟨a, ha, heq⟩ hc
  obtain ⟨a, ha, hne⟩ := h1
  obtain ⟨hdiv, hU, hB, -⟩ := Finset.mem_filter.mp ha
  obtain ⟨p, k, hp, hk, hpk⟩ := pp_of_ne (m / a) hne
  exact ⟨a, p, k, hdiv, hU, hB, hk, hp, hpk⟩

private def target (n B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).biUnion fun a =>
    (Finset.Icc 2 (Nat.log 2 n)).biUnion fun k =>
      (Finset.Icc 2 (Nat.sqrt (n / a))).image fun p => a * p ^ k

private lemma subset_target (n U B : ℕ) :
    (Finset.range (n + 1)).filter
        (fun m => cof U B ArithmeticFunction.vonMangoldt m ≠ cof U B wgt m) ⊆ target n B := by
  intro m hm
  obtain ⟨hmr, hne⟩ := Finset.mem_filter.mp hm
  have hmn : m ≤ n := by have h := Finset.mem_range.mp hmr; omega
  obtain ⟨a, p, k, had, hU, haB, hk, hp, hpk⟩ := witness U B m hne
  have hdiv : a ∣ m := (Nat.mem_divisors.mp had).1
  have hmul : a * p ^ k = m := by
    calc a * p ^ k = p ^ k * a := by ring
      _ = m / a * a := by rw [hpk]
      _ = m := Nat.div_mul_cancel hdiv
  refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_Icc.mpr ⟨by omega, haB⟩, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, ?_⟩
  · refine Nat.le_log_of_pow_le (by norm_num) ?_
    have h2 : 2 ^ k * a ≤ n := by
      calc 2 ^ k * a = a * 2 ^ k := by ring
        _ ≤ a * p ^ k := Nat.mul_le_mul (le_refl a) (Nat.pow_le_pow_left hp.two_le k)
        _ = m := hmul
        _ ≤ n := hmn
    calc 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ k * a := Nat.mul_le_mul (le_refl _) (by omega)
      _ ≤ n := h2
  · refine Finset.mem_image.mpr ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hmul⟩
    refine Nat.le_sqrt'.mpr ?_
    have h3 : p ^ 2 * a ≤ n := by
      calc p ^ 2 * a = a * p ^ 2 := by ring
        _ ≤ a * p ^ k := Nat.mul_le_mul (le_refl a) (Nat.pow_le_pow_right hp.pos hk)
        _ = m := hmul
        _ ≤ n := hmn
    exact (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr h3

private lemma card_target (n B : ℕ) :
    (target n B).card ≤ ∑ a ∈ Finset.Icc 1 B, Nat.log 2 n * Nat.sqrt (n / a) := by
  have hcard : ∀ m : ℕ, (Finset.Icc 2 m).card ≤ m := by
    intro m
    have h := Nat.card_Icc 2 m
    omega
  have key : ∀ a : ℕ, ((Finset.Icc 2 (Nat.log 2 n)).biUnion fun k =>
      (Finset.Icc 2 (Nat.sqrt (n / a))).image fun p => a * p ^ k).card
      ≤ Nat.log 2 n * Nat.sqrt (n / a) := by
    intro a
    have hsum : ∑ k ∈ Finset.Icc 2 (Nat.log 2 n),
          ((Finset.Icc 2 (Nat.sqrt (n / a))).image fun p => a * p ^ k).card
        ≤ ∑ k ∈ Finset.Icc 2 (Nat.log 2 n), Nat.sqrt (n / a) := by
      refine Finset.sum_le_sum fun k hk => ?_
      refine le_trans Finset.card_image_le ?_
      have h := Nat.card_Icc 2 (Nat.sqrt (n / a))
      omega
    have hconst : ∑ k ∈ Finset.Icc 2 (Nat.log 2 n), Nat.sqrt (n / a)
        = (Finset.Icc 2 (Nat.log 2 n)).card * Nat.sqrt (n / a) :=
      Finset.sum_const_nat (s := Finset.Icc 2 (Nat.log 2 n))
        (f := fun _ => Nat.sqrt (n / a)) (m := Nat.sqrt (n / a)) (fun x hx => rfl)
    calc ((Finset.Icc 2 (Nat.log 2 n)).biUnion fun k =>
            (Finset.Icc 2 (Nat.sqrt (n / a))).image fun p => a * p ^ k).card
        ≤ ∑ k ∈ Finset.Icc 2 (Nat.log 2 n),
            ((Finset.Icc 2 (Nat.sqrt (n / a))).image fun p => a * p ^ k).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ k ∈ Finset.Icc 2 (Nat.log 2 n), Nat.sqrt (n / a) := hsum
      _ = (Finset.Icc 2 (Nat.log 2 n)).card * Nat.sqrt (n / a) := hconst
      _ ≤ Nat.log 2 n * Nat.sqrt (n / a) :=
          Nat.mul_le_mul (hcard (Nat.log 2 n)) (le_refl _)
  unfold target
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun a ha => key a

private lemma sum_inv_sqrt_le : ∀ B : ℕ,
    (∑ b ∈ Finset.Icc 1 B, 1 / Real.sqrt (b : ℝ)) ≤ 2 * Real.sqrt (B : ℝ) := by
  intro B
  induction B with
  | zero =>
      have h0 : Finset.Icc (1 : ℕ) 0 = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      simp [h0]
  | succ B ih =>
    have hsplit : (∑ b ∈ Finset.Icc 1 (B + 1), 1 / Real.sqrt (b : ℝ))
        = (∑ b ∈ Finset.Icc 1 B, 1 / Real.sqrt (b : ℝ)) + 1 / Real.sqrt ((B + 1 : ℕ) : ℝ) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hkey : (1 : ℝ) / Real.sqrt ((B + 1 : ℕ) : ℝ)
        ≤ 2 * (Real.sqrt ((B + 1 : ℕ) : ℝ) - Real.sqrt (B : ℝ)) := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
      have e1 : Real.sqrt ((B + 1 : ℕ) : ℝ) ^ 2 = (B : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]
        push_cast
        ring
      have e2 : Real.sqrt (B : ℝ) ^ 2 = (B : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith [sq_nonneg (Real.sqrt ((B + 1 : ℕ) : ℝ) - Real.sqrt (B : ℝ))]
    calc ∑ b ∈ Finset.Icc 1 (B + 1), 1 / Real.sqrt (b : ℝ)
        = (∑ b ∈ Finset.Icc 1 B, 1 / Real.sqrt (b : ℝ)) + 1 / Real.sqrt ((B + 1 : ℕ) : ℝ) :=
          hsplit
      _ ≤ 2 * Real.sqrt (B : ℝ) + 2 * (Real.sqrt ((B + 1 : ℕ) : ℝ) - Real.sqrt (B : ℝ)) :=
          by exact add_le_add ih hkey
      _ = 2 * Real.sqrt ((B + 1 : ℕ) : ℝ) := by ring

theorem main (n U B : ℕ) :
    (((Finset.range (n + 1)).filter
        (fun m => cof U B ArithmeticFunction.vonMangoldt m ≠ cof U B wgt m)).card : ℝ)
      ≤ 2 * Real.sqrt n * Real.sqrt B * (Nat.log 2 n : ℝ) := by
  have hcard : ((Finset.range (n + 1)).filter
        (fun m => cof U B ArithmeticFunction.vonMangoldt m ≠ cof U B wgt m)).card
      ≤ ∑ a ∈ Finset.Icc 1 B, Nat.log 2 n * Nat.sqrt (n / a) :=
    le_trans (Finset.card_le_card (subset_target n U B)) (card_target n B)
  calc (((Finset.range (n + 1)).filter
        (fun m => cof U B ArithmeticFunction.vonMangoldt m ≠ cof U B wgt m)).card : ℝ)
      ≤ ((∑ a ∈ Finset.Icc 1 B, Nat.log 2 n * Nat.sqrt (n / a) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ∑ a ∈ Finset.Icc 1 B, ((Nat.log 2 n : ℝ) * (Nat.sqrt (n / a) : ℝ)) := by
        simp only [Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ a ∈ Finset.Icc 1 B, ((Nat.log 2 n : ℝ) * (Real.sqrt n / Real.sqrt a)) := by
        refine Finset.sum_le_sum fun a ha => ?_
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        calc (Nat.sqrt (n / a) : ℝ) ≤ Real.sqrt ((n / a : ℕ) : ℝ) := by
              refine (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr ?_
              exact_mod_cast Nat.sqrt_le' (n / a)
          _ ≤ Real.sqrt ((n : ℝ) / (a : ℝ)) := by
              refine Real.sqrt_le_sqrt ?_
              refine (le_div_iff₀ (by exact_mod_cast (show 0 < a by omega))).mpr ?_
              exact_mod_cast Nat.div_mul_le_self n a
          _ = Real.sqrt n / Real.sqrt a := Real.sqrt_div' _ (by positivity)
    _ = ∑ a ∈ Finset.Icc 1 B, ((Nat.log 2 n : ℝ) * Real.sqrt n * (1 / Real.sqrt (a : ℝ))) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        ring
    _ = (Nat.log 2 n : ℝ) * Real.sqrt n * ∑ a ∈ Finset.Icc 1 B, (1 / Real.sqrt (a : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (Nat.log 2 n : ℝ) * Real.sqrt n * (2 * Real.sqrt B) := by
        refine mul_le_mul_of_nonneg_left (sum_inv_sqrt_le B) ?_
        positivity
    _ = 2 * Real.sqrt n * Real.sqrt B * (Nat.log 2 n : ℝ) := by ring

end Conjectures.Goldbach.Type2PrimePowerSupport_aux

theorem Conjectures.Goldbach.Type2PrimePowerSupport :
    ∀ n U B : ℕ, let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
      let coeff := fun (v : ℕ → ℝ) (m : ℕ) => ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), (∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * v (m / a);
      (((Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)).card : ℝ) ≤ 2 * Real.sqrt n * Real.sqrt B * (Nat.log 2 n : ℝ) := by
  intro n U B
  dsimp only
  exact Conjectures.Goldbach.Type2PrimePowerSupport_aux.main n U B
