import Mathlib

open Finset

namespace PEqualNP.Outside

theorem L_goldbach_sieve_squarefree_average :
    ∀ (x : ℕ) (b : ℕ → ℝ), (∀ d, 0≤b d) → (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, b d) ≤ (x:ℝ)*∑ d ∈ Finset.Icc 1 x, b d/(d:ℝ) := by
  intro x b hb
  classical
  have hdiv (n : ℕ) (hn : n ∈ Finset.Icc 1 x) :
      n.divisors = (Finset.Icc 1 x).filter (fun d => d ∣ n) := by
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hnx : n ≤ x := (mem_Icc.mp hn).2
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hdn, _⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hdn
      exact ⟨⟨by omega, by omega⟩, hdn⟩
    · rintro ⟨_, hdn⟩
      exact ⟨hdn, by omega⟩
  have hlhs :
      (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, b d) =
        ∑ d ∈ Finset.Icc 1 x, (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) * b d := by
    calc
      (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, b d) =
          ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x, if d ∣ n then b d else 0 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hdiv n hn, Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, if d ∣ n then b d else 0 :=
        Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc 1 x, (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) * b d := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hlhs, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hcard : ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card ≤ x / d := by
    have hsub : ((Finset.Icc 1 x).filter (fun n => d ∣ n)).image (fun n => n / d) ⊆ Finset.Icc 1 (x / d) := by
      intro q hq
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
      have hn_icc := mem_Icc.mp (mem_filter.mp hn).1
      have hdn : d ∣ n := (mem_filter.mp hn).2
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
      have hq_pos : 1 ≤ n / d := by
        by_contra hlt
        have hzero : n / d = 0 := Nat.lt_one_iff.mp (not_le.mp hlt)
        rw [hzero, mul_zero] at hmul
        have hn_pos : 1 ≤ n := hn_icc.1
        omega
      exact mem_Icc.mpr ⟨hq_pos, Nat.div_le_div_right hn_icc.2⟩
    have hinj : Set.InjOn (fun n => n / d) (↑((Finset.Icc 1 x).filter (fun n => d ∣ n)) : Set ℕ) := by
      intro n₁ hn₁ n₂ hn₂ heq
      dsimp at heq
      have hdn₁ : d ∣ n₁ := (mem_filter.mp hn₁).2
      have hdn₂ : d ∣ n₂ := (mem_filter.mp hn₂).2
      calc
        n₁ = d * (n₁ / d) := (Nat.mul_div_cancel' hdn₁).symm
        _ = d * (n₂ / d) := by rw [heq]
        _ = n₂ := Nat.mul_div_cancel' hdn₂
    calc
      ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card =
          (((Finset.Icc 1 x).filter (fun n => d ∣ n)).image (fun n => n / d)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (x / d)).card := Finset.card_le_card hsub
      _ = x / d := by simp [Nat.card_Icc]
  have hmul_le : ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card * d ≤ x := by
    calc
      ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card * d ≤ (x / d) * d :=
        Nat.mul_le_mul_right d hcard
      _ ≤ x := Nat.div_mul_le_self x d
  have hreal_le : (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    exact_mod_cast hmul_le
  calc
    (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) * b d ≤ ((x : ℝ) / (d : ℝ)) * b d :=
      mul_le_mul_of_nonneg_right hreal_le (hb d)
    _ = (x : ℝ) * (b d / (d : ℝ)) := by ring

end PEqualNP.Outside
