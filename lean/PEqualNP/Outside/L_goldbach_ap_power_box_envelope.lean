import Mathlib
open Finset Filter Real
open scoped Topology

private lemma box_mem (n p a k : ℕ) (hk : k≤n) (hp : 2≤p) (ha : 2≤a)
    (he : p^a=k) (hal : a≤Nat.log 2 n) :
    k ∈ (range (n+1)) ∩ (((Icc 2 (Nat.sqrt n)).product (Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)) := by
  have hsq : p^2 ≤ p^a := Nat.pow_le_pow_right (by omega) ha
  have hroot : p≤Nat.sqrt n := Nat.le_sqrt.mpr (by simpa only [← sq] using hsq.trans (he.le.trans hk))
  exact mem_inter.mpr ⟨mem_range.mpr (by omega), mem_image.mpr
    ⟨(p,a), mem_product.mpr ⟨mem_Icc.mpr ⟨hp,hroot⟩,mem_Icc.mpr ⟨ha,hal⟩⟩,he⟩⟩

theorem PEqualNP.Outside.L_goldbach_ap_power_box_envelope : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k; let S := fun n : ℕ => (Finset.range (n+1)) ∩ (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)); ∀ n k : ℕ, 2≤n → k≤n → 0≤h k ∧ h k ≤ (if k∈S n then Real.log (n:ℝ) else 0) := by
  intro w h S n k hn hk
  have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hlog := Real.log_nonneg hnR
  by_cases hp : k.Prime
  · simp only [h,w,if_pos hp,ArithmeticFunction.vonMangoldt_apply_prime hp,sub_self,le_refl,true_and]
    split_ifs <;> positivity
  · simp only [h,w,if_neg hp,sub_zero]
    refine ⟨ArithmeticFunction.vonMangoldt_nonneg,?_⟩
    by_cases hpow : IsPrimePow k
    · obtain ⟨a,hal,ha,p,_,he,hprime⟩ := (isPrimePow_nat_iff_bounded_log k).mp hpow
      have ha2 : 2≤a := by
        by_contra! he'
        have ha1 : a=1 := by omega
        simp [ha1] at he
        exact hp (he ▸ hprime)
      have hs : k∈S n := box_mem n p a k hk hprime.two_le ha2 he.symm (hal.trans (Nat.log_mono_right hk))
      rw [if_pos hs]
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
        (by exact_mod_cast (he ▸ pow_pos hprime.pos a : 0<k)) (by exact_mod_cast hk))
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
      split_ifs <;> positivity
