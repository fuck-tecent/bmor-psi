import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_power_box_detect :
    let A := fun k : ℕ => if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card then Real.log (k:ℝ) else 0; let S := fun n : ℕ => (Finset.range (n+1)) ∩ (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)); ∀ n k : ℕ, k≤n → A k≠0 → k∈S n := by
  intro A S n k hkn hA
  have hex : 0 < ((Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card := by
    by_contra h
    exact hA (by simp only [A, ite_eq_right h])
  obtain ⟨a, ha⟩ := card_pos.mp hex
  obtain ⟨ha, heq⟩ := mem_filter.mp ha
  obtain ⟨ha2, hak⟩ := mem_Icc.mp ha
  have hk1 : k ≠ 1 := by
    rintro rfl
    simp at hak
    omega
  have hp := Nat.minFac_prime hk1
  have hsq : k.minFac ^ 2 ≤ n := calc
    _ ≤ k.minFac ^ a := Nat.pow_le_pow_right hp.pos ha2
    _ = k := heq
    _ ≤ n := hkn
  apply mem_inter.mpr
  refine ⟨mem_range.mpr (by omega), mem_image.mpr ⟨(k.minFac, a), ?_, heq⟩⟩
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨hp.two_le, Nat.le_sqrt'.mpr hsq⟩,
    mem_Icc.mpr ⟨ha2, hak.trans (Nat.log_mono_right hkn)⟩⟩
