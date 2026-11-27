import Mathlib

open Finset

namespace PEqualNP.Outside

theorem L_goldbach_central_block_moment_transfer :
    let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0; let C := fun n : ℕ => ∑ p ∈ (Finset.range (n+1)).filter (fun p => n≤3*p ∧ 3*p≤2*n), w p*w (n-p); let I := fun x : ℕ => (Finset.Icc x (2*x)).filter (fun n => Even n); let P := fun x : ℕ => (Finset.range (x+1)).filter (fun p => p.Prime ∧ x≤2*p ∧ 3*p≤2*x); ∀ x : ℕ, 5≤x → (∑ p ∈ P x, w p)^2 ≤ ∑ n ∈ I x, C n := by
  intro w C I P x hx
  classical
  have w_nonneg (p : ℕ) : 0 ≤ w p := by
    dsimp [w]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    · exact le_rfl
  let index (z : ℕ × ℕ) : ℕ × ℕ := (z.1 + z.2, z.1)
  let term (y : ℕ × ℕ) : ℝ :=
    if y.1 ≤ 3 * y.2 ∧ 3 * y.2 ≤ 2 * y.1 then w y.2 * w (y.1 - y.2) else 0
  have bounds {p : ℕ} (hp : p ∈ P x) : p < x + 1 ∧ p.Prime ∧ x ≤ 2 * p ∧ 3 * p ≤ 2 * x := by
    have hmem := mem_filter.mp hp
    exact ⟨mem_range.mp hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2⟩
  have oddP {p : ℕ} (hp : p ∈ P x) : Odd p := by
    have hb := bounds hp
    exact hb.2.1.odd_of_ne_two (by omega)
  have term_nonneg (y : ℕ × ℕ) : 0 ≤ term y := by
    dsimp [term]
    split_ifs
    · exact mul_nonneg (w_nonneg _) (w_nonneg _)
    · exact le_rfl
  have inj : Set.InjOn index (↑(P x ×ˢ P x) : Set (ℕ × ℕ)) := by
    intro z _ v _ he
    have hp : z.1 = v.1 := congrArg Prod.snd he
    have hs : z.1 + z.2 = v.1 + v.2 := congrArg Prod.fst he
    exact Prod.ext hp (by omega)
  have image_subset : (P x ×ˢ P x).image index ⊆ I x ×ˢ P x := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨hp, hq⟩ := mem_product.mp hz
    have hp' := bounds hp
    have hq' := bounds hq
    refine mem_product.mpr ⟨?_, hp⟩
    dsimp [index, I]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (oddP hp).add_odd (oddP hq)⟩
  calc
    (∑ p ∈ P x, w p) ^ 2 = ∑ z ∈ P x ×ˢ P x, w z.1 * w z.2 := by
      rw [Finset.sum_product (P x) (P x) (fun z => w z.1 * w z.2), pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ ≤ ∑ y ∈ I x ×ˢ P x, term y := by
      apply Finset.sum_le_sum_of_injOn index inj image_subset
      · intro z hz
        obtain ⟨hp, hq⟩ := mem_product.mp hz
        have hp' := bounds hp
        have hq' := bounds hq
        have hc : z.1 + z.2 ≤ 3 * z.1 ∧ 3 * z.1 ≤ 2 * (z.1 + z.2) := ⟨by omega, by omega⟩
        simp [index, term, hc]
      · exact fun y _ _ => term_nonneg y
    _ = ∑ n ∈ I x, ∑ p ∈ P x, term (n, p) := Finset.sum_product (I x) (P x) term
    _ ≤ ∑ n ∈ I x, C n := by
      refine sum_le_sum fun n hn => ?_
      have hxn : x ≤ n := (mem_Icc.mp (mem_filter.mp hn).1).1
      have hC : C n = ∑ p ∈ range (n + 1), term (n, p) := by
        dsimp [C, term]
        rw [sum_filter]
      rw [hC]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := bounds hp
        exact mem_range.mpr (by omega)
      · exact fun p _ _ => term_nonneg (n, p)

end PEqualNP.Outside
