import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_finite_power_count_via_exponent :
    ∀ n : ℕ, ((Finset.Icc 1 n).filter (fun k => 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac^a=k)).card)).card ≤ Nat.sqrt n + (Nat.log 2 n) * (Finset.Icc 1 n |>.filter (fun p => p^3 ≤ n)).card := by
  intro n
  let roots := (Icc 1 n).filter (fun p : ℕ => p^3 ≤ n)
  let squares := (Icc 1 n.sqrt).image (fun p : ℕ => p^2)
  let pairs := (Icc 1 (Nat.log 2 n)) ×ˢ roots
  let powers := pairs.image (fun z : ℕ × ℕ => z.2 ^ z.1)
  calc
    _ ≤ (squares ∪ powers).card := by
      apply card_le_card
      intro k hk
      obtain ⟨hk, hexp⟩ := mem_filter.mp hk
      obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk
      obtain ⟨a, ha⟩ := card_pos.mp hexp
      obtain ⟨ha, hpow⟩ := mem_filter.mp ha
      obtain ⟨ha2, hak⟩ := mem_Icc.mp ha
      have hpos := Nat.minFac_pos k
      by_cases h : a = 2
      · subst a
        apply mem_union_left
        refine mem_image.mpr ⟨k.minFac, mem_Icc.mpr ⟨hpos, ?_⟩, hpow⟩
        exact Nat.le_sqrt'.mpr (hpow.le.trans hkn)
      · apply mem_union_right
        refine mem_image.mpr ⟨(a,k.minFac), mem_product.mpr ⟨?_, ?_⟩, hpow⟩
        · exact mem_Icc.mpr ⟨by omega, hak.trans (Nat.log_mono_right hkn)⟩
        · apply mem_filter.mpr
          refine ⟨mem_Icc.mpr ⟨hpos,(Nat.minFac_le hk1).trans hkn⟩, ?_⟩
          calc
            k.minFac ^ 3 ≤ k.minFac ^ a := Nat.pow_le_pow_right hpos (by omega)
            _ = k := hpow
            _ ≤ n := hkn
    _ ≤ squares.card + powers.card := card_union_le _ _
    _ ≤ (Icc 1 n.sqrt).card + pairs.card := add_le_add card_image_le card_image_le
    _ = _ := by simp [pairs, roots]
