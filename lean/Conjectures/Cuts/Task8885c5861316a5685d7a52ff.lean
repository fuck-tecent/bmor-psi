import Mathlib


theorem Conjectures.Cuts.Task8885c5861316a5685d7a52ff : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ (x2 : ℕ),   (16 : ℕ) ≤ x2 →     have x4 : ℕ := Nat.log (2 : ℕ) x2 / (2 : ℕ);     have x5 : Finset ℕ := {x5 ∈ Finset.Ico x2 ((2 : ℕ) * x2) | Even x5 ∧ (0 : ℕ) < {x6 ∈ Finset.Icc (1 : ℕ) x4 | x1 (x5 - (2 : ℕ) ^ x6) = (0 : ℕ)}.card};     x5.card ≤ x4 * {x6 ∈ Finset.Icc (4 : ℕ) ((2 : ℕ) * x2) | Even x6 ∧ x1 x6 = (0 : ℕ)}.card) := by
  intro reps X hX
  let K := Nat.log 2 X / 2
  let ex := (Finset.Icc 4 (2*X)).filter fun m => Even m ∧ reps m = 0
  let shifts := Finset.Icc 1 K
  apply le_trans (Finset.card_le_card (t := (shifts ×ˢ ex).image
    (fun p : ℕ × ℕ => p.2 + 2^p.1)) ?_)
  · calc
      _ ≤ _ := Finset.card_image_le
      _ = _ := by simp [shifts, ex, K, Finset.card_product]
  · intro n hn
    obtain ⟨hnI, hen, hbad⟩ := Finset.mem_filter.mp hn
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hbad
    obtain ⟨hkI, hz⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hkI
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hnI
    have hlog := Nat.pow_log_le_self 2 (show X ≠ 0 by omega)
    have hsq : (2:ℕ)^k * 2^k ≤ X := by
      rw [← pow_add]
      exact le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hlog
    have hfit : 2^k + 4 ≤ n := by
      by_cases h : 2^k ≤ 4
      · omega
      · nlinarith [hsq, Nat.zero_le ((2:ℕ)^k - 5)]
    have he : Even ((2:ℕ)^k) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      exact ⟨2^j, by rw [pow_succ]; omega⟩
    apply Finset.mem_image.mpr
    refine ⟨(k, n - 2^k), Finset.mem_product.mpr ⟨hkI, ?_⟩, ?_⟩
    · change n - 2^k ∈ ex
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (Nat.sub_le n _).trans (Nat.le_of_lt hhi)⟩,
        (by obtain ⟨a, ha⟩ := hen; obtain ⟨b, hb⟩ := he; exact ⟨a-b, by omega⟩), hz⟩
    · dsimp
      omega
