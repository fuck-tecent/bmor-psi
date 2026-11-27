import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_singular_product_lower :
    ∀ (S : Finset ℕ), (∀ p ∈ S, Nat.Prime p ∧ 2 < p) → ({3,5,7} : Finset ℕ) ⊆ S → (75/128:ℝ) ≤ ∏ p ∈ S, (1-(1:ℝ)/((p:ℝ)-1)^2) := by
  intro S hS h357
  let f : ℕ → ℝ := fun p => 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2
  have hf_bounds : ∀ k : ℕ, 3 ≤ k → 0 ≤ f k ∧ f k ≤ 1 := by
    intro k hk
    have hk1 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
      have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hsq : (1 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 := by nlinarith
    have hdiv1 : (1 : ℝ) / ((k : ℝ) - 1) ^ 2 ≤ 1 := div_le_self zero_le_one hsq
    have hdiv0 : 0 ≤ (1 : ℝ) / ((k : ℝ) - 1) ^ 2 := by positivity
    dsimp [f]
    exact ⟨by linarith, by linarith⟩
  have hprod01 : ∀ U : Finset ℕ, (∀ k ∈ U, 0 ≤ f k ∧ f k ≤ 1) →
      0 ≤ (∏ k ∈ U, f k) ∧ (∏ k ∈ U, f k) ≤ 1 := by
    intro U hU
    induction U using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨ha0, ha1⟩ := hU a (Finset.mem_insert_self a s)
      obtain ⟨hs0, hs1⟩ := ih (fun k hk => hU k (Finset.mem_insert_of_mem hk))
      exact ⟨mul_nonneg ha0 hs0, le_trans (mul_le_mul_of_nonneg_right ha1 hs0) (by linarith)⟩
  have h357_val : ∏ p ∈ ({3, 5, 7} : Finset ℕ), f p = (175 / 256 : ℝ) := by
    have h3 : (3 : ℕ) ∉ ({5, 7} : Finset ℕ) := by decide
    have h5 : (5 : ℕ) ∉ ({7} : Finset ℕ) := by decide
    rw [Finset.prod_insert h3, Finset.prod_insert h5, Finset.prod_singleton]
    dsimp [f]
    norm_num
  let T : Finset ℕ := S \ {3, 5, 7}
  have hsplit : (∏ p ∈ T, f p) * ∏ p ∈ ({3, 5, 7} : Finset ℕ), f p = ∏ p ∈ S, f p :=
    Finset.prod_sdiff h357
  have hT_ge8 : ∀ p ∈ T, 8 ≤ p := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with ⟨hpS, hp_not⟩
    obtain ⟨hp_prime, hp_gt2⟩ := hS p hpS
    by_contra! hp8
    rcases (by omega : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7) with
      rfl | rfl | rfl | rfl | rfl
    · exact hp_not (Or.inl rfl)
    · exact (by decide : ¬ Nat.Prime 4) hp_prime
    · exact hp_not (Or.inr (Or.inl rfl))
    · exact (by decide : ¬ Nat.Prime 6) hp_prime
    · exact hp_not (Or.inr (Or.inr rfl))
  let n : ℕ := T.sup id + 1
  let I : Finset ℕ := Finset.Ico 8 (8 + n)
  have hTI : T ⊆ I := by
    intro p hp
    rw [Finset.mem_Ico]
    have hp8 : 8 ≤ p := hT_ge8 p hp
    have hpsup : p ≤ T.sup id := Finset.le_sup (f := id) hp
    omega
  have hI_split : (∏ k ∈ I \ T, f k) * (∏ p ∈ T, f p) = ∏ k ∈ I, f k :=
    Finset.prod_sdiff hTI
  have hrest_le1 : (∏ k ∈ I \ T, f k) ≤ 1 := by
    refine (hprod01 (I \ T) fun k hk => ?_).2
    have hkI : k ∈ I := (Finset.mem_sdiff.mp hk).1
    exact hf_bounds k (by have := (Finset.mem_Ico.mp hkI).1; omega)
  have hT_nonneg : 0 ≤ ∏ p ∈ T, f p := by
    refine (hprod01 T fun p hp => ?_).1
    exact hf_bounds p (by have := hT_ge8 p hp; omega)
  have hI_le_T : ∏ k ∈ I, f k ≤ ∏ p ∈ T, f p := by
    calc
      ∏ k ∈ I, f k = (∏ k ∈ I \ T, f k) * (∏ p ∈ T, f p) := hI_split.symm
      _ ≤ 1 * (∏ p ∈ T, f p) := mul_le_mul_of_nonneg_right hrest_le1 hT_nonneg
      _ = ∏ p ∈ T, f p := one_mul _
  have htel : ∀ m : ℕ, ∏ k ∈ Finset.Ico 8 (8 + m), f k =
      (6 : ℝ) / 7 * ((7 + (m : ℝ)) / (6 + (m : ℝ))) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Nat.add_succ, Finset.prod_Ico_succ_top (by omega : 8 ≤ 8 + m), ih]
      dsimp [f]
      push_cast
      rw [show (8 : ℝ) + (m : ℝ) - 1 = 7 + (m : ℝ) by ring]
      rw [show (6 : ℝ) + ((m : ℝ) + 1) = 7 + (m : ℝ) by ring]
      have h6 : (6 : ℝ) + (m : ℝ) ≠ 0 := by positivity
      have h7 : (7 : ℝ) + (m : ℝ) ≠ 0 := by positivity
      field_simp [h6, h7]
      ring
  have hI_ge : (6 : ℝ) / 7 ≤ ∏ k ∈ I, f k := by
    change (6 : ℝ) / 7 ≤ ∏ k ∈ Finset.Ico 8 (8 + n), f k
    rw [htel n]
    have h6pos : (0 : ℝ) < 6 + (n : ℝ) := by positivity
    have hfrac : (1 : ℝ) ≤ (7 + (n : ℝ)) / (6 + (n : ℝ)) :=
      (one_le_div h6pos).mpr (by linarith)
    linarith
  have hT_ge : (6 : ℝ) / 7 ≤ ∏ p ∈ T, f p := le_trans hI_ge hI_le_T
  change (75 / 128 : ℝ) ≤ ∏ p ∈ S, f p
  rw [← hsplit, h357_val]
  linarith
