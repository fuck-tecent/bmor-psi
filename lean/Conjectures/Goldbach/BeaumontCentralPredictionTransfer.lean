import Mathlib

open scoped BigOperators

private theorem aux_card_sq_le_sum {E T : Finset ℕ} {r b : ℕ → ℝ} {L : ℝ}
    (hT : T ⊆ E) (hz : ∀ n ∈ T, r n = 0) (hL : 0 < L) (hb : ∀ n ∈ E, L ≤ b n) :
    ((T.card : ℕ) : ℝ) * L ^ 2 ≤ ∑ n ∈ E, (r n - b n) ^ 2 := by
  calc ((T.card : ℕ) : ℝ) * L ^ 2 = ∑ n ∈ T, L ^ 2 := by simp
    _ ≤ ∑ n ∈ T, (r n - b n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [hz n hn, zero_sub, neg_sq]
        exact pow_le_pow_left₀ hL.le (hb n (hT hn)) 2
    _ ≤ ∑ n ∈ E, (r n - b n) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => sq_nonneg _)

theorem Conjectures.Goldbach.BeaumontCentralPredictionTransfer :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card; let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2; let R := fun n : ℕ => ((H n + H (n+2)):ℝ); (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ, (∀ n ∈ E X, M X ≤ b n) ∧ (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) → (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, (((Finset.Icc X (2*X)).filter (fun n => Even n ∧ H n=0 ∧ H (n+2)=0)).card:ℝ) ≤ ε*(X:ℝ)) := by
  dsimp only
  intro h ε hε
  obtain ⟨X₀, hX₀⟩ := h ε hε
  refine ⟨max X₀ 2, ?_⟩
  intro X hX
  obtain ⟨b, hb1, hb2⟩ := hX₀ X (le_trans (le_max_left _ _) hX)
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hM : 0 < (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := div_pos hXpos (pow_pos hlog 2)
  set T := (Finset.Icc X (2 * X)).filter (fun n => Even n ∧ ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n - p).Prime ∧ n ≤ 3 * p ∧ 3 * p ≤ 2 * n)).card = 0 ∧ ((Finset.range ((n + 2) + 1)).filter (fun p => p.Prime ∧ p ≤ (n + 2) ∧ ((n + 2) - p).Prime ∧ (n + 2) ≤ 3 * p ∧ 3 * p ≤ 2 * (n + 2))).card = 0) with hTdef
  have hsub : T ⊆ (Finset.Icc X (2 * X)).filter (fun n => Even n) := by
    intro n hn
    simp only [hTdef, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hz : ∀ n ∈ T, ((((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n - p).Prime ∧ n ≤ 3 * p ∧ 3 * p ≤ 2 * n)).card : ℝ) + (((Finset.range ((n + 2) + 1)).filter (fun p => p.Prime ∧ p ≤ (n + 2) ∧ ((n + 2) - p).Prime ∧ (n + 2) ≤ 3 * p ∧ 3 * p ≤ 2 * (n + 2))).card : ℝ)) = 0 := by
    intro n hn
    simp only [hTdef, Finset.mem_filter] at hn
    obtain ⟨-, -, h1, h2⟩ := hn
    simp [h1, h2]
  have hkey : ((T.card : ℕ) : ℝ) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) ^ 2 ≤
      ∑ n ∈ (Finset.Icc X (2 * X)).filter (fun n => Even n),
        (((((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n - p).Prime ∧ n ≤ 3 * p ∧ 3 * p ≤ 2 * n)).card : ℝ) + (((Finset.range ((n + 2) + 1)).filter (fun p => p.Prime ∧ p ≤ (n + 2) ∧ ((n + 2) - p).Prime ∧ (n + 2) ≤ 3 * p ∧ 3 * p ≤ 2 * (n + 2))).card : ℝ)) - b n) ^ 2 :=
    aux_card_sq_le_sum hsub hz hM hb1
  have hkey2 : ((T.card : ℕ) : ℝ) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) ^ 2 ≤
      ε * (X : ℝ) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) ^ 2 := hkey.trans hb2
  have hfin : ((T.card : ℕ) : ℝ) ≤ ε * (X : ℝ) :=
    le_of_mul_le_mul_right hkey2 (pow_pos hM 2)
  exact hfin
