import Mathlib

-- Character-orthogonality count from RagdollSandrone, upstream PR 1672.
private theorem oddCharacterCount :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); 2*odd.card=n.totient := by
  intro n _ hn
  dsimp only
  classical
  let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)
  change 2 * odd.card = n.totient
  have : Fact (2 < n) := ⟨hn⟩
  have hzero := DirichletCharacter.sum_characters_eq_zero ℂ (ZMod.neg_one_ne_one (n := n))
  have hcount : Fintype.card (DirichletCharacter ℂ n) = n.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have h : (2 : ℂ) * odd.card = (n.totient : ℂ) := calc
    (2 : ℂ) * odd.card = ∑ _χ ∈ odd, (2 : ℂ) := by simp [nsmul_eq_mul, mul_comm]
    _ = ∑ χ : DirichletCharacter ℂ n, (1 - χ (-1)) := by
      unfold odd
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro χ _
      rcases χ.even_or_odd with he | ho
      · change χ (-1) = 1 at he
        norm_num [he]
      · change χ (-1) = -1 at ho
        norm_num [ho]
    _ = (n.totient : ℂ) := by simp [Finset.sum_sub_distrib, hzero, hcount]
  exact_mod_cast h

theorem PEqualNP.Outside.L_goldbach_primitive_mean_power_replacement :
    ∀ (n : ℕ) [NeZero n], 2<n → let X := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ (A B : DirichletCharacter ℂ n → ℂ) (e : ℝ), 0≤e → (∀ χ∈X, ‖A χ-B χ‖ ≤ e) → let avg := fun f : DirichletCharacter ℂ n → ℝ => (2/(n.totient:ℝ))*∑ χ ∈ X, f χ; |avg (fun χ => ‖A χ‖^2)-avg (fun χ => ‖B χ‖^2)| ≤ 2*e*Real.sqrt (avg (fun χ => ‖B χ‖^2))+e^2 := by
  intro n _ hn X A B e he hAB avg
  classical
  let c : ℝ := 2 / (n.totient : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hφ : (0 : ℝ) < (n.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hcount : 2 * X.card = n.totient := oddCharacterCount n hn
  have hreal : (2 : ℝ) * (X.card : ℝ) = (n.totient : ℝ) := by exact_mod_cast hcount
  have hcard : c * (X.card : ℝ) = 1 := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, hreal, div_self hφ.ne']

  have hrms : c * (∑ i ∈ X, ‖B i‖) ≤ Real.sqrt (c * ∑ i ∈ X, ‖B i‖^2) := by
    have hCS : (∑ i ∈ X, ‖B i‖)^2 ≤ (X.card : ℝ) * ∑ i ∈ X, ‖B i‖^2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq X (fun _ => (1 : ℝ)) (fun i => ‖B i‖)
    apply Real.le_sqrt_of_sq_le
    calc
      (c * ∑ i ∈ X, ‖B i‖)^2 = c^2 * (∑ i ∈ X, ‖B i‖)^2 := by ring
      _ ≤ c^2 * ((X.card : ℝ) * ∑ i ∈ X, ‖B i‖^2) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg c)
      _ = (c * (X.card : ℝ)) * (c * ∑ i ∈ X, ‖B i‖^2) := by ring
      _ = _ := by rw [hcard, one_mul]

  have hpoint (i : DirichletCharacter ℂ n) (hi : i ∈ X) :
      |‖A i‖^2 - ‖B i‖^2| ≤ 2*e*‖B i‖ + e^2 := by
    have hd := (abs_norm_sub_norm_le (A i) (B i)).trans (hAB i hi)
    have hs : ‖A i‖ + ‖B i‖ ≤ 2*‖B i‖ + e := by
      linarith [(abs_le.mp hd).2]
    rw [show ‖A i‖^2 - ‖B i‖^2 = (‖A i‖ - ‖B i‖) * (‖A i‖ + ‖B i‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ e * (2*‖B i‖ + e) := mul_le_mul hd hs (add_nonneg (norm_nonneg _) (norm_nonneg _)) he
      _ = _ := by ring

  calc
    |c * (∑ i ∈ X, ‖A i‖^2) - c * (∑ i ∈ X, ‖B i‖^2)| =
        c * |∑ i ∈ X, (‖A i‖^2 - ‖B i‖^2)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hc]
    _ ≤ c * (∑ i ∈ X, |‖A i‖^2 - ‖B i‖^2|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ c * (∑ i ∈ X, (2*e*‖B i‖ + e^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) hc
    _ = 2*e*(c * ∑ i ∈ X, ‖B i‖) + (c * (X.card : ℝ))*e^2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = 2*e*(c * ∑ i ∈ X, ‖B i‖) + e^2 := by rw [hcard, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hrms (by positivity)) le_rfl
