import Mathlib

private theorem exists_maximum_fiber {α β : Type} [Fintype α] [Fintype β] [Nonempty β] [DecidableEq β]
    (code : α → β) :
    ∃ w : β, Fintype.card α ≤ Fintype.card β * (Finset.univ.filter fun a => code a = w).card := by
  classical
  let count (w : β) := (Finset.univ.filter fun a => code a = w).card
  obtain ⟨w, _, hmax⟩ := Finset.exists_max_image Finset.univ count Finset.univ_nonempty
  have hsum : Fintype.card α = ∑ b : β, count b := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (f := code) (s := Finset.univ) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _))
  refine ⟨w, ?_⟩
  calc
    Fintype.card α = ∑ b : β, count b := hsum
    _ ≤ ∑ _b : β, count w := Finset.sum_le_sum hmax
    _ = Fintype.card β * count w := by simp [Finset.sum_const]

theorem Conjectures.Cuts.Taskffecbfb927838e88467ff6d0 :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 x3 : ℕ) (x4 : Matrix (Fin x2) (Fin x3) ℝ), (0 : ℕ) < x2 → (0 : ℕ) < x3 → (∀ (x7 : Fin x2) (x8 : Fin x3), x4 x7 x8 = (0 : ℝ) ∨ x4 x7 x8 = (1 : ℝ)) → (1 : ℕ) ≤ x4.rank → x4.rank ≤ (1000 : ℕ) → ∃ (x10 : Finset (Fin x2)) (x11 : Finset (Fin x3)) (x12 : ℝ), (∀ x13 ∈ x10, ∀ x15 ∈ x11, x4 x13 x15 = x12) ∧ (↑x2 : ℝ) * (↑x3 : ℝ) ≤ (↑x10.card : ℝ) * (↑x11.card : ℝ) * Real.rpow (2 : ℝ) (x1 * (↑x4.rank : ℝ).rpow (49999 / 100000 : ℝ))) := by
  classical
  refine ⟨1001, by norm_num, ?_⟩
  intro m n M hm _hn hbool hrank hcap
  obtain ⟨basis, hbasis, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range M.col)
  choose column hcolumn using hbasis
  let code (i : Fin m) (k : Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range M.col)))) : Bool :=
    decide (M i (column k) = 1)
  have same_row (i i' : Fin m) (hcode : code i = code i') (j : Fin n) : M i j = M i' j := by
    have hcolumn_mem : M.col j ∈ Submodule.span ℝ (Set.range basis) := by
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self j)
    refine Submodule.span_induction (p := fun v _ => v i = v i') ?_ rfl ?_ ?_ hcolumn_mem
    · rintro _ ⟨k, rfl⟩
      rw [← hcolumn k]
      change M i (column k) = M i' (column k)
      have hbit := congrFun hcode k
      change decide (M i (column k) = 1) = decide (M i' (column k) = 1) at hbit
      rcases hbool i (column k) with hzero | hone <;>
        rcases hbool i' (column k) with hzero' | hone' <;>
        simp_all
    · intro x y _ _ hx hy
      change x i + y i = x i' + y i'
      rw [hx, hy]
    · intro r v _ hv
      change r * v i = r * v i'
      rw [hv]
  obtain ⟨w, hw⟩ := exists_maximum_fiber code
  let A := Finset.univ.filter (fun i => code i = w)
  have rows : m ≤ 2 ^ M.rank * A.card := by
    simpa only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      ← M.rank_eq_finrank_span_cols] using hw
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    by_contra! hz
    have hzero : A.card = 0 := by omega
    simp [hzero] at rows
    omega
  obtain ⟨i, hi⟩ := hA
  have hi_code : code i = w := (Finset.mem_filter.mp hi).2
  let bit (j : Fin n) : Bool := decide (M i j = 1)
  obtain ⟨b, hb⟩ := exists_maximum_fiber bit
  let B := Finset.univ.filter (fun j => bit j = b)
  have cols : n ≤ 2 * B.card := by simpa only [Fintype.card_fin, Fintype.card_bool] using hb
  refine ⟨A, B, if b then 1 else 0, ?_, ?_⟩
  · intro i' hi' j hj
    have hi'_code : code i' = w := (Finset.mem_filter.mp hi').2
    have hbit : bit j = b := (Finset.mem_filter.mp hj).2
    rw [same_row i' i (hi'_code.trans hi_code.symm) j]
    change decide (M i j = 1) = b at hbit
    rcases hbool i j with hzero | hone <;> subst b <;> simp_all
  · have hrows : (m : ℝ) ≤ (2 : ℝ) ^ M.rank * A.card := by exact_mod_cast rows
    have hcols : (n : ℝ) ≤ 2 * (B.card : ℝ) := by exact_mod_cast cols
    calc
      (m : ℝ) * n ≤ (2 ^ M.rank * A.card) * (2 * (B.card : ℝ)) :=
        mul_le_mul hrows hcols (Nat.cast_nonneg _) (by positivity)
      _ = (A.card : ℝ) * B.card * (2 : ℝ) ^ (M.rank + 1) := by rw [pow_succ]; ring
      _ ≤ (A.card : ℝ) * B.card * Real.rpow 2 (1001 * Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hr : (1 : ℝ) ≤ M.rank := by exact_mod_cast hrank
        have hcap' : (M.rank : ℝ) ≤ 1000 := by exact_mod_cast hcap
        have hpow : 1 ≤ Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ) :=
          Real.one_le_rpow hr (by norm_num)
        push_cast
        linarith
