import Mathlib

open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.TypeIiSpacingBound_aux

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def cap (H : ℕ) (x : ℝ) : ℝ :=
  if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  rw [Complex.norm_exp]
  simp

lemma E_pow (x : ℝ) (m : ℕ) : E x ^ m = E ((m : ℝ) * x) := by
  induction m with
  | zero => simp [E]
  | succ m ih =>
    rw [pow_succ, ih, ← E_add]
    congr 1
    push_cast
    ring

lemma E_sub_conj (x y : ℝ) : E (x - y) = E x * conj (E y) := by
  simp only [E, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma E_mul_star (x y : ℝ) : E x * (starRingEnd ℂ) (E y) = E (x - y) :=
  (E_sub_conj x y).symm

lemma cap_nonneg (H : ℕ) (x : ℝ) : 0 ≤ cap H x := by
  unfold cap
  split_ifs
  · positivity
  · exact le_min (Nat.cast_nonneg _) (div_nonneg (by norm_num) (norm_nonneg _))

lemma sum_Ico_pow_eq_shift (M L : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.Ico M (M + L), z ^ j = z ^ M * ∑ j ∈ Finset.range L, z ^ j := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => j - M) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range]
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    rw [Finset.mem_Ico] at hj₁ hj₂
    omega
  · intro r hr
    rw [Finset.mem_range] at hr
    refine ⟨M + r, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩, by omega⟩
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [← pow_add, Nat.add_sub_of_le hj.1]

lemma norm_sum_range_pow_le (L : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖∑ j ∈ Finset.range L, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

lemma sum_Ico_E_le_cap (M L H : ℕ) (x : ℝ) (hLH : L ≤ H) :
    ‖∑ m ∈ Finset.Ico M (M + L), E ((m : ℝ) * x)‖ ≤ cap H x := by
  have hrw : ∑ m ∈ Finset.Ico M (M + L), E ((m : ℝ) * x)
      = ∑ m ∈ Finset.Ico M (M + L), (E x) ^ m := by
    apply Finset.sum_congr rfl
    intro m _
    rw [E_pow]
  have htriv : ‖∑ m ∈ Finset.Ico M (M + L), (E x) ^ m‖ ≤ (L : ℝ) := by
    rw [sum_Ico_pow_eq_shift, norm_mul, norm_pow, norm_E, one_pow, one_mul]
    calc ‖∑ j ∈ Finset.range L, (E x) ^ j‖
        ≤ ∑ j ∈ Finset.range L, ‖(E x) ^ j‖ := norm_sum_le _ _
      _ = (L : ℝ) := by simp [norm_pow, norm_E]
  rw [hrw]
  by_cases hx : E x = 1
  · rw [cap, if_pos hx]
    exact htriv.trans (by exact_mod_cast hLH)
  · rw [cap, if_neg hx]
    refine le_min (htriv.trans (by exact_mod_cast hLH)) ?_
    rw [sum_Ico_pow_eq_shift, norm_mul, norm_pow, norm_E, one_pow, one_mul]
    have h := norm_sum_range_pow_le L (norm_E x) hx
    rwa [norm_sub_rev] at h

lemma sum_ite_cutoff (M H c : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ Finset.Ico M (M + H), (if m ≤ c then f m else 0)
      = ∑ m ∈ Finset.Ico M (min (M + H) (c + 1)), f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, lt_min h2 (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩, ?_⟩
    have h4 := lt_of_lt_of_le h2 (min_le_right _ _)
    omega

lemma sum_ite_mul_le (N M H q c : ℕ) (f : ℕ → ℂ)
    (hc : ∀ m, M ≤ m → m < M + H → (m * q ≤ N ↔ m ≤ c)) :
    ∑ m ∈ Finset.Ico M (M + H), (if m * q ≤ N then f m else 0)
      = ∑ m ∈ Finset.Ico M (min (M + H) (c + 1)), f m := by
  have hcong : ∀ m ∈ Finset.Ico M (M + H),
      (if m * q ≤ N then f m else 0) = (if m ≤ c then f m else 0) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    by_cases h : m * q ≤ N
    · rw [if_pos h, if_pos ((hc m hm.1 hm.2).mp h)]
    · rw [if_neg h, if_neg (fun h2 => h ((hc m hm.1 hm.2).mpr h2))]
  rw [Finset.sum_congr rfl hcong, sum_ite_cutoff]

lemma mul_max_iff (N k l m : ℕ) : (m * k ≤ N ∧ m * l ≤ N) ↔ (m * max k l ≤ N) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total k l with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  · intro h
    exact ⟨le_trans (Nat.mul_le_mul_left m (le_max_left k l)) h,
      le_trans (Nat.mul_le_mul_left m (le_max_right k l)) h⟩

lemma pair_bound (N M H : ℕ) (t : ℝ) (k l : ℕ) :
    ‖∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) *
          (starRingEnd ℂ) (if m * l ≤ N then E ((m : ℝ) * (l : ℝ) * t) else 0)‖
      ≤ cap H (((k : ℝ) - (l : ℝ)) * t) := by
  have hmlt : ∀ m : ℕ, (m : ℝ) * (k : ℝ) * t - (m : ℝ) * (l : ℝ) * t
      = (m : ℝ) * (((k : ℝ) - (l : ℝ)) * t) := by
    intro m
    ring
  have hterm : ∀ m : ℕ,
      (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) *
          (starRingEnd ℂ) (if m * l ≤ N then E ((m : ℝ) * (l : ℝ) * t) else 0)
      = (if m * k ≤ N ∧ m * l ≤ N then
          E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) := by
    intro m
    by_cases hk : m * k ≤ N
    · by_cases hl : m * l ≤ N
      · rw [if_pos hk, if_pos hl, if_pos ⟨hk, hl⟩, E_mul_star, hmlt m]
      · rw [if_pos hk, if_neg hl, if_neg (fun h : m * k ≤ N ∧ m * l ≤ N => hl h.2)]
        simp
    · rw [if_neg hk, if_neg (fun h : m * k ≤ N ∧ m * l ≤ N => hk h.1)]
      simp
  have hsum : ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) *
          (starRingEnd ℂ) (if m * l ≤ N then E ((m : ℝ) * (l : ℝ) * t) else 0)
      = ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N ∧ m * l ≤ N then
          E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) :=
    Finset.sum_congr rfl (fun m _ => hterm m)
  have hmaxsum : ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N ∧ m * l ≤ N then
          E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0)
      = ∑ m ∈ Finset.Ico M (M + H),
        (if m * max k l ≤ N then E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) := by
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : m * max k l ≤ N
    · rw [if_pos h, if_pos ((mul_max_iff N k l m).mpr h)]
    · rw [if_neg h, if_neg (fun hc => h ((mul_max_iff N k l m).mp hc))]
  have hcond : ∀ m : ℕ, M ≤ m → m < M + H →
      (m * max k l ≤ N ↔ m ≤ if max k l = 0 then M + H else N / max k l) := by
    intro m hm1 hm2
    by_cases hq : max k l = 0
    · rw [if_pos hq]
      constructor
      · intro _
        omega
      · intro _
        rw [hq, Nat.mul_zero]
        omega
    · rw [if_neg hq]
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)).symm
  rw [hsum, hmaxsum,
    sum_ite_mul_le N M H (max k l) (if max k l = 0 then M + H else N / max k l) _ hcond]
  by_cases hB : M ≤ min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1)
  · have hLB : min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1)
        = M + (min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1) - M) :=
      (Nat.add_sub_of_le hB).symm
    have hLH : min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1) - M ≤ H := by
      have h1 : min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1) ≤ M + H :=
        min_le_left _ _
      omega
    rw [hLB]
    exact sum_Ico_E_le_cap M _ H _ hLH
  · have hempty : Finset.Ico M
        (min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1)) = ∅ := by
      rw [Finset.Ico_eq_empty]
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    exact cap_nonneg H _

lemma energy_identity {α β : Type*} (s : Finset α) (u : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    ((∑ m ∈ s, ‖∑ n ∈ u, b n * z m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ u, ∑ k ∈ u, b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k) := by
  classical
  have hpoint (m : α) :
      (‖∑ n ∈ u, b n * z m n‖ ^ 2 : ℂ) =
        ∑ n ∈ u, ∑ k ∈ u,
          b n * (starRingEnd ℂ) (b k) *
            (z m n * (starRingEnd ℂ) (z m k)) := by
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  push_cast
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

lemma energy_le_correlations {α β : Type*} (s : Finset α) (u : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    (∑ m ∈ s, ‖∑ n ∈ u, b n * z m n‖ ^ 2) ≤
      ∑ n ∈ u, ∑ k ∈ u, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have h := congrArg Complex.re (energy_identity s u b z)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

lemma norm_bilinear_sq_le {α β : Type*} (s : Finset α) (u : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) :
    ‖∑ m ∈ s, a m * ∑ n ∈ u, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) *
        (∑ n ∈ u, ∑ k ∈ u, ‖b n‖ * ‖b k‖ *
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) := by
  calc
    _ ≤ (∑ m ∈ s, ‖a m‖ * ‖∑ n ∈ u, b n * z m n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using
        norm_sum_le s (fun m => a m * ∑ n ∈ u, b n * z m n)
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) *
        ∑ m ∈ s, ‖∑ n ∈ u, b n * z m n‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_le_correlations s u b z)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem main_aux (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M + H), a m *
        ∑ k ∈ K, (if m * k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2
      ≤ (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ ^ 2) *
        (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - (l : ℝ)) * t)) := by
  have hb : ∀ m k : ℕ, (if m * k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)
      = b k * (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) := by
    intro m k
    by_cases h : m * k ≤ N
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  have hL : ∑ m ∈ Finset.Ico M (M + H), a m *
        ∑ k ∈ K, (if m * k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)
      = ∑ m ∈ Finset.Ico M (M + H), a m *
        ∑ k ∈ K, b k * (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_congr rfl (fun k _ => hb m k)]
  rw [hL]
  have h := norm_bilinear_sq_le (Finset.Ico M (M + H)) K a b
    (fun m n => if m * n ≤ N then E ((m : ℝ) * (n : ℝ) * t) else 0)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun m _ => sq_nonneg _))
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left (pair_bound N M H t k l)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end Conjectures.Goldbach.TypeIiSpacingBound_aux

theorem Conjectures.Goldbach.TypeIiSpacingBound : let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖); ∀ (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ), let I := Finset.Ico M (M+H); ‖∑ m ∈ I, a m * ∑ k ∈ K, (if m*k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2 ≤ (∑ m ∈ I, ‖a m‖ ^ 2) * (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - (l : ℝ)) * t)) :=
  Conjectures.Goldbach.TypeIiSpacingBound_aux.main_aux
