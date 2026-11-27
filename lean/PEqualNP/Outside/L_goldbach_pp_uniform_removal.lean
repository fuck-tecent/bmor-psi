import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Classical in
private lemma pp_card (n : ℕ) :
    ((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card
      ≤ Nat.sqrt n * Nat.log 2 n := by
  have hsub : (Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) ⊆
      (Finset.Icc 2 (Nat.sqrt n) ×ˢ Finset.Icc 2 (Nat.log 2 n)).image (fun p : ℕ × ℕ => p.1 ^ p.2) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, b, a, hb, ha, rfl⟩ := hk
    have hkn' : b ^ a ≤ n := by omega
    rw [Finset.mem_image]
    refine ⟨(b, a), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨hb, ?_⟩, ha, ?_⟩
    · rw [Nat.le_sqrt']
      exact le_trans (Nat.pow_le_pow_right (by omega) ha) hkn'
    · apply Nat.le_log_of_pow_le Nat.one_lt_two
      exact le_trans (Nat.pow_le_pow_left hb a) hkn'
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = (Nat.sqrt n + 1 - 2) * (Nat.log 2 n + 1 - 2) := by simp
    _ ≤ Nat.sqrt n * Nat.log 2 n := Nat.mul_le_mul (by omega) (by omega)

private lemma log2_le (n : ℕ) (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have h1 : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  nlinarith

open Classical in
open Classical in
private lemma main_bound (n : ℕ) (hn : 1 ≤ n) (v : ℕ → ℝ) (hv : ∀ k, |v k| ≤ 1) :
    let A := fun k : ℕ => if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card then Real.log (k:ℝ) else 0
    ((|∑ k ∈ Finset.range (n+1), A k * v k * Real.log ((n+1:ℕ):ℝ)|) / (n:ℝ)) ^ 2
      ≤ 4 * (Real.log ((n+1:ℕ):ℝ)) ^ 6 / (n:ℝ) := by
  intro A
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log ((n+1:ℕ):ℝ) := Real.log_natCast_nonneg _
  set L := Real.log ((n+1:ℕ):ℝ) with hLdef
  have hA0 : ∀ k, 0 ≤ A k := by
    intro k; simp only [A]; split_ifs
    · exact Real.log_natCast_nonneg k
    · exact le_rfl
  have hAL : ∀ k ∈ Finset.range (n+1), A k ≤ L := by
    intro k hk
    have hkn : k < n + 1 := Finset.mem_range.mp hk
    simp only [A]
    split_ifs
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simpa using hL0
      · exact Real.log_le_log (by exact_mod_cast h0) (by push_cast; exact_mod_cast hkn.le)
    · exact hL0
  have hQ : ∀ k, 0 < A k → ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k := by
    intro k hk
    by_contra hcon
    have : A k = 0 := by
      simp only [A]
      rw [if_neg]
      intro hc
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hc
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      apply hcon
      have hk1 : k ≠ 1 := by
        rintro rfl
        have := ha.1.2
        simp at this
        omega
      exact ⟨k.minFac, a, (Nat.minFac_prime hk1).two_le, ha.1.1, ha.2⟩
    linarith
  have hpt : ∀ k ∈ Finset.range (n+1), |A k * v k * L|
      ≤ if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then L * L else 0 := by
    intro k hk
    split_ifs with hq
    · rw [abs_mul, abs_mul, abs_of_nonneg (hA0 k), abs_of_nonneg hL0]
      calc A k * |v k| * L ≤ L * 1 * L := by
            gcongr
            · exact hAL k hk
            · exact hv k
        _ = L * L := by ring
    · have : A k = 0 := by
        rcases (hA0 k).eq_or_lt with h | h
        · exact h.symm
        · exact absurd (hQ k h) hq
      simp [this]
  have hsum : |∑ k ∈ Finset.range (n+1), A k * v k * L|
      ≤ (((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ) * (L * L) := by
    calc _ ≤ ∑ k ∈ Finset.range (n+1), |A k * v k * L| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then L * L else 0) :=
          Finset.sum_le_sum hpt
      _ = _ := by rw [← Finset.sum_filter]; simp
  have hcard : (((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ)
      ≤ (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) := by exact_mod_cast pp_card n
  have hs2 : ((Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hl : (Nat.log 2 n : ℝ) ≤ 2 * L := by
    refine le_trans (log2_le n hn) ?_
    have : Real.log (n:ℝ) ≤ L := Real.log_le_log hN (by push_cast; linarith)
    linarith
  have hl0 : (0:ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have hs0 : (0:ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ (((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ) :=
    Nat.cast_nonneg _
  set c := (((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ) with hc
  have hc2 : c ^ 2 ≤ 4 * (n:ℝ) * L ^ 2 := by
    calc c ^ 2 ≤ ((Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ)) ^ 2 := pow_le_pow_left₀ hc0 hcard 2
      _ = (Nat.sqrt n : ℝ) ^ 2 * (Nat.log 2 n : ℝ) ^ 2 := by ring
      _ ≤ (n:ℝ) * (2 * L) ^ 2 := by
          apply mul_le_mul hs2 (pow_le_pow_left₀ hl0 hl 2) (by positivity) hN.le
      _ = 4 * (n:ℝ) * L ^ 2 := by ring
  have hM0 : 0 ≤ |∑ k ∈ Finset.range (n+1), A k * v k * L| := abs_nonneg _
  have h1 : |∑ k ∈ Finset.range (n+1), A k * v k * L| / (n:ℝ) ≤ c * (L * L) / (n:ℝ) :=
    div_le_div_of_nonneg_right hsum hN.le
  have h2 : (|∑ k ∈ Finset.range (n+1), A k * v k * L| / (n:ℝ)) ^ 2 ≤ (c * (L * L) / (n:ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  refine le_trans h2 ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) hN]
  have : (c * (L * L)) ^ 2 = c ^ 2 * L ^ 4 := by ring
  rw [this]
  have h3 : c ^ 2 * L ^ 4 ≤ 4 * (n:ℝ) * L ^ 2 * L ^ 4 :=
    mul_le_mul_of_nonneg_right hc2 (by positivity)
  have h4 : 0 ≤ L ^ 6 := by positivity
  nlinarith [h3, h4, hN]

theorem PEqualNP.Outside.L_goldbach_pp_uniform_removal :
    let A := fun k : ℕ => if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card then Real.log (k:ℝ) else 0; ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ∀ v : ℕ → ℝ, (∀ k, |v k|≤1) → |(∑ k ∈ Finset.range (n+1), A k*v k*Real.log ((n+1:ℕ):ℝ))/(n:ℝ)| < ε := by
  intro A ε hε
  have ht := Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have hδ : (0:ℝ) < ε ^ 2 / 8 := by positivity
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max ⌈x0⌉₊ 1, ?_⟩
  intro n hn v hv
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : (0:ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hx : x0 ≤ ((n+1:ℕ):ℝ) := by
    have h1 : x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
    have h2 : ⌈x0⌉₊ ≤ n := le_trans (le_max_left _ _) hn
    have h3 : (⌈x0⌉₊ : ℝ) ≤ n := by exact_mod_cast h2
    push_cast; linarith
  have hlt := hx0 _ hx
  have hmain := main_bound n hn1 v hv
  set L := Real.log ((n+1:ℕ):ℝ) with hL
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg _
  have hlt' : L ^ 6 < ε ^ 2 / 8 * ((n:ℝ) + 1) := by
    have hpos : (0:ℝ) < 1 * ((n+1:ℕ):ℝ) + 0 := by push_cast; linarith
    rw [div_lt_iff₀ hpos] at hlt
    push_cast at hlt
    linarith
  have hfin : 4 * L ^ 6 / (n:ℝ) < ε ^ 2 := by
    rw [div_lt_iff₀ hN]
    nlinarith [sq_nonneg ε]
  rw [abs_div, abs_of_pos hN]
  by_contra hcon
  push_neg at hcon
  have : ε ^ 2 ≤ (|∑ k ∈ Finset.range (n+1), A k * v k * L| / (n:ℝ)) ^ 2 :=
    pow_le_pow_left₀ hε.le hcon 2
  linarith
