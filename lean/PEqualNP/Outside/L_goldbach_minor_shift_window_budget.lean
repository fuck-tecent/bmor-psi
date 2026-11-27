import Mathlib

private lemma energy_anchor (r : ℕ → ℝ) (n H : ℕ) (e : ℝ) (he : 0 < e)
    (hlt : (∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2) < (H : ℝ) * e ^ 2) :
    ∃ j < H, |r (n + 2 * j)| < e := by
  by_contra hall
  push Not at hall
  have hge : ∑ _j ∈ Finset.range H, e ^ 2 ≤ ∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2 := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjH : j < H := Finset.mem_range.mp hj
    have habs : e ≤ |r (n + 2 * j)| := hall j hjH
    have hsq : e ^ 2 ≤ |r (n + 2 * j)| ^ 2 := by nlinarith [abs_nonneg (r (n + 2 * j))]
    rwa [sq_abs] at hsq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hge
  linarith

private lemma downward_transfer (r : ℕ → ℝ) (n j : ℕ) :
    r (n + 2 * j) - r n ≤ ∑ i ∈ Finset.range j, max 0 (r (n + 2 * (i + 1)) - r (n + 2 * i)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hstep : r (n + 2 * (j + 1)) - r (n + 2 * j) ≤ max 0 (r (n + 2 * (j + 1)) - r (n + 2 * j)) :=
      le_max_right _ _
    linarith

theorem PEqualNP.Outside.L_goldbach_minor_shift_window_budget :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t)); let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}; let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0; let high := fun (n k : ℕ) => w k - low n k; let I := fun (n : ℕ) (a b : ℕ → ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume; let r := fun n : ℕ => (I n (high n) (high n)).re / (n : ℝ); ∀ n H : ℕ, ∀ e : ℝ, 0 < n → 0 < H → 0 < e → (∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2) < (H : ℝ) * e ^ 2 → (∑ i ∈ Finset.range (H - 1), max 0 (r (n + 2 * (i + 1)) - r (n + 2 * i))) ≤ e → -(2 * e * (n : ℝ)) ≤ (I n (high n) (high n)).re := by
  intro w E S Q arcs low high I r n H e hn hH he hlt hvar
  obtain ⟨j, hjH, hjabs⟩ := energy_anchor r n H e he hlt
  have hlow : -e < r (n + 2 * j) := (abs_lt.mp hjabs).1
  have htr : r (n + 2 * j) - r n ≤ ∑ i ∈ Finset.range j, max 0 (r (n + 2 * (i + 1)) - r (n + 2 * i)) :=
    downward_transfer r n j
  have hsub : Finset.range j ⊆ Finset.range (H - 1) := by
    intro i hi
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
  have hsumle : (∑ i ∈ Finset.range j, max 0 (r (n + 2 * (i + 1)) - r (n + 2 * i))) ≤
      ∑ i ∈ Finset.range (H - 1), max 0 (r (n + 2 * (i + 1)) - r (n + 2 * i)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => le_max_left _ _)
  have hrn : -(2 * e) ≤ r n := by linarith
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul : -(2 * e) * (n : ℝ) ≤ r n * (n : ℝ) := mul_le_mul_of_nonneg_right hrn hnR.le
  have hrdef : r n * (n : ℝ) = (I n (high n) (high n)).re := by
    dsimp only [r]
    exact div_mul_cancel₀ _ hnR.ne'
  linarith
