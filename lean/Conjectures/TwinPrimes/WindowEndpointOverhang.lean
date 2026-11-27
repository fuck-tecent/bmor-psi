import Mathlib

/-- The gap-two loss at the right edge of the window `w X`.

`w X` is the set of `n` in `range (2*X+1)` with `X < n` and `50*n < 51*X`.  A starting point
`n ∈ w X` whose translate `n + 2` leaves the window must satisfy `50*n < 51*X ≤ 50*(n+2)`,
so the losing starting points all lie in an interval of length two: there are at most two of
them, and each contributes at most `A^2` to the sum.  Hence the difference between the
single-end short-window sum and the double-end short-window sum lies in `[0, 2*A^2]`. -/
theorem Conjectures.TwinPrimes.WindowEndpointOverhang :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ (X : ℕ) (f : ℕ → ℝ) (A : ℝ), 2 ≤ X → 0 ≤ A → (∀ n : ℕ, n ≤ 2*X+2 → 0 ≤ f n ∧ f n ≤ A) → 0 ≤ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ∧ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ≤ 2*A^2 := by
  dsimp only
  intro X f A hX hA hf
  let S : Finset ℕ :=
    (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
  let L : Finset ℕ := S.filter (fun n => n + 2 ∉ S)
  let g : ℕ → ℝ := fun n => f n * f (n + 2)
  change
    0 ≤ S.sum g - (S.filter (fun n => n + 2 ∈ S)).sum g ∧
      S.sum g - (S.filter (fun n => n + 2 ∈ S)).sum g ≤ 2 * A ^ 2
  have hS_mem (n : ℕ) (hn : n ∈ S) :
      n < 2 * X + 1 ∧ X < n ∧ 50 * n < 51 * X := by
    change n ∈ (Finset.range (2 * X + 1)).filter
      (fun n => X < n ∧ 50 * n < 51 * X) at hn
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hn).1,
      (Finset.mem_filter.mp hn).2⟩
  have hL_mem (n : ℕ) (hn : n ∈ L) : n ∈ S ∧ n + 2 ∉ S := by
    change n ∈ S.filter (fun n => n + 2 ∉ S) at hn
    exact Finset.mem_filter.mp hn
  have hL_overhang (n : ℕ) (hn : n ∈ L) : 51 * X ≤ 50 * (n + 2) := by
    rcases hL_mem n hn with ⟨hnS, hn2_notS⟩
    rcases hS_mem n hnS with ⟨hn_range, hXn, h50n⟩
    have hn2_range : n + 2 ∈ Finset.range (2 * X + 1) := by
      apply Finset.mem_range.mpr
      omega
    have hXn2 : X < n + 2 := by
      omega
    have hnot : ¬50 * (n + 2) < 51 * X := by
      intro hlt
      apply hn2_notS
      change n + 2 ∈ (Finset.range (2 * X + 1)).filter
        (fun n => X < n ∧ 50 * n < 51 * X)
      exact Finset.mem_filter.mpr ⟨hn2_range, ⟨hXn2, hlt⟩⟩
    omega
  have hcard : L.card ≤ 2 := by
    by_cases hL : L.Nonempty
    · let a : ℕ := L.min' hL
      have haL : a ∈ L := by
        dsimp [a]
        exact Finset.min'_mem L hL
      have hsub : L ⊆ ({a, a + 1} : Finset ℕ) := by
        intro n hn
        have hmin : a ≤ n := by
          dsimp [a]
          exact Finset.min'_le L n hn
        have h50n : 50 * n < 51 * X :=
          (hS_mem n (hL_mem n hn).1).2.2
        have hCa : 51 * X ≤ 50 * (a + 2) := hL_overhang a haL
        have hcases : n = a ∨ n = a + 1 := by
          omega
        rcases hcases with rfl | rfl
        · simp
        · simp
      calc
        L.card ≤ ({a, a + 1} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 2 := by simp
    · have hL_empty : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      simp [hL_empty]
  have hterm_bounds (n : ℕ) (hn : n ∈ L) : 0 ≤ g n ∧ g n ≤ A ^ 2 := by
    have hn_range : n < 2 * X + 1 := (hS_mem n (hL_mem n hn).1).1
    have hfn := hf n (by omega)
    have hfn2 := hf (n + 2) (by omega)
    constructor
    · dsimp [g]
      exact mul_nonneg hfn.1 hfn2.1
    · dsimp [g]
      calc
        f n * f (n + 2) ≤ A * f (n + 2) :=
          mul_le_mul_of_nonneg_right hfn.2 hfn2.1
        _ ≤ A * A := mul_le_mul_of_nonneg_left hfn2.2 hA
        _ = A ^ 2 := by ring
  have hsum_nonneg : 0 ≤ L.sum g := by
    apply Finset.sum_nonneg
    intro n hn
    exact (hterm_bounds n hn).1
  have hsum_upper : L.sum g ≤ 2 * A ^ 2 := by
    have hsum_card : L.sum g ≤ (L.card : ℝ) * A ^ 2 := by
      calc
        L.sum g ≤ ∑ n ∈ L, A ^ 2 :=
          Finset.sum_le_sum fun n hn => (hterm_bounds n hn).2
        _ = (L.card : ℝ) * A ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
    calc
      L.sum g ≤ (L.card : ℝ) * A ^ 2 := hsum_card
      _ ≤ 2 * A ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · exact sq_nonneg A
  have hdiff :
      S.sum g - (S.filter (fun n => n + 2 ∈ S)).sum g = L.sum g := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not S (fun n => n + 2 ∈ S) g
    dsimp [L]
    linarith
  constructor
  · rw [hdiff]
    exact hsum_nonneg
  · rw [hdiff]
    exact hsum_upper
