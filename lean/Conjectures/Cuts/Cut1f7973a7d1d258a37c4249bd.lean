import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- child 1 en: Identify the eighth moment on the unit interval with the number of equal four-term frequency sums, for any integer frequency map and finite support.
-- child 1 zh: 对任意整数频率映射和有限指标集，证明单位区间八阶矩等于两组四项频率和相等的有序解数。
-- child 2 en: Bound ordered collisions of four polynomial values after excluding all permutations of the first quadruple, with the stated sparse-support exponents.
-- child 2 zh: 剔除右侧只是左侧重排的解，按三次或更高次数的规定稀疏集指数，估计两组四项多项式值之和相等的有序解数。

theorem Conjectures.Cuts.Cut1f7973a7d1d258a37c4249bd
    (orthogonality : ∀ (f : ℕ → ℤ) (A : Finset ℕ),
      let K := fun t : ℝ => ∑ n ∈ A, Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (f n : ℂ) * (t : ℂ))
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let score := fun u : Fin 4 → ℕ => ∑ i, f (u i)
      intervalIntegral (fun t : ℝ => ‖K t‖^8) 0 1 MeasureTheory.volume =
        (((T.product T).filter (fun w => score w.1 = score w.2)).card : ℝ))
    (offDiagonal : ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ B : ℝ, 0 < B ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let T := Fintype.piFinset (fun _ : Fin 4 => A)
        let score := fun u : Fin 4 → ℕ => ∑ i, P.eval (u i : ℤ)
        (((T.product T).filter (fun w => score w.1 = score w.2 ∧
          ∀ σ : Equiv.Perm (Fin 4), w.2 ≠ w.1 ∘ σ)).card : ℝ) ≤
          B * (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then (5 : ℕ) else 4)) : (by
  classical
  exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
    let K := fun t : ℝ => ∑ n ∈ A, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((P.eval (n : ℤ) : ℤ) : ℂ) * (t : ℂ))
    intervalIntegral (fun t : ℝ => ‖K t‖^8) 0 1 MeasureTheory.volume ≤ C * (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then (5 : ℕ) else 4)) := by
  classical
  have diagonal_bound (A : Finset ℕ) (score : (Fin 4 → ℕ) → ℤ) :
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let pairs := T.product T
      (pairs.filter (fun w => score w.1 = score w.2)).card ≤
        (pairs.filter (fun w => score w.1 = score w.2 ∧
          ∀ σ : Equiv.Perm (Fin 4), w.2 ≠ w.1 ∘ σ)).card + 24 * A.card ^ 4 := by
    classical
    intro T pairs
    let off := pairs.filter (fun w => score w.1 = score w.2 ∧
      ∀ σ : Equiv.Perm (Fin 4), w.2 ≠ w.1 ∘ σ)
    let domain := T.product (Finset.univ : Finset (Equiv.Perm (Fin 4)))
    let diagonals := domain.image (fun w => (w.1, w.1 ∘ w.2))
    have cover : pairs.filter (fun w => score w.1 = score w.2) ⊆ off ∪ diagonals := by
      intro w hw
      obtain ⟨hpair, heq⟩ := Finset.mem_filter.mp hw
      by_cases h : ∃ σ : Equiv.Perm (Fin 4), w.2 = w.1 ∘ σ
      · obtain ⟨σ, hσ⟩ := h
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(w.1, σ),
          Finset.mem_product.mpr ⟨(Finset.mem_product.mp hpair).1, Finset.mem_univ _⟩,
          Prod.ext rfl hσ.symm⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨hpair, heq, fun σ hσ => h ⟨σ, hσ⟩⟩)
    have hdom : domain.card = 24 * A.card ^ 4 := by
      change (T ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4)))).card = _
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, T, Fintype.card_piFinset_const]
      rw [Nat.mul_comm]
      rfl
    exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_image_le.trans hdom.le) _))
  intro P hP ε hε
  obtain ⟨B, hB, hOff⟩ := offDiagonal P hP ε hε
  refine ⟨B + 24, by linarith, ?_⟩
  intro M hM A hA
  let score := fun u : Fin 4 → ℕ => ∑ i, P.eval (u i : ℤ)
  let T := Fintype.piFinset (fun _ : Fin 4 => A)
  let allPairs := (T.product T).filter (fun w => score w.1 = score w.2)
  let off := (T.product T).filter (fun w => score w.1 = score w.2 ∧
    ∀ σ : Equiv.Perm (Fin 4), w.2 ≠ w.1 ∘ σ)
  let k := if P.natDegree = 3 then (5 : ℕ) else 4
  have hcount : (allPairs.card : ℝ) ≤ (off.card : ℝ) + 24 * (A.card : ℝ)^4 := by
    exact_mod_cast diagonal_bound A score
  have hb : (off.card : ℝ) ≤ B * (M : ℝ)^ε * (A.card : ℝ)^k := hOff M hM A hA
  have hpow : (A.card : ℝ)^4 ≤ (A.card : ℝ)^k := by
    by_cases hz : A.card = 0
    · simp [k, hz]
    · have hone : (1 : ℝ) ≤ A.card := by exact_mod_cast (show 1 ≤ A.card by omega)
      apply pow_le_pow_right₀ hone
      dsimp [k]
      split <;> decide
  have hm : (1 : ℝ) ≤ (M : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ M by omega)) hε.le
  have hdiag : (A.card : ℝ)^4 ≤ (M : ℝ)^ε * (A.card : ℝ)^k :=
    hpow.trans (le_mul_of_one_le_left (by positivity) hm)
  have horth := orthogonality (fun n => P.eval (n : ℤ)) A
  exact horth.le.trans (hcount.trans (by
    calc
      (off.card : ℝ) + 24 * (A.card : ℝ)^4 ≤
        B * (M : ℝ)^ε * (A.card : ℝ)^k + 24 * ((M : ℝ)^ε * (A.card : ℝ)^k) := by
          linarith only [hb, hdiag]
      _ = (B + 24) * (M : ℝ)^ε * (A.card : ℝ)^k := by ring))
