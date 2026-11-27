import Mathlib

open Filter Finset
open scoped BigOperators Topology

theorem PEqualNP.Outside.L_goldbach_grh_windows_dyadic :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) →
    let A := fun (q a X : ℕ) =>
      ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k
    ∀ q a : ℕ, 0 < q → Nat.Coprime a q → ∀ e : ℝ, 0 < e →
      ∃ N : ℕ, ∀ X ≥ N,
        |(A q a (2 * X) - A q a X) - (X : ℝ) / Nat.totient q| ≤ e * (X : ℝ) := by
  intro _hGRH
  dsimp only
  intro q a hq ha e he
  let _ : NeZero q := ⟨hq.ne'⟩
  let A : ℕ → ℝ := fun X =>
    ∑ k ∈ (range (X + 1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k
  let L : ℝ := (q.totient : ℝ)⁻¹
  have hA : Tendsto (fun X : ℕ => A X / (X : ℝ)) atTop (𝓝 L) := by
    have H := (ArithmeticFunction.vonMangoldt.tendsto_sum_modEq_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine H.congr (fun X => ?_)
    have hs : Icc (0 : ℕ) X = range (X + 1) := by ext k; simp
    simp only [Function.comp_apply, Nat.floor_natCast, hs, Nat.ModEq, A]
  have hdouble : Tendsto (fun X : ℕ => 2 * X) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop M] with X hX
    omega
  have hraw := (((hA.comp hdouble).const_mul (2 : ℝ)).sub hA).sub_const L
  have hlimit : Tendsto (fun X : ℕ => ((A (2 * X) - A X) - (X : ℝ) / q.totient) /
      (X : ℝ)) atTop (𝓝 0) := by
    have hz : 2 * L - L - L = 0 := by ring
    rw [hz] at hraw
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hX₀ : (X : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hX
    dsimp [L]
    push_cast
    field_simp
  have hevent := (Metric.tendsto_nhds.mp hlimit) e he
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 1, fun X hX => ?_⟩
  have hpos : 0 < (X : ℝ) := by exact_mod_cast (le_max_right N 1).trans hX
  have hb := hN X ((le_max_left N 1).trans hX)
  change |(A (2 * X) - A X) - (X : ℝ) / q.totient| ≤ e * (X : ℝ)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos] at hb
  exact ((div_lt_iff₀ hpos).mp hb).le
