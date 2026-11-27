import Mathlib

theorem PEqualNP.Outside.L_goldbach_grh_windows_thirds :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ), 0<s.re → s.re<1 → DirichletCharacter.LFunction χ s=0 → s.re=1/2) → let A := fun (q a X : ℕ) => ∑ k ∈ (Finset.range (X+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k; ∀ q a:ℕ, 0<q → Nat.Coprime a q → ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ X≥N, |(A q a (2*X/3)-A q a (X/3))-(X:ℝ)/(3*Nat.totient q)|≤e*(X:ℝ) := by
  intro _
  dsimp only
  intro q a hq ha e he
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let A (n : ℕ) : ℝ := ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q),
    ArithmeticFunction.vonMangoldt k
  let d : ℝ := (q.totient : ℝ)⁻¹
  have scaled (c : ℝ) (hc : 0 < c) :
      Filter.Tendsto (fun X : ℕ => A ⌊c*(X:ℝ)⌋₊ / X) Filter.atTop (nhds (c*d)) := by
    have hX : Filter.Tendsto (fun X : ℕ => c*(X:ℝ)) Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos hc).mpr tendsto_natCast_atTop_atTop
    apply (((ArithmeticFunction.vonMangoldt.tendsto_sum_modEq_div_atTop ha).comp hX).const_mul c).congr
    intro X
    simp only [Function.comp_apply]
    change c * ((∑ k ∈ (Finset.Icc 0 ⌊c*(X:ℝ)⌋₊).filter (fun k => k % q=a % q),
      ArithmeticFunction.vonMangoldt k) / (c*X)) = A ⌊c*(X:ℝ)⌋₊ / X
    simp only [A, Nat.range_succ_eq_Icc_zero]
    rw [div_mul_eq_div_div, mul_div_assoc', mul_div_cancel₀ _ hc.ne']
  have h := (scaled (2/3) (by norm_num)).sub (scaled (1/3) (by norm_num))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp h e he
  refine ⟨max N 1, ?_⟩
  intro X hX
  have hx : (0:ℝ) < X := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hX)
  have hclose := hN X (le_trans (le_max_left _ _) hX)
  rw [Real.dist_eq] at hclose
  have hf2 : ⌊(2/3)*(X:ℝ)⌋₊ = 2*X/3 := by
    rw [show (2/3)*(X:ℝ) = (↑(2*X) : ℝ)/(3:ℕ) by push_cast; ring, Nat.floor_div_natCast, Nat.floor_natCast]
  have hf1 : ⌊(1/3)*(X:ℝ)⌋₊ = X/3 := by
    rw [show (1/3)*(X:ℝ) = (X:ℝ)/(3:ℕ) by ring, Nat.floor_div_natCast, Nat.floor_natCast]
  simp only [hf2,hf1] at hclose
  change |(A (2*X/3)-A (X/3))-(X:ℝ)/(3*q.totient:ℝ)| ≤ e*X
  have hid : (A (2*X/3)-A (X/3)-(X:ℝ)/(3*q.totient:ℝ))/X =
      (A (2*X/3)/X-A (X/3)/X) - ((2/3)*d - (1/3)*d) := by
    have hd : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    dsimp only [d]
    field_simp
    ring
  apply le_of_lt
  apply (div_lt_iff₀ hx).mp
  rw [← hid, abs_div, abs_of_pos hx] at hclose
  exact hclose
