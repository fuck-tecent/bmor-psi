import Mathlib

open Filter Finset
open scoped BigOperators Topology

theorem PEqualNP.Outside.L_goldbach_grh_windows_centered_prime :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) →
    ∀ q a : ℕ, 0 < q → Nat.Coprime a q →
      ∃ N : ℕ, ∀ X ≥ N, ∃ p : ℕ,
        Nat.Prime p ∧ p % q = a % q ∧ X < 3 * p ∧ 3 * p < 2 * X := by
  intro _hGRH q a hq ha
  let _ : NeZero q := ⟨hq.ne'⟩
  let P : ℝ → Finset ℕ := fun x => (Ioc 0 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  let θ : ℝ → ℝ := fun x => ∑ p ∈ P x, Real.log (p : ℝ)
  let L : ℝ := (q.totient : ℝ)⁻¹
  have hL : 0 < L := by dsimp [L]; exact inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hq)
  have hθ : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 L) :=
    Chebyshev.tendsto_sum_log_prime_modEq_div_atTop ha
  have hscaled (c : ℝ) (hc : 0 < c) :
      Tendsto (fun X : ℕ => θ (c * (X : ℝ)) / (X : ℝ)) atTop (𝓝 (c * L)) := by
    have hat : Tendsto (fun X : ℕ => c * (X : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
    refine ((hθ.comp hat).const_mul c).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hX₀ : (X : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hX
    dsimp only [Function.comp_apply]
    field_simp
  have hdiff : Tendsto (fun X : ℕ =>
      θ ((1 / 2 : ℝ) * (X : ℝ)) / (X : ℝ) - θ ((1 / 3 : ℝ) * (X : ℝ)) / (X : ℝ))
      atTop (𝓝 ((1 / 2 : ℝ) * L - (1 / 3 : ℝ) * L)) :=
    (hscaled (1 / 2) (by norm_num)).sub (hscaled (1 / 3) (by norm_num))
  have hlim : 0 < (1 / 2 : ℝ) * L - (1 / 3 : ℝ) * L := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdiff.eventually_const_lt hlim)
  refine ⟨max N 1, fun X hX => ?_⟩
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (le_max_right N 1).trans hX
  let lo : ℝ := (1 / 3 : ℝ) * X
  let hi : ℝ := (1 / 2 : ℝ) * X
  have hθlt : θ lo < θ hi := by
    have hh := hN X ((le_max_left N 1).trans hX)
    change 0 < θ hi / (X : ℝ) - θ lo / (X : ℝ) at hh
    rw [← sub_div] at hh
    exact sub_pos.mp ((div_pos_iff_of_pos_right hXp).mp hh)
  have hsub : P lo ⊆ P hi := by
    intro p hp
    obtain ⟨hpm, hpa⟩ := mem_filter.mp hp
    obtain ⟨hp₀, hp₁⟩ := mem_Ioc.mp hpm
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨hp₀, hp₁.trans (Nat.floor_mono (show lo ≤ hi by dsimp [lo, hi]; linarith))⟩, hpa⟩
  have hne : (P hi \ P lo).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro hz
    have h := sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
    rw [hz, sum_empty, zero_add] at h
    exact hθlt.ne h
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hphi, hplo⟩ := mem_sdiff.mp hp
  obtain ⟨hpI, hpPrime, hpClass⟩ := mem_filter.mp hphi
  obtain ⟨hp₀, hp₁⟩ := mem_Ioc.mp hpI
  have hlo : lo < (p : ℝ) := by
    apply (Nat.floor_lt (show 0 ≤ lo by dsimp [lo]; positivity)).mp
    exact lt_of_not_ge fun hh => hplo (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp₀, hh⟩, hpPrime, hpClass⟩)
  have hhi : (p : ℝ) ≤ hi := (by exact_mod_cast hp₁ : (p : ℝ) ≤ ⌊hi⌋₊).trans
    (Nat.floor_le (show 0 ≤ hi by dsimp [hi]; positivity))
  refine ⟨p, hpPrime, hpClass, ?_, ?_⟩
  · have h : (X : ℝ) < 3 * (p : ℝ) := by dsimp [lo] at hlo; linarith
    exact_mod_cast h
  · have h : 3 * (p : ℝ) < 2 * (X : ℝ) := by dsimp [hi] at hhi; linarith
    exact_mod_cast h
