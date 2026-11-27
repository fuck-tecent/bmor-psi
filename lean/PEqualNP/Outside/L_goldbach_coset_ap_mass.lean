import Mathlib.NumberTheory.LSeries.WeakPNT

open Filter Topology Finset

private lemma ap_sum_eq (q r n : ℕ) (hr : r < q) :
    (∑ p ∈ (Ioc 0 ⌊(n:ℝ)⌋₊).filter (fun p => p.Prime ∧ p ≡ r [MOD q]), Real.log p)
      = ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), (if k.Prime then Real.log (k:ℝ) else 0) := by
  rw [Nat.floor_natCast, ← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, Nat.ModEq, Nat.mod_eq_of_lt hr]
  constructor
  · rintro ⟨⟨_, h2⟩, h3, h4⟩
    exact ⟨by omega, h4, h3⟩
  · rintro ⟨h1, h4, h3⟩
    exact ⟨⟨h3.pos, by omega⟩, h3, h4⟩

private lemma ap_tendsto (q r : ℕ) [NeZero q] (hr : r < q) (hc : r.Coprime q) :
    Tendsto (fun n : ℕ => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r),
      (if k.Prime then Real.log (k:ℝ) else 0)) / (n:ℝ)) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h := (Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := q) hc).comp tendsto_natCast_atTop_atTop
  refine h.congr (fun n => ?_)
  simp only [Function.comp]
  rw [ap_sum_eq q r n hr]

theorem PEqualNP.Outside.L_goldbach_coset_ap_mass :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ q : ℕ, 0<q → ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ∀ r<q, r.Coprime q → |A n q r/(n:ℝ)-1/(q.totient:ℝ)| ≤ ε := by
  intro w F A q hq ε hε
  have : NeZero q := ⟨by omega⟩
  have key : ∀ r ∈ Finset.range q, ∀ᶠ n : ℕ in atTop, r.Coprime q → |A n q r/(n:ℝ)-1/(q.totient:ℝ)| ≤ ε := by
    intro r hr
    by_cases hc : r.Coprime q
    · have h := ap_tendsto q r (Finset.mem_range.1 hr) hc
      have h2 := (Metric.tendsto_nhds.1 h) ε hε
      filter_upwards [h2] with n hn _
      rw [Real.dist_eq] at hn
      simp only [A, F, w, one_div]
      exact hn.le
    · exact Filter.Eventually.of_forall (fun n h => absurd h hc)
  have := (Filter.eventually_all_finset (Finset.range q)).2 key
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 this
  exact ⟨X, fun n hn r hr hc => hX n hn r (Finset.mem_range.2 hr) hc⟩
