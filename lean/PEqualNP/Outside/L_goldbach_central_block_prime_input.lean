import Mathlib

/-!
# L-goldbach-central-block-prime-input

The Chebyshev mass of the interior prime block: for `x` large, the primes in
`[x / 2, 2x / 3]` carry logarithmic weight at least `x / 12`. The prime number
theorem for the Chebyshev function (`θ x / x → 1`) gives `θ (2x/3) − θ (x/2)`
asymptotic to `x / 6`; the coprime-free window sum dominates this difference
because every prime below `2x/3` either lies below `x/2` or inside the block.
-/

theorem PEqualNP.Outside.L_goldbach_central_block_prime_input :
    let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0; let P := fun x : ℕ => (Finset.range (x+1)).filter (fun p => p.Prime ∧ x≤2*p ∧ 3*p≤2*x); ∃ c : ℝ, 0<c ∧ ∃ X : ℕ, ∀ x≥X, c*(x:ℝ) ≤ ∑ p ∈ P x, w p := by
  intro w P
  refine ⟨(1:ℝ)/12, by norm_num, ?_⟩
  have h23 : Filter.Tendsto (fun x : ℝ => (2:ℝ)/3*x) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have h12 : Filter.Tendsto (fun x : ℝ => (1:ℝ)/2*x) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have u := Chebyshev.tendsto_theta_div_atTop.comp h23
  have v := Chebyshev.tendsto_theta_div_atTop.comp h12
  have hu : ∀ᶠ x in Filter.atTop, (27:ℝ)/28 < Chebyshev.theta ((2:ℝ)/3*x)/((2:ℝ)/3*x) :=
    u.eventually (isOpen_Ioi.mem_nhds (by norm_num))
  have hv : ∀ᶠ x in Filter.atTop, Chebyshev.theta ((1:ℝ)/2*x)/((1:ℝ)/2*x) < (29:ℝ)/28 :=
    v.eventually (isOpen_Iio.mem_nhds (by norm_num))
  have keyev : ∀ᶠ x in Filter.atTop, (1:ℝ)/12*x ≤ Chebyshev.theta ((2:ℝ)/3*x) - Chebyshev.theta ((1:ℝ)/2*x) := by
    filter_upwards [hu, hv, Filter.eventually_gt_atTop (0:ℝ)] with x hu1 hv1 hxpos
    have hx23 : (0:ℝ) < (2:ℝ)/3*x := by positivity
    have hx12 : (0:ℝ) < (1:ℝ)/2*x := by positivity
    have hx23ne : (2:ℝ)/3*x ≠ 0 := ne_of_gt hx23
    have hx12ne : (1:ℝ)/2*x ≠ 0 := ne_of_gt hx12
    have e1 : Chebyshev.theta ((2:ℝ)/3*x) = (Chebyshev.theta ((2:ℝ)/3*x)/((2:ℝ)/3*x))*((2:ℝ)/3*x) := (div_mul_cancel₀ _ hx23ne).symm
    have e2 : Chebyshev.theta ((1:ℝ)/2*x) = (Chebyshev.theta ((1:ℝ)/2*x)/((1:ℝ)/2*x))*((1:ℝ)/2*x) := (div_mul_cancel₀ _ hx12ne).symm
    rw [e1, e2]
    have hA : (9:ℝ)/14*x < (Chebyshev.theta ((2:ℝ)/3*x)/((2:ℝ)/3*x))*((2:ℝ)/3*x) := by
      have hr : (27:ℝ)/28*((2:ℝ)/3*x) < (Chebyshev.theta ((2:ℝ)/3*x)/((2:ℝ)/3*x))*((2:ℝ)/3*x) := mul_lt_mul_of_pos_right hu1 hx23
      rw [← show (27:ℝ)/28*((2:ℝ)/3*x) = (9:ℝ)/14*x from by ring]
      exact hr
    have hB : (Chebyshev.theta ((1:ℝ)/2*x)/((1:ℝ)/2*x))*((1:ℝ)/2*x) < (29:ℝ)/56*x := by
      have hr : (Chebyshev.theta ((1:ℝ)/2*x)/((1:ℝ)/2*x))*((1:ℝ)/2*x) < (29:ℝ)/28*((1:ℝ)/2*x) := mul_lt_mul_of_pos_right hv1 hx12
      rw [← show (29:ℝ)/28*((1:ℝ)/2*x) = (29:ℝ)/56*x from by ring]
      exact hr
    linarith
  have natkey := tendsto_natCast_atTop_atTop.eventually keyev
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp natkey
  have hsum : ∀ x : ℕ, 1 ≤ x → Chebyshev.theta ((2:ℝ)/3*((x:ℝ))) - Chebyshev.theta ((1:ℝ)/2*((x:ℝ))) ≤ ∑ p ∈ P x, w p := by
    intro x hx
    have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
    have hfl1 : (1:ℝ)/2*((x:ℝ)) < Nat.floor ((1:ℝ)/2*((x:ℝ))) + 1 := Nat.lt_floor_add_one _
    have hflle2 : ((Nat.floor ((2:ℝ)/3*((x:ℝ))) : ℕ) : ℝ) ≤ (2:ℝ)/3*((x:ℝ)) := Nat.floor_le (by positivity)
    have hflle1 : ((Nat.floor ((1:ℝ)/2*((x:ℝ))) : ℕ) : ℝ) ≤ (1:ℝ)/2*((x:ℝ)) := Nat.floor_le (by positivity)
    have hflo : x < 2 * (Nat.floor ((1:ℝ)/2*((x:ℝ))) + 1) := by
      have hc : ((x:ℝ)) < ((2 * (Nat.floor ((1:ℝ)/2*((x:ℝ))) + 1) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hc
    have hfhi : 3 * Nat.floor ((2:ℝ)/3*((x:ℝ))) ≤ 2 * x := by
      have hprod : (3:ℝ)*((2:ℝ)/3*((x:ℝ))) = 2*((x:ℝ)) := by field_simp
      have hc : ((3 * Nat.floor ((2:ℝ)/3*((x:ℝ))) : ℕ) : ℝ) ≤ 2*((x:ℝ)) := by
        push_cast
        linarith [hflle2, hprod]
      exact_mod_cast hc
    have hθhi : Chebyshev.theta ((2:ℝ)/3*((x:ℝ))) = ∑ p ∈ (Finset.Icc 0 (Nat.floor ((2:ℝ)/3*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ)) := Chebyshev.theta_eq_sum_Icc _
    have hθlo : Chebyshev.theta ((1:ℝ)/2*((x:ℝ))) = ∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ)) := Chebyshev.theta_eq_sum_Icc _
    have hsub : (Finset.Icc 0 (Nat.floor ((2:ℝ)/3*((x:ℝ))))).filter (fun p => p.Prime) ⊆ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x := by
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hple : p ≤ Nat.floor ((2:ℝ)/3*((x:ℝ))) := (Finset.mem_Icc.mp hmem.1).2
      have hpp' : p.Prime := hmem.2
      by_cases hc : p ≤ Nat.floor ((1:ℝ)/2*((x:ℝ)))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le p, hc⟩, hpp'⟩)
      · have hpr : ((p:ℝ)) ≤ (2:ℝ)/3*((x:ℝ)) := by
          have h1 : ((p:ℝ)) ≤ ((Nat.floor ((2:ℝ)/3*((x:ℝ))) : ℕ) : ℝ) := by exact_mod_cast hple
          linarith
        have hpx : ((p:ℝ)) ≤ ((x:ℝ)) := by linarith
        have hpN : p ≤ x := Nat.cast_le.mp hpx
        have h2p : x ≤ 2*p := by omega
        have h3p : 3*p ≤ 2*x := by omega
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨hpp', h2p, h3p⟩⟩)
    have hlognn : ∀ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x, (0:ℝ) ≤ Real.log ((p:ℝ)) := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · have hpp : p.Prime := (Finset.mem_filter.mp h).2
        exact Real.log_nonneg (by exact_mod_cast hpp.one_le)
      · have hpp : p.Prime := ((Finset.mem_filter.mp h).2).1
        exact Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hle : ∑ p ∈ (Finset.Icc 0 (Nat.floor ((2:ℝ)/3*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ)) ≤ ∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ)) + ∑ p ∈ P x, Real.log ((p:ℝ)) := by
      have hsplitU : (∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x, Real.log ((p:ℝ))) + (∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∩ P x, Real.log ((p:ℝ))) = (∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ))) + (∑ p ∈ P x, Real.log ((p:ℝ))) :=
        Finset.sum_union_inter
      have hnnI : (0:ℝ) ≤ ∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∩ P x, Real.log ((p:ℝ)) := by
        refine Finset.sum_nonneg (fun p hp => ?_)
        have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2
        exact Real.log_nonneg (by exact_mod_cast hpp.one_le)
      have hsd : (∑ p ∈ ((Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x) \ (Finset.Icc 0 (Nat.floor ((2:ℝ)/3*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ))) + (∑ p ∈ (Finset.Icc 0 (Nat.floor ((2:ℝ)/3*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ))) = (∑ p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x, Real.log ((p:ℝ))) := Finset.sum_sdiff (M := ℝ) hsub
      have hnnU : (0:ℝ) ≤ ∑ p ∈ ((Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x) \ (Finset.Icc 0 (Nat.floor ((2:ℝ)/3*((x:ℝ))))).filter (fun p => p.Prime), Real.log ((p:ℝ)) := by
        refine Finset.sum_nonneg (fun p hp => ?_)
        have hmem : p ∈ (Finset.Icc 0 (Nat.floor ((1:ℝ)/2*((x:ℝ))))).filter (fun p => p.Prime) ∪ P x := (Finset.mem_sdiff.mp hp).1
        exact hlognn p hmem
      linarith [hsd, hnnU, hsplitU, hnnI]
    have hwlog : ∑ p ∈ P x, Real.log ((p:ℝ)) = ∑ p ∈ P x, w p := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hpp : p.Prime := ((Finset.mem_filter.mp hp).2).1
      exact (if_pos hpp).symm
    rw [hθhi, hθlo, ← hwlog]
    linarith [hle]
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hkey := hX x (le_trans (le_max_left X 1) hx)
  have hx1 : 1 ≤ x := le_trans (le_max_right X 1) hx
  calc (1:ℝ)/12*((x:ℝ)) ≤ Chebyshev.theta ((2:ℝ)/3*((x:ℝ))) - Chebyshev.theta ((1:ℝ)/2*((x:ℝ))) := hkey
    _ ≤ ∑ p ∈ P x, w p := hsum x hx1
