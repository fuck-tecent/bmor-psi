import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_nonunit_l2 :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ n q : ℕ, 0<q → (∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q), (A n q r)^2) ≤ (∑ p ∈ q.primeFactors, Real.log (p:ℝ))^2 := by
  intro F w A n q hq
  let bad := (Finset.range q).filter (fun r => ¬r.Coprime q)
  let hits := (Finset.range (n + 1)).filter (fun k => k % q ∈ bad)
  have hw (k : ℕ) : 0 ≤ w k := by
    dsimp [w]
    split
    · exact Real.log_natCast_nonneg k
    · exact le_rfl
  have hA (r : ℕ) : 0 ≤ A n q r := Finset.sum_nonneg (fun k _ => hw k)
  have hsubset : hits.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hhits, hp⟩ := Finset.mem_filter.mp hk
    have hr := (Finset.mem_filter.mp hhits).2
    have hbad := (Finset.mem_filter.mp hr).2
    refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hq.ne'⟩
    by_contra hdvd
    apply hbad
    change Nat.gcd (k % q) q = 1
    rw [← Nat.gcd_rec q k, Nat.gcd_comm q k]
    exact hp.coprime_iff_not_dvd.mpr hdvd
  have hmass : (∑ r ∈ bad, A n q r) ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
    calc
      (∑ r ∈ bad, A n q r) = ∑ k ∈ hits, w k :=
        Finset.sum_fiberwise_eq_sum_filter (Finset.range (n + 1)) bad (fun k => k % q) w
      _ = ∑ k ∈ hits.filter Nat.Prime, Real.log (k : ℝ) := (Finset.sum_filter _ _).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _ _ => Real.log_natCast_nonneg k)
  calc
    (∑ r ∈ bad, (A n q r)^2) ≤ (∑ r ∈ bad, A n q r)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun r _ => hA r)
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun r _ => hA r)) hmass 2
