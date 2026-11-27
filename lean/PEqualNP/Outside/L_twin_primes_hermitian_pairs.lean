import Mathlib
theorem PEqualNP.Outside.L_twin_primes_hermitian_pairs : ∀ (n : ℕ) (A : Fin n → Fin n → ℂ), (∀ i j, A j i = star (A i j)) → ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2) |>.sum (fun z => A z.1 z.2)).im = 0 := by
  intro n A hA
  let S := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2)
  have hsum : (∑ z ∈ S, (A z.1 z.2).im) = ∑ z ∈ S, -(A z.1 z.2).im := by
    apply Finset.sum_bij (fun z _ => (z.2,z.1))
    · intro z hz
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact Ne.symm hz
    · intro a ha b hb h
      cases a; cases b; simp_all
    · intro z hz
      exact ⟨(z.2,z.1), by simpa [S, Finset.mem_filter] using (Ne.symm (by simpa [S, Finset.mem_filter] using hz)), by cases z; rfl⟩
    · intro z hz
      rw [hA z.1 z.2]
      simp
  have : (∑ z ∈ S, (A z.1 z.2).im) = 0 := by
    rw [Finset.sum_neg_distrib] at hsum
    linarith
  simpa [S, Complex.im_sum] using this

