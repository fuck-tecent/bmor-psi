import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mass_witness :
    ∀ (X Y:ℕ), 0<(∑ n ∈ Finset.Ico X (2*X),Finset.sum ((n^2+1).primeFactors.filter (fun p => Y<p)) (fun (p:ℕ) => Real.log (p:ℝ))) → ∃ n∈Finset.Ico X (2*X),∃ p:ℕ,Nat.Prime p ∧ p∣n^2+1 ∧ Y<p := by
  intro X Y hsum
  have hterm : ∃ n : ℕ, n ∈ Finset.Ico X (2*X) ∧ ∃ p : ℕ,
      p ∈ (n^2+1).primeFactors.filter (fun p => Y < p) ∧ 0 < Real.log (p:ℝ) := by
    by_contra h
    push_neg at h
    have hle : Finset.sum (Finset.Ico X (2*X))
        (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => Y < p))
          (fun (p : ℕ) => Real.log (p:ℝ))) ≤ 0 :=
      Finset.sum_nonpos (fun n hn => Finset.sum_nonpos (fun p hp => h n hn p hp))
    linarith
  obtain ⟨n, hnI, p, hpF, hlog⟩ := hterm
  obtain ⟨hpmem, hYp⟩ := Finset.mem_filter.mp hpF
  exact ⟨n, hnI, p, Nat.prime_of_mem_primeFactors hpmem,
    Nat.dvd_of_mem_primeFactors hpmem, hYp⟩
