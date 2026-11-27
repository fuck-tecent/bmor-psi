import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_valuation_excess_levels :
    ∀ m p : ℕ, m≠0 → p.Prime → (m.factorization p - 1) = ((Finset.Icc 2 (m.factorization p)).filter (fun j => p^j ∣ m)).card := by
  intro m p hm hp
  have hfilter : (Finset.Icc 2 (m.factorization p)).filter (fun j => p ^ j ∣ m) =
      Finset.Icc 2 (m.factorization p) := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact (hp.pow_dvd_iff_le_factorization hm).mpr (Finset.mem_Icc.mp hj).2
  rw [hfilter, Nat.card_Icc]
  omega
