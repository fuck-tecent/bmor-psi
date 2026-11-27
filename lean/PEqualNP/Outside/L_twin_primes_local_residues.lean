import Mathlib

theorem PEqualNP.Outside.L_twin_primes_local_residues :
    ∀ p : ℕ, p.Prime → ((Finset.range p).filter (fun n => Nat.Coprime n p ∧ Nat.Coprime (n+2) p)).card = if p=2 then 1 else p-2 := by
  intro p hp
  split_ifs with h2
  · subst h2; decide
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have key : (Finset.range p).filter (fun n => Nat.Coprime n p ∧ Nat.Coprime (n+2) p)
        = ((Finset.range p).erase 0).erase (p-2) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨hn, h1, h2'⟩
        refine ⟨?_, ?_, hn⟩
        · rintro rfl
          have : p - 2 + 2 = p := by omega
          rw [this, Nat.coprime_self] at h2'
          exact hp.one_lt.ne' h2'
        · rintro rfl
          rw [Nat.coprime_zero_left] at h1
          exact hp.one_lt.ne' h1
      · rintro ⟨hn2, hn0, hn⟩
        refine ⟨hn, ?_, ?_⟩
        · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          intro hd
          exact hn0 (Nat.eq_zero_of_dvd_of_lt hd hn)
        · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          rintro ⟨c, hc⟩
          rcases c with _ | _ | c
          · omega
          · apply hn2; omega
          · nlinarith
    rw [key, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_range]
    · omega
    · simp
      omega
    · simp
      omega
