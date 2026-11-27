import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_middle_root_cap :
    ∀ p x H:ℕ,Nat.Prime p → 2<p → H≤p → ((Finset.Ico x (x+H)).filter (fun n => p∣n^2+1)).card≤2 := by
  intro p x H hp h2 hHp
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hinj : ∀ a ∈ (Finset.Ico x (x+H)).filter (fun n => p∣n^2+1),
      ∀ b ∈ (Finset.Ico x (x+H)).filter (fun n => p∣n^2+1),
      (a : ZMod p) = (b : ZMod p) → a = b := by
    intro a ha b hb hab
    have haI : a ∈ Finset.Ico x (x+p) := by
      have h := (Finset.mem_filter.mp ha).1
      rw [Finset.mem_Ico] at h ⊢
      exact ⟨h.1, by omega⟩
    have hbI : b ∈ Finset.Ico x (x+p) := by
      have h := (Finset.mem_filter.mp hb).1
      rw [Finset.mem_Ico] at h ⊢
      exact ⟨h.1, by omega⟩
    have hmod : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rw [Finset.mem_Ico] at haI hbI
    obtain ⟨ha1, ha2⟩ := haI
    obtain ⟨hb1, hb2⟩ := hbI
    rcases le_total a b with hle | hle
    · have hk : b - a < p := by omega
      have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
      have h0 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hk
      omega
    · have hk : a - b < p := by omega
      have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have h0 : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hk
      omega
  have hroots : ∀ a ∈ ((Finset.Ico x (x+H)).filter (fun n => p∣n^2+1)).image
      (fun n : ℕ => (n : ZMod p)), a^2 + 1 = 0 := by
    intro a ha
    obtain ⟨n, hn, hna⟩ := Finset.mem_image.mp ha
    rw [← hna]
    have hdvd : p ∣ n^2+1 := (Finset.mem_filter.mp hn).2
    have hzero : ((n^2+1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n^2+1) p).mpr hdvd
    simpa using hzero
  have hcap : ∀ (s : Finset (ZMod p)), (∀ a ∈ s, a^2 + 1 = 0) → s.card ≤ 2 := by
    intro s hs
    by_cases hne : s.Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      have hsub : s ⊆ ({a0, -a0} : Finset (ZMod p)) := by
        intro b hb
        have hb2 : b^2 = -1 := by
          simpa using (add_eq_zero_iff_eq_neg.mp (hs b hb))
        have ha2 : a0^2 = -1 := by
          simpa using (add_eq_zero_iff_eq_neg.mp (hs a0 ha0))
        have hfac : (b - a0) * (b + a0) = 0 := by
          have hz : b^2 - a0^2 = 0 := by
            rw [hb2, ha2]
            ring
          calc (b - a0) * (b + a0) = b^2 - a0^2 := by ring
            _ = 0 := hz
        rcases mul_eq_zero.mp hfac with h | h
        · have hba : b = a0 := sub_eq_zero.mp h
          rw [hba]
          simp
        · have hba : b = -a0 := add_eq_zero_iff_eq_neg.mp h
          rw [hba]
          simp
      calc s.card ≤ ({a0, -a0} : Finset (ZMod p)).card := Finset.card_le_card hsub
        _ ≤ 2 := by
          have h1 := Finset.card_insert_le a0 ({-a0} : Finset (ZMod p))
          simp only [Finset.card_singleton] at h1
          omega
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp
  have hcard : (((Finset.Ico x (x+H)).filter (fun n => p∣n^2+1)).image (fun n : ℕ => (n : ZMod p))).card
      = ((Finset.Ico x (x+H)).filter (fun n => p∣n^2+1)).card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    exact hinj a ha b hb hab
  refine le_trans ?_ (hcap _ hroots)
  rw [← hcard]
