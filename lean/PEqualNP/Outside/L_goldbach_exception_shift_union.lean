import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_shift_union :
    ∀ (I H : Finset ℕ) (P : ℕ → Bool),
      (I.filter (fun n => (H.filter (fun h => P (n + h) = true)).Nonempty)).card ≤
        Finset.sum H (fun h => (I.filter (fun n => P (n + h) = true)).card) := by
  intro I H P
  calc
    (I.filter (fun n => (H.filter (fun h => P (n + h) = true)).Nonempty)).card ≤
        (H.biUnion (fun h => I.filter (fun n => P (n + h) = true))).card := by
      apply Finset.card_le_card
      intro n hn
      have hnI := (Finset.mem_filter.mp hn).1
      obtain ⟨h, hh⟩ := (Finset.mem_filter.mp hn).2
      obtain ⟨hhH, hhP⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_biUnion.mpr ⟨h, hhH, Finset.mem_filter.mpr ⟨hnI, hhP⟩⟩
    _ ≤ Finset.sum H (fun h => (I.filter (fun n => P (n + h) = true)).card) :=
      Finset.card_biUnion_le
