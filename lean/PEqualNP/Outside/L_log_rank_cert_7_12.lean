import Mathlib

open scoped BigOperators

/-! Certificate gap `L-log-rank-cert-7-12` (log-rank desk): powerset choose counts and disjointness. -/

theorem PEqualNP.Outside.L_log_rank_cert_7_12 : ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 7; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 12; R.card*C.card=Nat.choose S.card 7*Nat.choose (n-S.card) 12 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  constructor
  · rw [Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ_sdiff, Fintype.card_fin]
  · intro A hA B hB
    rw [Finset.mem_powersetCard] at hA hB
    obtain ⟨hAS, -⟩ := hA
    obtain ⟨hBS, -⟩ := hB
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp (hBS hb)).2 (hAS ha)
