import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_repair_cover :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∀ n (U D:Finset (ℕ×ℕ)), (∀ z∈U,z.1<n ∧ z.2<n) → (∀ a∈U,∀ b∈U,∀ c∈U,a≠b → a≠c → b≠c → ((b.1:ℤ)-a.1)*((c.2:ℤ)-a.2)=((b.2:ℤ)-a.2)*((c.1:ℤ)-a.1) → a∈D ∨ b∈D ∨ c∈D) → valid n (U \ D) := by
  dsimp only
  intro n U D h1 h2
  constructor
  · intro z hz
    exact h1 z (Finset.mem_sdiff.mp hz).1
  · intro a ha b hb c hc hab hac hbc heq
    have ha' : a ∈ U := (Finset.mem_sdiff.mp ha).1
    have hb' : b ∈ U := (Finset.mem_sdiff.mp hb).1
    have hc' : c ∈ U := (Finset.mem_sdiff.mp hc).1
    rcases h2 a ha' b hb' c hc' hab hac hbc heq with h | h | h
    · exact (Finset.mem_sdiff.mp ha).2 h
    · exact (Finset.mem_sdiff.mp hb).2 h
    · exact (Finset.mem_sdiff.mp hc).2 h
