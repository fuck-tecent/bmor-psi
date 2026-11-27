import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_reflection :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n a, a ∈ U q n → (n+q-a)%q ∈ U q n := by
  dsimp only
  intro q n a ha
  simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
  obtain ⟨haq, ha, hc⟩ := ha
  let b := (n + q - a) % q
  have hb : b < q := Nat.mod_lt _ (by omega)
  have h : Nat.ModEq q b (n + q - a) := Nat.mod_modEq _ _
  refine ⟨hb, h.gcd_eq.trans hc, ?_⟩
  have heq : b + (n + q - b) = (n + q - a) + a := by omega
  have href : Nat.ModEq q (n + q - b) a := h.add_left_cancel (by rw [heq])
  exact href.gcd_eq.trans ha
