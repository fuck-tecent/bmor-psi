import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

private theorem sieve_crt_aux (a k n : ℕ) : a ∣ k*(k+n) ↔ a ∣ (k % a)*((k % a)+n) := by
  have h : k ≡ k % a [MOD a] := (Nat.mod_modEq k a).symm
  have h2 : k*(k+n) ≡ (k % a)*((k % a)+n) [MOD a] := h.mul (h.add_right n)
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h3 => h2.symm.trans h3, fun h3 => h2.trans h3⟩

theorem PEqualNP.Outside.L_goldbach_sieve_residue_crt :
    let r := fun n q : ℕ => ((Finset.range q).filter (fun k => q ∣ k*(k+n))).card; ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → r n (a*b)=r n a*r n b := by
  intro r n a b ha hb hab
  have hmem : ∀ k, k < a * b → ((a * b) ∣ k*(k+n) ↔ (a ∣ (k % a)*((k % a)+n) ∧ b ∣ (k % b)*((k % b)+n))) := by
    intro k _
    rw [← sieve_crt_aux, ← sieve_crt_aux]
    exact ⟨fun h => ⟨Dvd.dvd.trans (dvd_mul_right a b) h, Dvd.dvd.trans (dvd_mul_left b a) h⟩,
      fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd hab h.1 h.2⟩
  show ((Finset.range (a*b)).filter (fun k => (a*b) ∣ k*(k+n))).card
    = ((Finset.range a).filter (fun k => a ∣ k*(k+n))).card * ((Finset.range b).filter (fun k => b ∣ k*(k+n))).card
  rw [← Finset.card_product]
  apply Finset.card_bij (fun k _ => (k % a, k % b))
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    have hk' : k < a * b := Finset.mem_range.1 hk1
    have := (hmem k hk').1 hk2
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ ha), ?_⟩,
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hb), ?_⟩⟩
    · rw [sieve_crt_aux, Nat.mod_mod]; exact this.1
    · rw [sieve_crt_aux, Nat.mod_mod]; exact this.2
  · intro k hk l hl h
    have hk' : k < a * b := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
    have hl' : l < a * b := Finset.mem_range.1 (Finset.mem_filter.1 hl).1
    have h1 : k % a = l % a := (Prod.mk.inj h).1
    have h2 : k % b = l % b := (Prod.mk.inj h).2
    have := (Nat.modEq_and_modEq_iff_modEq_mul hab).1 ⟨h1, h2⟩
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hl'] at this
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    obtain ⟨hp1a, hp1b⟩ := Finset.mem_filter.1 hp1
    obtain ⟨hp2a, hp2b⟩ := Finset.mem_filter.1 hp2
    have hp1' : p.1 < a := Finset.mem_range.1 hp1a
    have hp2' : p.2 < b := Finset.mem_range.1 hp2a
    let c := Nat.chineseRemainder hab p.1 p.2
    have hc : c.1 < a * b := Nat.chineseRemainder_lt_mul hab p.1 p.2 ha.ne' hb.ne'
    have hca : c.1 % a = p.1 := by
      have := c.2.1
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hp1']
    have hcb : c.1 % b = p.2 := by
      have := c.2.2
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hp2']
    refine ⟨c.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 hc, (hmem c.1 hc).2 ?_⟩, by rw [hca, hcb]⟩
    rw [hca, hcb]
    exact ⟨hp1b, hp2b⟩
