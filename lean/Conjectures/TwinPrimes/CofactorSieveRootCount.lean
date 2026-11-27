import Mathlib

theorem Conjectures.TwinPrimes.CofactorSieveRootCount :
    ∀ (r ℓ : ℕ), r.Prime → 2 < r → ℓ.Prime →
      ((Finset.range ℓ).filter (fun a => a % ℓ = 0 ∨ (r*a) % ℓ = 2 % ℓ)).card =
        if ℓ = 2 ∨ ℓ = r then 1 else 2 := by
  intro r ℓ hr hr2 hℓ
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  by_cases h2 : ℓ = 2
  · subst h2
    rw [if_pos (Or.inl rfl)]
    have hodd : r % 2 = 1 := by
      have ho := hr.odd_of_ne_two (by omega : r ≠ 2)
      exact Nat.odd_iff.mp ho
    have hT : ((Finset.range 2).filter (fun a => a % 2 = 0 ∨ (r*a) % 2 = 2 % 2)) = ({0} : Finset ℕ) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, h0 | h1⟩
        · interval_cases a <;> simp_all
        · interval_cases a
          · rfl
          · rw [mul_one] at h1
            omega
      · rintro rfl
        exact ⟨by norm_num, Or.inl (by norm_num)⟩
    rw [hT]
    simp
  · by_cases hlr : ℓ = r
    · rw [hlr]
      rw [if_pos (Or.inr rfl)]
      have hT : ((Finset.range r).filter (fun a => a % r = 0 ∨ (r*a) % r = 2 % r)) = ({0} : Finset ℕ) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, h0 | h1⟩
          · rw [Nat.mod_eq_of_lt ha] at h0
            exact h0
          · rw [Nat.mod_eq_zero_of_dvd (⟨a, rfl⟩ : r ∣ r * a), Nat.mod_eq_of_lt hr2] at h1
            omega
        · rintro rfl
          exact ⟨hr.pos, Or.inl (Nat.zero_mod r)⟩
      rw [hT]
      simp
    · rw [if_neg (by tauto)]
      have hrne : (r : ZMod ℓ) ≠ 0 := by
        intro h0
        have hd : ℓ ∣ r := (ZMod.natCast_eq_zero_iff r ℓ).mp h0
        rcases hr.eq_one_or_self_of_dvd ℓ hd with h | h
        · rw [h] at hℓ
          exact absurd hℓ (by norm_num)
        · exact hlr h
      have h2ne : (2 : ZMod ℓ) ≠ 0 := by
        intro h0
        have hd : ℓ ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).mp h0
        have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hd
        have hge : 2 ≤ ℓ := hℓ.two_le
        omega
      set y : ZMod ℓ := 2 * (r : ZMod ℓ)⁻¹ with hy
      have hry : (r : ZMod ℓ) * y = 2 := by
        rw [hy]
        calc (r : ZMod ℓ) * (2 * (r : ZMod ℓ)⁻¹) = 2 * ((r : ZMod ℓ) * (r : ZMod ℓ)⁻¹) := by ring
          _ = 2 * 1 := by rw [mul_inv_cancel₀ hrne]
          _ = 2 := by ring
      have hcval : ((y.val : ℕ) : ZMod ℓ) = y := ZMod.natCast_zmod_val y
      have hclt : y.val < ℓ := ZMod.val_lt y
      have hcsol : (r * y.val) % ℓ = 2 % ℓ := by
        have hz : ((r * y.val : ℕ) : ZMod ℓ) = ((2 : ℕ) : ZMod ℓ) := by
          push_cast
          rw [hcval]
          exact hry
        exact (ZMod.natCast_eq_natCast_iff' (r * y.val) 2 ℓ).mp hz
      have hcne : y.val ≠ 0 := by
        intro h
        have hy0 : y = 0 := by
          rw [← hcval, h]
          simp
        rw [hy0, mul_zero] at hry
        exact h2ne hry.symm
      have huniq : ∀ a : ℕ, a < ℓ → (r * a) % ℓ = 2 % ℓ → a = y.val := by
        intro a ha hmod
        have hza : ((r * a : ℕ) : ZMod ℓ) = ((2 : ℕ) : ZMod ℓ) :=
          (ZMod.natCast_eq_natCast_iff' (r * a) 2 ℓ).mpr hmod
        have hza' : (r : ZMod ℓ) * (a : ZMod ℓ) = 2 := by
          push_cast at hza ⊢
          exact hza
        have key : (r : ZMod ℓ) * ((a : ZMod ℓ) - (y.val : ZMod ℓ)) = 0 := by
          rw [mul_sub, hza', hcval, hry, sub_self]
        have hz' : (a : ZMod ℓ) - (y.val : ZMod ℓ) = 0 := by
          rcases mul_eq_zero.mp key with h | h
          · exact absurd h hrne
          · exact h
        have heq : ((a : ℕ) : ZMod ℓ) = ((y.val : ℕ) : ZMod ℓ) := by
          rwa [sub_eq_zero] at hz'
        have hmod2 := (ZMod.natCast_eq_natCast_iff' a y.val ℓ).mp heq
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hclt] at hmod2
        exact hmod2
      have hT : ((Finset.range ℓ).filter (fun a => a % ℓ = 0 ∨ (r*a) % ℓ = 2 % ℓ)) = insert 0 {y.val} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, h0 | h1⟩
          · left
            rw [Nat.mod_eq_of_lt ha] at h0
            exact h0
          · right
            exact huniq a ha h1
        · rintro (rfl | h)
          · exact ⟨hℓ.pos, Or.inl (Nat.zero_mod ℓ)⟩
          · rw [h]
            exact ⟨hclt, Or.inr hcsol⟩
      rw [hT]
      have h0ne : (0 : ℕ) ≠ y.val := by omega
      simp [h0ne]
