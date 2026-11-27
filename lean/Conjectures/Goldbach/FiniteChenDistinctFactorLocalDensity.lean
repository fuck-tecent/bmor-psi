import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

theorem Conjectures.Goldbach.FiniteChenDistinctFactorLocalDensity :
    ∀ (ℓ r n : ℕ), ℓ.Prime → let B := (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v) % ℓ = n % ℓ); B.card = (if ℓ∣r then (if ℓ∣n then ℓ else 1) else (if ℓ∣n then 1 else 2)) := by
  intro ℓ r n hℓ
  dsimp only
  by_cases hr : ℓ ∣ r
  · have hz (v : ℕ) : (r * v) % ℓ = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hr v)
    by_cases hn : ℓ ∣ n
    · simp [hr, hn, hz, Nat.mod_eq_zero_of_dvd hn]
    · have hn0 : n % ℓ ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
      have hB : (Finset.range ℓ).filter
          (fun v => v = 0 ∨ (r * v) % ℓ = n % ℓ) = {0} := by
        apply Finset.ext
        intro v
        simp only [Finset.mem_filter, Finset.mem_range, hz,
          Ne.symm hn0, or_false, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨hℓ.pos, rfl⟩
      rw [hB]
      simp [hr, hn]
  · have hco : Nat.Coprime r ℓ := (hℓ.coprime_iff_not_dvd.mpr hr).symm
    obtain ⟨s, _, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco hℓ.one_lt
    have hcancel (x : ℕ) : (s * ((r * x) % ℓ)) % ℓ = x % ℓ := by
      calc
        (s * ((r * x) % ℓ)) % ℓ = (s * (r * x)) % ℓ := by
          simp [Nat.mul_mod]
        _ = ((r * s) * x) % ℓ := by
          rw [← Nat.mul_assoc, Nat.mul_comm s r]
        _ = x % ℓ := by
          rw [Nat.mul_mod, hs, one_mul, Nat.mod_mod]
    have hinj (x : ℕ) (hx : x < ℓ) (y : ℕ) (hy : y < ℓ)
        (he : (r * x) % ℓ = (r * y) % ℓ) : x = y := by
      have h := congrArg (fun t : ℕ => (s * t) % ℓ) he
      rw [hcancel, hcancel, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
      exact h
    obtain ⟨u, hu, hroot⟩ := Nat.exists_mul_mod_eq_of_coprime n hco hℓ.ne_zero
    have hB : (Finset.range ℓ).filter
        (fun v => v = 0 ∨ (r * v) % ℓ = n % ℓ) = {0, u} := by
      apply Finset.ext
      intro v
      simp only [Finset.mem_filter, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, hv0 | hvroot⟩
        · exact Or.inl hv0
        · exact Or.inr (hinj v hv u hu (hvroot.trans hroot.symm))
      · rintro (rfl | rfl)
        · exact ⟨hℓ.pos, Or.inl rfl⟩
        · exact ⟨hu, Or.inr hroot⟩
    by_cases hn : ℓ ∣ n
    · have hu0 : u = 0 := hinj u hu 0 hℓ.pos (by
        simpa [Nat.mod_eq_zero_of_dvd hn] using hroot)
      rw [hB]
      simp [hr, hn, hu0]
    · have hu0 : u ≠ 0 := by
        intro heq
        apply hn
        apply Nat.dvd_of_mod_eq_zero
        have h : 0 = n % ℓ := by simpa [heq] using hroot
        exact h.symm
      rw [hB]
      simp [hr, hn, hu0, Ne.symm hu0]
