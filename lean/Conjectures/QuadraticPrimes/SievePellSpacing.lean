import Mathlib

theorem Conjectures.QuadraticPrimes.SievePellSpacing :
    ∀ (m a b u v : ℕ), (0 < m) → (0 < a) → (a < b) → (a^2 + 1 = m*u^2) → (b^2 + 1 = m*v^2) → 2*a < b := by
  intro m a b u v hm ha hab hA hB
  have hm1 : 1 ≤ m := by omega
  have hu1 : 1 ≤ u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_le_zero (by omega)
    subst hu0
    simp at hA
  have haz : (0:ℤ) < a := by exact_mod_cast ha
  have habz : (a:ℤ) < b := by exact_mod_cast hab
  have hm1z : (1:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm1
  have hu1z : (1:ℤ) ≤ (u:ℤ) := by exact_mod_cast hu1
  have hAz : (a:ℤ)^2 + 1 = (m:ℤ)*(u:ℤ)^2 := by exact_mod_cast hA
  have hBz : (b:ℤ)^2 + 1 = (m:ℤ)*(v:ℤ)^2 := by exact_mod_cast hB
  have ha0 : (0:ℤ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0:ℤ) ≤ b := Nat.cast_nonneg b
  have hu0 : (0:ℤ) ≤ u := Nat.cast_nonneg u
  have hv0 : (0:ℤ) ≤ v := Nat.cast_nonneg v
  have hm0 : (0:ℤ) ≤ m := Nat.cast_nonneg m
  have hsqvu : (u:ℤ)^2 < (v:ℤ)^2 := by
    have hmv : (0:ℤ) < (m:ℤ)*((v:ℤ)^2 - (u:ℤ)^2) := by
      have hkey : (b:ℤ)^2 - (a:ℤ)^2 = (m:ℤ)*((v:ℤ)^2 - (u:ℤ)^2) := by
        linear_combination hBz - hAz
      have hsqab : (a:ℤ)^2 < (b:ℤ)^2 := (sq_lt_sq₀ ha0 hb0).mpr habz
      rw [← hkey]
      exact sub_pos.mpr hsqab
    have hpos : (0:ℤ) < (v:ℤ)^2 - (u:ℤ)^2 := by
      by_contra hcon
      have hle : (v:ℤ)^2 - (u:ℤ)^2 ≤ 0 := not_lt.mp hcon
      exact absurd hmv (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hm0 hle))
    exact sub_pos.mp hpos
  have hkeyB : ((b:ℤ)*(u:ℤ))^2 = ((a:ℤ)*(v:ℤ))^2 + ((v:ℤ)^2 - (u:ℤ)^2) := by
    linear_combination ((u:ℤ)^2) * hBz - ((v:ℤ)^2) * hAz
  have hBpos : (0:ℤ) < (b:ℤ)*(u:ℤ) - (a:ℤ)*(v:ℤ) := by
    have hsq : ((a:ℤ)*(v:ℤ))^2 < ((b:ℤ)*(u:ℤ))^2 := by
      rw [hkeyB]
      exact lt_add_of_pos_right _ (sub_pos.mpr hsqvu)
    exact sub_pos.mpr ((sq_lt_sq₀ (mul_nonneg ha0 hv0) (mul_nonneg hb0 hu0)).mp hsq)
  have hkeyA : ((m:ℤ)*(u:ℤ)*(v:ℤ))^2 = ((a:ℤ)*(b:ℤ))^2 + ((a:ℤ)^2 + (b:ℤ)^2 + 1) := by
    linear_combination (-((b:ℤ)^2 + 1)) * hAz + (-((m:ℤ)*(u:ℤ)^2)) * hBz
  have hApos : (0:ℤ) < (m:ℤ)*(u:ℤ)*(v:ℤ) - (a:ℤ)*(b:ℤ) := by
    have hpos : (0:ℤ) < (a:ℤ)^2 + (b:ℤ)^2 + 1 := by positivity
    have hsq : ((a:ℤ)*(b:ℤ))^2 < ((m:ℤ)*(u:ℤ)*(v:ℤ))^2 := by
      rw [hkeyA]
      exact lt_add_of_pos_right _ hpos
    exact sub_pos.mpr ((sq_lt_sq₀ (mul_nonneg ha0 hb0)
      (mul_nonneg (mul_nonneg hm0 hu0) hv0)).mp hsq)
  obtain ⟨A, hAdef⟩ : ∃ A : ℤ, A = (m:ℤ)*(u:ℤ)*(v:ℤ) - (a:ℤ)*(b:ℤ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℤ, B = (b:ℤ)*(u:ℤ) - (a:ℤ)*(v:ℤ) := ⟨_, rfl⟩
  have hA1 : (1:ℤ) ≤ A := by rw [hAdef]; omega
  have hB1 : (1:ℤ) ≤ B := by rw [hBdef]; omega
  have hnorm : A^2 = (m:ℤ)*B^2 + 1 := by
    rw [hAdef, hBdef]
    linear_combination ((a:ℤ)^2 - (m:ℤ)*(u:ℤ)^2) * hBz - hAz
  have hB2 : (1:ℤ) ≤ B^2 := by nlinarith only [hB1]
  have hmB : (1:ℤ) ≤ (m:ℤ)*B^2 := by nlinarith only [hm1z, hB2]
  have hAsq : (2:ℤ) ≤ A^2 := by linarith only [hnorm, hmB]
  have hA2 : (2:ℤ) ≤ A := by
    by_contra h
    have hlt : A < 2 := not_le.mp h
    have heq : A = 1 := by omega
    rw [heq] at hAsq
    norm_num at hAsq
  have hrec : (b:ℤ) = (a:ℤ)*A + (m:ℤ)*(u:ℤ)*B := by
    rw [hAdef, hBdef]
    linear_combination (b:ℤ) * hAz
  have hlo : (2:ℤ)*(a:ℤ) ≤ (a:ℤ)*A := by nlinarith only [hA2, ha0]
  have hmu : (1:ℤ) ≤ (m:ℤ)*(u:ℤ) := by nlinarith only [hm1z, hu1z]
  have hmuB : (1:ℤ) ≤ (m:ℤ)*(u:ℤ)*B := by nlinarith only [hmu, hB1]
  have hfinal : (2:ℤ)*(a:ℤ) < (b:ℤ) := by linarith only [hrec, hlo, hmuB]
  exact_mod_cast hfinal
