import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach.PacketWheelGeometric_aux

private def residues (n : ℕ) : Finset ℕ :=
  (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)

private def fibers (n r : ℕ) : Finset ℕ :=
  Finset.range ((n - r) / 30 + 1)

private theorem sum_residues (n : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30), f k) =
      ∑ r ∈ residues n, ∑ j ∈ fibers n r, f (r + 30 * j) := by
  classical
  let forward : ℕ → Σ _ : ℕ, ℕ := fun k => ⟨k % 30, k / 30⟩
  let backward : (Σ _ : ℕ, ℕ) → ℕ := fun p => p.1 + 30 * p.2
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' forward backward ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hk_range, hk_coprime⟩
    have hk_le : k ≤ n := by simpa using Finset.mem_range.mp hk_range
    have hmod_lt : k % 30 < 30 := Nat.mod_lt _ (by omega)
    have hmod_coprime : Nat.Coprime (k % 30) 30 := by
      rw [← Nat.mod_add_div k 30] at hk_coprime
      exact (Nat.coprime_add_mul_left_left _ _ _).mp hk_coprime
    have hmod_le : k % 30 ≤ n := (Nat.mod_le _ _).trans hk_le
    have hquot_le : k / 30 ≤ (n - k % 30) / 30 := by
      apply (Nat.le_div_iff_mul_le (by omega)).2
      omega
    simp only [forward, Finset.mem_sigma, residues, fibers, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨⟨hmod_lt, hmod_coprime, hmod_le⟩, Nat.lt_succ_iff.mpr hquot_le⟩
  · rintro ⟨r, j⟩ hp
    have hp' : r ∈ residues n ∧ j ∈ fibers n r := Finset.mem_sigma.mp hp
    have hr_lt : r < 30 := by
      simpa [residues] using (Finset.mem_filter.mp hp'.1).1
    have hr_coprime : Nat.Coprime r 30 := by
      simpa [residues] using (Finset.mem_filter.mp hp'.1).2.1
    have hr_le : r ≤ n := by
      simpa [residues] using (Finset.mem_filter.mp hp'.1).2.2
    have hj_le : j ≤ (n - r) / 30 := by
      simpa [fibers] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hp'.2)
    have hj_mul_le : j * 30 ≤ n - r :=
      (Nat.le_div_iff_mul_le (by omega)).mp hj_le
    have hsum_le : r + 30 * j ≤ n := by omega
    have hsum_coprime : Nat.Coprime (r + 30 * j) 30 :=
      (Nat.coprime_add_mul_left_left _ _ _).mpr hr_coprime
    change r + 30 * j ∈ (Finset.range (n + 1)).filter
      (fun k => Nat.Coprime k 30)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hsum_coprime⟩
  · intro k _
    exact Nat.mod_add_div k 30
  · rintro ⟨r, j⟩ hp
    have hp' : r ∈ residues n ∧ j ∈ fibers n r := Finset.mem_sigma.mp hp
    have hr_lt : r < 30 := by
      simpa [residues] using (Finset.mem_filter.mp hp'.1).1
    apply Sigma.ext
    · change (r + 30 * j) % 30 = r
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_lt]
    · apply heq_of_eq
      change (r + 30 * j) / 30 = j
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr_lt, zero_add]
  · intro k _
    change f k = f (k % 30 + 30 * (k / 30))
    rw [Nat.mod_add_div]

end Conjectures.Goldbach.PacketWheelGeometric_aux

theorem Conjectures.Goldbach.PacketWheelGeometric :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n : ℕ) (t : ℝ), S n model t = ((30:ℝ)/8:ℂ)*(∑ r ∈ (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n), E ((r:ℝ)*t)*(∑ j ∈ Finset.range ((n-r)/30+1), E ((30:ℝ)*(j:ℝ)*t))) := by
  dsimp only
  intro n t
  classical
  let E : ℝ → ℂ := fun x : ℝ =>
    Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  change
    (∑ k ∈ Finset.range (n + 1),
      ((if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0 : ℝ) : ℂ) *
        E ((k : ℝ) * t)) =
      ((30 : ℝ) / 8 : ℂ) *
        ∑ r ∈ Conjectures.Goldbach.PacketWheelGeometric_aux.residues n,
          E ((r : ℝ) * t) *
            ∑ j ∈ Conjectures.Goldbach.PacketWheelGeometric_aux.fibers n r,
              E ((30 : ℝ) * (j : ℝ) * t)
  have hE (r j : ℕ) :
      E ((r : ℝ) * t) * E ((30 : ℝ) * (j : ℝ) * t) =
        E (((r + 30 * j : ℕ) : ℝ) * t) := by
    dsimp [E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hleft :
      (∑ k ∈ Finset.range (n + 1),
        ((if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0 : ℝ) : ℂ) *
          E ((k : ℝ) * t)) =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
          ((30 : ℝ) / 8 : ℂ) * E ((k : ℝ) * t) := by
    calc
      (∑ k ∈ Finset.range (n + 1),
        ((if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0 : ℝ) : ℂ) *
          E ((k : ℝ) * t)) =
          ∑ k ∈ Finset.range (n + 1),
            if Nat.Coprime k 30 then ((30 : ℝ) / 8 : ℂ) * E ((k : ℝ) * t)
            else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        split <;> simp_all
      _ = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
          ((30 : ℝ) / 8 : ℂ) * E ((k : ℝ) * t) := by
        rw [Finset.sum_filter]
  calc
    (∑ k ∈ Finset.range (n + 1),
      ((if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0 : ℝ) : ℂ) *
        E ((k : ℝ) * t)) =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
          ((30 : ℝ) / 8 : ℂ) * E ((k : ℝ) * t) := hleft
    _ = ((30 : ℝ) / 8 : ℂ) *
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
          E ((k : ℝ) * t) := by
      rw [Finset.mul_sum]
    _ = ((30 : ℝ) / 8 : ℂ) *
        ∑ r ∈ Conjectures.Goldbach.PacketWheelGeometric_aux.residues n,
          ∑ j ∈ Conjectures.Goldbach.PacketWheelGeometric_aux.fibers n r,
            E (((r + 30 * j : ℕ) : ℝ) * t) := by
      rw [Conjectures.Goldbach.PacketWheelGeometric_aux.sum_residues]
    _ = ((30 : ℝ) / 8 : ℂ) *
        ∑ r ∈ Conjectures.Goldbach.PacketWheelGeometric_aux.residues n,
          E ((r : ℝ) * t) *
            ∑ j ∈ Conjectures.Goldbach.PacketWheelGeometric_aux.fibers n r,
              E ((30 : ℝ) * (j : ℝ) * t) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (hE r j).symm
