import Mathlib

namespace PEqualNP.Outside.L_goldbach_ram_local_factor

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    phase ((h : ℝ) * (a : ℝ) / (q : ℝ))

theorem prime_sum (p h : ℕ) (hp : Nat.Prime p) :
    ram p h = if p ∣ h then (p : ℂ) - 1 else -1 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hz : IsPrimitiveRoot z p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have he (a : ℕ) : phase ((h : ℝ) * (a : ℝ) / (p : ℝ)) = (z ^ h) ^ a := by
    unfold phase z
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have filt : (Finset.range p).filter (fun a => Nat.Coprime a p) = (Finset.range p).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨ha, ham⟩
      exact ⟨fun ha0 => (hp.coprime_iff_not_dvd.mp ham.symm) (ha0 ▸ dvd_zero p), ha⟩
    · rintro ⟨han, ha⟩
      exact ⟨ha, (hp.coprime_iff_not_dvd.mpr (fun hd =>
        (not_le_of_gt ha) (Nat.le_of_dvd (Nat.pos_of_ne_zero han) hd))).symm⟩
  unfold ram
  rw [filt]
  simp_rw [he]
  have rem := Finset.sum_erase_add (Finset.range p) (fun a : ℕ => (z ^ h) ^ a)
    (Finset.mem_range.mpr hp.pos)
  rw [pow_zero] at rem
  by_cases hd : p ∣ h
  · rw [ite_eq_left hd]
    rw [(hz.pow_eq_one_iff_dvd h).mpr hd] at rem ⊢
    simp at rem
    simpa using eq_sub_of_add_eq rem
  · rw [ite_eq_right hd]
    rw [(hz.pow_of_coprime h (hp.coprime_iff_not_dvd.mpr hd).symm).geom_sum_eq_zero hp.one_lt] at rem
    exact eq_neg_of_add_eq_zero_left rem

theorem local_factor (p n : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p) :
    ((if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1)^2 : ℝ) : ℂ) =
      1 + ram p n / ((p : ℂ) - 1)^2 := by
  rw [prime_sum p n hp]
  have hne : (p : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show p ≠ 1 by omega)
  by_cases hd : p ∣ n
  · simp only [ite_eq_left hd]
    push_cast
    field_simp
    ring
  · simp only [ite_eq_right hd]
    push_cast
    ring

end PEqualNP.Outside.L_goldbach_ram_local_factor

theorem PEqualNP.Outside.L_goldbach_ram_local_factor : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2; ∀ p n, Nat.Prime p → 2<p → ((fac p n:ℝ):ℂ) = 1 + ram p n/((p:ℂ)-1)^2 := by
  dsimp only
  exact PEqualNP.Outside.L_goldbach_ram_local_factor.local_factor
