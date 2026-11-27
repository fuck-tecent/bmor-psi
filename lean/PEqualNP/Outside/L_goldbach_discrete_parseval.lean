import Mathlib

theorem PEqualNP.Outside.L_goldbach_discrete_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let c := fun (M j k : ℕ) => E ((j:ℝ)*(k:ℝ)/(M:ℝ)); let F := fun (M : ℕ) (f : ℕ → ℂ) (j : ℕ) => Finset.sum (Finset.range M) (fun k => f k*c M j k); ∀ M f, Finset.sum (Finset.range M) (fun j => ‖F M f j‖^2) = (M:ℝ)*Finset.sum (Finset.range M) (fun k => ‖f k‖^2) := by
  intro E c F M f
  by_cases hM : M = 0
  · subst M
    simp [F]
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (j k : ℕ) : c M j k = (ζ ^ k) ^ j := by
    dsimp [c, E, ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have unit (j k : ℕ) : ‖c M j k‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have orth (k l : ℕ) (hk : k < M) (hl : l < M) :
      ∑ j ∈ Finset.range M, c M j k * (starRingEnd ℂ) (c M j l) =
        if k = l then (M : ℂ) else 0 := by
    have term (j : ℕ) : c M j k * (starRingEnd ℂ) (c M j l) = (ζ^k / ζ^l)^j := by
      rw [← Complex.inv_eq_conj (unit j l), phase, phase, div_pow, div_eq_mul_inv]
    simp_rw [term]
    by_cases hkl : k = l
    · subst l
      simp [div_self (pow_ne_zero k hζ0)]
    · rw [ite_eq_right hkl, geom_sum_eq]
      · have hpow (i : ℕ) : (ζ^i)^M = 1 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        simp [div_pow, hpow]
      · exact fun h => hkl (hζ.pow_inj hk hl ((div_eq_one_iff_eq (pow_ne_zero _ hζ0)).mp h))
  let T := Finset.range M
  have expand (j : ℕ) :
      F M f j * (starRingEnd ℂ) (F M f j) =
        ∑ k ∈ T, ∑ l ∈ T, f k * (starRingEnd ℂ) (f l) *
          (c M j k * (starRingEnd ℂ) (c M j l)) := by
    dsimp only [F, T]
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    ring
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  change (∑ j ∈ T, ∑ k ∈ T, ∑ l ∈ T, _) = _
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  have inner (l : ℕ) (hl : l ∈ T) :
      ∑ j ∈ T, f k * (starRingEnd ℂ) (f l) * (c M j k * (starRingEnd ℂ) (c M j l)) =
        if k = l then (M : ℂ) * (f k * (starRingEnd ℂ) (f k)) else 0 := by
    rw [← Finset.mul_sum, orth k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)]
    split_ifs with h
    · rw [h, mul_comm]
    · exact mul_zero _
  rw [Finset.sum_congr rfl inner]
  simp [hk]
