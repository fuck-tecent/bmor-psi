import Mathlib

namespace Conjectures.Goldbach.PacketWheelSmoothEnvelope_aux

open scoped BigOperators

private lemma mod_eq_le_of_lt {k r : ℕ} (hr : r < 30) (hmod : k % 30 = r) : r ≤ k := by
  by_contra h
  have hk : k < 30 := lt_of_lt_of_le (Nat.lt_of_not_ge h) hr.le
  have hkmod := Nat.mod_eq_of_lt hk
  omega

private lemma fiber_sum_good (n r : ℕ) (hr : r < 30) (hcop : Nat.Coprime r 30)
    (hrn : r ≤ n) (f : ℕ → ℂ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 30 = r),
      if Nat.Coprime k 30 then f k else 0) =
      ∑ j ∈ Finset.range ((n - r) / 30 + 1), f (r + 30 * j) := by
  apply Finset.sum_nbij' (fun k => k / 30) (fun j => r + 30 * j)
  · intro k hk
    have hkrange := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hkmod := (Finset.mem_filter.mp hk).2
    have hkdecomp : r + 30 * (k / 30) = k := by
      rw [← hkmod]
      exact Nat.mod_add_div k 30
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 30)).2
    omega
  · intro j hj
    have hjle : j ≤ (n - r) / 30 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjmul : 30 * j ≤ n - r :=
      by simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 30)).mp hjle
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro k hk
    have hkmod := (Finset.mem_filter.mp hk).2
    rw [← hkmod]
    exact Nat.mod_add_div k 30
  · intro j hj
    rw [Nat.add_mul_div_left r j (by norm_num : 0 < 30),
      Nat.div_eq_of_lt hr, zero_add]
  · intro k hk
    have hkmod := (Finset.mem_filter.mp hk).2
    have hkcop : Nat.Coprime k 30 := by
      apply (ZMod.coprime_mod_iff_coprime k 30).mp
      simpa [hkmod] using hcop
    rw [if_pos hkcop]
    rw [← hkmod]
    exact congrArg f (Nat.mod_add_div k 30).symm

private lemma fiber_sum_bad_coprime (n r : ℕ) (hcop : ¬ Nat.Coprime r 30)
    (f : ℕ → ℂ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 30 = r),
      if Nat.Coprime k 30 then f k else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hkmod := (Finset.mem_filter.mp hk).2
  have hkcop : ¬ Nat.Coprime k 30 := by
    intro h
    apply hcop
    have h' := (ZMod.coprime_mod_iff_coprime k 30).mpr h
    simpa [hkmod] using h'
  rw [if_neg hkcop]

private lemma fiber_sum_bad_large (n r : ℕ) (hr : r < 30) (hrn : ¬ r ≤ n)
    (f : ℕ → ℂ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 30 = r),
      if Nat.Coprime k 30 then f k else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hkrange := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hkmod := (Finset.mem_filter.mp hk).2
  have hkr := mod_eq_le_of_lt hr hkmod
  exfalso
  apply hrn
  omega

lemma wheel_sum (n : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30), f k) =
      ∑ r ∈ (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n),
        ∑ j ∈ Finset.range ((n - r) / 30 + 1), f (r + 30 * j) := by
  classical
  rw [Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.range (n + 1)) (t := Finset.range 30)
    (g := fun k => k % 30)
    (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k (by norm_num)))
    (fun k => if Nat.Coprime k 30 then f k else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  have hr30 := Finset.mem_range.mp hr
  by_cases hgood : Nat.Coprime r 30 ∧ r ≤ n
  · rw [if_pos hgood]
    exact fiber_sum_good n r hr30 hgood.1 hgood.2 f
  · rw [if_neg hgood]
    by_cases hcop : Nat.Coprime r 30
    · exact fiber_sum_bad_large n r hr30 (fun h => hgood ⟨hcop, h⟩) f
    · exact fiber_sum_bad_coprime n r hcop f

lemma norm_geometric_mul_phase_le_two {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    ‖(∑ j ∈ Finset.range m, z ^ j) * (z - 1)‖ ≤ 2 := by
  rw [geom_sum_mul]
  calc
    ‖z ^ m - 1‖ ≤ ‖z ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz]; norm_num

private lemma phase_add (a b : ℝ) :
    Complex.exp (((2 * Real.pi * (a + b) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_nat_mul (x : ℝ) (j : ℕ) :
    Complex.exp (((2 * Real.pi * ((j : ℝ) * x) : ℝ) : ℂ) * Complex.I) =
      (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) ^ j := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma phase_residue (r j : ℕ) (t : ℝ) :
    Complex.exp (((2 * Real.pi * (((r + 30 * j : ℕ) : ℝ) * t) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * ((r : ℝ) * t) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((2 * Real.pi * ((30 : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ^ j := by
  rw [show (((r + 30 * j : ℕ) : ℝ) * t) = (r : ℝ) * t + (j : ℝ) * ((30 : ℝ) * t) by
    push_cast
    ring]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Conjectures.Goldbach.PacketWheelSmoothEnvelope_aux

open Conjectures.Goldbach.PacketWheelSmoothEnvelope_aux

theorem Conjectures.Goldbach.PacketWheelSmoothEnvelope :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let D := fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*‖E (30*t)-1‖^2); ∀ (n : ℕ) (t : ℝ), ‖S n model t‖^2 ≤ 3616*D n t := by
  intro E S model D n t
  classical
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let z := E ((30 : ℝ) * t)
  have hnorm_E : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    exact Complex.norm_exp_ofReal_mul_I _
  have hSform :
      S n model t =
        ((30 / 8 : ℝ) : ℂ) *
          ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
            E ((k : ℝ) * t) := by
    dsimp only [S, model]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with hk <;> norm_num [hk]
  have hglobal : ‖S n model t‖ ≤ (30 / 8 : ℝ) * ((n : ℝ) + 1) := by
    rw [hSform, norm_mul]
    have hsum :
        ‖∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
          E ((k : ℝ) * t)‖ ≤ ((n : ℝ) + 1) := by
      calc
        ‖∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
            E ((k : ℝ) * t)‖
            ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30),
                ‖E ((k : ℝ) * t)‖ := norm_sum_le _ _
        _ = (((Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30)).card : ℝ) := by
            simp [hnorm_E]
        _ ≤ ((n : ℝ) + 1) := by
            have hcard := Finset.card_filter_le (Finset.range (n + 1))
              (fun k => Nat.Coprime k 30)
            have hcard' : ((Finset.range (n + 1)).filter
              (fun k => Nat.Coprime k 30)).card ≤ n + 1 := by
              simpa using hcard
            have hcardreal : (((Finset.range (n + 1)).filter
              (fun k => Nat.Coprime k 30)).card : ℝ) ≤ (n : ℝ) + 1 := by
              exact_mod_cast hcard'
            exact hcardreal
    have hcnorm : ‖((30 / 8 : ℝ) : ℂ)‖ = (30 / 8 : ℝ) := by
      norm_num [Complex.norm_real]
    rw [hcnorm]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hN : 1 ≤ (n : ℝ) + 1 := by
    norm_num
  have hglobal_sq : ‖S n model t‖ ^ 2 ≤ 16 * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [norm_nonneg (S n model t),
      sq_nonneg (‖S n model t‖ - (30 / 8 : ℝ) * ((n : ℝ) + 1))]
  have hresidue : ∀ r j : ℕ,
      E ((((r + 30 * j : ℕ) : ℝ) * t)) =
        E ((r : ℝ) * t) * z ^ j := by
    intro r j
    dsimp only [E, z]
    exact phase_residue r j t
  have hprod :
      S n model t * (z - 1) =
        ((30 / 8 : ℝ) : ℂ) *
          ∑ r ∈ R, E ((r : ℝ) * t) *
            ((∑ j ∈ Finset.range ((n - r) / 30 + 1), z ^ j) * (z - 1)) := by
    rw [hSform]
    have hwheel := wheel_sum n (fun k => E ((k : ℝ) * t))
    rw [hwheel]
    change (((30 / 8 : ℝ) : ℂ) *
      ∑ r ∈ R, ∑ j ∈ Finset.range ((n - r) / 30 + 1),
        E ((((r + 30 * j : ℕ) : ℝ) * t))) * (z - 1) = _
    rw [mul_assoc, Finset.sum_mul]
    apply congrArg (fun x : ℂ => ((30 / 8 : ℝ) : ℂ) * x)
    apply Finset.sum_congr rfl
    intro r _
    simp_rw [hresidue r]
    rw [← Finset.mul_sum]
    ring
  have hznorm : ‖z‖ = 1 := hnorm_E _
  have hterm : ∀ r ∈ R,
      ‖E ((r : ℝ) * t) *
        ((∑ j ∈ Finset.range ((n - r) / 30 + 1), z ^ j) * (z - 1))‖ ≤ 2 := by
    intro r _
    rw [norm_mul, hnorm_E, one_mul]
    exact norm_geometric_mul_phase_le_two hznorm _
  have houter :
      ‖∑ r ∈ R, E ((r : ℝ) * t) *
        ((∑ j ∈ Finset.range ((n - r) / 30 + 1), z ^ j) * (z - 1))‖ ≤
        ∑ _r ∈ R, (2 : ℝ) := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have hcardR : R.card ≤ 8 := by
    have hsub : R ⊆ (Finset.range 30).filter (fun r => Nat.Coprime r 30) := by
      intro r hr
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2.1⟩
    exact (Finset.card_le_card hsub).trans_eq (by decide)
  have hsumtwo : (∑ _r ∈ R, (2 : ℝ)) ≤ 16 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcardreal : (R.card : ℝ) ≤ 8 := by exact_mod_cast hcardR
    nlinarith
  have hproduct_cap : ‖S n model t‖ * ‖z - 1‖ ≤ 60 := by
    have hnormprod : ‖S n model t * (z - 1)‖ ≤ 60 := by
      rw [hprod, norm_mul]
      have hcnorm : ‖((30 / 8 : ℝ) : ℂ)‖ = (30 / 8 : ℝ) := by
        norm_num [Complex.norm_real]
      rw [hcnorm]
      calc
        (30 / 8 : ℝ) * ‖∑ r ∈ R, E ((r : ℝ) * t) *
            ((∑ j ∈ Finset.range ((n - r) / 30 + 1), z ^ j) * (z - 1))‖
            ≤ (30 / 8 : ℝ) * ∑ _r ∈ R, (2 : ℝ) :=
              mul_le_mul_of_nonneg_left houter (by norm_num)
        _ ≤ (30 / 8 : ℝ) * 16 := mul_le_mul_of_nonneg_left hsumtwo (by norm_num)
        _ = 60 := by norm_num
    simpa [norm_mul] using hnormprod
  have hproduct_sq : (‖S n model t‖ * ‖z - 1‖) ^ 2 ≤ 3600 := by
    have hnonneg : 0 ≤ ‖S n model t‖ * ‖z - 1‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmul : 0 ≤ (‖S n model t‖ * ‖z - 1‖) *
        (60 - ‖S n model t‖ * ‖z - 1‖) :=
      mul_nonneg hnonneg (sub_nonneg.mpr hproduct_cap)
    nlinarith
  dsimp only [D]
  change ‖S n model t‖ ^ 2 ≤
    3616 * (((n : ℝ) + 1) ^ 2 /
      (1 + ((n : ℝ) + 1) ^ 2 * ‖E ((30 : ℝ) * t) - 1‖ ^ 2))
  have hden : 0 < 1 + ((n : ℝ) + 1) ^ 2 *
      ‖E ((30 : ℝ) * t) - 1‖ ^ 2 := by positivity
  rw [show 3616 * (((n : ℝ) + 1) ^ 2 /
      (1 + ((n : ℝ) + 1) ^ 2 * ‖E ((30 : ℝ) * t) - 1‖ ^ 2)) =
      (3616 * ((n : ℝ) + 1) ^ 2) /
        (1 + ((n : ℝ) + 1) ^ 2 * ‖E ((30 : ℝ) * t) - 1‖ ^ 2) by ring]
  rw [le_div_iff₀ hden]
  have hscaled :
      ((n : ℝ) + 1) ^ 2 * (‖S n model t‖ * ‖z - 1‖) ^ 2 ≤
        ((n : ℝ) + 1) ^ 2 * 3600 :=
    mul_le_mul_of_nonneg_left hproduct_sq (sq_nonneg _)
  dsimp only [z] at hscaled hproduct_sq
  nlinarith [hglobal_sq, hscaled]
