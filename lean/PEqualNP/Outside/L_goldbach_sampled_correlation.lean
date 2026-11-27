import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_sampled_correlation :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let c := fun (M j k : ℕ) => E ((j:ℝ)*(k:ℝ)/(M:ℝ)); let F := fun (M : ℕ) (f : ℕ → ℂ) (j : ℕ) => Finset.sum (Finset.range M) (fun k => f k*c M j k); let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); ∀ (n : ℕ) (w : ℕ → ℝ), let M := 2*n+1; let f := fun k : ℕ => if k≤n then (w k:ℂ) else 0; Finset.sum (Finset.range M) (fun j => (F M f j)^2 * star (c M j n)) = (M:ℂ)*(conv w w n:ℂ) := by
  classical
  intro E c F conv n w M f
  let T := range (n + 1)
  let W := fun a : ℕ => (w a : ℂ)
  have hM : M = 2 * n + 1 := rfl
  have : NeZero M := ⟨by omega⟩
  have phase (j k : ℕ) :
      c M j k = ZMod.stdAddChar ((k : ZMod M) * (j : ZMod M)) := by
    rw [← Nat.cast_mul, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
    dsimp [c, E]
    push_cast
    congr 1
    ring
  have conjPhase (x : ZMod M) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    change star (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, Complex.star_def]
  have orthogonal (x : ZMod M) :
      ∑ j ∈ range M, ZMod.stdAddChar (x * (j : ZMod M)) =
        if x = 0 then (M : ℂ) else 0 := by
    have full : ∑ j : ZMod M, ZMod.stdAddChar (x * j) =
        if x = 0 then (M : ℂ) else 0 := by
      split_ifs with hx
      · simp [hx, nsmul_eq_mul, ZMod.card]
      · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M hx)
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ j : ZMod M, ZMod.stdAddChar (x * j) := by
        apply Fintype.sum_equiv (ZMod.finEquiv M).toEquiv
        intro j
        congr 2
        exact Fin.cast_val_eq_self j
      _ = _ := full
  -- The indicator in f truncates both sample indices to T.
  have transform (j : ℕ) : F M f j = ∑ a ∈ T, W a * c M j a := by
    change (∑ a ∈ range M, f a * c M j a) = _
    calc
      _ = ∑ a ∈ T, f a * c M j a := by
        symm
        apply sum_subset
        · apply range_mono
          omega
        · intro a ha hT
          have : ¬ a ≤ n := by simpa [T, Nat.lt_succ_iff] using hT
          simp [f, this]
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        have : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
        simp [f, W, this]
  have kernel (a b : ℕ) (ha : a ∈ T) (hb : b ∈ T) :
      ∑ j ∈ range M, c M j a * c M j b * star (c M j n) =
        if b = n - a then (M : ℂ) else 0 := by
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    change a < n + 1 at ha'
    change b < n + 1 at hb'
    have aliasFree : (a : ZMod M) + b - n = 0 ↔ b = n - a := by
      rw [sub_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt (show a + b < M by omega),
        Nat.mod_eq_of_lt (show n < M by omega)]
      omega
    calc
      _ = ∑ j ∈ range M, ZMod.stdAddChar (((a : ZMod M) + (b : ZMod M) - (n : ZMod M)) * (j : ZMod M)) := by
        apply sum_congr rfl
        intro j _
        rw [phase, phase, phase, conjPhase, ← AddChar.map_add_eq_mul,
          ← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = _ := by simp only [orthogonal, aliasFree]
  -- Expand the square, then sum over frequencies before summing the weights.
  have expand (j : ℕ) :
      (F M f j)^2 * star (c M j n) =
        ∑ a ∈ T, ∑ b ∈ T, (W a * W b) * (c M j a * c M j b * star (c M j n)) := by
    rw [transform, pow_two]
    simp only [sum_mul, mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  calc
    _ = ∑ a ∈ T, ∑ b ∈ T, (W a * W b) *
          (∑ j ∈ range M, c M j a * c M j b * star (c M j n)) := by
      simp_rw [expand]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ a ∈ T, (M : ℂ) * (W a * W (n - a)) := by
      apply sum_congr rfl
      intro a ha
      have hmem : n - a ∈ T := mem_range.mpr (by omega)
      calc
        _ = ∑ b ∈ T, if b = n - a then (W a * W b) * (M : ℂ) else 0 := by
          apply sum_congr rfl
          intro b hb
          rw [kernel a b ha hb]
          split_ifs <;> simp
        _ = _ := by simp [hmem, mul_comm]
    _ = _ := by
      rw [← mul_sum]
      simp [T, W, conv, Complex.ofReal_sum]
