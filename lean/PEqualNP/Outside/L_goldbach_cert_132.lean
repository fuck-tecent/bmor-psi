import Mathlib

open Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Summing primitive roots over the divisors recovers all roots. Möbius inversion
then gives the sum at each exact order. -/
private theorem sumPrimitive (n : ℕ) :
    (∑ z ∈ primitiveRoots n ℂ, z) = (μ n : ℂ) := by
  classical
  let F : ArithmeticFunction ℂ := ⟨fun k => ∑ z ∈ primitiveRoots k ℂ, z, by simp⟩
  have hF : F * (ζ : ArithmeticFunction ℂ) = 1 := by
    ext k
    by_cases hk : k = 0
    · subst k; simp
    let : NeZero k := ⟨hk⟩
    have hk' := Nat.pos_of_ne_zero hk
    let z := Complex.exp (2 * Real.pi * Complex.I / k)
    have hz : IsPrimitiveRoot z k := Complex.isPrimitiveRoot_exp k hk
    rw [coe_mul_zeta_apply]
    change (∑ i ∈ k.divisors, ∑ t ∈ primitiveRoots i ℂ, t) = _
    rw [← Finset.sum_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    have hall : (∑ j ∈ Finset.range k, z ^ j) = ∑ t ∈ nthRootsFinset k (1 : ℂ), t := by
      apply Finset.sum_bij (fun j _ => z ^ j)
      · intro j _; apply (mem_nthRootsFinset hk' _).mpr
        rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
      · intro i hi j hj eq; exact hz.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) eq
      · intro x hx
        obtain ⟨j,hj,he⟩ := hz.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hk' _).mp hx)
        exact ⟨j,Finset.mem_range.mpr hj,he⟩
      · intros; rfl
    rw [← hall]
    by_cases h : k = 1
    · subst k; simp
    · rw [hz.geom_sum_eq_zero (by omega)]; simp [h]
  have hμ : F = (μ : ArithmeticFunction ℂ) := by
    calc F = (F * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) := by
            rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
         _ = _ := by rw [hF, one_mul]
  exact congrArg (fun f : ArithmeticFunction ℂ => f n) hμ

/-- A coprime frequency permutes the primitive roots of the given order. -/
private theorem ramanujan (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / q : ℝ) : ℂ) * Complex.I)) = (μ q : ℂ) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / q)
  have hz : IsPrimitiveRoot (Complex.exp θ) q := Complex.isPrimitiveRoot_exp_of_coprime a q hq.ne' ha
  rw [← sumPrimitive q]
  apply Finset.sum_bij (fun i _ => Complex.exp θ ^ i)
  · intro i hi; exact (mem_primitiveRoots hq).mpr (hz.pow_of_coprime i (Finset.mem_filter.mp hi).2)
  · intro i hi j hj; exact hz.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  · intro x hx
    obtain ⟨i,hi,hc,he⟩ := hz.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hx)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hc⟩,he⟩
  · intro i _; rw [← Complex.exp_nat_mul]; congr 1; dsimp [θ]; push_cast; ring

theorem PEqualNP.Outside.L_goldbach_cert_132 :
    ∀ a:ℕ, Nat.Coprime a 132 → (∑ b ∈ (Finset.range 132).filter (fun b => Nat.Coprime b 132), Complex.exp (((2*Real.pi*(a:ℝ)*b/132:ℝ):ℂ)*Complex.I))/(40:ℂ)=(0:ℂ)/40 := by
  intro a ha
  apply congrArg (fun z : ℂ => z / 40)
  have h := ramanujan 132 a (by decide) ha
  have hμ : μ 132 = 0 := by
    norm_num only [show 132 = 4 * 33 by decide,
      isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 4 33),
      show μ 4 = 0 by rw [show 4 = 2 ^ 2 by decide, moebius_apply_prime_pow (by norm_num : Nat.Prime 2) (by decide : 2 ≠ 0)]; decide,
      show 33 = 3 * 11 by decide,
      isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 3 11),
      moebius_apply_prime (by norm_num : Nat.Prime 3),
      moebius_apply_prime (by norm_num : Nat.Prime 11)]
  rw [hμ] at h
  exact_mod_cast h
