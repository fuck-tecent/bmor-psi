import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

/-- The sum of all roots is the divisor sum of the sums of primitive roots.
Dirichlet convolution with the Möbius function inverts that divisor sum. -/
private theorem sum_primitiveRoots_eq_moebius (q : ℕ) :
    (∑ z ∈ primitiveRoots q ℂ, z) = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  let f : ArithmeticFunction ℂ :=
    ⟨fun n => ∑ z ∈ primitiveRoots n ℂ, z, by simp [primitiveRoots_zero]⟩
  have hf : f * (ArithmeticFunction.zeta : ArithmeticFunction ℂ) = 1 := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ n.divisors, ∑ z ∈ primitiveRoots d ℂ, z) = _
    rw [← Finset.sum_biUnion (fun _ _ _ _ h => IsPrimitiveRoot.disjoint h),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    by_cases hn : n = 0
    · simp [hn]
    let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
    have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
    have hsum : (∑ z ∈ Polynomial.nthRootsFinset n (1 : ℂ), z) =
        ∑ k ∈ Finset.range n, ζ ^ k := by
      rw [Polynomial.nthRootsFinset_def, ← Multiset.toFinset_eq hζ.nthRoots_one_nodup,
        Finset.sum_mk, show (fun z : ℂ => z) = id from rfl, Multiset.map_id,
        hζ.nthRoots_eq (one_pow n : (1 : ℂ) ^ n = 1)]
      simp only [mul_one, Finset.sum, Finset.range_val]
    rw [hsum]
    by_cases hn₁ : n = 1
    · subst n
      simp
    · simpa [ArithmeticFunction.one_apply_ne hn₁] using hζ.geom_sum_eq_zero (by omega)
  have h : f = (ArithmeticFunction.moebius : ArithmeticFunction ℂ) := calc
    f = f * ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) := by simp
    _ = _ := by rw [← mul_assoc, hf, one_mul]
  exact congrArg (fun g : ArithmeticFunction ℂ => g q) h

/-- For a frequency coprime to the modulus, the Ramanujan sum equals the Möbius function. -/
private theorem ramanujan_sum_of_coprime (q : ℕ) (hq : 0 < q) (a : ℕ)
    (ha : Nat.Coprime a q) :
    (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / q : ℝ) : ℂ) * Complex.I)) =
      (ArithmeticFunction.moebius q : ℂ) := by
  let : NeZero q := ⟨hq.ne'⟩
  let t : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / q)
  have ht : IsPrimitiveRoot (Complex.exp t) q :=
    Complex.isPrimitiveRoot_exp_of_coprime a q hq.ne' ha
  rw [← sum_primitiveRoots_eq_moebius q]
  refine Finset.sum_bij (fun b _ => Complex.exp t ^ b) ?_ ?_ ?_ ?_
  · intro b hb
    exact (mem_primitiveRoots hq).2 (ht.pow_of_coprime b (Finset.mem_filter.1 hb).2)
  · intro b hb c hc hbc
    exact ht.pow_inj (Finset.mem_range.1 (Finset.mem_filter.1 hb).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hc).1) hbc
  · intro z hz
    obtain ⟨b, hb, hcop, heq⟩ := ht.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).1 hz)
    exact ⟨b, Finset.mem_filter.2 ⟨Finset.mem_range.2 hb, hcop⟩, heq⟩
  · intro b _
    have harg : (((2 * Real.pi * (a : ℝ) * b / q : ℝ) : ℂ) * Complex.I) = (b : ℂ) * t := by
      dsimp only [t]
      push_cast
      ring
    exact (congrArg Complex.exp harg).trans (Complex.exp_nat_mul t b)

theorem L_goldbach_cert_30 :
    ∀ a:ℕ, Nat.Coprime a 30 → (∑ b ∈ (Finset.range 30).filter (fun b => Nat.Coprime b 30), Complex.exp (((2*Real.pi*(a:ℝ)*b/30:ℝ):ℂ)*Complex.I))/(8:ℂ)=(-1:ℂ)/8 := by
  intro a ha
  have hμ : ArithmeticFunction.moebius 30 = -1 := by
    have hm := ArithmeticFunction.isMultiplicative_moebius
    change ArithmeticFunction.moebius (2 * 3 * 5) = -1
    rw [hm.map_mul_of_coprime (by decide : Nat.Coprime (2 * 3) 5),
      hm.map_mul_of_coprime (by decide : Nat.Coprime 2 3)]
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three,
      ArithmeticFunction.moebius_apply_prime Nat.prime_five]
  have hsum := ramanujan_sum_of_coprime 30 (by decide) a ha
  simp only [Nat.cast_ofNat, hμ, Int.cast_neg, Int.cast_one] at hsum
  rw [hsum]

end PEqualNP.Outside
