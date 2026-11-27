import Mathlib

namespace GoldbachCert_27

open Finset Polynomial ArithmeticFunction

private theorem sumByOrder (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, ∑ z ∈ primitiveRoots d ℂ, z) = (1 : ArithmeticFunction ℂ) n := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  have hz := Complex.isPrimitiveRoot_exp n hn.ne'
  have hd : Set.PairwiseDisjoint (n.divisors : Set ℕ) (fun d => primitiveRoots d ℂ) :=
    fun _ _ _ _ h => IsPrimitiveRoot.disjoint h
  rw [← sum_biUnion hd, ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  trans ∑ i ∈ range n, Complex.exp (2 * Real.pi * Complex.I / n) ^ i
  · symm
    refine sum_nbij _ (fun i _ => (mem_nthRootsFinset hn _).2 ?_)
      hz.injOn_pow ?_ (fun _ _ => rfl)
    · rw [← pow_mul, Nat.mul_comm i n, pow_mul, hz.pow_eq_one, one_pow]
    · intro z hz'
      obtain ⟨i, hi, hi'⟩ := hz.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hn _).1 hz')
      exact ⟨i, mem_range.mpr hi, hi'⟩
  · by_cases h : n = 1
    · subst n
      simp
    · exact (hz.geom_sum_eq_zero (by omega)).trans (one_apply_ne h).symm

private theorem sumPrimitive (q : ℕ) (hq : 0 < q) :
    (∑ z ∈ primitiveRoots q ℂ, z) = (moebius q : ℂ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq.mp sumByOrder q hq).symm
  exact h.trans (congrArg (fun f : ArithmeticFunction ℂ => f q)
    (mul_one (moebius : ArithmeticFunction ℂ)))

theorem kluyver (q a : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) :
    (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / q : ℝ) : ℂ) * Complex.I)) =
      (moebius q : ℂ) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hz := Complex.isPrimitiveRoot_exp_of_coprime a q hq.ne' ha
  refine Eq.trans ?_ (sumPrimitive q hq)
  refine sum_nbij _ (fun b hb => (mem_primitiveRoots hq).2
    (hz.pow_of_coprime b (mem_filter.mp hb).2))
    (hz.injOn_pow.mono (filter_subset _ _)) ?_ ?_
  · intro z hz'
    obtain ⟨b, hb, hc, rfl⟩ := hz.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).1 hz')
    exact ⟨b, mem_filter.mpr ⟨mem_range.mpr hb, hc⟩, rfl⟩
  · intro b _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

end GoldbachCert_27

open ArithmeticFunction in
theorem PEqualNP.Outside.L_goldbach_cert_27 :
    ∀ a:ℕ, Nat.Coprime a 27 → (∑ b ∈ (Finset.range 27).filter (fun b => Nat.Coprime b 27), Complex.exp (((2*Real.pi*(a:ℝ)*b/27:ℝ):ℂ)*Complex.I))/(18:ℂ)=(0:ℂ)/18 := by
  intro a ha
  have hm : moebius 27 = (0 : ℤ) := by
    simp only [moebius, coe_mk, cardFactors_apply,
      Nat.squarefree_iff_nodup_primeFactorsList (by decide : 27 ≠ 0), Nat.primeFactorsList_ofNat]
    decide
  refine congrArg (fun z : ℂ => z / 18) ((GoldbachCert_27.kluyver 27 a (by decide) ha).trans ?_)
  exact_mod_cast hm
