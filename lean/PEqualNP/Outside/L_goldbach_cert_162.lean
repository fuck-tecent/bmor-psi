import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FieldSimp

private theorem gb_sum_roots (n : ℕ) (hn : 0 < n) :
    ∑ η ∈ Polynomial.nthRootsFinset n (1:ℂ), η = if n = 1 then 1 else 0 := by
  by_cases h1 : n = 1
  · subst h1
    have : Polynomial.nthRootsFinset 1 (1:ℂ) = {1} := by
      ext x
      simp [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 1)]
    simp [this]
  · have hn0 : n ≠ 0 := hn.ne'
    have hζ := Complex.isPrimitiveRoot_exp n hn0
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hgt : 1 < n := by omega
    have : ∑ η ∈ Polynomial.nthRootsFinset n (1:ℂ), η = ∑ i ∈ Finset.range n, ζ ^ i := by
      symm
      refine Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro i _
        rw [Polynomial.mem_nthRootsFinset hn]
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      · intro i hi j hj h
        exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
      · intro x hx
        rw [Polynomial.mem_nthRootsFinset hn] at hx
        haveI : NeZero n := ⟨hn0⟩
        obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hx
        exact ⟨i, Finset.mem_range.mpr hi, e⟩
    rw [this, if_neg h1]
    exact hζ.geom_sum_eq_zero hgt

private theorem gb_sum_prim (n : ℕ) (hn : 0 < n) :
    ∑ η ∈ primitiveRoots n ℂ, η = (ArithmeticFunction.moebius n : ℂ) := by
  classical
  have key : ∀ m > 0, ∑ i ∈ m.divisors, (∑ η ∈ primitiveRoots i ℂ, η)
      = (fun m : ℕ => if m = 1 then (1:ℂ) else 0) m := by
    intro m hm
    show _ = (if m = 1 then (1:ℂ) else 0)
    rw [← gb_sum_roots m hm, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
      Finset.sum_biUnion]
    intro i _ j _ hij
    exact IsPrimitiveRoot.disjoint hij
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp key) n hn
  rw [← this, Nat.sum_divisorsAntidiagonal (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
    (if b = 1 then (1:ℂ) else 0))]
  rw [Finset.sum_eq_single n]
  · simp [Nat.div_self hn]
  · intro b hb hbn
    have hd : b ∣ n := Nat.dvd_of_mem_divisors hb
    have : n / b ≠ 1 := by
      intro h
      apply hbn
      have := Nat.div_mul_cancel hd
      rw [h] at this
      omega
    simp [this]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩) h
private theorem gb_sum_cop (q : ℕ) (hq : 0 < q) (a : ℕ) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      Complex.exp (((2*Real.pi*(a:ℝ)*b/q:ℝ):ℂ)*Complex.I)
      = (ArithmeticFunction.moebius q : ℂ) := by
  have hq0 : q ≠ 0 := hq.ne'
  have hζ := Complex.isPrimitiveRoot_exp_of_coprime a q hq0 ha
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (a / q))
  rw [← gb_sum_prim q hq]
  have hterm : ∀ b : ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/q:ℝ):ℂ)*Complex.I) = ζ ^ b := by
    intro b
    simp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  refine Finset.sum_bij (fun b _ => ζ ^ b) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [mem_primitiveRoots hq]
    exact hζ.pow_of_coprime b hb.2
  · intro i hi j hj h
    rw [Finset.mem_filter, Finset.mem_range] at hi hj
    exact hζ.pow_inj hi.1 hj.1 h
  · intro x hx
    rw [mem_primitiveRoots hq] at hx
    haveI : NeZero q := ⟨hq0⟩
    obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ?_, e⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hi, ?_⟩
    rw [← e] at hx
    exact (hζ.pow_iff_coprime hq i).mp hx

theorem PEqualNP.Outside.L_goldbach_cert_162 :
    ∀ a:ℕ, Nat.Coprime a 162 → (∑ b ∈ (Finset.range 162).filter (fun b => Nat.Coprime b 162), Complex.exp (((2*Real.pi*(a:ℝ)*b/162:ℝ):ℂ)*Complex.I))/(54:ℂ)=(0:ℂ)/54 := by
  intro a ha
  have h := gb_sum_cop 162 (by norm_num) a ha
  have hm : ArithmeticFunction.moebius 162 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun h => by have := Nat.isUnit_iff.mp (h 3 ⟨18, by norm_num⟩); omega)
  rw [hm, Int.cast_zero] at h
  simp only [Nat.cast_ofNat] at h
  rw [h]
