import Mathlib

namespace OddQuadraticRoot

open Finset

def rootCount (v : ℕ) : ℕ :=
  ((range v).filter fun h => (h ^ 2 + 1) % v = 0).card

abbrev ResidueRoots (v : ℕ) := {x : ZMod v // x ^ 2 = -1}

private theorem mod_zero_iff_root (v h : ℕ) :
    (h ^ 2 + 1) % v = 0 ↔ (h : ZMod v) ^ 2 = -1 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow,
    Nat.cast_one, eq_neg_iff_add_eq_zero]

theorem root_count_eq_card (v : ℕ) [NeZero v] :
    rootCount v = Fintype.card (ResidueRoots v) := by
  let S := (range v).filter fun h => (h ^ 2 + 1) % v = 0
  let e : ↥S ≃ ResidueRoots v := {
    toFun := fun x => ⟨(x.val : ZMod v), (mod_zero_iff_root v x.val).mp
      (mem_filter.mp x.property).2⟩
    invFun := fun x => ⟨x.val.val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt x.val),
      (mod_zero_iff_root v x.val.val).mpr (by simpa only [ZMod.natCast_zmod_val] using x.property)⟩⟩
    left_inv := fun x => Subtype.ext (ZMod.val_natCast_of_lt
      (mem_range.mp (mem_filter.mp x.property).1))
    right_inv := fun x => Subtype.ext (ZMod.natCast_zmod_val x.val)
  }
  exact (Fintype.card_coe S).symm.trans (Fintype.card_congr e)

theorem root_count_zero_of_prime_mod_four {p v : ℕ} (hp : p.Prime) (hDiv : p ∣ v)
    (hv : v ≠ 0) (hMod : p % 4 = 3) : rootCount v = 0 := by
  let _ : NeZero v := ⟨hv⟩
  have hpF : p ∈ v.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hDiv, hv⟩
  let _ : IsEmpty (ResidueRoots v) := ⟨fun x => by
    have hx : IsSquare (-1 : ZMod v) := ⟨x.val, by rw [← pow_two, x.property]⟩
    exact (Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hpF hx) hMod⟩
  rw [root_count_eq_card, Fintype.card_of_isEmpty]

private def rootUnit {v : ℕ} (x : ResidueRoots v) : (ZMod v)ˣ where
  val := x.val
  inv := -x.val
  val_inv := by rw [mul_neg, ← pow_two, x.property, neg_neg]
  inv_val := by rw [neg_mul, ← pow_two, x.property, neg_neg]

theorem root_count_prime_pow_le_two {p : ℕ} (hp : p.Prime) (hpTwo : p ≠ 2) (k : ℕ) :
    rootCount (p ^ k) ≤ 2 := by
  classical
  let _ : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let _ : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hpTwo k
  rw [root_count_eq_card]
  by_cases hInhabited : Nonempty (ResidueRoots (p ^ k))
  · obtain ⟨x₀⟩ := hInhabited
    let S : Finset (ZMod (p ^ k))ˣ := univ.filter fun u => u ^ 2 = 1
    have hMem (x : ResidueRoots (p ^ k)) : rootUnit x / rootUnit x₀ ∈ S := by
      have hSquares : (rootUnit x) ^ 2 = (rootUnit x₀) ^ 2 := by
        apply Units.ext
        change x.val ^ 2 = x₀.val ^ 2
        rw [x.property, x₀.property]
      exact mem_filter.mpr ⟨mem_univ _, by rw [div_pow, hSquares, div_self']⟩
    let f : ResidueRoots (p ^ k) → ↥S := fun x => ⟨rootUnit x / rootUnit x₀, hMem x⟩
    have hInjective : Function.Injective f := by
      intro x y hEq
      have hDiv := congrArg Subtype.val hEq
      change rootUnit x / rootUnit x₀ = rootUnit y / rootUnit x₀ at hDiv
      have hUnits := div_left_inj.mp hDiv
      exact Subtype.ext (congrArg Units.val hUnits)
    calc
      _ ≤ Fintype.card (↥S) := Fintype.card_le_of_injective f hInjective
      _ = S.card := Fintype.card_coe S
      _ ≤ 2 := IsCyclic.card_pow_eq_one_le (by decide : 0 < (2 : ℕ))
  · let _ : IsEmpty (ResidueRoots (p ^ k)) := not_nonempty_iff.mp hInhabited
    rw [Fintype.card_of_isEmpty]
    decide

private def rootsCRT {m n : ℕ} (hc : m.Coprime n) :
    ResidueRoots (m * n) ≃ ResidueRoots m × ResidueRoots n := by
  let e := ZMod.chineseRemainder hc
  refine {
    toFun := fun x => ?_
    invFun := fun x => ?_
    left_inv := ?_
    right_inv := ?_
  }
  · have h : (e x.val) ^ 2 = -1 := by
      simpa only [map_pow, map_neg, map_one] using congrArg e x.property
    exact ⟨⟨(e x.val).1, congrArg Prod.fst h⟩, ⟨(e x.val).2, congrArg Prod.snd h⟩⟩
  · let z : ZMod m × ZMod n := (x.1.val, x.2.val)
    have hz : z ^ 2 = -1 := Prod.ext x.1.property x.2.property
    exact ⟨e.symm z, by simpa only [map_pow, map_neg, map_one] using congrArg e.symm hz⟩
  · intro x
    exact Subtype.ext (e.symm_apply_apply x.val)
  · intro x
    have h := e.apply_symm_apply (x.1.val, x.2.val)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem root_count_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hc : m.Coprime n) :
    rootCount (m * n) = rootCount m * rootCount n := by
  let _ : NeZero m := ⟨hm⟩
  let _ : NeZero n := ⟨hn⟩
  let _ : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
  rw [root_count_eq_card, root_count_eq_card, root_count_eq_card,
    Fintype.card_congr (rootsCRT hc), Fintype.card_prod]


end OddQuadraticRoot

namespace OddQuadraticRoot

open ArithmeticFunction Finset ZMod

private def chiFourAF : ArithmeticFunction ℤ :=
  ⟨fun d => χ₄ (d : ZMod 4), by decide⟩

private theorem chiFourAF_multiplicative : chiFourAF.IsMultiplicative := by
  refine ⟨by decide, fun {m n} _ => ?_⟩
  change χ₄ ((m * n : ℕ) : ZMod 4) = χ₄ (m : ZMod 4) * χ₄ (n : ZMod 4)
  rw [Nat.cast_mul, map_mul]

private theorem divisor_sum_mul {m n : ℕ} (hc : m.Coprime n) :
    (∑ d ∈ (m * n).divisors, χ₄ (d : ZMod 4)) =
      (∑ d ∈ m.divisors, χ₄ (d : ZMod 4)) * (∑ d ∈ n.divisors, χ₄ (d : ZMod 4)) := by
  have hMult : IsMultiplicative ((zeta : ArithmeticFunction ℤ) * chiFourAF) :=
    isMultiplicative_zeta.natCast.mul chiFourAF_multiplicative
  have hApply (v : ℕ) :
      ((zeta : ArithmeticFunction ℤ) * chiFourAF) v = ∑ d ∈ v.divisors, χ₄ (d : ZMod 4) :=
    coe_zeta_mul_apply (f := chiFourAF) (x := v)
  have h := hMult.map_mul_of_coprime hc
  rw [hApply, hApply, hApply] at h
  exact h

private theorem root_count_le_divisor_sum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hOdd : Odd (p ^ k)) :
    (rootCount (p ^ k) : ℤ) ≤ ∑ d ∈ (p ^ k).divisors, χ₄ (d : ZMod 4) := by
  have hpTwo : p ≠ 2 := by
    intro he
    subst p
    have hZero := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hk.ne')
    have hOne := Nat.odd_iff.mp hOdd
    omega
  have hpOdd := hp.eq_two_or_odd.resolve_left hpTwo
  have hpMod : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.cast_pow, map_pow]
  rcases hpMod with hOne | hThree
  · have hRoots : (rootCount (p ^ k) : ℤ) ≤ 2 := by
      exact_mod_cast root_count_prime_pow_le_two hp hpTwo k
    have hK : (2 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
    simpa [χ₄_nat_one_mod_four hOne] using hRoots.trans hK
  · rw [root_count_zero_of_prime_mod_four hp (dvd_pow_self p hk.ne')
        (pow_ne_zero _ hp.ne_zero) hThree, Nat.cast_zero, χ₄_nat_three_mod_four hThree]
    rw [← Fin.sum_univ_eq_sum_range, Fin.sum_neg_one_pow]
    split <;> decide

theorem root_count_le_chi_four_divisor_sum (v : ℕ) (hv : Odd v) :
    (rootCount v : ℤ) ≤ ∑ d ∈ v.divisors, χ₄ (d : ZMod 4) := by
  induction v using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => exact root_count_le_divisor_sum_prime_pow hp hk hv
  | zero => simp at hv
  | one => decide
  | coprime m n hm hn hc ihM ihN =>
    rw [root_count_mul (by omega) (by omega) hc, Nat.cast_mul, divisor_sum_mul hc]
    have hM := ihM (Nat.odd_mul.mp hv).1
    have hN := ihN (Nat.odd_mul.mp hv).2
    exact mul_le_mul hM hN (Int.natCast_nonneg _) ((Int.natCast_nonneg _).trans hM)


end OddQuadraticRoot

open Finset ArithmeticFunction ZMod

namespace QuadraticRootAverage

private def chiArith : ArithmeticFunction ℤ :=
  ⟨fun n => χ₄ (n : ZMod 4), by decide⟩

private def oddZeta : ArithmeticFunction ℤ :=
  ⟨fun n => if Odd n then 1 else 0, by decide⟩

private theorem chi_prefix_value (n : ℕ) :
    (∑ i ∈ Ioc 0 n, chiArith i) = if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le n), ih]
    change (if n % 4 = 1 ∨ n % 4 = 2 then (1 : ℤ) else 0) + χ₄ ((n + 1 : ℕ) : ZMod 4) =
      if (n+1) % 4 = 1 ∨ (n+1) % 4 = 2 then 1 else 0
    rw [χ₄_nat_eq_if_mod_four (n+1),
      show (n+1) % 2 = (n % 4 + 1) % 2 by omega,
      show (n+1) % 4 = (n % 4 + 1) % 4 by omega]
    have hr := Nat.mod_lt n (by decide : 0 < 4)
    generalize n % 4 = r at hr ⊢
    interval_cases r <;> decide

private theorem chi_prefix_le (n : ℕ) :
    (∑ i ∈ Ioc 0 n, chiArith i) ≤ 1 := by
  rw [chi_prefix_value]
  split_ifs <;> norm_num

private theorem odd_zeta_mul (n : ℕ) :
    (oddZeta * chiArith) n =
      if Odd n then (∑ d ∈ n.divisors, χ₄ (d : ZMod 4)) else 0 := by
  by_cases hn : Odd n
  · rw [ite_eq_left hn]
    change (oddZeta * chiArith) n = ∑ d ∈ n.divisors, chiArith d
    rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply sum_congr rfl
    intro x hx
    obtain ⟨heq, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hOdd : Odd (x.1 * x.2) := by rw [heq]; exact hn
    have hOddFirst := (Nat.odd_mul.mp hOdd).1
    have hFirst : x.1 ≠ 0 := by
      intro h
      simp [h] at hOddFirst
    simp [oddZeta, natCoe_apply, zeta_apply_ne hFirst, hOddFirst]
  · rw [ite_eq_right hn, ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro x hx
    obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    by_cases hOdd : Odd x.1
    · have heven : x.2 % 2 = 0 := Nat.not_odd_iff.mp <| by
        intro hx2
        exact hn (heq ▸ (Nat.odd_mul.mpr ⟨hOdd,hx2⟩))
      change (if Odd x.1 then (1 : ℤ) else 0) * χ₄ (x.2 : ZMod 4) = 0
      rw [χ₄_nat_eq_if_mod_four, ite_eq_left heven, mul_zero]
    · change (if Odd x.1 then (1 : ℤ) else 0) * chiArith x.2 = 0
      rw [ite_eq_right hOdd, zero_mul]

theorem odd_divisor_character_prefix (n : ℕ) :
    (∑ v ∈ Ioc 0 n, if Odd v then (∑ d ∈ v.divisors, χ₄ (d : ZMod 4)) else 0) ≤ (n : ℤ) := by
  simp_rw [← odd_zeta_mul]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  calc
    _ ≤ ∑ _v ∈ Ioc 0 n, (1 : ℤ) := by
      apply sum_le_sum
      intro v _
      by_cases hv : Odd v
      · change (if Odd v then (1 : ℤ) else 0) * (∑ i ∈ Ioc 0 (n/v), chiArith i) ≤ 1
        simpa [hv] using chi_prefix_le (n/v)
      · change (if Odd v then (1 : ℤ) else 0) * (∑ i ∈ Ioc 0 (n/v), chiArith i) ≤ 1
        simp [hv]
    _ = _ := by simp [Nat.card_Ioc]

private theorem positive_range_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, f (i+1)) = ∑ i ∈ Icc 1 n, f i := by
  have h : Icc 1 n = Ico 1 (n+1) := by
    ext i
    simp only [mem_Icc, mem_Ico]
    omega
  rw [h, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem sqrt_weighted_of_prefix (f : ℕ → ℝ) (n : ℕ)
    (h : ∀ k : ℕ, (∑ i ∈ range k, f i) ≤ (k : ℝ)) :
    (∑ i ∈ range n, f i / Real.sqrt ((i : ℝ)+1)) ≤ 2 * Real.sqrt n := by
  let w := fun i : ℕ => (Real.sqrt ((i : ℝ)+1))⁻¹
  have hw (i : ℕ) : w (i+1) ≤ w i := by
    apply inv_anti₀ (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    push_cast
    linarith
  have hCompare : (∑ i ∈ range n, w i • f i) ≤ ∑ i ∈ range n, w i • (1 : ℝ) := by
    rw [Finset.sum_range_by_parts w f, Finset.sum_range_by_parts w (fun _ => (1 : ℝ))]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    apply sub_le_sub (mul_le_mul_of_nonneg_left (h n) (by dsimp [w]; positivity))
    apply sum_le_sum
    intro i _
    exact mul_le_mul_of_nonpos_left (h (i+1)) (sub_nonpos.mpr (hw i))
  have htel : (∑ i ∈ range n, w i) ≤ 2 * Real.sqrt n := by
    calc
      _ ≤ ∑ i ∈ range n, 2 * (Real.sqrt ((i : ℝ)+1) - Real.sqrt (i : ℝ)) := by
        apply sum_le_sum
        intro i _
        dsimp [w]
        have hpos : 0 < Real.sqrt ((i : ℝ)+1) := Real.sqrt_pos.2 (by positivity)
        rw [inv_eq_one_div, div_le_iff₀ hpos]
        nlinarith [Real.sq_sqrt (show 0 ≤ (i : ℝ)+1 by positivity),
          Real.sq_sqrt (show 0 ≤ (i : ℝ) by positivity),
          sq_nonneg (Real.sqrt ((i : ℝ)+1) - Real.sqrt (i : ℝ))]
      _ = _ := by
        rw [← mul_sum]
        simp only [← Nat.cast_succ, Finset.sum_range_sub (fun i : ℕ => Real.sqrt (i : ℝ)),
          Nat.cast_zero, Real.sqrt_zero, sub_zero]
  simp only [smul_eq_mul, mul_one] at hCompare
  simpa only [w, div_eq_mul_inv, mul_comm] using hCompare.trans htel

theorem odd_root_average_of_majorant (rho : ℕ → ℕ)
    (hMajorant : ∀ v, Odd v → (rho v : ℤ) ≤ ∑ d ∈ v.divisors, χ₄ (d : ZMod 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ, 1 ≤ V →
      (∑ v ∈ (Icc 1 V).filter Odd, (rho v : ℝ)) ≤ C*V ∧
      (∑ v ∈ (Icc 1 V).filter Odd, (rho v : ℝ)/Real.sqrt v) ≤ C*Real.sqrt V := by
  have hPrefix (V : ℕ) :
      (∑ v ∈ Icc 1 V, if Odd v then (rho v : ℝ) else 0) ≤ (V : ℝ) := by
    have hi : Icc 1 V = Ioc 0 V := by ext v; simp only [mem_Icc, mem_Ioc]; omega
    have hm :
        (∑ v ∈ Ioc 0 V, if Odd v then (rho v : ℤ) else 0) ≤ (V : ℤ) :=
      (sum_le_sum (fun v _ => by
        by_cases hv : Odd v
        · simpa [hv] using hMajorant v hv
        · simp [hv])).trans (odd_divisor_character_prefix V)
    rw [hi]
    exact_mod_cast hm
  let f : ℕ → ℝ := fun i => if Odd (i+1) then (rho (i+1) : ℝ) else 0
  have h (n : ℕ) : (∑ i ∈ range n, f i) ≤ (n : ℝ) := by
    exact (positive_range_sum (fun v => if Odd v then (rho v : ℝ) else 0) n).le.trans (hPrefix n)
  refine ⟨2, by norm_num, ?_⟩
  intro V _
  constructor
  · rw [sum_filter]
    exact (hPrefix V).trans (by linarith [Nat.cast_nonneg (α := ℝ) V])
  · rw [sum_filter]
    have hb := sqrt_weighted_of_prefix f V h
    have hEq : (∑ i ∈ range V, f i / Real.sqrt ((i : ℝ)+1)) =
        ∑ v ∈ Icc 1 V, if Odd v then (rho v : ℝ)/Real.sqrt v else 0 := by
      have he := positive_range_sum (fun v => if Odd v then (rho v : ℝ)/Real.sqrt v else 0) V
      rw [← he]
      apply sum_congr rfl
      intro i _
      by_cases hi : Odd (i+1) <;> simp [f, hi, Nat.cast_add]
    exact hEq ▸ hb

end QuadraticRootAverage

theorem Conjectures.QuadraticPrimes.OddQuadraticRootAverage :
    (let ρ := fun v : ℕ => ((Finset.range v).filter fun h => (h^2+1) % v=0).card; ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ, 1 ≤ V → (∑ v ∈ (Finset.Icc 1 V).filter Odd, (ρ v : ℝ)) ≤ C*V ∧ (∑ v ∈ (Finset.Icc 1 V).filter Odd, (ρ v : ℝ)/Real.sqrt v) ≤ C*Real.sqrt V) := by
  simpa only [OddQuadraticRoot.rootCount] using
    QuadraticRootAverage.odd_root_average_of_majorant OddQuadraticRoot.rootCount
      OddQuadraticRoot.root_count_le_chi_four_divisor_sum
