import Mathlib

open Finset

namespace Conjectures.Goldbach.FareyFullSieveRemainder_aux

/-! ### Counting one residue class in an interval -/

lemma ceil_diff_bound (x y q : ℚ) :
    |((⌈x / q⌉ - ⌈y / q⌉ : ℤ) : ℚ) - (x - y) / q| ≤ 1 := by
  have hxlo : x / q ≤ (⌈x / q⌉ : ℚ) := Int.le_ceil _
  have hxhi : (⌈x / q⌉ : ℚ) < x / q + 1 := Int.ceil_lt_add_one _
  have hylo : y / q ≤ (⌈y / q⌉ : ℚ) := Int.le_ceil _
  have hyhi : (⌈y / q⌉ : ℚ) < y / q + 1 := Int.ceil_lt_add_one _
  have hdiv : (x - y) / q = x / q - y / q := by ring
  rw [abs_le]
  rw [hdiv]
  simp only [Int.cast_sub]
  constructor <;> linarith

lemma ceil_diff_nonneg (x y q : ℚ) (hq : 0 < q) (hxy : y ≤ x) :
    0 ≤ ⌈x / q⌉ - ⌈y / q⌉ := by
  have hqxy : y / q ≤ x / q := by gcongr
  exact sub_nonneg.mpr (Int.ceil_le_ceil hqxy)

theorem card_modEq_Icc (m c l h : ℕ) (hm : 0 < m) (hlh : l ≤ h) :
    |(((Finset.Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℝ)
        - ((h - l + 1 : ℕ) : ℝ) / (m : ℝ)| ≤ 1 := by
  have hset : (Icc l h).filter (fun u => u ≡ c [MOD m]) =
      (Ico l (h + 1)).filter (fun u => u ≡ c [MOD m]) := by
    ext u
    simp [mem_filter, mem_Icc, mem_Ico]
  have hcard := Nat.Ico_filter_modEq_card l (h + 1) hm c
  have hlh' : l ≤ h + 1 := by omega
  have hxy : ((l : ℕ) : ℚ) - (c : ℚ) ≤ ((h + 1 : ℕ) : ℚ) - (c : ℚ) := by
    have hxy' : ((l : ℕ) : ℚ) ≤ ((h + 1 : ℕ) : ℚ) := by exact_mod_cast hlh'
    linarith
  have hceil_nonneg :
      0 ≤ ⌈(((h + 1 : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ -
        ⌈(((l : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ceil_diff_nonneg _ _ _ (by exact_mod_cast hm) hxy)
  have hlenQ : ((h - l + 1 : ℕ) : ℚ) =
      ((h + 1 : ℕ) : ℚ) - (l : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hlh]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hcard' : (((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℤ) =
      ⌈(((h + 1 : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ -
        ⌈(((l : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ := by
    rw [hset]
    rw [hcard]
    exact max_eq_left hceil_nonneg
  have hbound := ceil_diff_bound
    (((h + 1 : ℕ) : ℚ) - (c : ℚ)) (((l : ℕ) : ℚ) - (c : ℚ)) (m : ℚ)
  have hdiffQ :
      (((h + 1 : ℕ) : ℚ) - (c : ℚ)) -
          (((l : ℕ) : ℚ) - (c : ℚ)) = ((h - l + 1 : ℕ) : ℚ) := by
    rw [hlenQ]
    ring
  rw [hdiffQ] at hbound
  have hcardQ : (((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℚ) =
      ((⌈(((h + 1 : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ -
        ⌈(((l : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ : ℤ) : ℚ) := by
    exact_mod_cast hcard'
  have hmainQ :
      |(((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℚ) -
        ((h - l + 1 : ℕ) : ℚ) / (m : ℚ)| ≤ 1 := by
    rw [hcardQ]
    exact hbound
  have hmainR :
      ((|(((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℚ) -
        ((h - l + 1 : ℕ) : ℚ) / (m : ℚ)| : ℚ) : ℝ) ≤ (1 : ℝ) := by
    exact_mod_cast hmainQ
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hmainR

/-! ### Moebius inversion of the coprimality mask -/

theorem ind_coprime (n u : ℕ) (hn : 0 < n) :
    (∑ k ∈ n.divisors, if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else 0)
      = if Nat.Coprime n u then 1 else 0 := by
  classical
  let m := n.gcd u
  have hm : m ≠ 0 := by
    intro hm
    have hmn : m ∣ n := Nat.gcd_dvd_left n u
    rw [hm] at hmn
    exact hn.ne' (zero_dvd_iff.mp hmn)
  have hfilter : n.divisors.filter (fun k => k ∣ u) = m.divisors := by
    ext k
    constructor
    · intro hk
      rw [mem_filter] at hk
      rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hk.1) hk.2, hm⟩
    · intro hk
      rw [mem_filter]
      have hkm : k ∣ m := (Nat.mem_divisors.mp hk).1
      exact ⟨Nat.mem_divisors.mpr ⟨(dvd_gcd_iff k n u).mp hkm |>.1, hn.ne'⟩,
        (dvd_gcd_iff k n u).mp hkm |>.2⟩
  calc
    (∑ k ∈ n.divisors, if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else 0) =
        ∑ k ∈ n.divisors.filter (fun k => k ∣ u), ArithmeticFunction.moebius k := by
          rw [sum_filter]
    _ = ∑ k ∈ m.divisors, ArithmeticFunction.moebius k := by rw [hfilter]
    _ = if m = 1 then 1 else 0 := by
      have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
        ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
      exact h
    _ = if Nat.Coprime n u then 1 else 0 := by
      simp [m, Nat.coprime_iff_gcd_eq_one]

theorem sum_moebius_div (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)
      = (n.totient : ℝ) / (n : ℝ) := by
  classical
  let f : ArithmeticFunction ℝ :=
    ⟨fun k => if k = 0 then 0 else ((k : ℝ))⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    constructor
    · simp [f]
    · intro a b ha hb hab
      simp [f, ha, hb, Nat.mul_ne_zero ha hb, Nat.cast_mul, mul_inv_rev, mul_comm]
  have hprod := hf.prodPrimeFactors_one_sub f hn.ne'
  have htot : (n.totient : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    simpa only [map_mul, map_natCast, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors n)
  calc
    (∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) =
        ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) * f k := by
          apply sum_congr rfl
          intro k hk
          have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
          simp [f, hk0, div_eq_mul_inv]
    _ = ∏ p ∈ n.primeFactors, (1 - f p) := hprod.symm
    _ = ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
      apply prod_congr rfl
      intro p hp
      have hp0 : p ≠ 0 := (Nat.pos_of_mem_primeFactors hp).ne'
      simp [f, hp0]
    _ = (n.totient : ℝ) / (n : ℝ) := by
      rw [htot]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      exact (mul_div_cancel_left₀ _ hnR).symm

/-! ### The two roots modulo each prime factor -/

/-- Residues `x : ZMod d` with `x * (n - x) = 0`. -/
def Root (d n : ℕ) : Finset (ZMod d) :=
  match d with
  | 0 => {0, (n : ZMod 0)}
  | d + 1 => Finset.univ.filter (fun x => x * ((n : ZMod (d + 1)) - x) = 0)

theorem mem_Root (d n : ℕ) [NeZero d] (x : ZMod d) :
    x ∈ Root d n ↔ x * ((n : ZMod d) - x) = 0 := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => simp [Root]

/-- For `u ≤ n`, the natural-number divisibility `d ∣ u * (n - u)` is the same condition. -/
theorem mem_Root_iff (d n u : ℕ) (hu : u ≤ n) :
    (u : ZMod d) ∈ Root d n ↔ d ∣ u * (n - u) := by
  cases d with
  | zero =>
      simp only [Root, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · have hu0 : u = 0 := by exact_mod_cast h
          simp [hu0]
        · have hun : u = n := by exact_mod_cast h
          simp [hun]
      · intro h
        have hprod : u * (n - u) = 0 := zero_dvd_iff.mp h
        rcases Nat.mul_eq_zero.mp hprod with hu0 | hsub
        · exact Or.inl (by exact_mod_cast hu0)
        · have hun : u = n := by omega
          exact Or.inr (by exact_mod_cast hun)
  | succ d =>
      rw [mem_Root]
      rw [← Nat.cast_sub hu, ← Nat.cast_mul]
      exact ZMod.natCast_eq_zero_iff _ _

theorem mem_Root_crt (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) (x : ZMod (q * r)) :
    ZMod.chineseRemainder h x ∈ Root q n ×ˢ Root r n ↔ x ∈ Root (q * r) n := by
  set e := ZMod.chineseRemainder h
  have hnat : e ((n : ℕ) : ZMod (q * r)) =
      (((n : ℕ) : ZMod q), ((n : ℕ) : ZMod r)) := by
    rw [map_natCast]
    rfl
  have hmul : e (x * (((n : ℕ) : ZMod (q * r)) - x)) =
      ((e x).1 * (((n : ℕ) : ZMod q) - (e x).1),
        (e x).2 * (((n : ℕ) : ZMod r) - (e x).2)) := by
    rw [map_mul, map_sub, hnat]
    rfl
  simp only [Finset.mem_product, mem_Root]
  constructor
  · rintro ⟨h1, h2⟩
    apply e.injective
    rw [hmul, map_zero]
    exact Prod.ext h1 h2
  · intro hx
    have he : e (x * (((n : ℕ) : ZMod (q * r)) - x)) = 0 := by
      rw [hx, map_zero]
    rw [hmul] at he
    exact ⟨by simpa using congrArg Prod.fst he, by simpa using congrArg Prod.snd he⟩

/-- Multiplicativity of the root count via CRT. -/
theorem card_Root_mul (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) :
    (Root (q * r) n).card = (Root q n).card * (Root r n).card := by
  have hbij : (Root (q * r) n).card = (Root q n ×ˢ Root r n).card := by
    refine Finset.card_bij' (fun x (_ : x ∈ Root (q * r) n) => ZMod.chineseRemainder h x)
      (fun y (_ : y ∈ Root q n ×ˢ Root r n) => (ZMod.chineseRemainder h).symm y) ?_ ?_ ?_ ?_
    · intro x hx
      exact (mem_Root_crt q r n h x).2 hx
    · intro y hy
      refine (mem_Root_crt q r n h ((ZMod.chineseRemainder h).symm y)).1 ?_
      rwa [RingEquiv.apply_symm_apply]
    · intro x _
      exact RingEquiv.symm_apply_apply _ _
    · intro y _
      exact RingEquiv.apply_symm_apply _ _
  rw [hbij, Finset.card_product]

/-- Prime case: exactly two roots, namely `0` and `n`. -/
theorem card_Root_prime (p n : ℕ) (hp : Nat.Prime p) (hn : ¬p ∣ n) :
    (Root p n).card = 2 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : (n : ZMod p) ≠ 0 := by
    intro h
    exact hn ((ZMod.natCast_eq_zero_iff n p).1 h)
  have hroots : Root p n = {0, (n : ZMod p)} := by
    ext x
    simp only [mem_Root, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hx | hsub
      · exact Or.inl hx
      · exact Or.inr (sub_eq_zero.mp hsub).symm
    · rintro (rfl | rfl)
      · simp
      · simp
  rw [hroots, Finset.card_pair (Ne.symm hn0)]

theorem card_Root_prod (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    (hn : ∀ p ∈ s, ¬p ∣ n) :
    (Root (∏ p ∈ s, p) n).card = 2 ^ s.card := by
  revert hs hn
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have hroot : Root 1 n = (univ : Finset (ZMod 1)) := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        rw [mem_Root]
        have hx : x = 0 := Subsingleton.elim x 0
        subst x
        simp
      simp only [prod_empty, pow_zero]
      rw [hroot, Finset.card_univ, ZMod.card, Finset.card_empty, pow_zero]
  | @insert a s ha ih =>
      intro hs hn
      have hpa : Nat.Prime a := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hn' : ∀ p ∈ s, ¬p ∣ n := fun p hp => hn p (Finset.mem_insert_of_mem hp)
      have hprodpos : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp => (hs' p hp).pos
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        apply (Nat.coprime_primes hpa (hs' p hp)).2
        intro h
        subst p
        exact ha hp
      letI : NeZero a := ⟨hpa.ne_zero⟩
      letI : NeZero (∏ p ∈ s, p) := ⟨hprodpos.ne'⟩
      letI : NeZero (a * ∏ p ∈ s, p) := ⟨(Nat.mul_pos hpa.pos hprodpos).ne'⟩
      calc
        (Root (∏ p ∈ insert a s, p) n).card =
            (Root (a * ∏ p ∈ s, p) n).card := by
              rw [Finset.prod_insert ha]
        _ = (Root a n).card * (Root (∏ p ∈ s, p) n).card :=
          card_Root_mul a (∏ p ∈ s, p) n hcop
        _ = 2 * 2 ^ s.card := by
          rw [card_Root_prime a n hpa (hn a (Finset.mem_insert_self a s)), ih hs' hn']
        _ = 2 ^ (insert a s).card := by
          rw [Finset.card_insert_of_notMem ha, pow_succ]
          omega

/-- The main count. -/
theorem card_Root (d n : ℕ) (hd : 0 < d) (hsq : Squarefree d)
    (hcop : Nat.Coprime d n) :
    (Root d n).card = 2 ^ d.primeFactors.card := by
  have hs : ∀ p ∈ d.primeFactors, Nat.Prime p := fun _ hp =>
    Nat.prime_of_mem_primeFactors hp
  have hn : ∀ p ∈ d.primeFactors, ¬p ∣ n := by
    intro p hp
    have hpn : Nat.Coprime p n :=
      Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop
    exact (hs p hp).coprime_iff_not_dvd.mp hpn
  have h := card_Root_prod d.primeFactors hs hn
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  exact h

/-! ### The full-window sieve remainder -/

theorem main
    (n d l h : ℕ) (hn : 1 < n) (hd : 0 < d) (hsq : Squarefree d) (hcop : Nat.Coprime d n)
    (hlh : l ≤ h) (hh : h < n) :
    let r : ℝ := (2 : ℝ)^d.primeFactors.card
    let A := ((Finset.Icc l h).filter (fun u => u.Coprime n ∧ d ∣ u*(n-u))).card
    |(A:ℝ) - ((h-l+1 : ℕ):ℝ)*(n.totient:ℝ)*r/((d:ℝ)*n)| ≤ r*(n.divisors.card:ℝ) := by
  classical
  dsimp only
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set L : ℝ := ((h - l + 1 : ℕ) : ℝ) with hLdef
  set M : ℝ := L * (n.totient : ℝ) / ((d:ℝ) * (n:ℝ)) with hMdef
  set τ : ℝ := (n.divisors.card : ℝ) with hτdef
  -- membership characterisation
  have hmem : ∀ u ∈ Finset.Icc l h, (u : ZMod d) ∈ Root d n ↔ d ∣ u * (n - u) := by
    intro u hu
    refine mem_Root_iff d n u ?_
    have := Finset.mem_Icc.1 hu
    omega
  -- fibres over the root set
  have hfib : ∀ x ∈ Root d n,
      (((Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).filter
        (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).card
      = ((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card := by
    intro x hx
    have hset : ((Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).filter
        (fun u : ℕ => ((u : ℕ) : ZMod d) = x)
        = (Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x) := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu1, hu2, hu3⟩, hu4⟩; exact ⟨hu1, hu2, hu4⟩
      · rintro ⟨hu1, hu2, hu3⟩
        exact ⟨⟨hu1, hu2, (hmem u hu1).1 (by rw [hu3]; exact hx)⟩, hu3⟩
    rw [hset]
  -- total count as a sum over roots
  have hA : (((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).card : ℝ)
      = ∑ x ∈ Root d n, (((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) := by
    have h1 : ((Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).card
        = ∑ x ∈ Root d n, (((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).filter
            (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun u : ℕ => ((u : ℕ) : ZMod d))
        (s := (Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u)))
        (t := Root d n) (by
          intro u hu
          have hu' : u ∈ (Finset.Icc l h).filter
              (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u)) := hu
          have hu'' := Finset.mem_filter.1 hu'
          exact (hmem u hu''.1).2 hu''.2.2)
    rw [h1, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun x hx => by rw [hfib x hx])
  -- per-root bound
  have hN : ∀ x ∈ Root d n,
      |(((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M| ≤ τ := by
    intro x hx
    have hmu : ∀ u : ℕ, (if Nat.Coprime u n then (1:ℝ) else 0)
        = ∑ k ∈ n.divisors,
          (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) := by
      intro u
      have hR : ((∑ k ∈ n.divisors,
            if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else (0:ℤ) : ℤ) : ℝ)
          = ∑ k ∈ n.divisors,
            (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> simp)
      have h := ind_coprime n u (by omega)
      by_cases hcu : Nat.Coprime u n
      · have hcu' : Nat.Coprime n u := Nat.coprime_comm.mpr hcu
        have h1 : ((∑ k ∈ n.divisors,
            if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else (0:ℤ) : ℤ) : ℝ) = 1 := by
          calc _ = ((if Nat.Coprime n u then (1:ℤ) else (0:ℤ) : ℤ) : ℝ) := by rw [h]
            _ = 1 := by rw [if_pos hcu']; norm_num
        rw [hR] at h1
        rw [if_pos hcu]
        exact h1.symm
      · have hcu' : ¬ Nat.Coprime n u := fun h' => hcu (Nat.coprime_comm.mp h')
        have h1 : ((∑ k ∈ n.divisors,
            if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else (0:ℤ) : ℤ) : ℝ) = 0 := by
          calc _ = ((if Nat.Coprime n u then (1:ℤ) else (0:ℤ) : ℤ) : ℝ) := by rw [h]
            _ = 0 := by rw [if_neg hcu']; norm_num
        rw [hR] at h1
        rw [if_neg hcu]
        exact h1.symm
    -- Moebius expansion of the fibre count
    have hNeq : (((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
        = ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            (((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) := by
      have hset1 : (Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)
          = ((Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).filter
            (fun u : ℕ => Nat.Coprime u n) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hu1, hu2, hu3⟩; exact ⟨⟨hu1, hu3⟩, hu2⟩
        · rintro ⟨⟨hu1, hu3⟩, hu2⟩; exact ⟨hu1, hu2, hu3⟩
      have hset2 : ∀ k : ℕ, ((Finset.Icc l h).filter
              (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).filter (fun u : ℕ => k ∣ u)
          = (Finset.Icc l h).filter
            (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x) := by
        intro k
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hu1, hu2⟩, hu3⟩; exact ⟨hu1, hu3, hu2⟩
        · rintro ⟨hu1, hu2, hu3⟩; exact ⟨⟨hu1, hu3⟩, hu2⟩
      calc _ = ((((Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).filter
              (fun u : ℕ => Nat.Coprime u n)).card : ℝ) := by rw [hset1]
        _ = ∑ u ∈ (Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x),
              (if Nat.Coprime u n then (1:ℝ) else 0) :=
            Finset.natCast_card_filter _ _
        _ = ∑ u ∈ (Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x),
              ∑ k ∈ n.divisors,
                (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) :=
            Finset.sum_congr rfl (fun u _ => hmu u)
        _ = ∑ k ∈ n.divisors,
              ∑ u ∈ (Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x),
                (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hstep : ∀ u, (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0)
                = ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
                  (if k ∣ u then (1:ℝ) else 0) := by
              intro u; split_ifs <;> ring
            rw [Finset.sum_congr rfl (fun u _ => hstep u), ← Finset.mul_sum, Finset.sum_boole,
              hset2 k]
    -- each divisor class is a single residue class mod k*d
    have hcr : ∀ k ∈ n.divisors, ∃ c : ℕ, ∀ u : ℕ,
        (k ∣ u ∧ ((u : ℕ) : ZMod d) = x) ↔ u ≡ c [MOD (k * d)] := by
      intro k hk
      have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
      have hkd' : Nat.Coprime k d :=
        (Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_divisors hk) hcop).symm
      letI : NeZero k := ⟨hk0.ne'⟩
      letI : NeZero (k * d) := ⟨(Nat.mul_pos hk0 hd).ne'⟩
      set e := ZMod.chineseRemainder hkd' with he
      set y : ZMod (k * d) := e.symm (0, x) with hy
      refine ⟨y.val, fun u => ?_⟩
      have hE : e ((u : ℕ) : ZMod (k * d)) = ((u : ZMod k), ((u : ℕ) : ZMod d)) := by
        rw [map_natCast]; rfl
      have hyval : ((y.val : ℕ) : ZMod (k * d)) = y := ZMod.natCast_zmod_val y
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : ((u : ℕ) : ZMod (k * d)) = y := by
          apply e.injective
          rw [hE, RingEquiv.apply_symm_apply]
          exact Prod.ext_iff.2 ⟨(ZMod.natCast_eq_zero_iff u k).2 h1, h2⟩
        exact (ZMod.natCast_eq_natCast_iff u y.val (k * d)).1 (by rw [hyval]; exact h3)
      · intro hu
        have h3 : ((u : ℕ) : ZMod (k * d)) = y := by
          have h5 := (ZMod.natCast_eq_natCast_iff u y.val (k * d)).2 hu
          rw [hyval] at h5
          exact h5
        have h4 := congrArg e h3
        rw [hE, RingEquiv.apply_symm_apply] at h4
        exact ⟨(ZMod.natCast_eq_zero_iff u k).1 (congrArg Prod.fst h4), congrArg Prod.snd h4⟩
    -- hence each term is within 1 of L/(k*d)
    have hδ : ∀ k ∈ n.divisors,
        |(((Finset.Icc l h).filter
            (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
          - L / ((k:ℝ) * (d:ℝ))| ≤ 1 := by
      intro k hk
      obtain ⟨c, hc⟩ := hcr k hk
      have hset : (Finset.Icc l h).filter
            (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)
          = (Finset.Icc l h).filter (fun u : ℕ => u ≡ c [MOD (k * d)]) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hu1, hu2⟩; exact ⟨hu1, (hc u).1 hu2⟩
        · rintro ⟨hu1, hu2⟩; exact ⟨hu1, (hc u).2 hu2⟩
      rw [hset]
      have hthis := card_modEq_Icc (k * d) c l h (Nat.mul_pos (Nat.pos_of_mem_divisors hk) hd) hlh
      rw [Nat.cast_mul] at hthis
      simpa [hLdef] using hthis
    -- the main term identity
    have hmain : (((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M
        = ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
              - L / ((k:ℝ) * (d:ℝ))) := by
      rw [hNeq]
      have hsplit : ∀ k ∈ n.divisors,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
              (((Finset.Icc l h).filter
                (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
            = ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
                ((((Finset.Icc l h).filter
                  (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
                  - L / ((k:ℝ) * (d:ℝ)))
              + ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (L / ((k:ℝ) * (d:ℝ))) := by
        intro k _; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hsum2 : ∑ k ∈ n.divisors,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (L / ((k:ℝ) * (d:ℝ))) = M := by
        have hk0 : ∀ k ∈ n.divisors, (k:ℝ) ≠ 0 := by
          intro k hk; exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
        have hstep : ∀ k ∈ n.divisors,
            ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (L / ((k:ℝ) * (d:ℝ)))
              = (L / (d:ℝ)) * (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k:ℝ)) := by
          intro k hk
          field_simp
        rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_moebius_div n (by omega)]
        rw [hMdef]
        field_simp
      rw [hsum2]
      ring
    -- bound the error sum
    have hμ : ∀ k : ℕ, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
      intro k
      calc |((ArithmeticFunction.moebius k : ℤ) : ℝ)|
          = ((|(ArithmeticFunction.moebius k : ℤ)| : ℤ) : ℝ) := by rw [Int.cast_abs]
        _ ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    have hbd : |∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
              - L / ((k:ℝ) * (d:ℝ)))| ≤ τ := by
      calc |∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
              - L / ((k:ℝ) * (d:ℝ)))|
          ≤ ∑ k ∈ n.divisors, |((ArithmeticFunction.moebius k : ℤ) : ℝ) *
              ((((Finset.Icc l h).filter
                (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
                - L / ((k:ℝ) * (d:ℝ)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ n.divisors, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| *
              |(((Finset.Icc l h).filter
                (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
                - L / ((k:ℝ) * (d:ℝ))| :=
            Finset.sum_congr rfl (fun k _ => abs_mul _ _)
        _ ≤ ∑ k ∈ n.divisors, (1:ℝ) * 1 :=
            Finset.sum_le_sum (fun k hk =>
              mul_le_mul (hμ k) (hδ k hk) (abs_nonneg _) (by norm_num))
        _ = τ := by simp [hτdef]
    rw [hmain]
    exact hbd
  -- assemble
  have hfinal : |(((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).card : ℝ)
      - ((Root d n).card : ℝ) * M| ≤ ((Root d n).card : ℝ) * τ := by
    rw [hA]
    have hsplit : (∑ x ∈ Root d n, (((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ))
        - ((Root d n).card : ℝ) * M
        = ∑ x ∈ Root d n, ((((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M) := by
      have hsumM : ∑ x ∈ Root d n, M = ((Root d n).card : ℝ) * M := by
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_sub_distrib, hsumM]
    rw [hsplit]
    calc |∑ x ∈ Root d n, ((((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M)|
        ≤ ∑ x ∈ Root d n, |(((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Root d n, τ := Finset.sum_le_sum (fun x hx => hN x hx)
      _ = ((Root d n).card : ℝ) * τ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Root d n).card : ℝ) = (2 : ℝ) ^ d.primeFactors.card := by
    rw [card_Root d n hd hsq hcop]; push_cast; ring
  rw [hcard] at hfinal
  have hMval : (2 : ℝ) ^ d.primeFactors.card * M
      = L * (n.totient : ℝ) * (2 : ℝ) ^ d.primeFactors.card
        / ((d : ℝ) * (n : ℝ)) := by
    rw [hMdef]
    field_simp
  rw [← hMval]
  exact hfinal

end Conjectures.Goldbach.FareyFullSieveRemainder_aux

theorem Conjectures.Goldbach.FareyFullSieveRemainder :
    ∀ n d l h : ℕ, 1 < n → 0 < d → Squarefree d → d.Coprime n → l ≤ h → h < n → let r : ℝ := (2 : ℝ)^d.primeFactors.card; let A := ((Finset.Icc l h).filter (fun u => u.Coprime n ∧ d ∣ u*(n-u))).card; |(A:ℝ) - ((h-l+1 : ℕ):ℝ)*(n.totient:ℝ)*r/((d:ℝ)*n)| ≤ r*(n.divisors.card:ℝ) := by
  intro n d l h hn hd hsq hcop hlh hh
  exact Conjectures.Goldbach.FareyFullSieveRemainder_aux.main n d l h hn hd hsq hcop hlh hh
