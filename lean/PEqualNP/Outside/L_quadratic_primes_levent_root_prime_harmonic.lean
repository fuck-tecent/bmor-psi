import Mathlib

private lemma cheb_mod4_eventual :
    ∃ X : ℕ, ∀ n : ℕ, X ≤ n → 1 ≤ n →
      (49 / 100 : ℝ) * n ≤ (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)) ∧
      (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)) ≤ (51 / 100 : ℝ) * n := by
  have hc : Nat.Coprime 1 4 := by norm_num
  have hpnt := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 4) (a := 1) hc
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hpnt
  have hlim := hpnt.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim' : Filter.Tendsto (fun n : ℕ =>
      (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)) / n)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    convert hlim using 1 <;> norm_num
    funext n
    congr 1
    apply Finset.sum_congr
    · ext p
      simp [Nat.ModEq, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    · intro p hp
      rfl
  have hev := hlim'.eventually (Ioo_mem_nhds (show (49/100 : ℝ) < 1/2 by norm_num)
    (show (1/2 : ℝ) < 51/100 by norm_num))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  refine ⟨X, ?_⟩
  intro n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbounds := hX n hn
  exact ⟨(le_of_lt ((lt_div_iff₀ hnpos).mp hbounds.1)),
    (le_of_lt ((div_lt_iff₀ hnpos).mp hbounds.2))⟩

private lemma cutoff_cube (x p : ℕ) (hx : 0 < x)
    (hp : p^100000 ≤ (2*x)^132301) : p^3 ≤ (2*x)^4 := by
  by_contra h
  have hlt : (2*x)^4 < p^3 := Nat.lt_of_not_ge h
  have hpw := Nat.pow_lt_pow_left hlt (show 100000 ≠ 0 by norm_num)
  have hbound := Nat.pow_le_pow_left hp 3
  have hbase : 0 < 2*x := by omega
  have he := Nat.pow_le_pow_right hbase (show 396903 ≤ 400000 by norm_num)
  simp only [← pow_mul] at hpw hbound
  norm_num only at hpw hbound
  omega

private lemma recip_le_log_diff (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ)+1) ≤ Real.log ((n : ℝ)+1) - Real.log n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpos1 : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hpos1 hpos)
  rw [Real.log_div hpos1.ne' hpos.ne'] at h
  have heq : 1 - (((n : ℝ)+1) / n)⁻¹ = 1 / ((n : ℝ)+1) := by
    field_simp
    <;> ring
  rwa [heq] at h

/- Abel summation adapted from PR #2612 (https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2612), Apache-2.0. -/


private theorem abel_reciprocal_aux :
    let cheb := fun x : ℕ => ∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ); ∀ x y : ℕ, 1 ≤ x → x < y → (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)/p) = cheb y / y - cheb x / ((x : ℝ)+1) + ∑ n ∈ Finset.Ico (x+1) y, cheb n * (1/(n : ℝ)-1/((n : ℝ)+1)) := by
  intro cheb x y hx hxy
  have h_step : ∀ m : ℕ, cheb (m + 1) - cheb m =
      if (m + 1).Prime ∧ (m + 1) % 4 = 1 then Real.log ((m + 1 : ℕ) : ℝ) else 0 := by
    intro m
    dsimp only [cheb]
    have h_icc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext p
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not_mem : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [h_icc, Finset.filter_insert]
    split_ifs with hP
    · rw [Finset.sum_insert (fun h => h_not_mem (Finset.mem_filter.mp h).1)]
      ring
    · ring
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, y = x + 1 + d := ⟨y - (x + 1), by omega⟩
  induction d with
  | zero =>
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    have h_ioc : Finset.Ioc x (x + 1) = {x + 1} := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rw [h_ioc, Finset.filter_singleton]
    have hx1_ne : ((x : ℝ) + 1) ≠ 0 := by positivity
    have h_diff := h_step x
    split_ifs with hP
    · rw [Finset.sum_singleton]
      simp only [hP, and_self, ↓reduceIte] at h_diff
      push_cast at h_diff ⊢
      field_simp [hx1_ne]
      linarith
    · rw [Finset.sum_empty]
      simp only [hP, ↓reduceIte] at h_diff
      push_cast at h_diff ⊢
      field_simp [hx1_ne]
      linarith
  | succ d ih =>
    set m : ℕ := x + 1 + d
    have hxm : x < m := by omega
    have ih_m := ih hxm
    have h_add_assoc : x + 1 + (d + 1) = m + 1 := by omega
    rw [h_add_assoc]
    have h_ioc : Finset.Ioc x (m + 1) = insert (m + 1) (Finset.Ioc x m) := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have h_not_ioc : m + 1 ∉ Finset.Ioc x m := by simp
    have h_ico : Finset.Ico (x + 1) (m + 1) = insert m (Finset.Ico (x + 1) m) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have h_not_ico : m ∉ Finset.Ico (x + 1) m := by simp
    rw [h_ioc, Finset.filter_insert, h_ico, Finset.sum_insert h_not_ico]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    have hm1_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
    have h_diff := h_step m
    have h_alg : cheb (m + 1) / ((m + 1 : ℕ) : ℝ) - cheb x / ((x : ℝ) + 1) +
        (cheb m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) +
          ∑ n ∈ Finset.Ico (x + 1) m, cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
        (cheb m / (m : ℝ) - cheb x / ((x : ℝ) + 1) +
          ∑ n ∈ Finset.Ico (x + 1) m, cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) +
        (cheb (m + 1) - cheb m) / ((m + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp [hm_ne, hm1_ne]
      ring
    rw [h_alg, ← ih_m, h_diff]
    split_ifs with hP
    · rw [Finset.sum_insert (fun h => h_not_ioc (Finset.mem_filter.mp h).1)]
      ring
    · simp

private lemma prime_sum_bound (X x y : ℕ) (hxX : X ≤ x) (hx : 1 ≤ x) (hxy : x < y)
    (hupper : ∀ n : ℕ, X ≤ n → 1 ≤ n →
      (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)) ≤ (51 / 100 : ℝ) * n) :
    (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)/p) ≤
      (51 / 100 : ℝ) + (51 / 100 : ℝ) * (Real.log (y : ℝ) - Real.log ((x : ℝ)+1)) := by
  let theta : ℕ → ℝ := fun n => ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)
  have htheta (n : ℕ) : 0 ≤ theta n := by
    apply Finset.sum_nonneg
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hprime.one_le)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hybound : theta y / y ≤ (51/100 : ℝ) := by
    apply (div_le_iff₀ hypos).2
    exact hupper y (by omega) (by omega)
  have hxnonneg : 0 ≤ theta x / ((x : ℝ)+1) := by positivity
  have hterm : ∀ n ∈ Finset.Ico (x+1) y,
      theta n * (1/(n : ℝ)-1/((n : ℝ)+1)) ≤
        (51/100 : ℝ) * (Real.log ((n : ℝ)+1) - Real.log n) := by
    intro n hn
    have hn : x+1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1pos : (0 : ℝ) < (n : ℝ)+1 := by positivity
    have hd : 0 ≤ 1/(n : ℝ)-1/((n : ℝ)+1) := by
      apply sub_nonneg.mpr
      exact one_div_le_one_div_of_le hnpos (by linarith)
    have heq : (n : ℝ)*(1/(n : ℝ)-1/((n : ℝ)+1)) = 1/((n : ℝ)+1) := by
      field_simp
      <;> ring
    calc
      _ ≤ ((51/100 : ℝ)*n)*(1/(n : ℝ)-1/((n : ℝ)+1)) :=
        mul_le_mul_of_nonneg_right (hupper n (by omega) (by omega)) hd
      _ = (51/100 : ℝ) * (1/((n : ℝ)+1)) := by rw [mul_assoc, heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left (recip_le_log_diff n (by omega)) (by norm_num)
  have hsum : (∑ n ∈ Finset.Ico (x+1) y, theta n * (1/(n : ℝ)-1/((n : ℝ)+1))) ≤
      (51/100 : ℝ)*(Real.log (y : ℝ)-Real.log ((x : ℝ)+1)) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico (x+1) y, (51/100 : ℝ) * (Real.log ((n : ℝ)+1) - Real.log n) := Finset.sum_le_sum hterm
      _ = (51/100 : ℝ) * ∑ n ∈ Finset.Ico (x+1) y, (Real.log ((n : ℝ)+1) - Real.log n) := by rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        simpa using Finset.sum_Ico_sub (fun n : ℕ => Real.log (n : ℝ)) (show x+1 ≤ y by omega)
  have ha := abel_reciprocal_aux x y hx hxy
  change (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)/p) =
    theta y / y - theta x / ((x : ℝ)+1) + ∑ n ∈ Finset.Ico (x+1) y, theta n * (1/(n : ℝ)-1/((n : ℝ)+1)) at ha
  linarith


/- Root count adapted from PR #2604 (https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2604), Apache-2.0. -/

/-- The number of square roots of `-1` among the residues below a prime: one for the prime two,
two for the primes congruent to one mod four, and none for the primes congruent to three mod four.
The counting happens in the field of residues: a root `x` comes with `-x`, and the two standard
representatives below the prime are the value of `x` and the prime minus that value. -/
private theorem root_card_aux :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ p : ℕ, Nat.Prime p → (roots 1 p).card = if p=2 then 1 else if p % 4 = 1 then 2 else 0 := by
  intro roots p hp
  letI : Fact p.Prime := ⟨hp⟩
  have h1p : 1 < p := Nat.Prime.one_lt hp
  -- Unfold the local definition once, so that every later goal is a plain finset statement.
  have hroots : ∀ a q : ℕ, roots a q = Finset.filter (fun r => q ∣ r^2 + a) (Finset.range q) :=
    fun _ _ => rfl
  have key : ∀ r : ℕ, ((r^2 + 1 : ℕ) : ZMod p) = (r : ZMod p)^2 + 1 := by
    intro r
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  -- Membership in the filtered range says that the cast is a square root of minus one.
  have hmem : ∀ r : ℕ, r ∈ roots 1 p ↔ r < p ∧ (r : ZMod p)^2 = -1 := by
    intro r
    rw [hroots]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hdvd⟩
      refine ⟨hlt, neg_eq_iff_eq_neg.mp (neg_eq_iff_add_eq_zero.mpr ?_ )⟩
      rw [← key]
      exact (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mpr hdvd
    · rintro ⟨hlt, hroot⟩
      refine ⟨hlt, (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mp (key r ▸ ?_)⟩
      exact neg_eq_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mpr hroot)
  -- Going back from a root in the field to divisibility of the standard representative.
  have hdvd : ∀ r : ℕ, r < p → (r : ZMod p)^2 = -1 → p ∣ r^2 + 1 := by
    intro r hr hroot
    have h0 : ((r^2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [key]
      exact neg_eq_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mpr hroot)
    exact (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mp h0
  rcases hp.eq_two_or_odd with rfl | hodd
  · -- The even prime: the only root below two is one.
    have hset : (Finset.filter (fun r => 2 ∣ r^2 + 1) (Finset.range 2) : Finset ℕ) = {1} := by
      decide
    rw [hroots, hset, Finset.card_singleton]
    exact by decide
  · haveI hnz : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
    have hpos : p ≠ 2 := by omega
    have hfour : p % 4 = 1 ∨ p % 4 = 3 := by omega
    by_cases h1 : p % 4 = 1
    · -- Minus one is a square: pick a root and list its two representatives.
      obtain ⟨x, hx⟩ : ∃ y : ZMod p, y^2 = -1 := by
        obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega : p % 4 ≠ 3)
        exact ⟨y, by rw [pow_two]; exact hy.symm⟩
      have hval : x.val < p := ZMod.val_lt x
      have hcoe : (x.val : ZMod p) = x := @ZMod.natCast_zmod_val p hnz x
      have hsqv : (x.val : ZMod p)^2 = -1 := by rw [hcoe]; exact hx
      have had : p ∣ x.val^2 + 1 := hdvd x.val hval hsqv
      have hxv : 0 < x.val := by
        by_contra hz
        have hz2 : x.val = 0 := Nat.eq_zero_of_not_pos hz
        have hd : p ∣ 1 := by simpa [hz2] using had
        have : p ≤ 1 := Nat.le_of_dvd (by omega : (0 : ℕ) < 1) hd
        omega
      have hsub : p - x.val < p := by omega
      -- The negation of a root is the representative obtained by subtracting from the prime.
      have hpx : ((p - x.val : ℕ) : ZMod p) = -x := by
        rw [Nat.cast_sub (Nat.le_of_lt hval), ZMod.natCast_self, zero_sub, hcoe]
      have hmain : roots 1 p = {x.val, p - x.val} := by
        apply Finset.ext
        intro r
        have hiff : r ∈ ({x.val, p - x.val} : Finset ℕ) ↔ r = x.val ∨ r = p - x.val := by simp
        rw [hmem, hiff]
        constructor
        · rintro ⟨hr, hroot⟩
          have h2 : (r : ZMod p)^2 = x^2 := by rw [hx]; exact hroot
          have h3 : (r : ZMod p) = x ∨ (r : ZMod p) = -x := sq_eq_sq_iff_eq_or_eq_neg.mp h2
          rcases h3 with h | h
          · exact Or.inl (by
              have hc : ZMod.val (r : ZMod p) = ZMod.val x := congrArg ZMod.val h
              rwa [ZMod.val_natCast_of_lt hr] at hc)
          · exact Or.inr (by
              have hn : (r : ZMod p) = ((p - x.val : ℕ) : ZMod p) := by rw [hpx, h]
              have hc : ZMod.val (r : ZMod p) = ZMod.val ((p - x.val : ℕ) : ZMod p) :=
                congrArg ZMod.val hn
              rwa [ZMod.val_natCast_of_lt hr, ZMod.val_natCast_of_lt hsub] at hc)
        · rintro (h | h)
          · subst h
            exact ⟨hval, hsqv⟩
          · subst h
            refine ⟨hsub, ?_⟩
            rw [hpx, neg_sq, ← hcoe]
            exact hsqv
      have hne : x.val ≠ p - x.val := by omega
      rw [if_neg hpos, if_pos h1]
      exact Finset.card_eq_two.mpr ⟨x.val, p - x.val, hne, hmain⟩
    · -- Minus one is not a square: the filtered range is empty.
      have h3 : p % 4 = 3 := by
        rcases hfour with h | h
        · exact absurd h h1
        · exact h
      have hempty : roots 1 p = ∅ := by
        apply Finset.ext
        intro r
        rw [hmem]
        constructor
        · rintro ⟨_, hroot⟩
          exact absurd h3 (ZMod.mod_four_ne_three_of_sq_eq_neg_one hroot)
        · exact fun h => absurd h (by simp)
      rw [if_neg hpos, if_neg h1, hempty, Finset.card_empty]


theorem PEqualNP.Outside.L_quadratic_primes_levent_root_prime_harmonic :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); ∃ X : ℕ, ∀ x ≥ X, (∑ p ∈ primes x, ((roots 1 p).card : ℝ) * Real.log (p : ℝ)/p) ≤ (2/5 : ℝ)*Real.log (x : ℝ) := by
  intro roots primes
  obtain ⟨X, hX⟩ := cheb_mod4_eventual
  have hloglim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogev : ∀ᶠ x : ℕ in Filter.atTop, (100 : ℝ) ≤ Real.log x :=
    hloglim.eventually (Filter.eventually_ge_atTop 100)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlogev
  refine ⟨max X (max N 2), ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxN : N ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx : (100 : ℝ) ≤ Real.log x := hN x hxN
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  let S : Finset ℕ := primes x
  by_cases hs : S.Nonempty
  · let y : ℕ := S.max' hs
    have hyS : y ∈ S := S.max'_mem hs
    have hydata := Finset.mem_filter.mp hyS
    have hyinterval := Finset.mem_Ioc.mp hydata.1
    have hxy : x < y := hyinterval.1
    have hyprime : Nat.Prime y := hydata.2.1
    have hcut := cutoff_cube x y (by omega) hydata.2.2
    have hypos : (0 : ℝ) < y := by exact_mod_cast hyprime.pos
    have hreal : (y : ℝ)^3 ≤ ((2 : ℝ)*x)^4 := by exact_mod_cast hcut
    have hlogpow := Real.log_le_log (show 0 < (y : ℝ)^3 by positivity) hreal
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hxpos.ne'] at hlogpow
    have hlogy : 3*Real.log y ≤ 4*(Real.log 2+Real.log x) := by simpa using hlogpow
    have hloglower : Real.log (x : ℝ) ≤ Real.log ((x : ℝ)+1) := Real.log_le_log hxpos (by linarith)
    have hup : ∀ n : ℕ, X ≤ n → 1 ≤ n →
        (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)) ≤ (51/100 : ℝ)*n := by
      intro n hn hn1
      exact (hX n hn hn1).2
    have hps := prime_sum_bound X x y hxX (by omega) hxy hup
    let A : Finset ℕ := S.filter (fun p => p % 4 = 1)
    let C : Finset ℕ := (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1)
    have hsub : A ⊆ C := by
      intro p hp
      obtain ⟨hpS, hpmod⟩ := Finset.mem_filter.mp hp
      have hpdata := Finset.mem_filter.mp hpS
      have hpint := Finset.mem_Ioc.mp hpdata.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpint.1, S.le_max' p hpS⟩, hpdata.2.1, hpmod⟩
    have hnonneg : ∀ p ∈ C, p ∉ A → 0 ≤ Real.log (p : ℝ)/p := by
      intro p hp _
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (by positivity)
    have hsubsum := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    have heq : (∑ p ∈ S, ((roots 1 p).card : ℝ)*Real.log (p : ℝ)/p) =
        2 * ∑ p ∈ A, Real.log (p : ℝ)/p := by
      calc
        _ = ∑ p ∈ S, if p % 4 = 1 then 2*(Real.log (p : ℝ)/p) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpd := Finset.mem_filter.mp hp
          have hpp : Nat.Prime p := hpd.2.1
          have hxp : x < p := (Finset.mem_Ioc.mp hpd.1).1
          have hpne : p ≠ 2 := by omega
          have hcard := root_card_aux p hpp
          change (roots 1 p).card = _ at hcard
          by_cases hm : p % 4 = 1
          · simp [hm, hpne] at hcard
            simp [hm, hcard, mul_div_assoc]
          · simp [hm, hpne] at hcard
            simp [hm, hcard]
        _ = _ := by
          rw [Finset.mul_sum]
          exact (Finset.sum_filter _ _).symm
    rw [heq]
    have hh : (∑ p ∈ A, Real.log (p : ℝ)/p) ≤
        (51/100 : ℝ) + (51/100 : ℝ)*(Real.log y-Real.log ((x : ℝ)+1)) := le_trans hsubsum hps
    nlinarith
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ p ∈ S, ((roots 1 p).card : ℝ)*Real.log (p : ℝ)/p) ≤ _
    rw [hempty]
    simp only [Finset.sum_empty]
    have : 0 ≤ Real.log (x : ℝ) := by linarith
    positivity
