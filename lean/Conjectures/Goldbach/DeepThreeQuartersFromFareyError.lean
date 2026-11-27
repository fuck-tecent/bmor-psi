import Mathlib

namespace Conjectures.Goldbach.DeepThreeQuartersFromFareyError_aux

lemma prod_ratio_le_card_add_one :
    ∀ S : Finset ℕ, (∀ p ∈ S, 2 ≤ p) →
      ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (S.card : ℝ) + 1 := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S IH =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨m, hmS, hmax⟩ : ∃ m, m ∈ S ∧ ∀ p ∈ S, p ≤ m :=
        ⟨S.max' hne, Finset.max'_mem S hne, fun p hp => Finset.le_max' S p hp⟩
      have h2m : 2 ≤ m := hS m hmS
      have hmcast : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2m
      have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
      have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      have hcard : S.card ≤ m - 1 := by
        have hsub : S ⊆ Finset.Icc 2 m := fun p hp =>
          Finset.mem_Icc.mpr ⟨hS p hp, hmax p hp⟩
        have h1 := Finset.card_le_card hsub
        rw [Nat.card_Icc] at h1
        omega
      have hkey : ((m : ℝ) / ((m : ℝ) - 1)) * (S.card : ℝ) ≤ (S.card : ℝ) + 1 := by
        have hr : (S.card : ℝ) ≤ (m : ℝ) - 1 := by
          have h2 : (S.card : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
          have h3 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
        have hsplit : ((m : ℝ) / ((m : ℝ) - 1)) * (S.card : ℝ)
            = (S.card : ℝ) + (S.card : ℝ) / ((m : ℝ) - 1) := by
          field_simp [hm1.ne']
          ring
        have h4 : (S.card : ℝ) / ((m : ℝ) - 1) ≤ 1 := (div_le_one hm1).mpr hr
        rw [hsplit]
        linarith
      have hIH : ∏ p ∈ S.erase m, ((p : ℝ) / ((p : ℝ) - 1))
          ≤ ((S.erase m).card : ℝ) + 1 :=
        IH (S.erase m) (Finset.erase_ssubset hmS)
          (fun p hp => hS p (Finset.mem_of_mem_erase hp))
      calc ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
          = (∏ p ∈ S.erase m, ((p : ℝ) / ((p : ℝ) - 1))) * ((m : ℝ) / ((m : ℝ) - 1)) :=
            (Finset.prod_erase_mul S (fun p => (p : ℝ) / ((p : ℝ) - 1)) hmS).symm
        _ = ((m : ℝ) / ((m : ℝ) - 1)) * ∏ p ∈ S.erase m, ((p : ℝ) / ((p : ℝ) - 1)) := by
            ring
        _ ≤ ((m : ℝ) / ((m : ℝ) - 1)) * (((S.erase m).card : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hIH (div_pos hm0 hm1).le
        _ = ((m : ℝ) / ((m : ℝ) - 1)) * (S.card : ℝ) := by
            have h1 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
            rw [Finset.card_erase_of_mem hmS, Nat.cast_sub h1]
            ring
        _ ≤ (S.card : ℝ) + 1 := hkey

lemma one_le_prod_pred :
    ∀ S : Finset ℕ, (∀ p ∈ S, 2 ≤ p) → (1 : ℝ) ≤ ∏ p ∈ S, ((p : ℝ) - 1) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hS
    rw [Finset.prod_insert ha]
    have h2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS a (Finset.mem_insert_self a s)
    nlinarith [ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))]

theorem totient_ratio_le (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / (Nat.totient q : ℝ) ≤ 1 + Real.log q / Real.log 2 := by
  have hqpos : 0 < q := by omega
  have hmem : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hphi : (Nat.totient q : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqpos
    exact h1.ne'
  have hB1 : (1 : ℝ) ≤ ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) :=
    one_le_prod_pred q.primeFactors hmem
  have hB : (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) ≠ 0 :=
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hB1))
  have hpred : ∀ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 :=
    fun p hp => by rw [Nat.cast_sub (by have := hmem p hp; omega), Nat.cast_one]
  have heq : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ))
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := Finset.prod_congr rfl hpred
  have hcast : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
      = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    calc (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
        = ((Nat.totient q * ∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_prod]
      _ = ((q * ∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) := by
          rw [Nat.totient_mul_prod_primeFactors]
      _ = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_prod, heq]
  have hmain : (q : ℝ) / (Nat.totient q : ℝ)
      = (∏ p ∈ q.primeFactors, (p : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
    refine (div_eq_div_iff hphi hB).mpr ?_
    calc (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1)
        = (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) := hcast.symm
      _ = (∏ p ∈ q.primeFactors, (p : ℝ)) * (Nat.totient q : ℝ) := by ring
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card = ∏ _ ∈ q.primeFactors, (2 : ℕ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ q.primeFactors, p := Finset.prod_le_prod (fun p hp => hmem p hp)
      _ ≤ q := Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  have hlog : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
    have h1 : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
      have h1' : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpow
      simpa using h1'
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    exact h2
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  calc (q : ℝ) / (Nat.totient q : ℝ)
      = (∏ p ∈ q.primeFactors, (p : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := hmain
    _ = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
        rw [Finset.prod_div_distrib]
    _ ≤ (q.primeFactors.card : ℝ) + 1 := prod_ratio_le_card_add_one q.primeFactors hmem
    _ ≤ 1 + Real.log q / Real.log 2 := by linarith

theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  field_simp

theorem expSum_norm_le_card (n : ℕ) (β : ℝ) :
    ‖∑ k ∈ Finset.Icc 1 n, Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)‖
      ≤ (n : ℝ) := by
  have hnorm (k : ℕ) : ‖Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    have h1 : Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (Complex.I * ((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ)) := by
      congr 1
      ring
    rw [h1, Complex.norm_exp_I_mul_ofReal]
  calc ‖∑ k ∈ Finset.Icc 1 n, Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ k ∈ Finset.Icc 1 n, ‖Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
    _ = ∑ _ ∈ Finset.Icc 1 n, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hnorm k
    _ = (n : ℝ) := by
        induction n with
        | zero => simp
        | succ m ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            push_cast
            ring

theorem expSum_norm_le_inv (n : ℕ) (β : ℝ) (hβ : β ≠ 0) (hβ' : |β| ≤ 1 / 2) :
    ‖∑ k ∈ Finset.Icc 1 n, Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 / (2 * |β|) := by
  have hsinlb : 2 * |β| ≤ |Real.sin (Real.pi * β)| := by
    have hx : |Real.pi * β| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      calc Real.pi * |β| ≤ Real.pi * (1 / 2) :=
            mul_le_mul_of_nonneg_left hβ' Real.pi_pos.le
        _ = Real.pi / 2 := by ring
    calc 2 * |β| = 2 / Real.pi * |Real.pi * β| := by
          rw [abs_mul, abs_of_pos Real.pi_pos]
          field_simp
      _ ≤ |Real.sin (Real.pi * β)| := Real.mul_abs_le_abs_sin hx
  have hsin0 : Real.sin (Real.pi * β) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hsinlb
    have h2 := abs_pos.mpr hβ
    linarith
  have hkey := norm_geometric_phase_sum_le hsin0 n
  have hshift (w : ℂ) (m : ℕ) :
      (∑ k ∈ Finset.Icc 1 m, w ^ k) = w * ∑ j ∈ Finset.range m, w ^ j := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, pow_succ]
        ring
  have hterm (k : ℕ) : Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (Complex.I * (2 * Real.pi * β : ℝ))) ^ k := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc ‖∑ k ∈ Finset.Icc 1 n, Complex.exp (((2 * Real.pi * ((k : ℝ) * β) : ℝ) : ℂ) * Complex.I)‖
      = ‖∑ k ∈ Finset.Icc 1 n, (Complex.exp (Complex.I * (2 * Real.pi * β : ℝ))) ^ k‖ := by
        apply congrArg norm
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
    _ = ‖(Complex.exp (Complex.I * (2 * Real.pi * β : ℝ)))
        * ∑ j ∈ Finset.range n, (Complex.exp (Complex.I * (2 * Real.pi * β : ℝ))) ^ j‖ :=
        congrArg norm (hshift _ n)
    _ = ‖∑ j ∈ Finset.range n, (Complex.exp (Complex.I * (2 * Real.pi * β : ℝ))) ^ j‖ := by
        rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    _ ≤ 1 / |Real.sin (Real.pi * β)| := hkey
    _ ≤ 1 / (2 * |β|) := by
        apply one_div_le_one_div_of_le
        · linarith [abs_pos.mpr hβ]
        · exact hsinlb

theorem dirichlet_nat (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ (q : ℝ) ≤ Real.sqrt n ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * Real.sqrt n) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hnR
  have hsqrtpos : (0 : ℝ) < Real.sqrt (n : ℝ) := lt_of_lt_of_le zero_lt_one hsqrt1
  have hBpos : (0 : ℕ) < ⌊Real.sqrt (n : ℝ)⌋₊ := Nat.floor_pos.mpr hsqrt1
  obtain ⟨s, hs, hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hBpos
  have hdpos : (0 : ℝ) < (s.den : ℝ) := Nat.cast_pos.mpr s.pos
  have hBposR : (0 : ℝ) < (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) := Nat.cast_pos.mpr hBpos
  rw [Rat.cast_def, mul_comm (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * (s.den : ℝ) - (s.num : ℝ)| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl, hu⟩ := abs_lt.mp hclose
  have ht0' : 0 ≤ t * (s.den : ℝ) := mul_nonneg ht0 hdpos.le
  have ht1' : t * (s.den : ℝ) ≤ (s.den : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right ht1 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < (s.num : ℝ) by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by
    exact_mod_cast (show (s.num : ℝ) < (s.den : ℝ) + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = (s.num : ℝ) := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
      _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by
    exact_mod_cast (show (s.num.natAbs : ℤ) ≤ (s.den : ℤ) by omega)
  have hdenle : (s.den : ℝ) ≤ Real.sqrt (n : ℝ) := by
    calc (s.den : ℝ) ≤ (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) := by exact_mod_cast hd
      _ ≤ Real.sqrt (n : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrtlt : Real.sqrt (n : ℝ) < (((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) + 1 :=
    Nat.lt_floor_add_one _
  rw [← hcast'] at hs
  refine ⟨s.num.natAbs, s.den, s.pos, hle, s.reduced, hdenle, ?_⟩
  calc |t - (s.num.natAbs : ℝ) / (s.den : ℝ)|
      ≤ 1 / ((s.den : ℝ) * ((((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ)) + 1)) := hs
    _ ≤ 1 / ((s.den : ℝ) * Real.sqrt (n : ℝ)) := by
        apply one_div_le_one_div_of_le (mul_pos hdpos hsqrtpos)
        exact mul_le_mul_of_nonneg_left hsqrtlt.le hdpos.le

theorem asymp_bound (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (e : ℝ) (he : 0 < e) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C₁ * (1 + Real.log n) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) +
          C₂ * (1 + Real.log n) * (n : ℝ) ^ ((2 : ℝ) / 3)
        ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + e) := by
  let δ : ℝ := min (e / 4) (1 / 24)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos he (by norm_num)) (by norm_num)
  have hδe : δ ≤ e / 4 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ24 : δ ≤ 1 / 24 := by
    dsimp [δ]
    exact min_le_right _ _
  let M : ℝ := 1 + 1 / δ
  have hM : 1 ≤ M := by
    dsimp [M]
    have hinv : 0 ≤ 1 / δ := one_div_nonneg.mpr hδpos.le
    linarith
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  let K : ℝ := C₁ * M ^ 2 + C₂ * M
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg hC₁ (sq_nonneg M)) (mul_nonneg hC₂ hM0)
  let X : ℝ := (K + 1) ^ (2 / e)
  let N : ℕ := max 1 ⌈X⌉₊
  refine ⟨N, ?_⟩
  intro n hnN
  have hn1 : 1 ≤ n := by
    exact (le_max_left 1 ⌈X⌉₊).trans (by simpa [N] using hnN)
  have hceil : ⌈X⌉₊ ≤ n := by
    exact (le_max_right 1 ⌈X⌉₊).trans (by simpa [N] using hnN)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnR0 : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one hnR1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR1
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ :=
    Real.log_natCast_le_rpow_div n hδpos
  have hpδ : (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnR1 hδpos.le
  have hlog1 : 1 + Real.log (n : ℝ) ≤ M * (n : ℝ) ^ δ := by
    calc 1 + Real.log (n : ℝ) ≤ 1 + (n : ℝ) ^ δ / δ := by linarith
      _ ≤ (n : ℝ) ^ δ + (n : ℝ) ^ δ / δ := by linarith
      _ = M * (n : ℝ) ^ δ := by dsimp [M]; ring
  have hleft0 : 0 ≤ 1 + Real.log (n : ℝ) := by
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR1
    linarith
  have hright0 : 0 ≤ M * (n : ℝ) ^ δ :=
    mul_nonneg hM0 (Real.rpow_nonneg hnR0 δ)
  have hsquare0 : (1 + Real.log (n : ℝ)) ^ 2 ≤ (M * (n : ℝ) ^ δ) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hleft0 hlog1
  have hpδ_sq : ((n : ℝ) ^ δ) ^ 2 = (n : ℝ) ^ (δ * 2) := by
    calc ((n : ℝ) ^ δ) ^ 2 = ((n : ℝ) ^ δ) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (n : ℝ) ^ (δ * 2) := (Real.rpow_mul hnR0 δ 2).symm
  have hsquare : (1 + Real.log (n : ℝ)) ^ 2 ≤ M ^ 2 * (n : ℝ) ^ (2 * δ) := by
    calc (1 + Real.log (n : ℝ)) ^ 2 ≤ (M * (n : ℝ) ^ δ) ^ 2 := hsquare0
      _ = M ^ 2 * ((n : ℝ) ^ δ) ^ 2 := by ring
      _ = M ^ 2 * (n : ℝ) ^ (δ * 2) := by rw [hpδ_sq]
      _ = M ^ 2 * (n : ℝ) ^ (2 * δ) := by rw [show δ * 2 = 2 * δ by ring]
  have hp34 : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hnR0 _
  have hterm1 : C₁ * (1 + Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) ≤
      C₁ * M ^ 2 * (n : ℝ) ^ (3 / 4 + 2 * δ) := by
    have h1 : C₁ * (1 + Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) ≤
        C₁ * (M ^ 2 * (n : ℝ) ^ (2 * δ)) * (n : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hC₁) hp34
    have h2 : C₁ * (M ^ 2 * (n : ℝ) ^ (2 * δ)) * (n : ℝ) ^ ((3 : ℝ) / 4)
        = C₁ * M ^ 2 * ((n : ℝ) ^ (2 * δ) * (n : ℝ) ^ ((3 : ℝ) / 4)) := by ring
    have h3 : C₁ * M ^ 2 * ((n : ℝ) ^ (2 * δ) * (n : ℝ) ^ ((3 : ℝ) / 4))
        = C₁ * M ^ 2 * (n : ℝ) ^ (2 * δ + (3 : ℝ) / 4) := by rw [Real.rpow_add hnpos]
    calc C₁ * (1 + Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 4)
        ≤ C₁ * (M ^ 2 * (n : ℝ) ^ (2 * δ)) * (n : ℝ) ^ ((3 : ℝ) / 4) := h1
      _ = C₁ * M ^ 2 * ((n : ℝ) ^ (2 * δ) * (n : ℝ) ^ ((3 : ℝ) / 4)) := h2
      _ = C₁ * M ^ 2 * (n : ℝ) ^ (2 * δ + (3 : ℝ) / 4) := h3
      _ = C₁ * M ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 4 + 2 * δ) := by
          rw [show (2 : ℝ) * δ + 3 / 4 = 3 / 4 + 2 * δ by ring]
  have hp23 : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hnR0 _
  have hterm2 : C₂ * (1 + Real.log (n : ℝ)) * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
      C₂ * M * (n : ℝ) ^ (2 / 3 + δ) := by
    have h1 : C₂ * (1 + Real.log (n : ℝ)) * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
        C₂ * (M * (n : ℝ) ^ δ) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog1 hC₂) hp23
    have h2 : C₂ * (M * (n : ℝ) ^ δ) * (n : ℝ) ^ ((2 : ℝ) / 3)
        = C₂ * M * ((n : ℝ) ^ δ * (n : ℝ) ^ ((2 : ℝ) / 3)) := by ring
    have h3 : C₂ * M * ((n : ℝ) ^ δ * (n : ℝ) ^ ((2 : ℝ) / 3))
        = C₂ * M * (n : ℝ) ^ (δ + (2 : ℝ) / 3) := by rw [Real.rpow_add hnpos]
    calc C₂ * (1 + Real.log (n : ℝ)) * (n : ℝ) ^ ((2 : ℝ) / 3)
        ≤ C₂ * (M * (n : ℝ) ^ δ) * (n : ℝ) ^ ((2 : ℝ) / 3) := h1
      _ = C₂ * M * ((n : ℝ) ^ δ * (n : ℝ) ^ ((2 : ℝ) / 3)) := h2
      _ = C₂ * M * (n : ℝ) ^ (δ + (2 : ℝ) / 3) := h3
      _ = C₂ * M * (n : ℝ) ^ ((2 : ℝ) / 3 + δ) := by
          rw [show δ + (2 : ℝ) / 3 = 2 / 3 + δ by ring]
  have hexp1 : (3 : ℝ) / 4 + 2 * δ ≤ 3 / 4 + e / 2 := by nlinarith [hδe]
  have hexp2 : (2 : ℝ) / 3 + δ ≤ 3 / 4 + e / 2 := by nlinarith [hδ24, he.le]
  have hpow1 : (n : ℝ) ^ (3 / 4 + 2 * δ) ≤ (n : ℝ) ^ (3 / 4 + e / 2) :=
    Real.rpow_le_rpow_of_exponent_le hnR1 hexp1
  have hpow2 : (n : ℝ) ^ (2 / 3 + δ) ≤ (n : ℝ) ^ (3 / 4 + e / 2) :=
    Real.rpow_le_rpow_of_exponent_le hnR1 hexp2
  have hcoef1 : 0 ≤ C₁ * M ^ 2 := mul_nonneg hC₁ (sq_nonneg M)
  have hcoef2 : 0 ≤ C₂ * M := mul_nonneg hC₂ hM0
  have hleft : C₁ * (1 + Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) +
      C₂ * (1 + Real.log (n : ℝ)) * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
      K * (n : ℝ) ^ (3 / 4 + e / 2) := by
    calc C₁ * (1 + Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (3 / 4) +
          C₂ * (1 + Real.log (n : ℝ)) * (n : ℝ) ^ (2 / 3) ≤
        C₁ * M ^ 2 * (n : ℝ) ^ (3 / 4 + e / 2) + C₂ * M * (n : ℝ) ^ (3 / 4 + e / 2) := add_le_add
          (hterm1.trans (mul_le_mul_of_nonneg_left hpow1 hcoef1))
          (hterm2.trans (mul_le_mul_of_nonneg_left hpow2 hcoef2))
      _ = K * (n : ℝ) ^ (3 / 4 + e / 2) := by dsimp [K]; ring
  have hXn : X ≤ (n : ℝ) := by
    calc X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
      _ ≤ (n : ℝ) := by exact_mod_cast hceil
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact Real.rpow_nonneg (by linarith [hK]) _
  have hmon : X ^ (e / 2) ≤ (n : ℝ) ^ (e / 2) :=
    Real.rpow_le_rpow hX0 hXn (by positivity)
  have hnest : X ^ (e / 2) = K + 1 := by
    dsimp [X]
    rw [← Real.rpow_mul (by linarith [hK] : (0 : ℝ) ≤ K + 1)]
    have hprod : (2 / e) * (e / 2) = 1 := by field_simp [he.ne']
    rw [hprod, Real.rpow_one]
  have hKpow : K ≤ (n : ℝ) ^ (e / 2) := by
    calc K ≤ K + 1 := by linarith
      _ = X ^ (e / 2) := hnest.symm
      _ ≤ (n : ℝ) ^ (e / 2) := hmon
  have hbase0 : 0 ≤ (n : ℝ) ^ (3 / 4 + e / 2) := Real.rpow_nonneg hnR0 _
  have hfinal : K * (n : ℝ) ^ (3 / 4 + e / 2) ≤ (n : ℝ) ^ (3 / 4 + e) := by
    calc K * (n : ℝ) ^ (3 / 4 + e / 2) ≤ (n : ℝ) ^ (e / 2) * (n : ℝ) ^ (3 / 4 + e / 2) :=
        mul_le_mul_of_nonneg_right hKpow hbase0
      _ = (n : ℝ) ^ ((e : ℝ) / 2 + (3 / 4 + e / 2)) :=
        (Real.rpow_add hnpos (e / 2) (3 / 4 + e / 2)).symm
      _ = (n : ℝ) ^ (3 / 4 + e) := by
        rw [show (e : ℝ) / 2 + (3 / 4 + e / 2) = 3 / 4 + e by ring]
  exact hleft.trans hfinal

end Conjectures.Goldbach.DeepThreeQuartersFromFareyError_aux

open Conjectures.Goldbach.DeepThreeQuartersFromFareyError_aux

set_option maxHeartbeats 800000 in
theorem Conjectures.Goldbach.DeepThreeQuartersFromFareyError :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊;
    let H := fun n : ℕ => 256 * Q₁ n * Q n;
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))};
    let I := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k : ℝ) * β);
    (∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ a q : ℕ, 1 ≤ q → a ≤ q → a.Coprime q → (q : ℝ) ≤ Real.sqrt n → ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Real.sqrt n) → ‖S n w ((a : ℝ) / (q : ℝ) + β) - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β‖ ≤ K * (Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)))) → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η) := by
  intro w E S Q Q₁ H wideArcs I
  rintro ⟨K, hK, N₀, hN₀⟩ η hη
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : (0:ℝ) < 1/Real.log 2 := one_div_pos.mpr hlog2
  have hc2 : (0:ℝ) < 1 + 1/Real.log 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := asymp_bound (2*K) (4*(1 + 1/Real.log 2))
    (by linarith) (by linarith) η hη
  refine ⟨max (max N₁ N₀) 8, ?_⟩
  intro n hn t ht hnot
  have h8 : (8:ℕ) ≤ n := le_trans (le_max_right _ _) hn
  have hN1n : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN0n : N₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) h8
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hsqrt0 : (0:ℝ) ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have hsqrtpos : (0:ℝ) < Real.sqrt (n:ℝ) := by rw [Real.sqrt_pos]; exact hnpos
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (n:ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hnR1
  have hsqrt2 : (2:ℝ) ≤ Real.sqrt (n:ℝ) := by
    have h4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 4 ≤ n by omega)
    have hs4 : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc (2:ℝ) = Real.sqrt (4:ℝ) := hs4.symm
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt h4
  have hL0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hnR1
  have hr13 : (1:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Real.one_le_rpow hnR1 (by norm_num)
  have hr13pos : (0:ℝ) < (n:ℝ)^(1/3:ℝ) := Real.rpow_pos_of_pos hnpos _
  have hQ1one : (1:ℕ) ≤ Q₁ n := by
    have h : (0:ℕ) < ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := Nat.floor_pos.mpr hr13
    have h2 : (0:ℕ) < Q₁ n := h
    omega
  have hQ1low : (n:ℝ)^(1/3:ℝ) < 2 * ((Q₁ n : ℕ):ℝ) := by
    have h1 := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    have h1' : (n:ℝ)^(1/3:ℝ) < ((Q₁ n : ℕ):ℝ) + 1 := h1
    have h3 : (1:ℝ) ≤ ((Q₁ n : ℕ):ℝ) := by exact_mod_cast hQ1one
    linarith
  obtain ⟨a, q, hq1, haq, hcop, hqs, hβbd⟩ := dirichlet_nat t ht.1 ht.2 n hn1
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
  have hq0 : (0:ℝ) ≤ (q:ℝ) := hqpos.le
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqn : (q:ℝ) ≤ (n:ℝ) := hqs.trans (Real.sqrt_le_iff.mpr ⟨hn0, by nlinarith⟩)
  have hφpos : (0:ℝ) < ((q.totient : ℕ):ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
  have hnot' : ¬ (∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ ((H n : ℕ):ℝ)/((q:ℝ)*(n:ℝ))) := hnot
  have h34 : (n:ℝ)^(3/4:ℝ) = Real.sqrt ((n:ℝ) * Real.sqrt (n:ℝ)) := by
    rw [Real.sqrt_mul hn0 (Real.sqrt (n:ℝ)), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hn0,
      ← Real.rpow_add hnpos]
    norm_num
  have hqn34 : Real.sqrt ((q:ℝ)*(n:ℝ)) ≤ (n:ℝ)^(3/4:ℝ) := by
    calc Real.sqrt ((q:ℝ)*(n:ℝ)) ≤ Real.sqrt (Real.sqrt (n:ℝ) * (n:ℝ)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hqs hn0)
      _ = Real.sqrt ((n:ℝ) * Real.sqrt (n:ℝ)) := by congr 1; ring
      _ = (n:ℝ)^(3/4:ℝ) := h34.symm
  have hnβ : (n:ℝ)*|t - (a:ℝ)/(q:ℝ)| ≤ Real.sqrt (n:ℝ) / (q:ℝ) := by
    have h1 : (n:ℝ)*|t - (a:ℝ)/(q:ℝ)| ≤ (n:ℝ) * (1/((q:ℝ)*Real.sqrt (n:ℝ))) :=
      mul_le_mul_of_nonneg_left hβbd hn0
    have h2 : (n:ℝ) * (1/((q:ℝ)*Real.sqrt (n:ℝ))) = Real.sqrt (n:ℝ)/(q:ℝ) := by
      have hs : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
        rw [← pow_two]; exact Real.sq_sqrt hn0
      calc (n:ℝ) * (1/((q:ℝ)*Real.sqrt (n:ℝ)))
          = (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) * (1/((q:ℝ)*Real.sqrt (n:ℝ))) := by rw [hs]
        _ = Real.sqrt (n:ℝ)/(q:ℝ) := by field_simp [hqpos.ne', hsqrtpos.ne'] <;> ring
    linarith
  have hprod : Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)
      ≤ (n:ℝ)^(3/4:ℝ) := by
    calc Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)
        ≤ Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.sqrt (Real.sqrt (n:ℝ)/(q:ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnβ) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((n:ℝ) * Real.sqrt (n:ℝ)) := by
          rw [← Real.sqrt_mul (mul_nonneg hq0 hn0) (Real.sqrt (n:ℝ)/(q:ℝ))]
          congr 1
          field_simp [hqpos.ne'] <;> ring
      _ = (n:ℝ)^(3/4:ℝ) := h34.symm
  have hsum : Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.log (n:ℝ) *
      (Real.log (n:ℝ) + Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|))
      ≤ 2 * ((n:ℝ)^(3/4:ℝ) * (1 + Real.log (n:ℝ))^2) := by
    have hp34 : (0:ℝ) ≤ (n:ℝ)^(3/4:ℝ) := Real.rpow_nonneg hn0 _
    have hb1 : Real.sqrt ((q:ℝ)*(n:ℝ)) * (Real.log (n:ℝ))^2
        ≤ (n:ℝ)^(3/4:ℝ) * (1 + Real.log (n:ℝ))^2 :=
      mul_le_mul hqn34 (by nlinarith) (by positivity) (by positivity)
    have hb2 : (Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)) * Real.log (n:ℝ)
        ≤ (n:ℝ)^(3/4:ℝ) * (1 + Real.log (n:ℝ))^2 :=
      (mul_le_mul_of_nonneg_right hprod hL0).trans
        (mul_le_mul_of_nonneg_left (by nlinarith) hp34)
    have key : Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.log (n:ℝ) *
        (Real.log (n:ℝ) + Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|))
        = Real.sqrt ((q:ℝ)*(n:ℝ)) * (Real.log (n:ℝ))^2
          + (Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)) * Real.log (n:ℝ) := by
      ring
    rw [key]
    linarith
  have hErr : K * (Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.log (n:ℝ) *
      (Real.log (n:ℝ) + Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)))
      ≤ 2 * K * (1 + Real.log (n:ℝ))^2 * (n:ℝ)^(3/4:ℝ) := by
    calc K * (Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.log (n:ℝ) *
        (Real.log (n:ℝ) + Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)))
        ≤ K * (2 * ((n:ℝ)^(3/4:ℝ) * (1 + Real.log (n:ℝ))^2)) :=
          mul_le_mul_of_nonneg_left hsum hK.le
      _ = 2 * K * (1 + Real.log (n:ℝ))^2 * (n:ℝ)^(3/4:ℝ) := by ring
  have hmu : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  have hmain_norm : ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
      ≤ (1:ℝ) / ((q.totient : ℕ):ℝ) * ‖I n (t - (a:ℝ)/(q:ℝ))‖ := by
    calc ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
        = (‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ / ‖((q.totient : ℕ) : ℂ)‖)
            * ‖I n (t - (a:ℝ)/(q:ℝ))‖ := by rw [norm_mul, norm_div]
      _ ≤ (1 / ((q.totient : ℕ):ℝ)) * ‖I n (t - (a:ℝ)/(q:ℝ))‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [Complex.norm_natCast]
          exact div_le_div_of_nonneg_right hmu hφpos.le
  have hratio : (q:ℝ) / ((q.totient : ℕ):ℝ) ≤ 1 + Real.log (q:ℝ) / Real.log 2 :=
    totient_ratio_le q hq1
  have hlogq : Real.log (q:ℝ) ≤ Real.log (n:ℝ) := Real.log_le_log hqpos hqn
  have hcomb : 1 + Real.log (q:ℝ) / Real.log 2 ≤ (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) := by
    have h2 : Real.log (q:ℝ)/Real.log 2 ≤ Real.log (n:ℝ)/Real.log 2 :=
      div_le_div_of_nonneg_right hlogq hlog2.le
    have h3 : Real.log (n:ℝ)/Real.log 2 = (1/Real.log 2) * Real.log (n:ℝ) := by ring
    calc 1 + Real.log (q:ℝ)/Real.log 2 ≤ 1 + (1/Real.log 2) * Real.log (n:ℝ) := by linarith
      _ ≤ (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) := by nlinarith [hL0, hinv]
  have hR := hN₀ n hN0n a q hq1 haq hcop hqs (t - (a:ℝ)/(q:ℝ)) hβbd
  rw [show (a:ℝ)/(q:ℝ) + (t - (a:ℝ)/(q:ℝ)) = t by ring] at hR
  have hmain : ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
      ≤ 4 * (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) * (n:ℝ)^(2/3:ℝ) := by
    clear hN₀ hR hErr hsum hprod hnβ h34 hqn34 hnot ht hn hN₁ hN1n hN0n h8
    have hbig : (0:ℝ) ≤ 4 * (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) * (n:ℝ)^(2/3:ℝ) := by
      have : (0:ℝ) ≤ (n:ℝ)^(2/3:ℝ) := Real.rpow_nonneg hn0 _
      have : (0:ℝ) ≤ (1 + Real.log (n:ℝ)) := by linarith
      have : (0:ℝ) ≤ (1 + 1/Real.log 2) := hc2.le
      positivity
    by_cases hcase : Q₁ n < q
    · have hqnat : Q₁ n + 1 ≤ q := hcase
      have hqbig : (n:ℝ)^(1/3:ℝ) < (q:ℝ) := by
        have h1 := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
        have h1' : (n:ℝ)^(1/3:ℝ) < ((Q₁ n : ℕ):ℝ) + 1 := h1
        have h2 : ((Q₁ n : ℕ):ℝ) + 1 ≤ (q:ℝ) := by exact_mod_cast hqnat
        linarith
      have hnq : (n:ℝ)/(q:ℝ) ≤ (n:ℝ)^(2/3:ℝ) := by
        have h1 : (n:ℝ)/(q:ℝ) < (n:ℝ)/((n:ℝ)^(1/3:ℝ)) := by
          rw [div_lt_div_iff₀ hqpos hr13pos]
          exact mul_lt_mul_of_pos_left hqbig hnpos
        have h2 : (n:ℝ)/((n:ℝ)^(1/3:ℝ)) = (n:ℝ)^(2/3:ℝ) := by
          rw [div_eq_iff hr13pos.ne', ← Real.rpow_add hnpos]
          norm_num
        linarith
      have hI : ‖I n (t - (a:ℝ)/(q:ℝ))‖ ≤ (n:ℝ) := expSum_norm_le_card n _
      calc ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
          ≤ (1:ℝ) / ((q.totient : ℕ):ℝ) * ‖I n (t - (a:ℝ)/(q:ℝ))‖ := hmain_norm
        _ ≤ (1:ℝ) / ((q.totient : ℕ):ℝ) * (n:ℝ) :=
            mul_le_mul_of_nonneg_left hI (by positivity)
        _ = ((q:ℝ)/((q.totient : ℕ):ℝ)) * ((n:ℝ)/(q:ℝ)) := by
            field_simp [hφpos.ne', hqpos.ne'] <;> ring
        _ ≤ (1 + Real.log (q:ℝ)/Real.log 2) * ((n:ℝ)^(2/3:ℝ)) :=
            mul_le_mul hratio hnq (by positivity) (by positivity)
        _ ≤ ((1 + 1/Real.log 2) * (1 + Real.log (n:ℝ))) * ((n:ℝ)^(2/3:ℝ)) :=
            mul_le_mul_of_nonneg_right hcomb (by positivity)
        _ ≤ 4 * (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) * (n:ℝ)^(2/3:ℝ) := by linarith
    · have hcase' : q ≤ Q₁ n := le_of_not_gt hcase
      have hQn1 : (1:ℝ) ≤ ((Q n : ℕ):ℝ) := by
        have h1 : (1:ℕ) ≤ Nat.log 2 (n+2) := by
          have := Nat.log_pos (b := 2) (by norm_num) (by omega : (2:ℕ) ≤ n+2)
          omega
        have h2 : (1:ℕ) ≤ Q n := by
          have : Q n = (Nat.log 2 (n+2))^2 := rfl
          nlinarith [h1]
        exact_mod_cast h2
      have hHcast : ((H n : ℕ):ℝ) = 256 * ((Q₁ n : ℕ):ℝ) * ((Q n : ℕ):ℝ) := by
        show ((256 * Q₁ n * Q n : ℕ):ℝ) = 256 * ((Q₁ n : ℕ):ℝ) * ((Q n : ℕ):ℝ)
        push_cast
        ring
      have hHpos : (0:ℝ) < ((H n : ℕ):ℝ) := by
        have h1 : (0:ℕ) < Q₁ n := by omega
        have h2 : (0:ℕ) < Q n := by
          have : (1:ℕ) ≤ Q n := by exact_mod_cast hQn1
          omega
        have h3 : (0:ℕ) < H n := by
          have : H n = 256 * Q₁ n * Q n := rfl
          exact Nat.mul_pos (Nat.mul_pos (by norm_num) h1) h2
        exact_mod_cast h3
      have hβgt : ((H n : ℕ):ℝ)/((q:ℝ)*(n:ℝ)) < |t - (a:ℝ)/(q:ℝ)| := by
        refine lt_of_not_ge (fun hcon => hnot' ⟨q, a, hq1, hcase', haq, hcop, hcon⟩)
      have hβpos : (0:ℝ) < |t - (a:ℝ)/(q:ℝ)| :=
        lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) (by positivity)) hβgt
      have hβne : t - (a:ℝ)/(q:ℝ) ≠ 0 := by
        intro h
        rw [h, abs_zero] at hβpos
        exact lt_irrefl _ hβpos
      have hβhalf : |t - (a:ℝ)/(q:ℝ)| ≤ 1/2 := by
        refine hβbd.trans ?_
        have h2 : (2:ℝ) ≤ (q:ℝ) * Real.sqrt (n:ℝ) := by
          calc (2:ℝ) = 1 * 2 := by ring
            _ ≤ (q:ℝ) * Real.sqrt (n:ℝ) := mul_le_mul hqR1 hsqrt2 (by norm_num) hq0
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hI : ‖I n (t - (a:ℝ)/(q:ℝ))‖ ≤ 1/(2*|t - (a:ℝ)/(q:ℝ)|) :=
        expSum_norm_le_inv n _ hβne hβhalf
      have hdenlb : (256:ℝ) * (n:ℝ)^(1/3:ℝ) ≤ 2 * ((H n : ℕ):ℝ) := by
        rw [hHcast]
        have h1 : (256:ℝ)*(n:ℝ)^(1/3:ℝ) ≤ 512 * ((Q₁ n : ℕ):ℝ) := by
          have h9 := hQ1low.le
          linarith
        calc (256:ℝ)*(n:ℝ)^(1/3:ℝ) ≤ 512 * ((Q₁ n : ℕ):ℝ) := h1
          _ = 512 * ((Q₁ n : ℕ):ℝ) * 1 := by ring
          _ ≤ 512 * ((Q₁ n : ℕ):ℝ) * ((Q n : ℕ):ℝ) :=
              mul_le_mul_of_nonneg_left hQn1 (by positivity)
          _ = 2 * (256 * ((Q₁ n : ℕ):ℝ) * ((Q n : ℕ):ℝ)) := by ring
      have hden : (n:ℝ)/(2*((H n : ℕ):ℝ)) ≤ (n:ℝ)^(2/3:ℝ) := by
        have hH2 : (0:ℝ) < 2*((H n : ℕ):ℝ) := by linarith
        rw [div_le_iff₀ hH2]
        have hnp : (n:ℝ) = (n:ℝ)^((2:ℝ)/3) * (n:ℝ)^((1:ℝ)/3) := by
          rw [← Real.rpow_add hnpos]
          norm_num
        have h1 : (n:ℝ)^((2:ℝ)/3) * (n:ℝ)^((1:ℝ)/3) ≤
            (n:ℝ)^((2:ℝ)/3) * (256 * (n:ℝ)^((1:ℝ)/3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hn0 _)
          linarith [Real.rpow_nonneg hn0 (1/3:ℝ)]
        have h2 : (n:ℝ)^((2:ℝ)/3) * (256 * (n:ℝ)^((1:ℝ)/3)) ≤
            (n:ℝ)^((2:ℝ)/3) * (2*((H n : ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_left hdenlb (Real.rpow_nonneg hn0 _)
        exact hnp.le.trans (h1.trans h2)
      calc ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
          ≤ (1:ℝ) / ((q.totient : ℕ):ℝ) * ‖I n (t - (a:ℝ)/(q:ℝ))‖ := hmain_norm
        _ ≤ (1:ℝ) / ((q.totient : ℕ):ℝ) * (1/(2*|t - (a:ℝ)/(q:ℝ)|)) :=
            mul_le_mul_of_nonneg_left hI (by positivity)
        _ ≤ (1:ℝ) / ((q.totient : ℕ):ℝ) * (1/(2*(((H n : ℕ):ℝ)/((q:ℝ)*(n:ℝ))))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h1 : (2:ℝ)*(((H n : ℕ):ℝ)/((q:ℝ)*(n:ℝ))) ≤ 2*|t - (a:ℝ)/(q:ℝ)| := by
              linarith [hβgt.le]
            exact one_div_le_one_div_of_le (by positivity) h1
        _ = ((q:ℝ)/((q.totient : ℕ):ℝ)) * ((n:ℝ)/(2*((H n : ℕ):ℝ))) := by
            field_simp [hφpos.ne', hqpos.ne', hHpos.ne'] <;> ring
        _ ≤ (1 + Real.log (q:ℝ)/Real.log 2) * ((n:ℝ)/(2*((H n : ℕ):ℝ))) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
        _ ≤ ((1 + 1/Real.log 2) * (1 + Real.log (n:ℝ))) * ((n:ℝ)/(2*((H n : ℕ):ℝ))) :=
            mul_le_mul_of_nonneg_right hcomb (by positivity)
        _ ≤ ((1 + 1/Real.log 2) * (1 + Real.log (n:ℝ))) * ((n:ℝ)^(2/3:ℝ)) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ ≤ 4 * (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) * (n:ℝ)^(2/3:ℝ) := by linarith
  have htri : ‖S n w t‖ ≤ ‖S n w t - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
      + ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖ := by
    have h1 : ‖S n w t‖ = ‖(S n w t - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ)))
        + ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ)))‖ := by
      congr 1
      ring
    rw [h1]
    exact norm_add_le _ _
  calc ‖S n w t‖ ≤ ‖S n w t - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖
      + ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n (t - (a:ℝ)/(q:ℝ))‖ := htri
    _ ≤ K * (Real.sqrt ((q:ℝ)*(n:ℝ)) * Real.log (n:ℝ) *
        (Real.log (n:ℝ) + Real.sqrt ((n:ℝ)*|t - (a:ℝ)/(q:ℝ)|)))
        + 4 * (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) * (n:ℝ)^(2/3:ℝ) := add_le_add hR hmain
    _ ≤ 2 * K * (1 + Real.log (n:ℝ))^2 * (n:ℝ)^(3/4:ℝ)
        + 4 * (1 + 1/Real.log 2) * (1 + Real.log (n:ℝ)) * (n:ℝ)^(2/3:ℝ) := add_le_add hErr (le_refl _)
    _ ≤ (n:ℝ)^(3/4 + η) := hN₁ n hN1n

