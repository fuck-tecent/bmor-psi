import Mathlib

namespace PEqualNP.Outside

private theorem qp100_proper_base {x n : ℕ} (hn : n ∈ Finset.Ioc x (2 * x))
    (hvm : ArithmeticFunction.vonMangoldt (n ^ 2 + 1) ≠ 0) (hnprime : ¬ (n ^ 2 + 1).Prime) :
    ∃ p k : ℕ, p.Prime ∧ Odd k ∧ 3 ≤ k ∧ n ^ 2 + 1 = p ^ k ∧ p ^ 3 ≤ (2 * x) ^ 2 + 1 := by
  have hn_bounds : x < n ∧ n ≤ 2 * x := Finset.mem_Ioc.mp hn
  have hn_pos : 1 ≤ n := by omega
  have hpp : IsPrimePow (n ^ 2 + 1) := by
    rw [ArithmeticFunction.vonMangoldt_apply] at hvm
    split_ifs at hvm with h
    · exact h
    · exact False.elim (hvm rfl)
  rcases (isPrimePow_nat_iff (n ^ 2 + 1)).mp hpp with ⟨p, k, hp, _, hpk⟩
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    rw [hk1, pow_one] at hpk
    exact hnprime (hpk ▸ hp)
  have hodd : Odd k := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | hodd
    · exfalso
      have hsq_eq : (p ^ m) ^ 2 = n ^ 2 + 1 := by
        calc
          (p ^ m) ^ 2 = p ^ m * p ^ m := sq (p ^ m)
          _ = p ^ (m + m) := (pow_add p m m).symm
          _ = p ^ k := by rw [hm]
          _ = n ^ 2 + 1 := hpk
      have hn_lt : n + 1 ≤ p ^ m := by
        by_contra hle
        have hpm_le : p ^ m ≤ n := not_lt.mp hle
        have hpm_sq : (p ^ m) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hpm_le 2
        omega
      have hstep : (n + 1) ^ 2 ≤ (p ^ m) ^ 2 := Nat.pow_le_pow_left hn_lt 2
      nlinarith
    · exact hodd
  have hk3 : 3 ≤ k := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hp3_le : p ^ 3 ≤ (2 * x) ^ 2 + 1 := by
    calc
      p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk3
      _ = n ^ 2 + 1 := hpk
      _ ≤ (2 * x) ^ 2 + 1 := Nat.add_le_add_right (Nat.pow_le_pow_left hn_bounds.2 2) 1
  exact ⟨p, k, hp, hodd, hk3, hpk.symm, hp3_le⟩

private theorem qp100_decomp {x n : ℕ} (hx : 2 ≤ x)
    (hn : n ∈ (Finset.Ioc x (2 * x)).filter
      (fun n => ArithmeticFunction.vonMangoldt (n ^ 2 + 1) ≠ 0 ∧ ¬ (n ^ 2 + 1).Prime)) :
    ∃ z : ℕ × ℕ, z.1 < ⌊2 * (x : ℝ) ^ (2 / 3 : ℝ)⌋₊ ∧
      z.2 < ⌊6 * Real.log (2 * (x : ℝ))⌋₊ ∧ n ^ 2 + 1 = (z.1 + 1) ^ (z.2 + 1) := by
  rcases Finset.mem_filter.mp hn with ⟨hn_ioc, hvm, hnprime⟩
  rcases qp100_proper_base hn_ioc hvm hnprime with ⟨p, k, hp, _, hk3, hpk, hp3⟩
  have hp3_8x2_nat : p ^ 3 ≤ 8 * x ^ 2 := by nlinarith [hp3, hx]
  have hp3_8x2 : (p : ℝ) ^ 3 ≤ 8 * (x : ℝ) ^ 2 := by exact_mod_cast hp3_8x2_nat
  have hrpow_cube : (2 * (x : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 8 * (x : ℝ) ^ 2 := by
    have h1 : ((x : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (x : ℝ) ^ 2 := by
      calc
        ((x : ℝ) ^ (2 / 3 : ℝ)) ^ 3
          = ((x : ℝ) ^ (2 / 3 : ℝ)) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
        _ = (x : ℝ) ^ ((2 / 3 : ℝ) * 3) := (Real.rpow_mul (Nat.cast_nonneg x) _ _).symm
        _ = (x : ℝ) ^ ((2 : ℕ) : ℝ) := by norm_num
        _ = (x : ℝ) ^ 2 := Real.rpow_natCast (x : ℝ) 2
    calc
      (2 * (x : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 8 * (((x : ℝ) ^ (2 / 3 : ℝ)) ^ 3) := by ring
      _ = 8 * (x : ℝ) ^ 2 := by rw [h1]
  have hp_real_le : (p : ℝ) ≤ 2 * (x : ℝ) ^ (2 / 3 : ℝ) := by
    set A := 2 * (x : ℝ) ^ (2 / 3 : ℝ)
    have hA_nonneg : 0 ≤ A := by positivity
    have hcube_le : (p : ℝ) ^ 3 ≤ A ^ 3 := by linarith [hp3_8x2, hrpow_cube]
    by_contra hlt
    have hgt : A < (p : ℝ) := not_le.mp hlt
    have hp_pos_r : (0 : ℝ) < (p : ℝ) := lt_of_le_of_lt hA_nonneg hgt
    have hquad_pos : 0 < (p : ℝ) ^ 2 + (p : ℝ) * A + A ^ 2 := by positivity
    have hdiff_pos : 0 < ((p : ℝ) - A) * ((p : ℝ) ^ 2 + (p : ℝ) * A + A ^ 2) :=
      mul_pos (sub_pos.mpr hgt) hquad_pos
    linarith [hcube_le, hdiff_pos, (by ring : (p : ℝ) ^ 3 - A ^ 3 = ((p : ℝ) - A) * ((p : ℝ) ^ 2 + (p : ℝ) * A + A ^ 2))]
  have hp_le : p ≤ ⌊2 * (x : ℝ) ^ (2 / 3 : ℝ)⌋₊ := Nat.le_floor hp_real_le
  have hn_le_2x : n ≤ 2 * x := (Finset.mem_Ioc.mp hn_ioc).2
  have h2pow_nat : 2 ^ k ≤ (2 * x) ^ 3 := by
    have h1 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
    have h2 : n ^ 2 ≤ (2 * x) ^ 2 := Nat.pow_le_pow_left hn_le_2x 2
    nlinarith [h1, hpk, h2, hx]
  have h2pow_real : ((2 : ℝ) ^ k) ≤ (2 * (x : ℝ)) ^ 3 := by exact_mod_cast h2pow_nat
  have hlog_le : (k : ℝ) * Real.log 2 ≤ 3 * Real.log (2 * (x : ℝ)) := by
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((2 * (x : ℝ)) ^ 3) :=
      Real.log_le_log (by positivity) h2pow_real
    simpa [Real.log_pow] using h1
  have hk_real_le : (k : ℝ) ≤ 6 * Real.log (2 * (x : ℝ)) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [Real.log_two_gt_d9]
  have hk_le : k ≤ ⌊6 * Real.log (2 * (x : ℝ))⌋₊ := Nat.le_floor hk_real_le
  have hp_pos : 1 ≤ p := hp.pos
  refine ⟨(p - 1, k - 1), by dsimp; omega, by dsimp; omega, ?_⟩
  dsimp
  have ha : p - 1 + 1 = p := by omega
  have hb : k - 1 + 1 = k := by omega
  rw [ha, hb, hpk]

private theorem qp100_card_bound (x : ℕ) (hx : 2 ≤ x) :
    ((((Finset.Ioc x (2 * x)).filter
      (fun n => ArithmeticFunction.vonMangoldt (n ^ 2 + 1) ≠ 0 ∧ ¬ (n ^ 2 + 1).Prime)).card : ℝ)) ≤
    12 * (x : ℝ) ^ (2 / 3 : ℝ) * Real.log (2 * (x : ℝ)) := by
  set U := (Finset.Ioc x (2 * x)).filter
    (fun n => ArithmeticFunction.vonMangoldt (n ^ 2 + 1) ≠ 0 ∧ ¬ (n ^ 2 + 1).Prime)
  set P_max := ⌊2 * (x : ℝ) ^ (2 / 3 : ℝ)⌋₊
  set K_max := ⌊6 * Real.log (2 * (x : ℝ))⌋₊
  let g : ℕ → ℕ × ℕ := fun n =>
    if h : n ∈ U then Classical.choose (qp100_decomp hx h) else (0, 0)
  have hg_eq : ∀ {n : ℕ} (hn : n ∈ U), n ^ 2 + 1 = ((g n).1 + 1) ^ ((g n).2 + 1) := by
    intro n hn
    simp only [g, hn, ↓reduceDIte]
    exact (Classical.choose_spec (qp100_decomp hx hn)).2.2
  have hsub : U.image g ⊆ Finset.range P_max ×ˢ Finset.range K_max := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    simp only [g, hn, ↓reduceDIte, Finset.mem_product, Finset.mem_range]
    have hspec := Classical.choose_spec (qp100_decomp hx hn)
    exact ⟨hspec.1, hspec.2.1⟩
  have hinj : Set.InjOn g U := by
    intro n1 hn1 n2 hn2 heq
    have hs1 := hg_eq hn1
    have hs2 := hg_eq hn2
    have hsq_eq : n1 ^ 2 + 1 = n2 ^ 2 + 1 := by rw [hs1, hs2, heq]
    nlinarith
  have hcard_nat : U.card ≤ P_max * K_max := by
    calc
      U.card = (U.image g).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range P_max ×ˢ Finset.range K_max).card := Finset.card_le_card hsub
      _ = P_max * K_max := by simp only [Finset.card_product, Finset.card_range]
  have hcard_real : (U.card : ℝ) ≤ (P_max : ℝ) * (K_max : ℝ) := by exact_mod_cast hcard_nat
  have h2x_ge1 : (1 : ℝ) ≤ 2 * (x : ℝ) := by
    have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hlog_nonneg : 0 ≤ Real.log (2 * (x : ℝ)) := Real.log_nonneg h2x_ge1
  have hP_le : (P_max : ℝ) ≤ 2 * (x : ℝ) ^ (2 / 3 : ℝ) := Nat.floor_le (by positivity)
  have hK_le : (K_max : ℝ) ≤ 6 * Real.log (2 * (x : ℝ)) := Nat.floor_le (by positivity)
  have hPK_le : (P_max : ℝ) * (K_max : ℝ) ≤ 12 * (x : ℝ) ^ (2 / 3 : ℝ) * Real.log (2 * (x : ℝ)) := by
    have h1 : (P_max : ℝ) * (K_max : ℝ) ≤
        (2 * (x : ℝ) ^ (2 / 3 : ℝ)) * (6 * Real.log (2 * (x : ℝ))) :=
      mul_le_mul hP_le hK_le (Nat.cast_nonneg K_max) (by positivity)
    linarith
  exact le_trans hcard_real hPK_le

theorem L_quadratic_primes_levent_prime_values_power_mass :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let pp := fun x : ℕ => ∑ n ∈ (block x).filter (fun n => ¬ Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1); ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ x ≥ X, pp x ≤ ε*x := by
  intro block pp ε hε
  set M : ℕ := ⌈11664 / ε⌉₊ + 2
  refine ⟨M ^ 9, fun x hx => ?_⟩
  have hM_ge2 : 2 ≤ M := by omega
  have hx_ge2 : 2 ≤ x := by
    calc
      2 ≤ 2 ^ 9 := by decide
      _ ≤ M ^ 9 := Nat.pow_le_pow_left hM_ge2 9
      _ ≤ x := hx
  set U := (block x).filter
    (fun n => ArithmeticFunction.vonMangoldt (n ^ 2 + 1) ≠ 0 ∧ ¬ (n ^ 2 + 1).Prime)
  have hpp_eq : pp x = ∑ n ∈ U, ArithmeticFunction.vonMangoldt (n ^ 2 + 1) := by
    dsimp only [pp, U]
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h0 : ArithmeticFunction.vonMangoldt (n ^ 2 + 1) = 0
    · simp [h0]
    · simp [h0]
  have hx2_r : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_ge2
  have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
  have h2x_ge1 : (1 : ℝ) ≤ 2 * (x : ℝ) := by linarith
  have hlog_nonneg : 0 ≤ Real.log (2 * (x : ℝ)) := Real.log_nonneg h2x_ge1
  have hpp_le_card : pp x ≤ (U.card : ℝ) * (3 * Real.log (2 * (x : ℝ))) := by
    rw [hpp_eq]
    calc
      (∑ n ∈ U, ArithmeticFunction.vonMangoldt (n ^ 2 + 1))
        ≤ ∑ _n ∈ U, (3 * Real.log (2 * (x : ℝ))) := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            have hn_le_2x : n ≤ 2 * x := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
            have hn2_le_nat : n ^ 2 + 1 ≤ (2 * x) ^ 3 := by
              have h2 : n ^ 2 ≤ (2 * x) ^ 2 := Nat.pow_le_pow_left hn_le_2x 2
              nlinarith [h2, hx_ge2]
            have hn2_le_real : ((n ^ 2 + 1 : ℕ) : ℝ) ≤ (2 * (x : ℝ)) ^ 3 := by
              exact_mod_cast hn2_le_nat
            have hn2_pos : (0 : ℝ) < ((n ^ 2 + 1 : ℕ) : ℝ) := by positivity
            have hlog1 : Real.log ((n ^ 2 + 1 : ℕ) : ℝ) ≤ Real.log ((2 * (x : ℝ)) ^ 3) :=
              Real.log_le_log hn2_pos hn2_le_real
            rw [Real.log_pow] at hlog1
            exact le_trans ArithmeticFunction.vonMangoldt_le_log (by simpa using hlog1)
      _ = (U.card : ℝ) * (3 * Real.log (2 * (x : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (U.card : ℝ) ≤ 12 * (x : ℝ) ^ (2 / 3 : ℝ) * Real.log (2 * (x : ℝ)) :=
    qp100_card_bound x hx_ge2
  have hpp_36 : pp x ≤ 36 * (x : ℝ) ^ (2 / 3 : ℝ) * Real.log (2 * (x : ℝ)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 3 * Real.log (2 * (x : ℝ)))
    nlinarith [hpp_le_card, h1, sq (Real.log (2 * (x : ℝ)))]
  set t : ℝ := (x : ℝ) ^ (1 / 9 : ℝ)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hx_pos (1 / 9 : ℝ)
  have ht9 : t ^ 9 = (x : ℝ) := by
    calc
      t ^ 9 = t ^ ((9 : ℕ) : ℝ) := (Real.rpow_natCast t 9).symm
      _ = (x : ℝ) ^ ((1 / 9 : ℝ) * 9) := (Real.rpow_mul (le_of_lt hx_pos) _ _).symm
      _ = (x : ℝ) ^ (1 : ℝ) := by norm_num
      _ = (x : ℝ) := Real.rpow_one (x : ℝ)
  have ht6 : t ^ 6 = (x : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      t ^ 6 = t ^ ((6 : ℕ) : ℝ) := (Real.rpow_natCast t 6).symm
      _ = (x : ℝ) ^ ((1 / 9 : ℝ) * 6) := (Real.rpow_mul (le_of_lt hx_pos) _ _).symm
      _ = (x : ℝ) ^ (2 / 3 : ℝ) := by norm_num
  have hlog_18t : Real.log (2 * (x : ℝ)) ≤ 18 * t := by
    have h2x_le_sq : 2 * (x : ℝ) ≤ (x : ℝ) ^ 2 := by
      have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_ge2
      nlinarith
    have h2x_le_t18 : 2 * (x : ℝ) ≤ t ^ 18 := by
      calc
        2 * (x : ℝ) ≤ (x : ℝ) ^ 2 := h2x_le_sq
        _ = (t ^ 9) ^ 2 := by rw [ht9]
        _ = t ^ 18 := by ring
    have hl1 : Real.log (2 * (x : ℝ)) ≤ Real.log (t ^ 18) :=
      Real.log_le_log (by positivity) h2x_le_t18
    rw [Real.log_pow] at hl1
    have hl2 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht_pos
    have hl1' : Real.log (2 * (x : ℝ)) ≤ 18 * Real.log t := by simpa using hl1
    linarith
  have hlog_sq : Real.log (2 * (x : ℝ)) ^ 2 ≤ (18 * t) ^ 2 := by
    nlinarith [hlog_nonneg, hlog_18t]
  have hpp_t8 : pp x ≤ 11664 * t ^ 8 := by
    rw [← ht6] at hpp_36
    have ht6_nonneg : 0 ≤ 36 * t ^ 6 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hlog_sq ht6_nonneg
    linarith [hpp_36, h1, (by ring : 36 * t ^ 6 * (18 * t) ^ 2 = 11664 * t ^ 8)]
  have hM_le_t : (M : ℝ) ≤ t := by
    have hMx_real : (M : ℝ) ^ 9 ≤ (x : ℝ) := by exact_mod_cast hx
    have hr := Real.rpow_le_rpow (by positivity) hMx_real (by norm_num : (0 : ℝ) ≤ 1 / 9)
    have hM9 : ((M : ℝ) ^ 9) ^ (1 / 9 : ℝ) = (M : ℝ) := by
      calc
        ((M : ℝ) ^ 9) ^ (1 / 9 : ℝ)
          = ((M : ℝ) ^ ((9 : ℕ) : ℝ)) ^ (1 / 9 : ℝ) := by rw [Real.rpow_natCast]
        _ = (M : ℝ) ^ (((9 : ℕ) : ℝ) * (1 / 9 : ℝ)) :=
            (Real.rpow_mul (Nat.cast_nonneg M) _ _).symm
        _ = (M : ℝ) ^ (1 : ℝ) := by norm_num
        _ = (M : ℝ) := Real.rpow_one (M : ℝ)
    rwa [hM9] at hr
  have hdiv_le_t : 11664 / ε ≤ t := by
    have hc : 11664 / ε ≤ (⌈11664 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hMc : (⌈11664 / ε⌉₊ : ℝ) ≤ (M : ℝ) := by
      dsimp only [M]
      push_cast
      linarith
    exact le_trans hc (le_trans hMc hM_le_t)
  have h11664_le : 11664 ≤ ε * t := by
    have hm := mul_le_mul_of_nonneg_right hdiv_le_t (le_of_lt hε)
    rw [div_mul_cancel₀ 11664 (ne_of_gt hε)] at hm
    linarith
  have ht8_nonneg : 0 ≤ t ^ 8 := by positivity
  have hfinal : 11664 * t ^ 8 ≤ ε * (x : ℝ) := by
    calc
      11664 * t ^ 8 ≤ (ε * t) * t ^ 8 := mul_le_mul_of_nonneg_right h11664_le ht8_nonneg
      _ = ε * t ^ 9 := by ring
      _ = ε * (x : ℝ) := by rw [ht9]
  exact le_trans hpp_t8 hfinal

end PEqualNP.Outside
