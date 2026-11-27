import Mathlib

namespace PEqualNP.Outside

private noncomputable def qp108_cheb (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)

private theorem qp108_cheb_nonneg (n : ℕ) : 0 ≤ qp108_cheb n := by
  refine Finset.sum_nonneg (fun p hp => ?_)
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact Real.log_nonneg (by exact_mod_cast hp1)

private theorem qp108_cheb_upper :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → qp108_cheb n ≤ (51 / 100 : ℝ) * (n : ℝ) := by
  have hcop : Nat.Coprime 1 4 := by decide
  have htend_real := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 4) (a := 1) hcop
  have htend_nat := htend_real.comp tendsto_natCast_atTop_atTop
  have hset_eq : ∀ n : ℕ,
      (Finset.Icc 1 n).filter (fun p => p.Prime ∧ p % 4 = 1) =
      (Finset.Ioc 0 n).filter (fun p => p.Prime ∧ p ≡ 1 [MOD 4]) := by
    intro n
    rw [Finset.ext_iff]
    intro p
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    change (1 ≤ p ∧ p ≤ n) ∧ p.Prime ∧ p % 4 = 1 ↔ (0 < p ∧ p ≤ n) ∧ p.Prime ∧ p % 4 = 1 % 4
    constructor
    · rintro ⟨⟨h1, h2⟩, hp, hm⟩
      exact ⟨⟨by omega, h2⟩, hp, by omega⟩
    · rintro ⟨⟨h1, h2⟩, hp, hm⟩
      exact ⟨⟨by omega, h2⟩, hp, by omega⟩
  have hcongr : (fun n : ℕ => qp108_cheb n / (n : ℝ)) =
      ((fun t : ℝ => (∑ p ∈ (Finset.Ioc 0 ⌊t⌋₊).filter (fun p => p.Prime ∧ p ≡ 1 [MOD 4]),
        Real.log (p : ℝ)) / t) ∘ (fun n : ℕ => (n : ℝ))) := by
    funext n
    simp only [Function.comp_apply, Nat.floor_natCast, qp108_cheb, hset_eq n]
  rw [← hcongr] at htend_nat
  have htot : ((Nat.totient 4 : ℝ))⁻¹ = (1 / 2 : ℝ) := by
    have ht4 : Nat.totient 4 = 2 := by decide
    rw [ht4]
    norm_num
  rw [htot] at htend_nat
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp htend_nat) (1 / 100 : ℝ) (by norm_num)
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left N₀ 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hdist : dist (qp108_cheb n / (n : ℝ)) (1 / 2 : ℝ) < 1 / 100 := hN₀ n hn0
  rw [Real.dist_eq] at hdist
  have hdiv_le : qp108_cheb n / (n : ℝ) ≤ 51 / 100 := by linarith [(abs_lt.mp hdist).2]
  have hmul := mul_le_mul_of_nonneg_right hdiv_le (le_of_lt hn_pos)
  rw [div_mul_cancel₀ _ (ne_of_gt hn_pos)] at hmul
  linarith

private theorem qp108_roots_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ((Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)).card =
      if p % 4 = 1 then 2 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with hp1 | hp3
  · simp only [hp1, ↓reduceIte]
    have hp_ne3 : p % 4 ≠ 3 := by omega
    obtain ⟨u, hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr hp_ne3
    have hu_sq : u ^ 2 = -1 := by simpa [sq] using hu.symm
    have hu_ne : u ≠ -u := by
      intro h_eq
      have h2u : (2 : ZMod p) * u = 0 := by linear_combination h_eq
      have h2_nz : (2 : ZMod p) ≠ 0 := by
        intro h0
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        have hge : 2 ≤ p := hp.two_le
        omega
      have hu0 : u = 0 := (mul_eq_zero.mp h2u).resolve_left h2_nz
      rw [hu0] at hu_sq
      norm_num at hu_sq
    have hval_ne : u.val ≠ (-u).val := by
      intro h
      have hc := congr_arg (fun n : ℕ => (n : ZMod p)) h
      simp only [ZMod.natCast_zmod_val] at hc
      exact hu_ne hc
    have h_set : (Finset.range p).filter (fun r => p ∣ r ^ 2 + 1) = {u.val, (-u).val} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hr_lt, hr_dvd⟩
        have hz0 : ((r ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ p).mpr hr_dvd
        push_cast at hz0
        have hfac : ((r : ZMod p) - u) * ((r : ZMod p) + u) = 0 := by
          linear_combination hz0 - hu_sq
        rcases mul_eq_zero.mp hfac with h1 | h2
        · left
          have hru : (r : ZMod p) = u := sub_eq_zero.mp h1
          rw [← hru, ZMod.val_natCast_of_lt hr_lt]
        · right
          have hru : (r : ZMod p) = -u := eq_neg_of_add_eq_zero_left h2
          rw [← hru, ZMod.val_natCast_of_lt hr_lt]
      · rintro (rfl | rfl)
        · refine ⟨ZMod.val_lt u, (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
          push_cast
          rw [ZMod.natCast_zmod_val, hu_sq, neg_add_cancel]
        · refine ⟨ZMod.val_lt (-u), (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
          push_cast
          rw [ZMod.natCast_zmod_val, neg_sq, hu_sq, neg_add_cancel]
    rw [h_set, Finset.card_pair hval_ne]
  · have hp_not1 : p % 4 ≠ 1 := by omega
    simp only [hp_not1, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ hr_dvd
    have hz0 : ((r ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hr_dvd
    push_cast at hz0
    have h_ex : IsSquare (-1 : ZMod p) := ⟨(r : ZMod p), by linear_combination -hz0⟩
    have hp_ne3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp h_ex
    exact hp_ne3 hp3

private theorem qp108_abel_reciprocal (x y : ℕ) (hx : 1 ≤ x) (hxy : x < y) :
    (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ) / (p : ℝ)) =
    qp108_cheb y / (y : ℝ) - qp108_cheb x / ((x : ℝ) + 1) +
      ∑ n ∈ Finset.Ico (x + 1) y, qp108_cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  have h_step : ∀ m : ℕ, qp108_cheb (m + 1) - qp108_cheb m =
      if (m + 1).Prime ∧ (m + 1) % 4 = 1 then Real.log ((m + 1 : ℕ) : ℝ) else 0 := by
    intro m
    dsimp only [qp108_cheb]
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
    have h_alg : qp108_cheb (m + 1) / ((m + 1 : ℕ) : ℝ) - qp108_cheb x / ((x : ℝ) + 1) +
        (qp108_cheb m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) +
          ∑ n ∈ Finset.Ico (x + 1) m, qp108_cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
        (qp108_cheb m / (m : ℝ) - qp108_cheb x / ((x : ℝ) + 1) +
          ∑ n ∈ Finset.Ico (x + 1) m, qp108_cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) +
        (qp108_cheb (m + 1) - qp108_cheb m) / ((m + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp [hm_ne, hm1_ne]
      ring
    rw [h_alg, ← ih_m, h_diff]
    split_ifs with hP
    · rw [Finset.sum_insert (fun h => h_not_ioc (Finset.mem_filter.mp h).1)]
      ring
    · simp

private theorem qp108_log_step {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hu_pos : 0 < (n : ℝ) / ((n : ℝ) + 1) := div_pos hn_pos hn1_pos
  have hlog := Real.log_le_sub_one_of_pos hu_pos
  rw [Real.log_div (ne_of_gt hn_pos) (ne_of_gt hn1_pos)] at hlog
  have hsub : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
    field_simp [ne_of_gt hn1_pos]
    ring
  push_cast
  linarith

private theorem qp108_sum_ico_sub (f : ℕ → ℝ) (a d : ℕ) :
    (∑ n ∈ Finset.Ico a (a + d), (f (n + 1) - f n)) = f (a + d) - f a := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hico : Finset.Ico a (a + (d + 1)) = insert (a + d) (Finset.Ico a (a + d)) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot : a + d ∉ Finset.Ico a (a + d) := by simp
    rw [hico, Finset.sum_insert hnot, ih]
    have heq : a + (d + 1) = a + d + 1 := by omega
    rw [heq]
    ring

private theorem qp108_pow_to_floor {E1 E2 x p : ℕ} (hE1 : 0 < E1) (hx1 : 1 ≤ x)
    (hratio : (E2 : ℝ) / (E1 : ℝ) ≤ (132301 : ℝ) / 100000)
    (hp_pow : p ^ E1 ≤ (2 * x) ^ E2) :
    p ≤ ⌊(2 * (x : ℝ)) ^ ((132301 : ℝ) / 100000)⌋₊ := by
  have hE1_r : (0 : ℝ) < (E1 : ℝ) := by exact_mod_cast hE1
  have hpow_r : (p : ℝ) ^ E1 ≤ (2 * (x : ℝ)) ^ E2 := by exact_mod_cast hp_pow
  have hr := Real.rpow_le_rpow (by positivity) hpow_r (by positivity : 0 ≤ 1 / (E1 : ℝ))
  have hp_lhs : ((p : ℝ) ^ E1) ^ (1 / (E1 : ℝ)) = (p : ℝ) := by
    calc
      ((p : ℝ) ^ E1) ^ (1 / (E1 : ℝ))
        = ((p : ℝ) ^ (E1 : ℝ)) ^ (1 / (E1 : ℝ)) := by rw [Real.rpow_natCast]
      _ = (p : ℝ) ^ ((E1 : ℝ) * (1 / (E1 : ℝ))) := (Real.rpow_mul (Nat.cast_nonneg p) _ _).symm
      _ = (p : ℝ) ^ (1 : ℝ) := by
          congr 1
          field_simp [ne_of_gt hE1_r]
      _ = (p : ℝ) := Real.rpow_one (p : ℝ)
  have hx_rhs : ((2 * (x : ℝ)) ^ E2) ^ (1 / (E1 : ℝ)) = (2 * (x : ℝ)) ^ ((E2 : ℝ) / (E1 : ℝ)) := by
    calc
      ((2 * (x : ℝ)) ^ E2) ^ (1 / (E1 : ℝ))
        = ((2 * (x : ℝ)) ^ (E2 : ℝ)) ^ (1 / (E1 : ℝ)) := by rw [Real.rpow_natCast]
      _ = (2 * (x : ℝ)) ^ ((E2 : ℝ) * (1 / (E1 : ℝ))) :=
          (Real.rpow_mul (by positivity) _ _).symm
      _ = (2 * (x : ℝ)) ^ ((E2 : ℝ) / (E1 : ℝ)) := by
          congr 1
          ring
  rw [hp_lhs, hx_rhs] at hr
  have h2x_ge1 : (1 : ℝ) ≤ 2 * (x : ℝ) := by
    have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    linarith
  exact Nat.le_floor (le_trans hr (Real.rpow_le_rpow_of_exponent_le h2x_ge1 hratio))

private theorem qp108_harmonic_gen (E1 E2 : ℕ) (hE1 : 0 < E1)
    (hratio : (E2 : ℝ) / (E1 : ℝ) ≤ (132301 : ℝ) / 100000) :
    ∃ X : ℕ, ∀ x ≥ X,
      (∑ p ∈ (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter (fun p => Nat.Prime p ∧ p ^ E1 ≤ (2 * x) ^ E2),
        ((((Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)).card : ℝ) * Real.log (p : ℝ) / (p : ℝ))) ≤
      (2 / 5 : ℝ) * Real.log (x : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := qp108_cheb_upper
  refine ⟨max N₀ (2 ^ 120), fun x hx => ?_⟩
  have hx_N0 : N₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx_2120 : 2 ^ 120 ≤ x := le_trans (le_max_right _ _) hx
  have hx_ge2 : 2 ≤ x := le_trans (by decide : 2 ≤ 2 ^ 120) hx_2120
  have hx_ge1 : 1 ≤ x := le_trans (by omega : 1 ≤ 2) hx_ge2
  have hx_r2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_ge2
  have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog_x_60 : 60 ≤ Real.log (x : ℝ) := by
    have hpow_r : (2 : ℝ) ^ 120 ≤ (x : ℝ) := by exact_mod_cast hx_2120
    have hl1 : Real.log ((2 : ℝ) ^ 120) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hpow_r
    rw [Real.log_pow] at hl1
    have hl1' : (120 : ℝ) * Real.log 2 ≤ Real.log (x : ℝ) := by simpa using hl1
    linarith [Real.log_two_gt_d9]
  set P_set := (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter
    (fun p => Nat.Prime p ∧ p ^ E1 ≤ (2 * x) ^ E2)
  set y : ℕ := ⌊(2 * (x : ℝ)) ^ ((132301 : ℝ) / 100000)⌋₊
  have h2x_le_y : 2 * x ≤ y := by
    have h1_le_2x : (1 : ℝ) ≤ 2 * (x : ℝ) := by linarith
    have hr := Real.rpow_le_rpow_of_exponent_le h1_le_2x (by norm_num : (1 : ℝ) ≤ 132301 / 100000)
    rw [Real.rpow_one] at hr
    have hcast : ((2 * x : ℕ) : ℝ) ≤ (2 * (x : ℝ)) ^ ((132301 : ℝ) / 100000) := by
      simpa using hr
    exact Nat.le_floor hcast
  have hxy : x < y := lt_of_lt_of_le (by omega : x < 2 * x) h2x_le_y
  have hsum_to_ioc :
      (∑ p ∈ P_set,
        ((((Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)).card : ℝ) * Real.log (p : ℝ) / (p : ℝ))) ≤
      2 * (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1),
        Real.log (p : ℝ) / (p : ℝ)) := by
    have hflt : (∑ p ∈ P_set.filter (fun p => p % 4 = 1), Real.log (p : ℝ) / (p : ℝ)) =
        ∑ p ∈ P_set, if p % 4 = 1 then Real.log (p : ℝ) / (p : ℝ) else 0 :=
      Finset.sum_filter (s := P_set) (p := fun p : ℕ => p % 4 = 1)
        (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ))
    have hrewrite :
        (∑ p ∈ P_set,
          ((((Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)).card : ℝ) * Real.log (p : ℝ) / (p : ℝ))) =
        2 * (∑ p ∈ P_set.filter (fun p => p % 4 = 1), Real.log (p : ℝ) / (p : ℝ)) := by
      rw [hflt, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rcases Finset.mem_filter.mp hp with ⟨hp_ioc, hp_prime, _⟩
      have hx_lt_p : x < p := (Finset.mem_Ioc.mp hp_ioc).1
      have hp_ne2 : p ≠ 2 := by omega
      rw [qp108_roots_odd_prime hp_prime hp_ne2]
      split_ifs <;> simp [mul_div_assoc]
    rw [hrewrite]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => ?_)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_P, hp_mod⟩
      rcases Finset.mem_filter.mp hp_P with ⟨hp_ioc, hp_prime, hp_pow⟩
      have hx_lt_p : x < p := (Finset.mem_Ioc.mp hp_ioc).1
      have hp_le_y : p ≤ y := qp108_pow_to_floor hE1 hx_ge1 hratio hp_pow
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hx_lt_p, hp_le_y⟩, hp_prime, hp_mod⟩
    · have hp1 : 1 ≤ p := le_trans hx_ge1 (le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1)
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp1)) (Nat.cast_nonneg p)
  have habel := qp108_abel_reciprocal x y hx_ge1 hxy
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    have : (2 : ℝ) < (y : ℝ) := by exact_mod_cast (lt_of_le_of_lt hx_ge2 hxy)
    linarith
  have hbound_y : qp108_cheb y / (y : ℝ) ≤ 51 / 100 := by
    have hy_N0 : N₀ ≤ y := le_trans hx_N0 (le_of_lt hxy)
    have hcy := hN₀ y hy_N0
    have hm := div_le_div_of_nonneg_right hcy (le_of_lt hy_pos)
    rwa [mul_div_cancel_right₀ _ (ne_of_gt hy_pos)] at hm
  have hbound_x_nonneg : 0 ≤ qp108_cheb x / ((x : ℝ) + 1) :=
    div_nonneg (qp108_cheb_nonneg x) (by positivity)
  have hico_le :
      (∑ n ∈ Finset.Ico (x + 1) y, qp108_cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) ≤
      (51 / 100 : ℝ) * (Real.log (y : ℝ) - Real.log (((x + 1 : ℕ) : ℝ))) := by
    calc
      (∑ n ∈ Finset.Ico (x + 1) y, qp108_cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        ≤ ∑ n ∈ Finset.Ico (x + 1) y,
            (51 / 100 : ℝ) * (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            have hn_ge : x + 1 ≤ n := (Finset.mem_Ico.mp hn).1
            have hn_N0 : N₀ ≤ n := le_trans hx_N0 (by omega)
            have hn1 : 1 ≤ n := by omega
            have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
            have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
            have hdiff_eq : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
              field_simp [ne_of_gt hn_pos, ne_of_gt hn1_pos]
              ring
            have hdiff_nonneg : 0 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
              rw [hdiff_eq]
              positivity
            have hc_le := mul_le_mul_of_nonneg_right (hN₀ n hn_N0) hdiff_nonneg
            have hsimp : ((51 / 100 : ℝ) * (n : ℝ)) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
                (51 / 100 : ℝ) * (1 / ((n : ℝ) + 1)) := by
              rw [hdiff_eq]
              field_simp [ne_of_gt hn_pos, ne_of_gt hn1_pos]
            rw [hsimp] at hc_le
            exact le_trans hc_le (mul_le_mul_of_nonneg_left (qp108_log_step hn1) (by norm_num))
      _ = (51 / 100 : ℝ) * (∑ n ∈ Finset.Ico (x + 1) y,
            (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ))) := by
            rw [← Finset.mul_sum]
      _ = (51 / 100 : ℝ) * (Real.log (y : ℝ) - Real.log (((x + 1 : ℕ) : ℝ))) := by
            obtain ⟨d, hd⟩ : ∃ d : ℕ, y = x + 1 + d := ⟨y - (x + 1), by omega⟩
            rw [hd, qp108_sum_ico_sub (fun k : ℕ => Real.log (k : ℝ)) (x + 1) d]
  have hlog_x_le_x1 : Real.log (x : ℝ) ≤ Real.log (((x + 1 : ℕ) : ℝ)) := by
    refine Real.log_le_log hx_pos ?_
    push_cast
    linarith
  have hlog_y_le : Real.log (y : ℝ) ≤
      ((132301 : ℝ) / 100000) * (Real.log 2 + Real.log (x : ℝ)) := by
    have hy_r : (y : ℝ) ≤ (2 * (x : ℝ)) ^ ((132301 : ℝ) / 100000) := Nat.floor_le (by positivity)
    have hl := Real.log_le_log hy_pos hy_r
    rw [Real.log_rpow (by positivity), Real.log_mul (by norm_num) (ne_of_gt hx_pos)] at hl
    exact hl
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [hsum_to_ioc, habel, hbound_y, hbound_x_nonneg, hico_le, hlog_x_le_x1, hlog_y_le,
    hlog2_le1, hlog2_nonneg, hlog_x_60]

private theorem qp108_e1_pos : (0 : ℕ) < 100000 := by omega
private theorem qp108_ratio_le : ((132301 : ℕ) : ℝ) / ((100000 : ℕ) : ℝ) ≤ (132301 : ℝ) / 100000 := by
  norm_num

private theorem qp109_ioc_card_le (x : ℕ) : (Finset.Ioc x (2 * x)).card ≤ x := by
  let f : ℕ → ℕ := fun n => n - (x + 1)
  have hsub : (Finset.Ioc x (2 * x)).image f ⊆ Finset.range x := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    rcases Finset.mem_Ioc.mp hn with ⟨h1, h2⟩
    exact Finset.mem_range.mpr (by dsimp [f]; omega)
  have hinj : Set.InjOn f (Finset.Ioc x (2 * x)) := by
    intro n1 hn1 n2 hn2 heq
    have h1 := (Finset.mem_Ioc.mp hn1).1
    have h2 := (Finset.mem_Ioc.mp hn2).1
    dsimp [f] at heq
    omega
  calc
    (Finset.Ioc x (2 * x)).card = ((Finset.Ioc x (2 * x)).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range x).card := Finset.card_le_card hsub
    _ = x := Finset.card_range x

private theorem qp109_scale_gen (E1 E2 : ℕ) (hE1 : 0 < E1)
    (hratio : (E2 : ℝ) / (E1 : ℝ) ≤ (132301 : ℝ) / 100000) :
    ∃ X : ℕ, ∀ x ≥ X,
      (∑ p ∈ (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter (fun p => Nat.Prime p ∧ p ^ E1 ≤ (2 * x) ^ E2),
        ((((Finset.Ioc x (2 * x)).filter (fun n => p ^ E1 ≤ n ^ E2)).card : ℝ) *
          (((Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)).card : ℝ) / (p : ℝ) * Real.log (p : ℝ))) ≤
      (2 / 5 : ℝ) * ((x : ℝ) * Real.log (x : ℝ)) := by
  obtain ⟨X, hX⟩ := qp108_harmonic_gen E1 E2 hE1 hratio
  refine ⟨X, fun x hx => ?_⟩
  set primes_g := (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter
    (fun p => Nat.Prime p ∧ p ^ E1 ≤ (2 * x) ^ E2)
  set roots_1 := fun p : ℕ => (Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)
  have hmodel_le :
      (∑ p ∈ primes_g,
        ((((Finset.Ioc x (2 * x)).filter (fun n => p ^ E1 ≤ n ^ E2)).card : ℝ) *
          ((roots_1 p).card : ℝ) / (p : ℝ) * Real.log (p : ℝ))) ≤
      (x : ℝ) * (∑ p ∈ primes_g, (((roots_1 p).card : ℝ) * Real.log (p : ℝ) / (p : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hlog_nonneg : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    have hwin_nat : ((Finset.Ioc x (2 * x)).filter (fun n => p ^ E1 ≤ n ^ E2)).card ≤ x :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (qp109_ioc_card_le x)
    have hwin_r : (((Finset.Ioc x (2 * x)).filter (fun n => p ^ E1 ≤ n ^ E2)).card : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast hwin_nat
    have hfac_nonneg : 0 ≤ ((roots_1 p).card : ℝ) * Real.log (p : ℝ) / (p : ℝ) := by positivity
    calc
      (((Finset.Ioc x (2 * x)).filter (fun n => p ^ E1 ≤ n ^ E2)).card : ℝ) *
          ((roots_1 p).card : ℝ) / (p : ℝ) * Real.log (p : ℝ)
        = (((Finset.Ioc x (2 * x)).filter (fun n => p ^ E1 ≤ n ^ E2)).card : ℝ) *
            (((roots_1 p).card : ℝ) * Real.log (p : ℝ) / (p : ℝ)) := by ring
      _ ≤ (x : ℝ) * (((roots_1 p).card : ℝ) * Real.log (p : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hwin_r hfac_nonneg
  have hmain := mul_le_mul_of_nonneg_left (hX x hx) (Nat.cast_nonneg x)
  linarith

theorem L_quadratic_primes_levent_scale_input :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let budget := fun x : ℕ => (x : ℝ) * Real.log (x : ℝ); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let model := fun a x : ℕ => ∑ p ∈ primes x, ((window x p).card : ℝ) * ((roots a p).card : ℝ) / p * Real.log (p : ℝ); ∃ X : ℕ, ∀ x ≥ X, model 1 x ≤ (2/5 : ℝ)*budget x := by
  intro block budget roots primes window model
  exact qp109_scale_gen 100000 132301 qp108_e1_pos qp108_ratio_le

end PEqualNP.Outside
