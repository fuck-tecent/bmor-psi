import Mathlib

private lemma norm_add_le_max {K : Type*} [SeminormedAddCommGroup K] [IsUltrametricDist K]
    (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max (x + y) y 0
  simpa [dist_eq_norm] using h

private lemma norm_sub_le_max {K : Type*} [SeminormedAddCommGroup K] [IsUltrametricDist K]
    (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using norm_add_le_max x (-y)

private lemma norm_add_eq_left {K : Type*} [SeminormedAddCommGroup K] [IsUltrametricDist K]
    {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  apply le_antisymm
  · exact (norm_add_le_max x y).trans (max_le le_rfl h.le)
  · by_contra hlt
    push_neg at hlt
    have h1 : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
      simpa [add_sub_cancel_right] using norm_sub_le_max (x + y) y
    exact not_lt_of_ge h1 (max_lt hlt h)

private lemma norm_tsum_nat_le {K : Type*} [NormedAddCommGroup K] [IsUltrametricDist K]
    {f : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hf : Summable f) (hbound : ∀ n, ‖f n‖ ≤ C) :
    ‖∑' n : ℕ, f n‖ ≤ C := by
  have hpart : ∀ N : ℕ, ‖∑ i ∈ Finset.range N, f i‖ ≤ C := by
    intro N
    induction N with
    | zero => simpa using hC
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (norm_add_le_max _ _).trans (max_le ih (hbound N))
  exact le_of_tendsto hf.tendsto_sum_tsum_nat.norm (Filter.Eventually.of_forall hpart)

private lemma real_pow_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg ha0 n]

private lemma real_pow_anti {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {m n : ℕ} (h : m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  nlinarith [pow_nonneg ha0 m, real_pow_le_one ha0 ha1 d]

private lemma real_pow_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    nlinarith [pow_nonneg ha0 n, pow_nonneg (ha0.trans hab) n]

private lemma real_pow_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {n : ℕ} (hn : 0 < n) :
    a ^ n < 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [pow_succ]
    nlinarith [pow_nonneg ha0 n, real_pow_le_one ha0 ha1.le n]

private lemma norm_embed_le_one {K : Type*} [NontriviallyNormedField K]
    [Fact (Nat.Prime 29)] [NormedAlgebra (Padic 29) K] (a : PadicInt 29) :
    ‖algebraMap (Padic 29) K (a : Padic 29)‖ ≤ 1 := by
  rw [Algebra.algebraMap_eq_smul_one]
  calc ‖(a : Padic 29) • (1 : K)‖
      ≤ ‖(a : Padic 29)‖ * ‖(1 : K)‖ := norm_smul_le _ _
    _ = ‖a‖ := by rw [norm_one, mul_one, PadicInt.norm_coe]
    _ ≤ 1 := PadicInt.norm_le_one a

private lemma add_one_le_pow_29 (v : ℕ) : v + 1 ≤ 29 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    omega

private lemma add_two_le_pow_29 {v : ℕ} (hv : 1 ≤ v) : v + 2 ≤ 29 ^ v := by
  cases v with
  | zero => omega
  | succ v =>
    clear hv
    induction v with
    | zero => norm_num
    | succ v ih =>
      rw [pow_succ]
      omega

private lemma multiplicity_29_le_sub_one (k : ℕ) : multiplicity 29 (k + 1) ≤ k := by
  have hdvd : 29 ^ multiplicity 29 (k + 1) ∣ k + 1 := by apply pow_multiplicity_dvd
  have hle : 29 ^ multiplicity 29 (k + 1) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdvd
  have h1 : multiplicity 29 (k + 1) + 1 ≤ 29 ^ multiplicity 29 (k + 1) := add_one_le_pow_29 _
  omega

private lemma multiplicity_29_succ_le (k : ℕ) : multiplicity 29 (k + 2) ≤ k := by
  by_cases h0 : multiplicity 29 (k + 2) = 0
  · omega
  · have hv : 1 ≤ multiplicity 29 (k + 2) := Nat.pos_of_ne_zero h0
    have hdvd : 29 ^ multiplicity 29 (k + 2) ∣ k + 2 := by apply pow_multiplicity_dvd
    have hle : 29 ^ multiplicity 29 (k + 2) ≤ k + 2 := Nat.le_of_dvd (by omega) hdvd
    have h2 : multiplicity 29 (k + 2) + 2 ≤ 29 ^ multiplicity 29 (k + 2) := add_two_le_pow_29 hv
    omega

private lemma two_mul_div_two_mul_succ (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
  have h2 : 2 ∣ n * (n + 1) := by
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨j * (2 * j + 1), by ring⟩
    · exact ⟨(2 * j + 1) * (j + 1), by ring⟩
  exact Nat.mul_div_cancel' h2

private lemma t_sub_self_norm_le {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] {r x : K} (hr29 : r ^ 14 = (29 : K)) (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (hn_norm : ∀ n : ℕ, 0 < n → ‖(n : K)‖ = ‖r‖ ^ (14 * multiplicity 29 n))
    (hx : ‖x‖ ≤ ‖r‖) :
    ‖(∑' k : ℕ, (-1 : K) ^ k * ((29 : K) * x) ^ (k + 1) / ((k + 1 : ℕ) : K)) / (29 : K) - x‖ ≤
      ‖r‖ ^ 4 := by
  let f : ℕ → K := fun k => (-1 : K) ^ k * ((29 : K) * x) ^ (k + 1) / ((k + 1 : ℕ) : K)
  have h29_norm : ‖(29 : K)‖ = ‖r‖ ^ 14 := by
    rw [← hr29, norm_pow]
  have h29_ne : (29 : K) ≠ 0 := norm_pos_iff.mp (by rw [h29_norm]; exact pow_pos hr0 14)
  have hfk_norm : ∀ k : ℕ,
      ‖f k‖ = ‖r‖ ^ (14 * (k + 1) - 14 * multiplicity 29 (k + 1)) * ‖x‖ ^ (k + 1) := by
    intro k
    dsimp only [f]
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_pow, norm_mul, h29_norm, mul_pow, ← pow_mul, hn_norm (k + 1) (Nat.succ_pos k)]
    have hm : multiplicity 29 (k + 1) ≤ k := multiplicity_29_le_sub_one k
    have hsplit : ‖r‖ ^ (14 * (k + 1)) =
        ‖r‖ ^ (14 * (k + 1) - 14 * multiplicity 29 (k + 1)) *
          ‖r‖ ^ (14 * multiplicity 29 (k + 1)) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hsplit]
    have hne : ‖r‖ ^ (14 * multiplicity 29 (k + 1)) ≠ 0 := pow_ne_zero _ hr0.ne'
    field_simp [hne]
  have hf_sum : Summable f := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg r) hr1) (fun k => ?_)
    rw [hfk_norm k]
    have h1 : ‖r‖ ^ (14 * (k + 1) - 14 * multiplicity 29 (k + 1)) ≤ 1 :=
      real_pow_le_one hr0.le hr1.le _
    have h2 : ‖x‖ ^ (k + 1) ≤ ‖r‖ ^ (k + 1) := real_pow_mono (norm_nonneg x) hx (k + 1)
    have h3 : ‖r‖ ^ (k + 1) ≤ ‖r‖ ^ k := real_pow_anti hr0.le hr1.le (Nat.le_succ k)
    nlinarith [pow_nonneg (norm_nonneg x) (k + 1)]
  have hf_tail_sum : Summable (fun k : ℕ => f (k + 1)) := (summable_nat_add_iff 1).mpr hf_sum
  have htail_bound : ∀ k : ℕ, ‖f (k + 1)‖ ≤ ‖r‖ ^ 30 := by
    intro k
    rw [hfk_norm (k + 1)]
    have hm : multiplicity 29 (k + 2) ≤ k := multiplicity_29_succ_le k
    have h1 : ‖r‖ ^ (14 * (k + 2) - 14 * multiplicity 29 (k + 2)) ≤ ‖r‖ ^ 28 :=
      real_pow_anti hr0.le hr1.le (by omega)
    have h2 : ‖x‖ ^ (k + 2) ≤ ‖r‖ ^ (k + 2) := real_pow_mono (norm_nonneg x) hx (k + 2)
    have h3 : ‖r‖ ^ (k + 2) ≤ ‖r‖ ^ 2 := real_pow_anti hr0.le hr1.le (by omega)
    have hmul : ‖r‖ ^ (14 * (k + 2) - 14 * multiplicity 29 (k + 2)) * ‖x‖ ^ (k + 2) ≤
        ‖r‖ ^ 28 * ‖r‖ ^ 2 :=
      mul_le_mul h1 (h2.trans h3) (pow_nonneg (norm_nonneg x) (k + 2)) (pow_nonneg hr0.le 28)
    simpa [← pow_add] using hmul
  have htsum_tail : ‖∑' k : ℕ, f (k + 1)‖ ≤ ‖r‖ ^ 30 :=
    norm_tsum_nat_le (pow_nonneg hr0.le 30) hf_tail_sum htail_bound
  have hf0 : f 0 = (29 : K) * x := by simp [f]
  have htsum_eq : (∑' k : ℕ, f k) / (29 : K) - x = (∑' k : ℕ, f (k + 1)) / (29 : K) := by
    rw [hf_sum.tsum_eq_zero_add, hf0]
    field_simp [h29_ne]
    ring
  change ‖(∑' k : ℕ, f k) / (29 : K) - x‖ ≤ ‖r‖ ^ 4
  rw [htsum_eq, norm_div, h29_norm]
  calc ‖∑' k : ℕ, f (k + 1)‖ / ‖r‖ ^ 14
      ≤ ‖r‖ ^ 30 / ‖r‖ ^ 14 := div_le_div_of_nonneg_right htsum_tail (pow_nonneg hr0.le 14)
    _ = ‖r‖ ^ 16 := by field_simp [hr0.ne']
    _ ≤ ‖r‖ ^ 4 := real_pow_anti hr0.le hr1.le (by decide)

private lemma theta_approx {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] {r w : K} {m : ℕ} (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (hm : m ≤ 2) (hw : ‖w‖ = ‖r‖ ^ m) :
    ‖(∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * w ^ (2 * n + 1)) - (w + w⁻¹)‖ ≤ ‖r‖ ^ 8 := by
  let g : ℤ → K := fun n => (r ^ 14) ^ (n * (n + 1) / 2) * w ^ (2 * n + 1)
  have hpos_bound : ∀ k : ℕ, ‖g ((k + 1 : ℕ) : ℤ)‖ ≤ ‖r‖ ^ (8 + k) := by
    intro k
    dsimp only [g]
    let a : ℕ := (k + 1) * (k + 2) / 2
    have ha : 2 * a = (k + 1) * (k + 2) := two_mul_div_two_mul_succ (k + 1)
    have hmul : ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) + 1) = 2 * (a : ℤ) := by
      have haZ : (2 : ℤ) * (a : ℤ) = (((k + 1) * (k + 2) : ℕ) : ℤ) := by exact_mod_cast ha
      have hring : ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) + 1) =
          (((k + 1) * (k + 2) : ℕ) : ℤ) := by push_cast; ring
      linarith
    have hexp1 : ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) + 1) / 2 = (a : ℤ) := by
      rw [hmul]; omega
    have hexp2 : 2 * ((k + 1 : ℕ) : ℤ) + 1 = ((2 * k + 3 : ℕ) : ℤ) := by push_cast; ring
    rw [hexp1, hexp2, zpow_natCast, zpow_natCast, norm_mul, norm_pow, norm_pow,
      norm_pow, hw, ← pow_mul, ← pow_mul, ← pow_add]
    exact real_pow_anti hr0.le hr1.le (by nlinarith)
  have hneg_bound : ∀ k : ℕ, ‖g (-(((k + 1 : ℕ) : ℤ) + 1))‖ ≤ ‖r‖ ^ (8 + k) := by
    intro k
    dsimp only [g]
    let b : ℕ := (k + 1) * (k + 2) / 2
    have hb : 2 * b = (k + 1) * (k + 2) := two_mul_div_two_mul_succ (k + 1)
    have hmul : (-(((k + 1 : ℕ) : ℤ) + 1)) * (-(((k + 1 : ℕ) : ℤ) + 1) + 1) = 2 * (b : ℤ) := by
      have hbZ : (2 : ℤ) * (b : ℤ) = (((k + 1) * (k + 2) : ℕ) : ℤ) := by exact_mod_cast hb
      have hring : (-(((k + 1 : ℕ) : ℤ) + 1)) * (-(((k + 1 : ℕ) : ℤ) + 1) + 1) =
          (((k + 1) * (k + 2) : ℕ) : ℤ) := by push_cast; ring
      linarith
    have hexp1 : (-(((k + 1 : ℕ) : ℤ) + 1)) * (-(((k + 1 : ℕ) : ℤ) + 1) + 1) / 2 = (b : ℤ) := by
      rw [hmul]; omega
    have hexp2 : 2 * (-(((k + 1 : ℕ) : ℤ) + 1)) + 1 = -((2 * k + 3 : ℕ) : ℤ) := by push_cast; ring
    rw [hexp1, hexp2, zpow_natCast, zpow_neg, zpow_natCast, norm_mul, norm_pow, norm_pow,
      norm_inv, norm_pow, hw, ← pow_mul, ← pow_mul]
    have hineq : m * (2 * k + 3) + (8 + k) ≤ 14 * b := by nlinarith
    have hsub : ‖r‖ ^ (14 * b) * (‖r‖ ^ (m * (2 * k + 3)))⁻¹ =
        ‖r‖ ^ (14 * b - m * (2 * k + 3)) := by
      have hsplit : ‖r‖ ^ (14 * b) =
          ‖r‖ ^ (14 * b - m * (2 * k + 3)) * ‖r‖ ^ (m * (2 * k + 3)) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hsplit]
      have hne : ‖r‖ ^ (m * (2 * k + 3)) ≠ 0 := pow_ne_zero _ hr0.ne'
      field_simp [hne]
    rw [hsub]
    exact real_pow_anti hr0.le hr1.le (by omega)
  have hpos_tail_sum : Summable (fun k : ℕ => g ((k + 1 : ℕ) : ℤ)) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg r) hr1) (fun k =>
      (hpos_bound k).trans (real_pow_anti hr0.le hr1.le (by omega)))
  have hneg_tail_sum : Summable (fun k : ℕ => g (-(((k + 1 : ℕ) : ℤ) + 1))) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg r) hr1) (fun k =>
      (hneg_bound k).trans (real_pow_anti hr0.le hr1.le (by omega)))
  have hpos_sum : Summable (fun k : ℕ => g (k : ℤ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => g (k : ℤ)) 1).mp hpos_tail_sum
  have hneg_sum : Summable (fun k : ℕ => g (-((k : ℤ) + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => g (-((k : ℤ) + 1))) 1).mp hneg_tail_sum
  have hf1_zero : g ((0 : ℕ) : ℤ) = w := by
    dsimp only [g]
    have h1 : ((0 : ℕ) : ℤ) * (((0 : ℕ) : ℤ) + 1) / 2 = 0 := by norm_num
    have h2 : 2 * ((0 : ℕ) : ℤ) + 1 = 1 := by norm_num
    rw [h1, h2, zpow_zero, one_mul, zpow_one]
  have hf2_zero : g (-(((0 : ℕ) : ℤ) + 1)) = w⁻¹ := by
    dsimp only [g]
    have h1 : (-(((0 : ℕ) : ℤ) + 1)) * (-(((0 : ℕ) : ℤ) + 1) + 1) / 2 = 0 := by norm_num
    have h2 : 2 * (-(((0 : ℕ) : ℤ) + 1)) + 1 = -1 := by norm_num
    rw [h1, h2, zpow_zero, one_mul, zpow_neg_one]
  have hdecomp : (∑' n : ℤ, g n) - (w + w⁻¹) =
      (∑' k : ℕ, g ((k + 1 : ℕ) : ℤ)) + (∑' k : ℕ, g (-(((k + 1 : ℕ) : ℤ) + 1))) := by
    rw [tsum_of_nat_of_neg_add_one hpos_sum hneg_sum,
      hpos_sum.tsum_eq_zero_add, hneg_sum.tsum_eq_zero_add, hf1_zero, hf2_zero]
    ring
  have hpos_tsum : ‖∑' k : ℕ, g ((k + 1 : ℕ) : ℤ)‖ ≤ ‖r‖ ^ 8 :=
    norm_tsum_nat_le (pow_nonneg hr0.le 8) hpos_tail_sum (fun k =>
      (hpos_bound k).trans (real_pow_anti hr0.le hr1.le (by omega)))
  have hneg_tsum : ‖∑' k : ℕ, g (-(((k + 1 : ℕ) : ℤ) + 1))‖ ≤ ‖r‖ ^ 8 :=
    norm_tsum_nat_le (pow_nonneg hr0.le 8) hneg_tail_sum (fun k =>
      (hneg_bound k).trans (real_pow_anti hr0.le hr1.le (by omega)))
  change ‖(∑' n : ℤ, g n) - (w + w⁻¹)‖ ≤ ‖r‖ ^ 8
  rw [hdecomp]
  exact (norm_add_le_max _ _).trans (max_le hpos_tsum hneg_tsum)

theorem Conjectures.JoshiAbc.LocalThetaGeneration :
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩; ∀ (K : Type) [NontriviallyNormedField K] [NormedAlgebra (Padic 29) K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); let embed := fun (a : PadicInt 29) => algebraMap (Padic 29) K (a:Padic 29); let t := fun (x : K) => (∑' k : ℕ, (-1:K)^k*((29:K)*x)^(k+1)/((k+1:ℕ):K))/(29:K); ∀ (r z : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖<1 → z^7=1 → ‖z‖=1 → ‖1+z^2‖=1 → (∀ n : ℕ, 0<n → ‖(n:K)‖ = ‖r‖^(14*multiplicity 29 n)) → (∀ u : K, ‖u‖ ≤ 1 → ∃ a : PadicInt 29, ‖u-embed a‖ ≤ ‖r‖) → let ξ := theta (r^14) z / theta (r^14) (r^2*z); let u := theta (r^14) (r*z) / theta (r^14) (r^2*z); ∀ x : K, ‖x‖ ≤ ‖r‖ → ∃ a b c : PadicInt 29, ‖x - (embed a*t r + embed b*t ξ + embed c*t u)‖ ≤ ‖r‖^4 := by
  intro K _ _ _ _ _ theta embed t r z hr29 hr0 hr1 _ hz1 h1z2 hn_norm happrox ξ u x hx
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩
  have hr4_le : ‖r‖ ^ 4 ≤ ‖r‖ := by
    simpa only [pow_one] using
      (real_pow_anti hr0.le hr1.le (show (1 : ℕ) ≤ 4 by decide))
  have hr_ne : r ≠ 0 := norm_pos_iff.mp hr0
  have hz_ne : z ≠ 0 := norm_pos_iff.mp (by rw [hz1]; norm_num)
  let T0 : K := theta (r ^ 14) z
  let T1 : K := theta (r ^ 14) (r * z)
  let T2 : K := theta (r ^ 14) (r ^ 2 * z)
  let R0 : K := T0 - (z + z⁻¹)
  let R1 : K := T1 - (r * z + (r * z)⁻¹)
  let R2 : K := T2 - (r ^ 2 * z + (r ^ 2 * z)⁻¹)
  have hR0 : ‖R0‖ ≤ ‖r‖ ^ 8 :=
    theta_approx hr0 hr1 (m := 0) (by decide) (by rw [hz1, pow_zero])
  have hR1 : ‖R1‖ ≤ ‖r‖ ^ 8 :=
    theta_approx hr0 hr1 (m := 1) (by decide) (by rw [norm_mul, hz1, mul_one, pow_one])
  have hR2 : ‖R2‖ ≤ ‖r‖ ^ 8 :=
    theta_approx hr0 hr1 (m := 2) (by decide) (by rw [norm_mul, norm_pow, hz1, mul_one])
  let δ2 : K := r ^ 4 * z ^ 2 + r ^ 2 * z * R2
  have hδ2 : ‖δ2‖ ≤ ‖r‖ ^ 4 := by
    have h1 : ‖r ^ 4 * z ^ 2‖ = ‖r‖ ^ 4 := by rw [norm_mul, norm_pow, norm_pow, hz1, one_pow, mul_one]
    have h2 : ‖r ^ 2 * z * R2‖ ≤ ‖r‖ ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow, hz1, mul_one]
      calc ‖r‖ ^ 2 * ‖R2‖
          ≤ ‖r‖ ^ 2 * ‖r‖ ^ 8 := mul_le_mul_of_nonneg_left hR2 (pow_nonneg hr0.le 2)
        _ = ‖r‖ ^ 10 := by ring
        _ ≤ ‖r‖ ^ 4 := real_pow_anti hr0.le hr1.le (by decide)
    exact (norm_add_le_max _ _).trans (max_le h1.le h2)
  have hδ2_lt : ‖δ2‖ < ‖(1 : K)‖ := by
    rw [norm_one]
    exact hδ2.trans_lt (real_pow_lt_one hr0.le hr1 (by decide))
  have h1δ2_norm : ‖1 + δ2‖ = 1 := by
    simpa [norm_one] using norm_add_eq_left hδ2_lt
  have h1δ2_ne : 1 + δ2 ≠ 0 := norm_pos_iff.mp (by rw [h1δ2_norm]; norm_num)
  have hT2_eq : T2 = (r ^ 2 * z)⁻¹ * (1 + δ2) := by
    have hT2_def : T2 = r ^ 2 * z + (r ^ 2 * z)⁻¹ + R2 := by dsimp only [R2]; ring
    rw [hT2_def]
    dsimp only [δ2]
    field_simp [hr_ne, hz_ne]
    ring
  have hξ_sub_eq : ξ - r ^ 2 * (1 + z ^ 2) = r ^ 2 * (z * R0 - (1 + z ^ 2) * δ2) / (1 + δ2) := by
    have hT0_def : T0 = z + z⁻¹ + R0 := by dsimp only [R0]; ring
    change T0 / T2 - r ^ 2 * (1 + z ^ 2) = _
    rw [hT0_def, hT2_eq]
    field_simp [hr_ne, hz_ne, h1δ2_ne]
    ring
  have hξ_sub : ‖ξ - r ^ 2 * (1 + z ^ 2)‖ ≤ ‖r‖ ^ 4 := by
    rw [hξ_sub_eq, norm_div, h1δ2_norm, div_one, norm_mul, norm_pow]
    have h1 : ‖z * R0‖ ≤ ‖r‖ ^ 4 := by
      rw [norm_mul, hz1, one_mul]
      exact hR0.trans (real_pow_anti hr0.le hr1.le (by decide))
    have h2 : ‖(1 + z ^ 2) * δ2‖ ≤ ‖r‖ ^ 4 := by
      rw [norm_mul, h1z2, one_mul]
      exact hδ2
    have hnum : ‖z * R0 - (1 + z ^ 2) * δ2‖ ≤ ‖r‖ ^ 4 :=
      (norm_sub_le_max _ _).trans (max_le h1 h2)
    calc ‖r‖ ^ 2 * ‖z * R0 - (1 + z ^ 2) * δ2‖
        ≤ ‖r‖ ^ 2 * ‖r‖ ^ 4 := mul_le_mul_of_nonneg_left hnum (pow_nonneg hr0.le 2)
      _ = ‖r‖ ^ 6 := by ring
      _ ≤ ‖r‖ ^ 4 := real_pow_anti hr0.le hr1.le (by decide)
  have hξ_norm : ‖ξ‖ ≤ ‖r‖ := by
    have hsplit : ξ = r ^ 2 * (1 + z ^ 2) + (ξ - r ^ 2 * (1 + z ^ 2)) := by ring
    rw [hsplit]
    have h1 : ‖r ^ 2 * (1 + z ^ 2)‖ ≤ ‖r‖ := by
      rw [norm_mul, norm_pow, h1z2, mul_one]
      simpa only [pow_one] using
        (real_pow_anti hr0.le hr1.le (show (1 : ℕ) ≤ 2 by decide))
    exact (norm_add_le_max _ _).trans (max_le h1 (hξ_sub.trans hr4_le))
  have hu_sub_eq : u - (r + r ^ 3 * z ^ 2) = r * (r * z * R1 - (1 + r ^ 2 * z ^ 2) * δ2) / (1 + δ2) := by
    have hT1_def : T1 = r * z + (r * z)⁻¹ + R1 := by dsimp only [R1]; ring
    change T1 / T2 - (r + r ^ 3 * z ^ 2) = _
    rw [hT1_def, hT2_eq]
    field_simp [hr_ne, hz_ne, h1δ2_ne]
    ring
  have hu_sub : ‖u - (r + r ^ 3 * z ^ 2)‖ ≤ ‖r‖ ^ 4 := by
    rw [hu_sub_eq, norm_div, h1δ2_norm, div_one, norm_mul]
    have h1 : ‖r * z * R1‖ ≤ ‖r‖ ^ 4 := by
      rw [norm_mul, norm_mul, hz1, mul_one]
      calc ‖r‖ * ‖R1‖
          ≤ ‖r‖ * ‖r‖ ^ 8 := mul_le_mul_of_nonneg_left hR1 hr0.le
        _ = ‖r‖ ^ 9 := by ring
        _ ≤ ‖r‖ ^ 4 := real_pow_anti hr0.le hr1.le (by decide)
    have h2 : ‖(1 + r ^ 2 * z ^ 2) * δ2‖ ≤ ‖r‖ ^ 4 := by
      have hfac : ‖1 + r ^ 2 * z ^ 2‖ ≤ 1 := by
        have hr2z2 : ‖r ^ 2 * z ^ 2‖ ≤ 1 := by
          rw [norm_mul, norm_pow, norm_pow, hz1, one_pow, mul_one]
          exact real_pow_le_one hr0.le hr1.le 2
        exact (norm_add_le_max _ _).trans (max_le (by rw [norm_one]) hr2z2)
      rw [norm_mul]
      calc ‖1 + r ^ 2 * z ^ 2‖ * ‖δ2‖
          ≤ 1 * ‖r‖ ^ 4 := mul_le_mul hfac hδ2 (norm_nonneg δ2) (by norm_num)
        _ = ‖r‖ ^ 4 := one_mul _
    have hnum : ‖r * z * R1 - (1 + r ^ 2 * z ^ 2) * δ2‖ ≤ ‖r‖ ^ 4 :=
      (norm_sub_le_max _ _).trans (max_le h1 h2)
    calc ‖r‖ * ‖r * z * R1 - (1 + r ^ 2 * z ^ 2) * δ2‖
        ≤ ‖r‖ * ‖r‖ ^ 4 := mul_le_mul_of_nonneg_left hnum hr0.le
      _ = ‖r‖ ^ 5 := by ring
      _ ≤ ‖r‖ ^ 4 := real_pow_anti hr0.le hr1.le (by decide)
  have hu_norm : ‖u‖ ≤ ‖r‖ := by
    have hsplit : u = (r + r ^ 3 * z ^ 2) + (u - (r + r ^ 3 * z ^ 2)) := by ring
    rw [hsplit]
    have h1 : ‖r + r ^ 3 * z ^ 2‖ ≤ ‖r‖ := by
      have hr3z2 : ‖r ^ 3 * z ^ 2‖ ≤ ‖r‖ := by
        rw [norm_mul, norm_pow, norm_pow, hz1, one_pow, mul_one]
        simpa only [pow_one] using
          (real_pow_anti hr0.le hr1.le (show (1 : ℕ) ≤ 3 by decide))
      exact (norm_add_le_max _ _).trans (max_le le_rfl hr3z2)
    exact (norm_add_le_max _ _).trans (max_le h1 (hu_sub.trans hr4_le))
  have ht_r : ‖t r - r‖ ≤ ‖r‖ ^ 4 :=
    t_sub_self_norm_le hr29 hr0 hr1 hn_norm le_rfl
  have ht_ξ : ‖t ξ - ξ‖ ≤ ‖r‖ ^ 4 :=
    t_sub_self_norm_le hr29 hr0 hr1 hn_norm hξ_norm
  have ht_u : ‖t u - u‖ ≤ ‖r‖ ^ 4 :=
    t_sub_self_norm_le hr29 hr0 hr1 hn_norm hu_norm
  let v2 : K := r ^ 2 * (1 + z ^ 2)
  let v3 : K := r ^ 3 * z ^ 2
  have ht_ξ_v2 : ‖t ξ - v2‖ ≤ ‖r‖ ^ 4 := by
    have hsplit : t ξ - v2 = (t ξ - ξ) + (ξ - v2) := by ring
    rw [hsplit]
    exact (norm_add_le_max _ _).trans (max_le ht_ξ hξ_sub)
  have ht_ur_v3 : ‖(t u - t r) - v3‖ ≤ ‖r‖ ^ 4 := by
    have hsplit : (t u - t r) - v3 = ((t u - u) - (t r - r)) + (u - (r + v3)) := by ring
    rw [hsplit]
    have h1 : ‖(t u - u) - (t r - r)‖ ≤ ‖r‖ ^ 4 :=
      (norm_sub_le_max _ _).trans (max_le ht_u ht_r)
    exact (norm_add_le_max _ _).trans (max_le h1 hu_sub)
  have hxr : ‖x / r‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one hr0).mpr hx
  obtain ⟨a1, ha1⟩ := happrox (x / r) hxr
  let x1 : K := x - embed a1 * t r
  have hx1 : ‖x1‖ ≤ ‖r‖ ^ 2 := by
    have hstep : ‖x - embed a1 * r‖ ≤ ‖r‖ ^ 2 := by
      have heq : x - embed a1 * r = (x / r - embed a1) * r := by field_simp [hr_ne]
      rw [heq, norm_mul]
      calc ‖x / r - embed a1‖ * ‖r‖
          ≤ ‖r‖ * ‖r‖ := mul_le_mul_of_nonneg_right ha1 hr0.le
        _ = ‖r‖ ^ 2 := by ring
    have herr : ‖embed a1 * (t r - r)‖ ≤ ‖r‖ ^ 2 := by
      rw [norm_mul]
      calc ‖embed a1‖ * ‖t r - r‖
          ≤ 1 * ‖r‖ ^ 4 := mul_le_mul (norm_embed_le_one a1) ht_r (norm_nonneg _) (by norm_num)
        _ = ‖r‖ ^ 4 := one_mul _
        _ ≤ ‖r‖ ^ 2 := real_pow_anti hr0.le hr1.le (by decide)
    have hsplit : x1 = (x - embed a1 * r) - embed a1 * (t r - r) := by dsimp only [x1]; ring
    rw [hsplit]
    exact (norm_sub_le_max _ _).trans (max_le hstep herr)
  have hv2_norm : ‖v2‖ = ‖r‖ ^ 2 := by
    dsimp only [v2]
    rw [norm_mul, norm_pow, h1z2, mul_one]
  have hv2_ne : v2 ≠ 0 := norm_pos_iff.mp (by rw [hv2_norm]; exact pow_pos hr0 2)
  have hx1v2 : ‖x1 / v2‖ ≤ 1 := by
    rw [norm_div, hv2_norm]
    exact (div_le_one (pow_pos hr0 2)).mpr hx1
  obtain ⟨b, hb⟩ := happrox (x1 / v2) hx1v2
  let x2 : K := x1 - embed b * t ξ
  have hx2 : ‖x2‖ ≤ ‖r‖ ^ 3 := by
    have hstep : ‖x1 - embed b * v2‖ ≤ ‖r‖ ^ 3 := by
      have heq : x1 - embed b * v2 = (x1 / v2 - embed b) * v2 := by field_simp [hv2_ne]
      rw [heq, norm_mul, hv2_norm]
      calc ‖x1 / v2 - embed b‖ * ‖r‖ ^ 2
          ≤ ‖r‖ * ‖r‖ ^ 2 := mul_le_mul_of_nonneg_right hb (pow_nonneg hr0.le 2)
        _ = ‖r‖ ^ 3 := by ring
    have herr : ‖embed b * (t ξ - v2)‖ ≤ ‖r‖ ^ 3 := by
      rw [norm_mul]
      calc ‖embed b‖ * ‖t ξ - v2‖
          ≤ 1 * ‖r‖ ^ 4 := mul_le_mul (norm_embed_le_one b) ht_ξ_v2 (norm_nonneg _) (by norm_num)
        _ = ‖r‖ ^ 4 := one_mul _
        _ ≤ ‖r‖ ^ 3 := real_pow_anti hr0.le hr1.le (by decide)
    have hsplit : x2 = (x1 - embed b * v2) - embed b * (t ξ - v2) := by dsimp only [x2]; ring
    rw [hsplit]
    exact (norm_sub_le_max _ _).trans (max_le hstep herr)
  have hv3_norm : ‖v3‖ = ‖r‖ ^ 3 := by
    dsimp only [v3]
    rw [norm_mul, norm_pow, norm_pow, hz1, one_pow, mul_one]
  have hv3_ne : v3 ≠ 0 := norm_pos_iff.mp (by rw [hv3_norm]; exact pow_pos hr0 3)
  have hx2v3 : ‖x2 / v3‖ ≤ 1 := by
    rw [norm_div, hv3_norm]
    exact (div_le_one (pow_pos hr0 3)).mpr hx2
  obtain ⟨c, hc⟩ := happrox (x2 / v3) hx2v3
  have hx3 : ‖x2 - embed c * (t u - t r)‖ ≤ ‖r‖ ^ 4 := by
    have hstep : ‖x2 - embed c * v3‖ ≤ ‖r‖ ^ 4 := by
      have heq : x2 - embed c * v3 = (x2 / v3 - embed c) * v3 := by field_simp [hv3_ne]
      rw [heq, norm_mul, hv3_norm]
      calc ‖x2 / v3 - embed c‖ * ‖r‖ ^ 3
          ≤ ‖r‖ * ‖r‖ ^ 3 := mul_le_mul_of_nonneg_right hc (pow_nonneg hr0.le 3)
        _ = ‖r‖ ^ 4 := by ring
    have herr : ‖embed c * ((t u - t r) - v3)‖ ≤ ‖r‖ ^ 4 := by
      rw [norm_mul]
      calc ‖embed c‖ * ‖(t u - t r) - v3‖
          ≤ 1 * ‖r‖ ^ 4 := mul_le_mul (norm_embed_le_one c) ht_ur_v3 (norm_nonneg _) (by norm_num)
        _ = ‖r‖ ^ 4 := one_mul _
    have hsplit : x2 - embed c * (t u - t r) = (x2 - embed c * v3) - embed c * ((t u - t r) - v3) := by
      ring
    rw [hsplit]
    exact (norm_sub_le_max _ _).trans (max_le hstep herr)
  refine ⟨a1 - c, b, c, ?_⟩
  have hembed_sub : embed (a1 - c) = embed a1 - embed c := by
    dsimp only [embed]
    rw [PadicInt.coe_sub, map_sub]
  have hfinal : x - (embed (a1 - c) * t r + embed b * t ξ + embed c * t u) =
      x2 - embed c * (t u - t r) := by
    dsimp only [x2, x1]
    rw [hembed_sub]
    ring
  rw [hfinal]
  exact hx3
