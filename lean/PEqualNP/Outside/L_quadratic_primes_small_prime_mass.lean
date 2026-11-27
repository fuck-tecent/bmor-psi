import Mathlib

open scoped BigOperators

private def vp (n p : ℕ) : ℝ := (((n^2+1).factorization p : ℕ) : ℝ)

private noncomputable def bnd (x p : ℕ) : ℝ := 2*(x:ℝ)/((p:ℝ)-1) + 2*((Nat.log p ((2*x)^2+1) : ℕ) : ℝ)

private def psetAll (x : ℕ) : Finset ℕ := (Finset.range (x+1)).filter (fun p => p.Prime)

private def pset1 (x : ℕ) : Finset ℕ := (Finset.range (x+1)).filter (fun p => p.Prime ∧ p % 4 = 1)

/-! 复制自已 ACCEPTED 的同类文件：奇素数模 p^k 的 -1 平方根至多两个。 -/

private lemma pair_lemma_of_le {p k r s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hsr : s ≤ r) (hrq : r < p ^ k) (hsq : s < p ^ k)
    (hr : p ^ k ∣ r ^ 2 + 1) (hs : p ^ k ∣ s ^ 2 + 1) :
    r = s ∨ r + s = p ^ k := by
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hp2le : 2 ≤ p := hp.two_le
  have hpq : p ∣ p ^ k := dvd_pow_self p hk0
  have hqr : p ∣ r ^ 2 + 1 := hpq.trans hr
  have hqs : p ∣ s ^ 2 + 1 := hpq.trans hs
  have hpr : ¬ p ∣ r := by
    intro h
    have h2 : p ∣ r ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left h r
    have hone : p ∣ (r ^ 2 + 1) - r ^ 2 := Nat.dvd_sub hqr h2
    have h1 : (r ^ 2 + 1) - r ^ 2 = 1 := by omega
    rw [h1] at hone
    exact hp.not_dvd_one hone
  have hps : ¬ p ∣ s := by
    intro h
    have h2 : p ∣ s ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left h s
    have hone : p ∣ (s ^ 2 + 1) - s ^ 2 := Nat.dvd_sub hqs h2
    have h1 : (s ^ 2 + 1) - s ^ 2 = 1 := by omega
    rw [h1] at hone
    exact hp.not_dvd_one hone
  have hrne : r ≠ 0 := by
    intro h0
    have h1 : p ^ k ∣ 1 := by simpa [h0] using hr
    have h2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk0 p)
    have h3 : p ^ k ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hsq : s ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hsr 2
  have hdiff0 : p ^ k ∣ (r ^ 2 + 1) - (s ^ 2 + 1) := Nat.dvd_sub hr hs
  have hdiff : p ^ k ∣ r ^ 2 - s ^ 2 := by
    have heq : (r ^ 2 + 1) - (s ^ 2 + 1) = r ^ 2 - s ^ 2 := by omega
    rwa [heq] at hdiff0
  have hfac : r ^ 2 - s ^ 2 = (r + s) * (r - s) := sq_tsub_sq r s
  have hmul : p ^ k ∣ (r + s) * (r - s) := by rw [hfac] at hdiff; exact hdiff
  by_cases hdvd : p ∣ r - s
  · have hpns : ¬ p ∣ r + s := by
      intro hps2
      have h2r : p ∣ 2 * r := by
        have h := Nat.dvd_add hdvd hps2
        have heq : (r - s) + (r + s) = 2 * r := by omega
        rwa [heq] at h
      rcases hp.dvd_mul.mp h2r with h | h
      · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
        omega
      · exact hpr h
    have hcop : Nat.Coprime (p ^ k) (r + s) :=
      Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpns)
    have hdiv : p ^ k ∣ r - s := hcop.dvd_of_dvd_mul_left hmul
    left
    have hlt : r - s < p ^ k := by omega
    have h0 : r - s = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega
  · have hcop : Nat.Coprime (p ^ k) (r - s) :=
      Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hdvd)
    have hdiv : p ^ k ∣ r + s := hcop.dvd_of_dvd_mul_right hmul
    right
    have hpos : r + s ≠ 0 := by omega
    have hlt : r + s < 2 * p ^ k := by omega
    exact Nat.eq_of_dvd_of_lt_two_mul hpos hdiv hlt

private lemma pair_lemma {p k r s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hrq : r < p ^ k) (hsq : s < p ^ k)
    (hr : p ^ k ∣ r ^ 2 + 1) (hs : p ^ k ∣ s ^ 2 + 1) :
    r = s ∨ r + s = p ^ k := by
  rcases le_total s r with hsr | hrs
  · exact pair_lemma_of_le hp hp2 hk hsr hrq hsq hr hs
  · rcases pair_lemma_of_le hp hp2 hk hrs hsq hrq hs hr with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)

private lemma roots_le_two (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)).card ≤ 2 := by
  classical
  by_cases hne : ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)).Nonempty
  · obtain ⟨r0, hr0⟩ := hne
    have hr0' := Finset.mem_filter.mp hr0
    have hsub : ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)) ⊆
        ({r0, p ^ k - r0} : Finset ℕ) := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      have hslt : s < p ^ k := Finset.mem_range.mp hs'.1
      have hrlt : r0 < p ^ k := Finset.mem_range.mp hr0'.1
      have hkey := pair_lemma hp hp2 hk hrlt hslt hr0'.2 hs'.2
      rcases hkey with h | h
      · simp [h]
      · have h2 : s = p ^ k - r0 := by omega
        simp [h2]
    calc ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)).card
        ≤ ({r0, p ^ k - r0} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          have h := Finset.card_insert_le r0 ({p ^ k - r0} : Finset ℕ)
          simp only [Finset.card_singleton] at h
          omega
  · have hempty : ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

/-! 单个剩余类在区间内的个数上界。 -/

private lemma fiber_card_le (x q r : ℕ) :
    ((Finset.Ioc x (2 * x)).filter (fun n => n % q = r)).card ≤ x / q + 1 := by
  classical
  set S := (Finset.Ioc x (2 * x)).filter (fun n => n % q = r) with hS
  rcases Finset.eq_empty_or_nonempty S with hS0 | hne
  · rw [hS0]
    simp
  · have ha_mem : S.min' hne ∈ S := Finset.min'_mem S hne
    have hb_mem : S.max' hne ∈ S := Finset.max'_mem S hne
    have hle_a : ∀ n ∈ S, S.min' hne ≤ n := by
      intro n hn
      have h := Finset.min'_le S n hn
      rwa [show (⟨n, hn⟩ : S.Nonempty) = hne from Subsingleton.elim _ _] at h
    have hle_b : ∀ n ∈ S, n ≤ S.max' hne := by
      intro n hn
      have h := Finset.le_max' S n hn
      rwa [show (⟨n, hn⟩ : S.Nonempty) = hne from Subsingleton.elim _ _] at h
    have hmaps : Set.MapsTo (fun n => (n - S.min' hne) / q) (↑S : Set ℕ)
        (↑(Finset.range ((S.max' hne - S.min' hne) / q + 1)) : Set ℕ) := by
      intro n hn
      simp only [Finset.mem_coe] at hn ⊢
      rw [Finset.mem_range]
      have h1 : n ≤ S.max' hne := hle_b n hn
      have h2 : n - S.min' hne ≤ S.max' hne - S.min' hne := Nat.sub_le_sub_right h1 _
      exact Nat.lt_succ_of_le (Nat.div_le_div_right h2)
    have hinj : Set.InjOn (fun n => (n - S.min' hne) / q) (↑S : Set ℕ) := by
      intro n hn m hm hk
      simp only [Finset.mem_coe] at hn hm
      have hk' : (n - S.min' hne) / q = (m - S.min' hne) / q := hk
      have hna : q ∣ n - S.min' hne := by
        have hmod : Nat.ModEq q n (S.min' hne) := by
          have h1 : n % q = r := (Finset.mem_filter.mp hn).2
          have h2 : S.min' hne % q = r := (Finset.mem_filter.mp ha_mem).2
          show n % q = S.min' hne % q
          rw [h1, h2]
        exact (Nat.modEq_iff_dvd' (hle_a n hn)).mp hmod.symm
      have hma : q ∣ m - S.min' hne := by
        have hmod : Nat.ModEq q m (S.min' hne) := by
          have h1 : m % q = r := (Finset.mem_filter.mp hm).2
          have h2 : S.min' hne % q = r := (Finset.mem_filter.mp ha_mem).2
          show m % q = S.min' hne % q
          rw [h1, h2]
        exact (Nat.modEq_iff_dvd' (hle_a m hm)).mp hmod.symm
      have hna' : n - S.min' hne = q * ((n - S.min' hne) / q) := by
        rw [mul_comm]
        exact (Nat.div_mul_cancel hna).symm
      have hma' : m - S.min' hne = q * ((m - S.min' hne) / q) := by
        rw [mul_comm]
        exact (Nat.div_mul_cancel hma).symm
      have h3 : n - S.min' hne = m - S.min' hne := by rw [hna', hma', hk']
      have han : S.min' hne ≤ n := hle_a n hn
      have ham : S.min' hne ≤ m := hle_a m hm
      omega
    have hcard := Finset.card_le_card_of_injOn (fun n => (n - S.min' hne) / q) hmaps hinj
    simp only [Finset.card_range] at hcard
    have hbI : S.max' hne ∈ Finset.Ioc x (2 * x) := (Finset.mem_filter.mp hb_mem).1
    have haI : S.min' hne ∈ Finset.Ioc x (2 * x) := (Finset.mem_filter.mp ha_mem).1
    have hb : S.max' hne ≤ 2 * x := (Finset.mem_Ioc.mp hbI).2
    have ha : x < S.min' hne := (Finset.mem_Ioc.mp haI).1
    have hba : S.max' hne - S.min' hne ≤ x - 1 := by omega
    have hdiv : (S.max' hne - S.min' hne) / q ≤ x / q :=
      Nat.div_le_div_right (by omega)
    omega

private lemma interval_count (x q : ℕ) (hq : 0 < q) :
    ((Finset.Ioc x (2 * x)).filter (fun n => q ∣ n ^ 2 + 1)).card ≤
      (x / q + 1) * ((Finset.range q).filter (fun r => q ∣ r ^ 2 + 1)).card := by
  classical
  set S := (Finset.Ioc x (2 * x)).filter (fun n => q ∣ n ^ 2 + 1) with hS
  have hmap : Set.MapsTo (fun n => n % q) (↑S : Set ℕ) (↑(Finset.range q) : Set ℕ) := by
    intro n hn
    simp only [Finset.mem_coe] at hn ⊢
    exact Finset.mem_range.mpr (Nat.mod_lt n hq)
  have hfib : S.card = ∑ b ∈ Finset.range q, (S.filter (fun a => a % q = b)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hbound : ∑ b ∈ Finset.range q, (S.filter (fun a => a % q = b)).card
      ≤ ∑ b ∈ Finset.range q, (x / q + 1) * (if q ∣ b ^ 2 + 1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases hroot : q ∣ b ^ 2 + 1
    · rw [if_pos hroot, Nat.mul_one]
      have hsub : S.filter (fun a => a % q = b) ⊆ (Finset.Ioc x (2 * x)).filter (fun n => n % q = b) := by
        intro n hn
        have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
        have hnb : n % q = b := (Finset.mem_filter.mp hn).2
        have hnI : n ∈ Finset.Ioc x (2 * x) := (Finset.mem_filter.mp hnS).1
        exact Finset.mem_filter.mpr ⟨hnI, hnb⟩
      exact le_trans (Finset.card_le_card hsub) (fiber_card_le x q b)
    · rw [if_neg hroot, Nat.mul_zero]
      have hempty : S.filter (fun a => a % q = b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
        have hnb : n % q = b := (Finset.mem_filter.mp hn).2
        have hdn : q ∣ n ^ 2 + 1 := (Finset.mem_filter.mp hnS).2
        have hmod : Nat.ModEq q (n ^ 2 + 1) (b ^ 2 + 1) := by
          have hnm : Nat.ModEq q n b := by
            show n % q = b % q
            rw [hnb, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
          exact Nat.ModEq.add_right 1 (Nat.ModEq.pow 2 hnm)
        have hzero : (n ^ 2 + 1) % q = 0 := Nat.dvd_iff_mod_eq_zero.mp hdn
        have hbzero : (b ^ 2 + 1) % q = 0 := by
          have hEq : (n ^ 2 + 1) % q = (b ^ 2 + 1) % q := hmod
          rw [← hEq, hzero]
        exact hroot (Nat.dvd_iff_mod_eq_zero.mpr hbzero)
      rw [hempty]
      simp
  calc S.card = ∑ b ∈ Finset.range q, (S.filter (fun a => a % q = b)).card := hfib
    _ ≤ ∑ b ∈ Finset.range q, (x / q + 1) * (if q ∣ b ^ 2 + 1 then 1 else 0) := hbound
    _ = (x / q + 1) * ((Finset.range q).filter (fun r => q ∣ r ^ 2 + 1)).card := by
        rw [Finset.card_filter, Finset.mul_sum]

/-! 素数幂的区间计数：对奇素数 p、指数 i>0，解数不超过 2*(x/p^i+1)。 -/

private lemma pow_count_le {p i x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hi : 0 < i) :
    ((Finset.Ioc x (2 * x)).filter (fun n => p ^ i ∣ n ^ 2 + 1)).card
      ≤ 2 * (x / p ^ i + 1) := by
  have hq : 0 < p ^ i := pow_pos hp.pos i
  have h1 : ((Finset.Ioc x (2 * x)).filter (fun n => p ^ i ∣ n ^ 2 + 1)).card
      ≤ (x / p ^ i + 1) * ((Finset.range (p ^ i)).filter (fun r => p ^ i ∣ r ^ 2 + 1)).card :=
    interval_count x (p ^ i) hq
  have h2 : ((Finset.range (p ^ i)).filter (fun r => p ^ i ∣ r ^ 2 + 1)).card ≤ 2 :=
    roots_le_two p i hp hp2 hi
  have h3 : (x / p ^ i + 1) * ((Finset.range (p ^ i)).filter (fun r => p ^ i ∣ r ^ 2 + 1)).card
      ≤ (x / p ^ i + 1) * 2 := Nat.mul_le_mul_left _ h2
  have h4 : (x / p ^ i + 1) * 2 = 2 * (x / p ^ i + 1) := by ring
  omega

/-! 奇素数 p 若整除 n^2+1 则 p % 4 = 1。 -/

private lemma prime_mod_four {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ n ^ 2 + 1) :
    p % 4 = 1 := by
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact h
  have hmod : (n : ZMod p) ^ 2 = -1 := by
    push_cast at h0
    linear_combination h0
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : p % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hmod
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | ho
    · exact absurd h2 hp2
    · exact ho
  have hp4 : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  omega

private lemma geom_part (p : ℕ) (hp : 2 ≤ p) (b : ℕ) :
    Finset.sum (Finset.Ico 1 b) (fun i => ((p:ℝ))⁻¹ ^ i) ≤ 1/((p:ℝ)-1) := by
  set r : ℝ := ((p:ℝ))⁻¹ with hr
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hr0 : (0:ℝ) < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, inv_lt_one₀ hp0]
    exact_mod_cast hp
  have hne : r ≠ 1 := ne_of_lt hr1
  have hd : (0:ℝ) < 1 - r := by linarith
  have hsum : Finset.sum (Finset.Ico 1 b) (fun i => r ^ i) = r * ((r ^ (b-1) - 1)/(r - 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h1 : ∀ j ∈ Finset.range (b - 1), r ^ (1 + j) = r * r ^ j := by
      intro j hj
      rw [pow_add, pow_one]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, geom_sum_eq hne]
  rw [hsum]
  have hkey : ((r ^ (b-1) - 1)/(r - 1)) = (1 - r ^ (b-1))/(1 - r) := by
    field_simp
    ring
  rw [hkey]
  have hle : (1 - r ^ (b-1))/(1 - r) ≤ 1/(1 - r) := by
    rw [div_le_div_iff₀ hd hd]
    nlinarith [pow_nonneg hr0.le (b-1)]
  refine le_trans (mul_le_mul_of_nonneg_left hle hr0.le) ?_
  rw [mul_one_div]
  rw [hr]
  have h1 : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by
    have h2 : (p:ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hp0]
      exact_mod_cast (by omega : 1 ≤ p)
    linarith
  have h2 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  have hEq : ((p:ℝ))⁻¹ * (((p:ℝ)) - 1) = 1 * (1 - ((p:ℝ))⁻¹) := by
    have hpne : (p:ℝ) ≠ 0 := ne_of_gt hp0
    field_simp
  linarith

private lemma abelIco (m d : ℕ) (A g : ℕ → ℝ) :
    Finset.sum (Finset.Ico m (m + d)) (fun k => (A (k+1) - A k) * g k)
      = A (m+d) * g (m+d) - A m * g m
        - Finset.sum (Finset.Ico m (m+d)) (fun k => A (k+1) * (g (k+1) - g k)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hle : m ≤ m + d := Nat.le_add_right m d
      have htop : m + (d + 1) = m + d + 1 := by omega
      rw [htop]
      rw [Finset.sum_Ico_succ_top (f := fun k => (A (k+1) - A k) * g k) hle]
      rw [Finset.sum_Ico_succ_top (f := fun k => A (k+1) * (g (k+1) - g k)) hle]
      rw [ih]
      ring

private lemma small_swap (x : ℕ) :
    Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (fun p => vp n p * Real.log (p:ℝ)))
      = Finset.sum (psetAll x) (fun p => Real.log (p:ℝ) * Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p)) := by
  have hstep : ∀ n ∈ Finset.Ioc x (2*x),
      Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (fun p => vp n p * Real.log (p:ℝ))
      = Finset.sum (psetAll x) (fun p => vp n p * Real.log (p:ℝ)) := by
    intro n hn
    have hn0 : n^2+1 ≠ 0 := by positivity
    apply Finset.sum_subset
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp'.1).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
    · intro p hpP hpn
      have hpP' := Finset.mem_filter.mp hpP
      have hpd : ¬ p ∣ n^2+1 := by
        intro hd
        have hpx : p ≤ x := by
          have := Finset.mem_range.mp hpP'.1
          omega
        exact hpn (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpP'.2, hd, hn0⟩, hpx⟩)
      simp only [vp]
      rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      simp
  calc Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (fun p => vp n p * Real.log (p:ℝ)))
      = Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum (psetAll x) (fun p => vp n p * Real.log (p:ℝ))) := Finset.sum_congr rfl hstep
    _ = Finset.sum (psetAll x) (fun p => Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p * Real.log (p:ℝ))) := Finset.sum_comm
    _ = Finset.sum (psetAll x) (fun p => Real.log (p:ℝ) * Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p)) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_mul]
        ring


private lemma count_le_bnd (x p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p) ≤ bnd x p := by
  set M := (2*x)^2+1 with hM
  set b := (Nat.log p M).succ with hbdef
  have hp2le : 2 ≤ p := hp.two_le
  have hMpos : 0 < M := by positivity
  have hlt : M < p ^ b := by
    rw [hbdef]
    exact Nat.lt_pow_succ_log_self (by omega : 1 < p) M
  have hfac : ∀ n ∈ Finset.Ioc x (2*x),
      ((n^2+1).factorization p : ℕ) = ((Finset.Ico 1 b).filter (fun i => p^i ∣ n^2+1)).card := by
    intro n hn
    have hnle : n ≤ 2*x := (Finset.mem_Ioc.mp hn).2
    have hsq : n^2 ≤ (2*x)^2 := Nat.pow_le_pow_left hnle 2
    have hlt2 : n^2+1 < p^b := by omega
    exact Nat.factorization_eq_card_pow_dvd_of_lt hp (by positivity) hlt2
  have hone : ∀ n ∈ Finset.Ioc x (2*x),
      vp n p = Finset.sum (Finset.Ico 1 b) (fun i => if p^i ∣ n^2+1 then (1:ℝ) else 0) := by
    intro n hn
    rw [vp, hfac n hn, ← Finset.sum_boole]
  calc Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p)
      = Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum (Finset.Ico 1 b) (fun i => if p^i ∣ n^2+1 then (1:ℝ) else 0)) := Finset.sum_congr rfl hone
    _ = Finset.sum (Finset.Ico 1 b) (fun i => Finset.sum (Finset.Ioc x (2*x)) (fun n => if p^i ∣ n^2+1 then (1:ℝ) else 0)) := Finset.sum_comm
    _ ≤ Finset.sum (Finset.Ico 1 b) (fun i => 2*((x:ℝ)/((p:ℝ)^i)) + 2) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have hi0 : 0 < i := by omega
        have hcnt : ((Finset.Ioc x (2 * x)).filter (fun n => p ^ i ∣ n ^ 2 + 1)).card ≤ 2 * (x / p ^ i + 1) :=
          pow_count_le hp hp2 hi0
        rw [Finset.sum_boole]
        have h3 : (((Finset.Ioc x (2*x)).filter (fun n => p^i ∣ n^2+1)).card : ℝ)
            ≤ 2 * (((x / p^i : ℕ) : ℝ) + 1) := by
          have hc : (((2 * (x / p^i + 1) : ℕ)) : ℝ) = 2 * (((x / p^i : ℕ) : ℝ) + 1) := by
            push_cast
            ring
          rw [← hc]
          exact_mod_cast hcnt
        have h4 : ((x / p^i : ℕ) : ℝ) ≤ (x:ℝ)/((p:ℝ)^i) := by
          have h6 := Nat.cast_div_le (α := ℝ) (m := x) (n := p^i)
          rwa [Nat.cast_pow] at h6
        linarith
    _ = 2*(x:ℝ) * Finset.sum (Finset.Ico 1 b) (fun i => (((p:ℝ)^i))⁻¹) + 2*(((Finset.Ico 1 b).card : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [div_eq_mul_inv]
          ring
        · rw [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ bnd x p := by
        show 2*(x:ℝ) * Finset.sum (Finset.Ico 1 b) (fun i => (((p:ℝ)^i))⁻¹) + 2*(((Finset.Ico 1 b).card : ℕ) : ℝ)
          ≤ 2*(x:ℝ)/((p:ℝ)-1) + 2*((Nat.log p M : ℕ) : ℝ)
        have hcard : ((Finset.Ico 1 b).card : ℕ) = Nat.log p M := by
          rw [Nat.card_Ico]
          simp [hbdef]
        rw [hcard]
        have hsum_eq : Finset.sum (Finset.Ico 1 b) (fun i => (((p:ℝ)^i))⁻¹)
            = Finset.sum (Finset.Ico 1 b) (fun i => ((p:ℝ))⁻¹ ^ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [inv_pow]
        rw [hsum_eq]
        have hg : Finset.sum (Finset.Ico 1 b) (fun i => ((p:ℝ))⁻¹ ^ i) ≤ 1/((p:ℝ)-1) := geom_part p hp2le b
        have hx0 : (0:ℝ) ≤ 2*(x:ℝ) := by positivity
        have h7 := mul_le_mul_of_nonneg_left hg hx0
        have h8 : 2*(x:ℝ)*(1/((p:ℝ)-1)) = 2*(x:ℝ)/((p:ℝ)-1) := by rw [mul_one_div]
        linarith

/-! ### 前缀和与 PNT-AP -/

private noncomputable def apLog (k : ℕ) : ℝ := if k.Prime ∧ k % 4 = 1 then Real.log (k:ℝ) else 0

private noncomputable def apSum (n : ℕ) : ℝ := Finset.sum (Finset.range n) apLog

private lemma apLog_nonneg (k : ℕ) : 0 ≤ apLog k := by
  rw [apLog]
  split_ifs with h
  · apply Real.log_nonneg
    exact_mod_cast (Nat.Prime.one_lt h.1).le
  · exact le_refl 0

private lemma apLog_lt_five {k : ℕ} (hk : k < 5) : apLog k = 0 := by
  rw [apLog]
  have h : ¬ (Nat.Prime k ∧ k % 4 = 1) := by
    interval_cases k <;> decide
  simp only [apLog, h, if_false]

private lemma apSum_five : apSum 5 = 0 := by
  rw [apSum, show (5:ℕ) = 5 from rfl]
  apply Finset.sum_eq_zero
  intro k hk
  exact apLog_lt_five (Finset.mem_range.mp hk)

private lemma apSum_mono {n m : ℕ} (h : n ≤ m) : apSum n ≤ apSum m := by
  rw [apSum, apSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
  intro k hk _
  exact apLog_nonneg k

private lemma nat_eventually_helper {P : ℝ → Prop} (h : ∀ᶠ t : ℝ in Filter.atTop, P t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P (n:ℝ) := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h
  refine ⟨⌈R⌉₊ + 1, fun n hn => hR (n:ℝ) ?_⟩
  have h1 : R ≤ ((⌈R⌉₊ : ℕ) : ℝ) := Nat.le_ceil R
  have h2 : ((⌈R⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (le_trans (Nat.le_succ ⌈R⌉₊) hn)
  linarith

private lemma apSum_eq_APtheta (n : ℕ) :
    (Finset.sum ((Finset.Ioc 0 n).filter (fun p => p.Prime ∧ p ≡ 1 [MOD 4])) (fun p => Real.log (p:ℝ))) = apSum (n+1) := by
  have hset : (Finset.Ioc 0 n).filter (fun p => p.Prime ∧ p ≡ 1 [MOD 4])
      = (Finset.range (n+1)).filter (fun p => p.Prime ∧ p % 4 = 1) := by
    ext p
    constructor
    · intro hp
      have hp1 := Finset.mem_filter.mp hp
      have hI := Finset.mem_Ioc.mp hp1.1
      have hpmod : p % 4 = 1 := by
        have h := hp1.2.2
        change p % 4 = 1 % 4 at h
        rw [h]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp1.2.1, hpmod⟩
    · intro hp
      have hp1 := Finset.mem_filter.mp hp
      have hlt : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1.1)
      have hpos : 0 < p := hp1.2.1.pos
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpos, hlt⟩, hp1.2.1, ?_⟩
      have hpmod : p % 4 = 1 := hp1.2.2
      change p % 4 = 1 % 4
      rw [hpmod]
  rw [hset, apSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

private lemma apSum_nonneg (n : ℕ) : 0 ≤ apSum n := by
  rw [apSum]
  apply Finset.sum_nonneg
  intro k hk
  exact apLog_nonneg k

private lemma apSum_eventual_bound (d : ℝ) (hd : 0 < d) :
    ∃ T : ℕ, ∀ n : ℕ, T ≤ n → apSum (n+1) ≤ (1/2 + d) * (n:ℝ) := by
  have htr := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 4) (a := 1) (by decide : Nat.Coprime 1 4)
  have hφ : (((Nat.totient 4 : ℕ)) : ℝ)⁻¹ = (1/2 : ℝ) := by
    have h2 : Nat.totient 4 = 2 := by decide
    rw [h2]
    norm_num
  rw [hφ] at htr
  have hev : ∀ᶠ (t : ℝ) in Filter.atTop,
      Finset.sum ((Finset.Ioc 0 ⌊t⌋₊).filter (fun p => p.Prime ∧ p ≡ 1 [MOD 4])) (fun p => Real.log (p:ℝ)) ≤ (1/2 + d) * t := by
    filter_upwards [htr.eventually (isOpen_Iio.mem_nhds (show (1/2:ℝ) < 1/2 + d by linarith)),
      Filter.eventually_gt_atTop (0:ℝ)] with t ht ht0
    rw [div_lt_iff₀ ht0] at ht
    exact le_of_lt ht
  obtain ⟨N, hN⟩ := nat_eventually_helper hev
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Nat.floor_natCast, apSum_eq_APtheta] at h1
  exact h1

private lemma harmonic_cast (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = Finset.sum (Finset.Icc 1 n) (fun i => ((i:ℝ))⁻¹) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

private lemma sum_inv_le_log (x : ℕ) (hx : 4 ≤ x) :
    Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)-1)) ≤ 1 + Real.log (x:ℝ) := by
  have hshift : Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)-1))
      = Finset.sum (Finset.Ico 4 x) (fun j => ((j:ℝ))⁻¹) := by
    rw [← Finset.sum_Ico_add (fun k : ℕ => 1/((k:ℝ)-1)) 4 x 1]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    rw [one_div]
    ring_nf
  rw [hshift]
  have hsub : Finset.sum (Finset.Ico 4 x) (fun j => ((j:ℝ))⁻¹) ≤ Finset.sum (Finset.Icc 1 x) (fun j => ((j:ℝ))⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      have h := Finset.mem_Ico.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j hj _
      positivity
  refine le_trans hsub ?_
  rw [← harmonic_cast]
  exact harmonic_le_one_add_log x

private lemma telesc_aux : ∀ n : ℕ, 4 ≤ n →
    Finset.sum (Finset.Ico 5 (n+1)) (fun k => 1/((k:ℝ) * ((k:ℝ)-1))) ≤ 1/4 - 1/(n:ℝ) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 4 with hlt | hge
      · have hn3 : n = 3 := by omega
        subst hn3
        have hempty : Finset.Ico 5 (3+1+1) = (∅ : Finset ℕ) := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro k hk
          have := Finset.mem_Ico.mp hk
          omega
        rw [hempty]
        simp
      · rw [Finset.sum_Ico_succ_top (by omega : 5 ≤ n+1) (f := fun k => 1/((k:ℝ) * ((k:ℝ)-1)))]
        have h1 := ih hge
        have hkey : 1/((((n+1:ℕ)):ℝ) * ((((n+1:ℕ)):ℝ)-1)) = 1/(n:ℝ) - 1/(((n+1:ℕ)):ℝ) := by
          have hn0 : (0:ℝ) < (n:ℝ) := by positivity
          have hn0' : (n:ℝ) ≠ 0 := ne_of_gt hn0
          have hn1' : ((n:ℝ) + 1) ≠ 0 := by positivity
          have e1 : (((n+1:ℕ)):ℝ) = (n:ℝ) + 1 := by push_cast; ring
          rw [e1, show (n:ℝ) + 1 - 1 = (n:ℝ) from by ring]
          rw [div_sub_div _ _ hn0' hn1']

          ring_nf
        rw [hkey]
        push_cast at h1 ⊢
        linarith

private lemma telesc_bound {x : ℕ} (hx : 4 ≤ x) :
    Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ) * ((k:ℝ)-1))) ≤ 1/4 := by
  have h := telesc_aux x hx
  have h1 : (0:ℝ) < 1/(x:ℝ) := by positivity
  linarith

private lemma apSum_succ_sub (k : ℕ) : apSum (k+1) - apSum k = apLog k := by
  rw [apSum, apSum, Finset.sum_range_succ]
  ring

private lemma abel_main (d : ℝ) (hd : 0 < d) :
    ∃ K : ℝ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      Finset.sum (pset1 x) (fun p => Real.log (p:ℝ)/((p:ℝ)-1)) ≤ (1/2 + d) * Real.log (x:ℝ) + K := by
  obtain ⟨T, hT⟩ := apSum_eventual_bound d hd
  have hCnn : 0 ≤ apSum (T+1) := apSum_nonneg (T+1)
  have hC : ∀ n, apSum (n+1) ≤ (1/2+d)*(n:ℝ) + apSum (T+1) := by
    intro n
    by_cases hn : n < T
    · have h1 : apSum (n+1) ≤ apSum (T+1) := apSum_mono (by omega)
      have h2 : (0:ℝ) ≤ (1/2+d)*(n:ℝ) := by
        apply mul_nonneg (by linarith) (by positivity)
      linarith
    · have h1 := hT n (by omega)
      linarith
  refine ⟨2*(1/2+d) + 2*(apSum (T+1)) + 1, 5, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by positivity
  have hc0 : (0:ℝ) ≤ 1/2 + d := by linarith
  -- step 1: the sum over pset1 as a sum over Ico 5 (x+1)
  have hS1 : Finset.sum (pset1 x) (fun p => Real.log (p:ℝ)/((p:ℝ)-1))
      = Finset.sum (Finset.range (x+1)) (fun k => apLog k * (1/((k:ℝ)-1))) := by
    rw [pset1, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k.Prime ∧ k % 4 = 1
    · rw [if_pos h, apLog, if_pos h, div_eq_mul_one_div]
    · rw [if_neg h, apLog, if_neg h]
      ring
  have hS2 : Finset.sum (Finset.range (x+1)) (fun k => apLog k * (1/((k:ℝ)-1)))
      = Finset.sum (Finset.Ico 5 (x+1)) (fun k => apLog k * (1/((k:ℝ)-1))) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr (by have := Finset.mem_Ico.mp hk; omega)
    · intro k hk hk5
      have hklt : k < 5 := by
        by_contra hcon
        exact hk5 (Finset.mem_Ico.mpr ⟨by omega, by have := Finset.mem_range.mp hk; omega⟩)
      rw [apLog_lt_five hklt]
      ring
  -- step 2: Abel
  have hx5 : 5 + (x - 4) = x + 1 := by omega
  have habel := abelIco 5 (x-4) apSum (fun k : ℕ => 1/((k:ℝ)-1))
  rw [hx5] at habel
  have hg : ∀ k : ℕ, 2 ≤ k → (1/((((k+1:ℕ)):ℝ)-1) - 1/((k:ℝ)-1)) = -(1/((k:ℝ)*((k:ℝ)-1))) := by
    intro k hk
    have hk1 : (1:ℝ) < (k:ℝ) := by exact_mod_cast hk
    have hk0 : (0:ℝ) < (k:ℝ) := by linarith
    have hk0' : (k:ℝ) ≠ 0 := ne_of_gt hk0
    have hk1' : ((k:ℝ) - 1) ≠ 0 := by
      have h2 : (0:ℝ) < (k:ℝ) - 1 := by linarith
      exact ne_of_gt h2
    have e1 : (((k+1:ℕ)):ℝ) - 1 = (k:ℝ) := by push_cast; ring
    rw [e1, div_sub_div _ _ hk0' hk1']
    ring_nf
  have hmain : Finset.sum (Finset.Ico 5 (x+1)) (fun k => apLog k * (1/((k:ℝ)-1)))
      = apSum (x+1) * (1/(x:ℝ)) + Finset.sum (Finset.Ico 5 (x+1)) (fun k => apSum (k+1) * (1/((k:ℝ)*((k:ℝ)-1)))) := by
    rw [show Finset.sum (Finset.Ico 5 (x+1)) (fun k => apLog k * (1/((k:ℝ)-1)))
        = Finset.sum (Finset.Ico 5 (x+1)) (fun k => (apSum (k+1) - apSum k) * (1/((k:ℝ)-1))) from by
      apply Finset.sum_congr rfl
      intro k hk
      rw [apSum_succ_sub k]]
    rw [habel]
    have hgx : (1/((((x+1:ℕ)):ℝ)-1)) = 1/(x:ℝ) := by
      congr 1
      push_cast
      ring
    have hz : apSum 5 * (1/((((5:ℕ)):ℝ) - 1)) = 0 := by
      rw [apSum_five]
      ring
    rw [hgx, hz]
    rw [show Finset.sum (Finset.Ico 5 (x+1)) (fun k => apSum (k+1) * (1/((((k+1:ℕ)):ℝ)-1) - 1/((k:ℝ)-1)))
        = Finset.sum (Finset.Ico 5 (x+1)) (fun k => -(apSum (k+1) * (1/((k:ℝ)*((k:ℝ)-1))))) from by
      apply Finset.sum_congr rfl
      intro k hk
      have hk5 : 5 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [hg k (by omega)]
      ring]
    rw [Finset.sum_neg_distrib]
    ring
  -- step 3: termwise bound
  have hterm : ∀ k ∈ Finset.Ico 5 (x+1),
      apSum (k+1) * (1/((k:ℝ)*((k:ℝ)-1))) ≤ ((1/2+d)*(k:ℝ) + apSum (T+1)) * (1/((k:ℝ)*((k:ℝ)-1))) := by
    intro k hk
    have hk5 : 5 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    have hden : (0:ℝ) < 1/((k:ℝ)*((k:ℝ)-1)) := by
      apply one_div_pos.mpr
      nlinarith
    have h1 := hC k
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt hden)
  -- step 4: expand
  have hpt : Finset.sum (Finset.Ico 5 (x+1)) (fun k => ((1/2+d)*(k:ℝ) + apSum (T+1)) * (1/((k:ℝ)*((k:ℝ)-1))))
      = (1/2+d) * Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)-1))
        + apSum (T+1) * Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)*((k:ℝ)-1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk5 : 5 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    have hk0 : (0:ℝ) < (k:ℝ) := by linarith
    have hk1 : (0:ℝ) < (k:ℝ) - 1 := by linarith
    field_simp
  -- step 5: final bound
  have hb1 : (1/2+d) * Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)-1)) ≤ (1/2+d) * (1 + Real.log (x:ℝ)) :=
    mul_le_mul_of_nonneg_left (sum_inv_le_log x hx4) hc0
  have hb2 : apSum (T+1) * Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)*((k:ℝ)-1))) ≤ apSum (T+1) * (1/4) :=
    mul_le_mul_of_nonneg_left (telesc_bound hx4) hCnn
  have hapx : apSum (x+1) * (1/(x:ℝ)) ≤ (1/2+d) + apSum (T+1) := by
    have h1 := hC x
    have h2 : apSum (x+1) * (1/(x:ℝ)) = apSum (x+1)/(x:ℝ) := by rw [mul_one_div]
    rw [h2, div_le_iff₀ hx0]
    have h3 : (1/2+d)*(x:ℝ) + apSum (T+1) ≤ ((1/2+d) + apSum (T+1)) * (x:ℝ) := by
      have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      nlinarith
    linarith
  have hstep : Finset.sum (Finset.Ico 5 (x+1)) (fun k => apSum (k+1) * (1/((k:ℝ)*((k:ℝ)-1))))
      ≤ (1/2+d) * Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)-1))
        + apSum (T+1) * Finset.sum (Finset.Ico 5 (x+1)) (fun k => 1/((k:ℝ)*((k:ℝ)-1))) := by
    rw [← hpt]
    exact Finset.sum_le_sum hterm
  rw [hS1, hS2, hmain]
  linarith

private lemma four_not_dvd (n : ℕ) : ¬ (4 ∣ n^2+1) := by
  intro h
  have h0 : ((n^2+1 : ℕ) : ZMod 4) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact h
  push_cast at h0
  have hdec : ∀ x : ZMod 4, x^2 + 1 ≠ 0 := by decide
  exact hdec (n : ZMod 4) h0

private lemma fact_two_le_one (n : ℕ) : (n^2+1).factorization 2 ≤ 1 := by
  have hfac := Nat.factorization_eq_card_pow_dvd (n^2+1) (Nat.prime_two)
  rw [hfac]
  have hsub : ((Finset.Ico 1 (n^2+1)).filter (fun i => 2^i ∣ n^2+1)) ⊆ ({1} : Finset ℕ) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi'.1).1
    have hlt : i < 2 := by
      by_contra hcon
      have hi2 : 2 ≤ i := by omega
      have h4 : 4 ∣ 2^i := by
        refine ⟨2^(i-2), ?_⟩
        rw [show i = 2 + (i-2) from by omega, pow_add]
        norm_num
      exact four_not_dvd n (h4.trans hi'.2)
    simp only [Finset.mem_singleton]
    omega
  calc ((Finset.Ico 1 (n^2+1)).filter (fun i => 2^i ∣ n^2+1)).card ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := by simp

private lemma t2_bound (x : ℕ) :
    Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n 2) ≤ (x:ℝ) := by
  have h1 : ∀ n ∈ Finset.Ioc x (2*x), vp n 2 ≤ 1 := by
    intro n hn
    have h2 := fact_two_le_one n
    simp only [vp]
    exact_mod_cast h2
  calc Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n 2) ≤ Finset.sum (Finset.Ioc x (2*x)) (fun _ => (1:ℝ)) := Finset.sum_le_sum h1
    _ = ((Finset.Ioc x (2*x)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (x:ℝ) := by
        rw [Nat.card_Ioc]
        rw [show 2*x - x = x from by omega]

private lemma log_mul_log_le (p M : ℕ) (hp : p.Prime) (hM : 0 < M) :
    Real.log (p:ℝ) * (Nat.log p M : ℝ) ≤ Real.log (M:ℝ) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have h1 : p ^ (Nat.log p M) ≤ M := Nat.pow_log_le_self p (by omega)
  have h2 : Real.log ((p:ℝ)^(Nat.log p M)) ≤ Real.log (M:ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast h1
  rw [Real.log_pow] at h2
  linarith [h2]

private lemma log_M_le (x : ℕ) (hx : 5 ≤ x) :
    Real.log ((((2*x)^2+1 : ℕ)):ℝ) ≤ 3 * Real.log (x:ℝ) := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hcast : (((2*x)^2+1 : ℕ):ℝ) = (2*(x:ℝ))^2 + 1 := by push_cast; ring
  have hM : (2*(x:ℝ))^2 + 1 ≤ 5 * (x:ℝ)^2 := by nlinarith
  have h1 : Real.log (((2*x)^2+1 : ℕ):ℝ) ≤ Real.log (5 * (x:ℝ)^2) := by
    rw [hcast]
    apply Real.log_le_log (by positivity) hM
  have h2 : Real.log (5 * (x:ℝ)^2) = Real.log 5 + 2*Real.log (x:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 5 ≤ Real.log (x:ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hx
  linarith

private lemma primeCounting_bound :
    ∃ C : ℝ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x → ((Nat.primeCounting x : ℕ) : ℝ) ≤ C * (x:ℝ) / Real.log (x:ℝ) := by
  have h := Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num)
  obtain ⟨X, hX⟩ := nat_eventually_helper h
  refine ⟨Real.log 4 + 1, max X 4, fun x hx => ?_⟩
  have h1 := hX x (le_trans (le_max_left _ _) hx)
  rw [Nat.floor_natCast] at h1
  exact h1

private lemma err_bound :
    ∃ K : ℝ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * (Nat.log p ((2*x)^2+1) : ℝ)) ≤ K * (x:ℝ) := by
  obtain ⟨Cp, Xp, hCp⟩ := primeCounting_bound
  refine ⟨Cp * 3, max Xp 5, fun x hx => ?_⟩
  have hx5 : 5 ≤ x := le_trans (le_max_right _ _) hx
  have hxp : Xp ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := Real.log_pos hx1
  have hMpos : 0 < (2*x)^2+1 := by positivity
  have hcard : (pset1 x).card ≤ Nat.primeCounting x := by
    have hsub : pset1 x ⊆ (Finset.range (x+1)).filter (fun p => p.Prime) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
    calc (pset1 x).card ≤ ((Finset.range (x+1)).filter (fun p => p.Prime)).card := Finset.card_le_card hsub
      _ = Nat.primeCounting x := by
          rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hterm : ∀ p ∈ pset1 x,
      Real.log (p:ℝ) * (Nat.log p ((2*x)^2+1) : ℝ) ≤ Real.log ((((2*x)^2+1 : ℕ)):ℝ) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact log_mul_log_le p ((2*x)^2+1) hp'.2.1 hMpos
  have hlogM : (0:ℝ) ≤ Real.log ((((2*x)^2+1 : ℕ)):ℝ) := by
    apply Real.log_nonneg
    have h2 : (1:ℕ) ≤ (2*x)^2+1 := by omega
    exact_mod_cast h2
  calc Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * (Nat.log p ((2*x)^2+1) : ℝ))
      ≤ Finset.sum (pset1 x) (fun _ => Real.log ((((2*x)^2+1 : ℕ)):ℝ)) := Finset.sum_le_sum hterm
    _ = ((pset1 x).card : ℝ) * Real.log ((((2*x)^2+1 : ℕ)):ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.primeCounting x : ℕ) : ℝ) * Real.log ((((2*x)^2+1 : ℕ)):ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · exact hlogM
    _ ≤ ((Nat.primeCounting x : ℕ) : ℝ) * (3 * Real.log (x:ℝ)) := by
        apply mul_le_mul_of_nonneg_left (log_M_le x hx5)
        positivity
    _ ≤ (Cp * (x:ℝ) / Real.log (x:ℝ)) * (3 * Real.log (x:ℝ)) := by
        apply mul_le_mul_of_nonneg_right (hCp x hxp) (by linarith)
    _ = Cp * 3 * (x:ℝ) := by
        field_simp

private lemma pset1_bnd_split (x : ℕ) :
    Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * bnd x p)
      = 2*(x:ℝ) * Finset.sum (pset1 x) (fun p => Real.log (p:ℝ)/((p:ℝ)-1))
        + 2 * Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * (Nat.log p ((2*x)^2+1) : ℝ)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [bnd]
  ring

private lemma small_split (x : ℕ) :
    Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (fun p => vp n p * Real.log (p:ℝ)))
      ≤ Real.log 2 * (x:ℝ) + Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * bnd x p) := by
  rw [small_swap x]
  have hsub : pset1 x ⊆ psetAll x := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
  rw [← Finset.sum_sdiff hsub]
  have h1 : Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p))
      ≤ Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * bnd x p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hp2 : p ≠ 2 := by
      intro hcon
      rw [hcon] at hp'
      have h1 := hp'.2.2
      norm_num at h1
    have hT := count_le_bnd x p hp'.2.1 hp2
    have hlog : (0:ℝ) ≤ Real.log (p:ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (Nat.Prime.one_lt hp'.2.1).le
    exact mul_le_mul_of_nonneg_left hT hlog
  have h2 : Finset.sum (psetAll x \ pset1 x) (fun p => Real.log (p:ℝ) * Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p))
      ≤ Real.log 2 * (x:ℝ) := by
    have hstep : ∀ p ∈ psetAll x \ pset1 x,
        Real.log (p:ℝ) * Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p) ≤ if p = 2 then Real.log 2 * (x:ℝ) else 0 := by
      intro p hp
      have hpA := Finset.mem_sdiff.mp hp
      have hpP : p.Prime := (Finset.mem_filter.mp hpA.1).2
      by_cases h2 : p = 2
      · rw [if_pos h2, h2]
        have hT := t2_bound x
        have hlog : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact mul_le_mul_of_nonneg_left hT hlog
      · rw [if_neg h2]
        have hT0 : Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p) = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          have hnd : ¬ p ∣ n^2+1 := by
            intro hd
            have h4 := prime_mod_four hpP h2 hd
            have hpx : p ≤ x := by
              have h9 := Finset.mem_range.mp (Finset.mem_filter.mp hpA.1).1
              omega
            exact hpA.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpP, h4⟩)
          simp only [vp]
          rw [Nat.factorization_eq_zero_of_not_dvd hnd]
          simp
        rw [hT0]
        simp
    calc Finset.sum (psetAll x \ pset1 x) (fun p => Real.log (p:ℝ) * Finset.sum (Finset.Ioc x (2*x)) (fun n => vp n p))
        ≤ Finset.sum (psetAll x \ pset1 x) (fun p => if p = 2 then Real.log 2 * (x:ℝ) else 0) := Finset.sum_le_sum hstep
      _ = (if 2 ∈ psetAll x \ pset1 x then Real.log 2 * (x:ℝ) else 0) := by
          rw [Finset.sum_ite_eq']
      _ ≤ Real.log 2 * (x:ℝ) := by
          split_ifs with h
          · exact le_refl _
          · have hlog : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
            nlinarith
  linarith

theorem PEqualNP.Outside.L_quadratic_primes_small_prime_mass :
    let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p:ℝ); let small := fun (x : ℕ) => Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (w n)); ∀ e : ℝ, 0 < e → ∃ X : ℕ, ∀ x : ℕ, X ≤ x → small x ≤ (1+e)*(x:ℝ)*Real.log (x:ℝ) := by
  dsimp only
  intro e he
  have hd8 : (0:ℝ) < e/8 := by linarith
  obtain ⟨K1, X1, hK1⟩ := abel_main (e/8) hd8
  obtain ⟨K2, X2, hK2⟩ := err_bound
  have hlogtop : ∀ᶠ (t : ℝ) in Filter.atTop,
      (Real.log 2 + 2*K1 + 2*K2) ≤ (e/2) * Real.log t := by
    have h1 : ∀ᶠ (t : ℝ) in Filter.atTop, (Real.log 2 + 2*K1 + 2*K2)/(e/2) ≤ Real.log t :=
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop _)
    filter_upwards [h1] with t ht
    rw [div_le_iff₀ (by linarith : (0:ℝ) < e/2)] at ht
    linarith
  obtain ⟨X3, hX3⟩ := nat_eventually_helper hlogtop
  refine ⟨max X1 (max X2 (max X3 5)), fun x hx => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X2 ≤ x := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hx3 : X3 ≤ x := le_trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hx
  have hx5 : 5 ≤ x := le_trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hx
  have hA := hK1 x hx1
  have hE := hK2 x hx2
  have hK := hX3 x hx3
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hx1' : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hlogx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg hx1'
  have hS := small_split x
  have hsplit := pset1_bnd_split x
  have h2 : 2*(x:ℝ) * Finset.sum (pset1 x) (fun p => Real.log (p:ℝ)/((p:ℝ)-1))
      ≤ 2*(x:ℝ) * ((1/2+e/8)*Real.log (x:ℝ) + K1) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h3 : 2 * Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * (Nat.log p ((2*x)^2+1) : ℝ))
      ≤ 2*(K2*(x:ℝ)) := by
    have h4 := mul_le_mul_of_nonneg_left hE (show (0:ℝ) ≤ 2 by norm_num)
    linarith
  have h6 := mul_le_mul_of_nonneg_right hK hx0
  calc Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => p ≤ x)) (fun p => vp n p * Real.log (p:ℝ)))
      ≤ Real.log 2 * (x:ℝ) + Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * bnd x p) := hS
    _ = Real.log 2 * (x:ℝ) + (2*(x:ℝ) * Finset.sum (pset1 x) (fun p => Real.log (p:ℝ)/((p:ℝ)-1))
          + 2 * Finset.sum (pset1 x) (fun p => Real.log (p:ℝ) * (Nat.log p ((2*x)^2+1) : ℝ))) := by
        rw [hsplit]
    _ ≤ Real.log 2 * (x:ℝ) + (2*(x:ℝ)*((1/2+e/8)*Real.log (x:ℝ) + K1) + 2*(K2*(x:ℝ))) := by
        linarith
    _ = (1 + e/4) * ((x:ℝ) * Real.log (x:ℝ)) + (Real.log 2 + 2*K1 + 2*K2) * (x:ℝ) := by ring
    _ ≤ (1 + e/4) * ((x:ℝ) * Real.log (x:ℝ)) + (e/2) * Real.log (x:ℝ) * (x:ℝ) := by linarith
    _ ≤ (1 + e) * (x:ℝ) * Real.log (x:ℝ) := by
        have h7 : (0:ℝ) ≤ (x:ℝ) * Real.log (x:ℝ) := mul_nonneg hx0 hlogx
        nlinarith
