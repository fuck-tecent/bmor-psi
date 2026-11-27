import Mathlib
import Conjectures.Goldbach.DynShiftFactorMean

private lemma bcb_card_upper (s : ℕ) (hs : 1 ≤ s) :
    (((Finset.Icc s (2*s)).filter Nat.Prime).card : ℝ) * Real.log s ≤ 3 * s := by
  have hexp : Chebyshev.theta ((2*s : ℕ) : ℝ) =
      ∑ p ∈ Finset.Ioc 0 (2*s), (if p.Prime then Real.log (p:ℝ) else 0) := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, Finset.sum_filter]
  have h1 : ((Finset.Icc s (2*s)).filter Nat.Prime).card * Real.log s ≤
      ∑ p ∈ (Finset.Icc s (2*s)).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := Finset.mem_filter.mp hp
    have h2 := Finset.mem_Icc.mp hp'.1
    exact Real.log_le_log (by exact_mod_cast hs) (by exact_mod_cast h2.1)
  have h2 : ∑ p ∈ (Finset.Icc s (2*s)).filter Nat.Prime, Real.log (p:ℝ) ≤
      Chebyshev.theta ((2*s : ℕ) : ℝ) := by
    rw [hexp, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => Real.log_natCast_nonneg p)
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have h2 := Finset.mem_Icc.mp hp'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h2.2⟩, hp'.2⟩
  have h3 := Chebyshev.theta_le_log4_mul_x (x := ((2*s : ℕ) : ℝ)) (by positivity)
  have h4 : Real.log 4 ≤ 1.4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [this]; have := Real.log_two_lt_d9; linarith
  push_cast at h3 h2
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h4 hs0]

private lemma bcb_log_cube (s : ℕ) : Real.log s ^ 3 ≤ 27 * s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hL : 0 ≤ Real.log s := Real.log_natCast_nonneg s
  have h1 := Real.add_one_le_exp (Real.log s / 3)
  have h2 : (Real.log s / 3) ^ 3 ≤ Real.exp (Real.log s / 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h3 : Real.exp (Real.log s / 3) ^ 3 = s := by
    rw [← Real.exp_nat_mul]
    rw [show ((3:ℕ):ℝ) * (Real.log s / 3) = Real.log s by push_cast; ring]
    exact Real.exp_log hsR
  rw [h3] at h2
  nlinarith

private lemma bcb_pair (Kc : ℝ) (Z0 : ℕ)
    (hZ : ∀ Z : ℕ, Z0 ≤ Z → ∀ a d : ℕ, 0 < d → Even d → d ≤ Z →
      (((Finset.Icc a (a + Z)).filter (fun m => m.Prime ∧ (m + d).Prime)).card : ℝ) ≤
        Kc * (Z : ℝ) * (∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2))) / (Real.log (Z : ℝ))^2)
    (s W y p q : ℕ) (hs3 : 3 ≤ s) (hW : Z0 ≤ W) (hsW : s ≤ W)
    (B : Finset ℕ) (hB : B ⊆ Finset.Ico y (y+W))
    (hp : p ∈ (Finset.Icc s (2*s)).filter Nat.Prime) (hq : q ∈ (Finset.Icc s (2*s)).filter Nat.Prime)
    (hpq : p < q) :
    ((B.filter (fun n => p ≤ n ∧ q ≤ n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card : ℝ) ≤
      Kc * (W : ℝ) * (∏ l ∈ (q-p).primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2))) / (Real.log (W : ℝ))^2 := by
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hp2 := Finset.mem_Icc.mp hp'.1
  have hq2 := Finset.mem_Icc.mp hq'.1
  have hpodd : Odd p := hp'.2.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq'.2.odd_of_ne_two (by omega)
  have hev : Even (q - p) := Nat.Odd.sub_odd hqodd hpodd
  refine le_trans ?_ (hZ W hW (y - q) (q - p) (by omega) hev (by omega))
  refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn (fun n => n - q) ?_ ?_)
  · intro n hn
    beta_reduce
    have hn' := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    have hB' := Finset.mem_Ico.mp (hB hn'.1)
    obtain ⟨h1, h2, h3, h4⟩ := hn'.2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h4, ?_⟩)
    rw [show n - q + (q - p) = n - p by omega]; exact h3
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    simp only at hab
    have := ha'.2.2.1; have := hb'.2.2.1
    omega

private lemma bcb_block (Kc Cm : ℝ) (hKc : 0 ≤ Kc) (Z0 : ℕ) (S : ℕ → ℝ)
    (hS : ∀ d, S d = ∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2)))
    (hZ : ∀ Z : ℕ, Z0 ≤ Z → ∀ a d : ℕ, 0 < d → Even d → d ≤ Z →
      (((Finset.Icc a (a + Z)).filter (fun m => m.Prime ∧ (m + d).Prime)).card : ℝ) ≤
        Kc * (Z : ℝ) * (∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2))) / (Real.log (Z : ℝ))^2)
    (s W y : ℕ) (hs3 : 3 ≤ s) (hW : Z0 ≤ W) (hsW : s ≤ W)
    (B : Finset ℕ) (hB : B ⊆ Finset.Ico y (y+W))
    (hm : ∑ p ∈ (Finset.Icc s (2*s)).filter Nat.Prime,
        ∑ q ∈ ((Finset.Icc s (2*s)).filter Nat.Prime).filter (fun q => p < q), S (q-p)
        ≤ Cm * ((((Finset.Icc s (2*s)).filter Nat.Prime).card : ℕ) : ℝ)^2) :
    ∑ n ∈ B, ((((Finset.Icc s (2*s)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ)^2 ≤
      ((((Finset.Icc s (2*s)).filter Nat.Prime).card : ℕ) : ℝ) * W +
        2 * (Kc * (W:ℝ) / Real.log (W:ℝ)^2) * (Cm * ((((Finset.Icc s (2*s)).filter Nat.Prime).card : ℕ) : ℝ)^2) := by
  set Pf := (Finset.Icc s (2*s)).filter Nat.Prime with hPf
  set G : ℝ := Kc * (W:ℝ) / Real.log (W:ℝ)^2 with hG
  let T : ℕ → ℕ → ℕ := fun p q => (B.filter (fun n => p ≤ n ∧ q ≤ n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card
  have hTsymm : ∀ p q, T p q = T q p := by
    intro p q
    simp only [T]
    congr 1
    ext n
    simp only [Finset.mem_filter]
    tauto
  have hTle : ∀ p q, T p q ≤ W := by
    intro p q
    simp only [T]
    calc _ ≤ B.card := Finset.card_filter_le _ _
      _ ≤ (Finset.Ico y (y+W)).card := Finset.card_le_card hB
      _ = W := by simp
  have hTpair : ∀ p ∈ Pf, ∀ q ∈ Pf, p < q → (T p q : ℝ) ≤ G * S (q-p) := by
    intro p hp q hq hpq
    have := bcb_pair Kc Z0 hZ s W y p q hs3 hW hsW B hB hp hq hpq
    rw [hS]
    simp only [T]
    refine le_trans this (le_of_eq ?_)
    simp only [hG]; ring
  have hsq : ∀ n, ((Pf.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ)^2 =
      ∑ p ∈ Pf, ∑ q ∈ Pf, ((if (p ≤ n ∧ Nat.Prime (n-p)) then (1:ℝ) else 0) *
        (if (q ≤ n ∧ Nat.Prime (n-q)) then (1:ℝ) else 0)) := by
    intro n
    rw [sq, Finset.card_filter]
    push_cast
    rw [Finset.sum_mul_sum]
  have hsum : ∑ n ∈ B, ((Pf.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ)^2 =
      ∑ p ∈ Pf, ∑ q ∈ Pf, (T p q : ℝ) := by
    simp only [hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [T, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases a : p ≤ n <;> by_cases b : q ≤ n <;> by_cases c : Nat.Prime (n-p) <;>
      by_cases d : Nat.Prime (n-q) <;> simp [a, b, c, d]
  have hsplit : ∑ p ∈ Pf, ∑ q ∈ Pf, (T p q : ℝ) =
      ∑ p ∈ Pf, (T p p : ℝ) + ∑ p ∈ Pf, ∑ q ∈ Pf, (if p < q then (T p q : ℝ) else 0)
        + ∑ p ∈ Pf, ∑ q ∈ Pf, (if q < p then (T p q : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have : ∑ q ∈ Pf, (T p q : ℝ) = ∑ q ∈ Pf, ((if q = p then (T p q : ℝ) else 0) +
        (if p < q then (T p q : ℝ) else 0) + (if q < p then (T p q : ℝ) else 0)) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rcases lt_trichotomy p q with h | h | h
      · simp [h, h.ne', not_lt.mpr h.le]
      · subst h; simp
      · simp [h, h.ne, not_lt.mpr h.le]
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Pf p, if_pos hp]
  have hdiag : ∑ p ∈ Pf, (T p p : ℝ) ≤ (Pf.card : ℝ) * W := by
    calc _ ≤ ∑ p ∈ Pf, (W : ℝ) := Finset.sum_le_sum fun p _ => by exact_mod_cast hTle p p
      _ = _ := by simp
  have hup : ∑ p ∈ Pf, ∑ q ∈ Pf, (if p < q then (T p q : ℝ) else 0) ≤ G * (Cm * (Pf.card : ℝ)^2) := by
    have hG0 : 0 ≤ G := by
      simp only [hG]; positivity
    calc _ = ∑ p ∈ Pf, ∑ q ∈ Pf.filter (fun q => p < q), (T p q : ℝ) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ p ∈ Pf, ∑ q ∈ Pf.filter (fun q => p < q), G * S (q - p) := by
          refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
          have hq' := Finset.mem_filter.mp hq
          exact hTpair p hp q hq'.1 hq'.2
      _ = G * ∑ p ∈ Pf, ∑ q ∈ Pf.filter (fun q => p < q), S (q - p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hG0
  have hdown : ∑ p ∈ Pf, ∑ q ∈ Pf, (if q < p then (T p q : ℝ) else 0) =
      ∑ p ∈ Pf, ∑ q ∈ Pf, (if p < q then (T p q : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hTsymm]
  rw [hsum, hsplit, hdown]
  linarith

private lemma bcb_final (Kc Cm : ℝ) (hKc : 0 < Kc) (hCm : 0 < Cm) (s W X : ℕ) (c : ℝ)
    (hs3 : 3 ≤ s) (hsW : s ≤ W) (hc0 : 0 ≤ c) (hcu : c * Real.log s ≤ 3 * s)
    (hX1 : s * s ≤ X) (hX2 : X < (s+1)*(s+1)) :
    c * W + 2 * (Kc * (W:ℝ) / Real.log (W:ℝ)^2) * (Cm * c^2) ≤
      (256 * (81 + 18 * Kc * Cm)) * (W:ℝ) * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2)^2 := by
  have hs3R : (3:ℝ) ≤ s := by exact_mod_cast hs3
  have hsWR : (s:ℝ) ≤ W := by exact_mod_cast hsW
  have hL : 0 < Real.log s := Real.log_pos (by linarith)
  have hLw : Real.log s ≤ Real.log W := Real.log_le_log (by linarith) hsWR
  have hX2' : X ≤ s ^ 4 := by
    have h1 : X < 4 * (s*s) := by nlinarith
    have h2 : 4 ≤ s * s := by nlinarith
    calc X ≤ 4 * (s*s) := h1.le
      _ ≤ (s*s)*(s*s) := Nat.mul_le_mul_right _ h2
      _ = s^4 := by ring
  have hXR1 : (s:ℝ)^2 ≤ X := by exact_mod_cast (by nlinarith : s^2 ≤ X)
  have hXR0 : (0:ℝ) < X := by nlinarith
  have hXR2 : (X:ℝ) ≤ (s:ℝ)^4 := by exact_mod_cast hX2'
  have hlogX : Real.log X ≤ 4 * Real.log s := by
    have := Real.log_le_log hXR0 hXR2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogX0 : 0 < Real.log X := Real.log_pos (by nlinarith)
  have hcube := bcb_log_cube s
  have hM : (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2)^2 = X / (Real.log X)^4 := by
    rw [div_pow, Real.sq_sqrt hXR0.le]; ring
  rw [hM]
  set L := Real.log s with hLdef
  set A : ℝ := (W:ℝ) * (s:ℝ)^2 / L^4 with hA
  have hA0 : 0 ≤ A := by positivity
  have hsR : (0:ℝ) < s := by linarith
  have hWR : (0:ℝ) < W := by linarith
  have hL4 : 0 < L^4 := by positivity
  have hcL : c ≤ 3 * s / L := by rw [le_div_iff₀ hL]; exact hcu
  have claim1 : c * W ≤ 81 * A := by
    have h1 : c * W ≤ 3 * s / L * W := mul_le_mul_of_nonneg_right hcL hWR.le
    refine le_trans h1 ?_
    rw [hA, div_mul_eq_mul_div, show 81 * ((W:ℝ) * (s:ℝ)^2 / L^4) = (81 * W * s^2) / L^4 by ring,
      div_le_div_iff₀ hL hL4]
    nlinarith [mul_le_mul_of_nonneg_left hcube (by positivity : (0:ℝ) ≤ 3 * s * W * L)]
  have claim2 : 2 * (Kc * (W:ℝ) / Real.log (W:ℝ)^2) * (Cm * c^2) ≤ 18 * Kc * Cm * A := by
    have h1 : Kc * (W:ℝ) / Real.log (W:ℝ)^2 ≤ Kc * (W:ℝ) / L^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hL.le hLw 2)
    have h2 : c^2 ≤ (3 * s / L)^2 := pow_le_pow_left₀ hc0 hcL 2
    calc _ ≤ 2 * (Kc * (W:ℝ) / L^2) * (Cm * (3 * s / L)^2) := by gcongr
      _ = _ := by rw [hA]; field_simp; ring
  have claim3 : (81 + 18 * Kc * Cm) * A ≤ (256 * (81 + 18 * Kc * Cm)) * (W:ℝ) * (X / Real.log X ^ 4) := by
    have h4 : Real.log X ^ 4 ≤ 256 * L^4 := by
      calc _ ≤ (4 * L)^4 := pow_le_pow_left₀ hlogX0.le hlogX 4
        _ = _ := by ring
    have h5 : (s:ℝ)^2/(256*L^4) ≤ X/Real.log X^4 :=
      div_le_div₀ hXR0.le hXR1 (by positivity) h4
    calc (81 + 18 * Kc * Cm) * A = (256 * (81 + 18 * Kc * Cm)) * (W:ℝ) * ((s:ℝ)^2/(256*L^4)) := by
          rw [hA]; field_simp
      _ ≤ _ := by gcongr
  nlinarith

theorem Conjectures.Goldbach.DynBlockCollisionBudget :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → (∑ n ∈ B X y, (H X n:ℝ)^2) ≤ C*(W X:ℝ)*(M X)^2 := by
  intro E P H W B M
  obtain ⟨Kc, hKc, Z0, hZ⟩ := shifted_pair_upper
  obtain ⟨Cm, hCm, Xm, hm⟩ := Conjectures.Goldbach.DynShiftFactorMean
  refine ⟨256 * (81 + 18 * Kc * Cm), by positivity, max Xm ((max Z0 3) * (max Z0 3)), ?_⟩
  intro X hX y hy1 hy2
  have hXm : Xm ≤ X := le_trans (le_max_left _ _) hX
  have hsN : max Z0 3 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (le_trans (le_max_right _ _) hX)
  have hs3 : 3 ≤ Nat.sqrt X := le_trans (le_max_right _ _) hsN
  have hsZ : Z0 ≤ Nat.sqrt X := le_trans (le_max_left _ _) hsN
  have hsq1 : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  have hsq2 : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
  have hr : 1 ≤ Nat.sqrt (Nat.sqrt X) := by
    rw [Nat.le_sqrt]; omega
  have hsW : Nat.sqrt X ≤ W X := by
    show Nat.sqrt X ≤ Nat.sqrt X * Nat.sqrt (Nat.sqrt X)
    exact Nat.le_mul_of_pos_right _ hr
  have hBsub : B X y ⊆ Finset.Ico y (y + W X) := by
    intro n hn
    have := (Finset.mem_filter.mp hn).2
    exact Finset.mem_Ico.mpr this
  have hm' := hm X hXm
  have key := bcb_block Kc Cm hKc.le Z0 (fun d => ∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2)))
    (fun d => rfl) hZ (Nat.sqrt X) (W X) y hs3 (le_trans hsZ hsW) hsW (B X y) hBsub hm'
  have hfin := bcb_final Kc Cm hKc hCm (Nat.sqrt X) (W X) X
    ((((Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime).card : ℕ) : ℝ) hs3 hsW (Nat.cast_nonneg _)
    (bcb_card_upper _ (by omega)) hsq1 hsq2
  exact le_trans key hfin
