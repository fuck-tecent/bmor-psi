import Mathlib

private theorem wsrb_meas (X : ℕ) (ρ n : ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)} := by
  have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q} ∩ {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [h]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem wsrb_add (g : ℝ → ℂ) (hg : Continuous g) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hd : Disjoint B C) :
    (intervalIntegral (fun t => (B ∪ C).indicator g t) (0:ℝ) 1 MeasureTheory.volume).re =
      (intervalIntegral (fun t => B.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re +
      (intervalIntegral (fun t => C.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re := by
  have hi : ∀ D : Set ℝ, MeasurableSet D →
      IntervalIntegrable (fun t => D.indicator g t) MeasureTheory.volume 0 1 := by
    intro D hD
    have := (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this ⊢
    exact this.indicator hD
  have : (fun t => (B ∪ C).indicator g t) = fun t => B.indicator g t + C.indicator g t := by
    funext t
    rw [Set.indicator_union_of_disjoint hd]
  rw [this, intervalIntegral.integral_add (hi B hB) (hi C hC), Complex.add_re]

private theorem wsrb_core (g : ℕ → ℝ → ℂ) (hg : ∀ n, Continuous (g n))
    (W A Lw I : ℕ → Set ℝ) (hW : ∀ n, MeasurableSet (W n)) (hA : ∀ n, MeasurableSet (A n))
    (hL : ∀ n, MeasurableSet (Lw n)) (hI : ∀ n, MeasurableSet (I n))
    (N0 : ℕ) (hsub : ∀ n, N0 ≤ n → Lw n ⊆ W n)
    (J : ℕ → Set ℝ → ℝ)
    (hJ : ∀ n B, J n B = (intervalIntegral (fun t => B.indicator (g n) t) (0:ℝ) 1 MeasureTheory.volume).re)
    (h1 : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (Lw n \ A n))
    (h2 : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n:ℝ)) ≤ J n (((W n \ A n) \ (Lw n \ A n)) ∩ I n))
    (h3 : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n:ℝ)) ≤ J n (((W n \ A n) \ (Lw n \ A n)) \ I n)) :
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (W n \ A n) := by
  intro e he
  obtain ⟨N1, k1⟩ := h1 (e/3) (by positivity)
  obtain ⟨N2, k2⟩ := h2 (e/3) (by positivity)
  obtain ⟨N3, k3⟩ := h3 (e/3) (by positivity)
  refine ⟨max N0 (max N1 (max N2 N3)), fun n hn hev => ?_⟩
  have a0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have a1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have a2 : N2 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have a3 : N3 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have b1 := k1 n a1 hev
  have b2 := k2 n a2 hev
  have b3 := k3 n a3 hev
  set X := W n \ A n with hX
  set L := Lw n \ A n with hLd
  have hLX : L ⊆ X := Set.diff_subset_diff_left (hsub n a0)
  have mX : MeasurableSet X := (hW n).diff (hA n)
  have mL : MeasurableSet L := (hL n).diff (hA n)
  have mR : MeasurableSet (X \ L) := mX.diff mL
  have mRI : MeasurableSet ((X \ L) ∩ I n) := mR.inter (hI n)
  have mRJ : MeasurableSet ((X \ L) \ I n) := mR.diff (hI n)
  have e1 : X = L ∪ (((X \ L) ∩ I n) ∪ ((X \ L) \ I n)) := by
    rw [Set.inter_union_diff, Set.union_diff_cancel hLX]
  have d1 : Disjoint ((X \ L) ∩ I n) ((X \ L) \ I n) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact ht'.2 ht.2
  have d2 : Disjoint L (((X \ L) ∩ I n) ∪ ((X \ L) \ I n)) := by
    rw [Set.inter_union_diff]
    exact Set.disjoint_sdiff_right
  have : J n X = J n L + (J n ((X \ L) ∩ I n) + J n ((X \ L) \ I n)) := by
    rw [hJ, hJ, hJ, hJ]
    conv_lhs => rw [e1]
    rw [wsrb_add (g n) (hg n) _ _ mL (mRI.union mRJ) d2, wsrb_add (g n) (hg n) _ _ mRI mRJ d1]
  rw [this]
  linarith

private theorem wsrb_pow (L : ℕ) (hL : 40 ≤ L) : L ^ 6 + 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : 10 * (L + 1) ≤ 11 * L := by omega
    have h2 : (10 * (L + 1)) ^ 6 ≤ (11 * L) ^ 6 := Nat.pow_le_pow_left h1 6
    have h3 : 10 ^ 6 * (L + 1) ^ 6 ≤ 2 * 10 ^ 6 * L ^ 6 := by
      calc 10 ^ 6 * (L + 1) ^ 6 = (10 * (L + 1)) ^ 6 := by ring
        _ ≤ (11 * L) ^ 6 := h2
        _ = 11 ^ 6 * L ^ 6 := by ring
        _ ≤ 2 * 10 ^ 6 * L ^ 6 := by
          apply Nat.mul_le_mul_right; norm_num
    have h4 : (L + 1) ^ 6 ≤ 2 * L ^ 6 := by
      have : 10 ^ 6 * (L + 1) ^ 6 ≤ 10 ^ 6 * (2 * L ^ 6) := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by norm_num)
    have h5 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
    omega

private theorem wsrb_ev : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (Nat.log 2 (n+2))^2 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
  refine ⟨2 ^ 40, fun n hn => ?_⟩
  have hl : 40 ≤ Nat.log 2 (n+2) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    omega
  have hp := wsrb_pow _ hl
  have hq : 2 ^ Nat.log 2 (n+2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have h6 : (Nat.log 2 (n+2)) ^ 6 ≤ n := by omega
  apply Nat.le_floor
  have h6' : (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 3 ≤ (n:ℝ) := by
    have : (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 3 = (((Nat.log 2 (n+2))^6 : ℕ) : ℝ) := by
      push_cast; ring
    rw [this]; exact_mod_cast h6
  have h0 : (0:ℝ) ≤ (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc (((Nat.log 2 (n+2))^2 : ℕ) : ℝ)
      = ((((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 3) ^ (1/3:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
    _ ≤ (n:ℝ) ^ (1/3:ℝ) := Real.rpow_le_rpow (by positivity) h6' (by norm_num)

theorem Conjectures.Goldbach.WideSignedRemainderBridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor lowPart → (floor (fun n => remainder n ∩ inner n)) → (floor (fun n => remainder n \ inner n)) → (floor (fun n => wideArcs n \ arcs n)) := by
  intro w E S Q arcs f Q₁ H wideArcs lowWideArcs lowPart remainder inner J floor h1 h2 h3
  obtain ⟨N0, hN0⟩ := wsrb_ev
  have hcont : ∀ n, Continuous (f n) := by
    intro n
    simp only [f, S, E]
    fun_prop
  refine wsrb_core f hcont wideArcs arcs lowWideArcs inner ?_ ?_ ?_ ?_ N0 ?_ J (fun _ _ => rfl) h1 h2 h3
  · intro n; exact wsrb_meas _ _ _
  · intro n; exact wsrb_meas _ _ _
  · intro n; exact wsrb_meas _ _ _
  · intro n; exact wsrb_meas _ _ _
  · intro n hn t ht
    obtain ⟨q, a, h1', h2', h3', h4', h5'⟩ := ht
    have hQ : Q n ≤ Q₁ n := hN0 n hn
    refine ⟨q, a, h1', le_trans h2' hQ, h3', h4', ?_⟩
    exact h5'
