import Mathlib

open Finset

namespace Conjectures.Goldbach.RectangularCornerBudget_aux

noncomputable section

def harmonicBox (M : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 M, (d:ℝ)⁻¹

def invHit (q u : ℕ) : ℝ := if q ∣ u then (u:ℝ)⁻¹ else 0

theorem invHit_nonneg (q u : ℕ) : 0 ≤ invHit q u := by
  unfold invHit
  split_ifs <;> positivity

theorem harmonicBox_nonneg (M : ℕ) : 0 ≤ harmonicBox M :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem hitHarmonic (M q : ℕ) (hq : 0 < q) :
    (∑ u ∈ Finset.Icc 1 M, invHit q u) ≤ (q:ℝ)⁻¹ * harmonicBox M := by
  let S := Finset.Icc 1 (M/q)
  have hs : (Finset.Icc 1 M).filter (q ∣ ·) = S.image (fun k => q * k) := by
    ext u
    constructor
    · intro h
      obtain ⟨huk, huq⟩ := Finset.mem_filter.mp h
      obtain ⟨k, rfl⟩ := huq
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp huk
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by cases k <;> simp_all,
        (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using h2)⟩, rfl⟩
    · intro h
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hq hk1,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hk2⟩, dvd_mul_right _ _⟩
  unfold invHit
  rw [← Finset.sum_filter, hs,
    Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  simp only [Nat.cast_mul, mul_inv, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)) (fun _ _ _ => by positivity)

theorem rect (A D : ℕ) (T : ℕ → ℝ) (hT : ∀ q, 0 ≤ T q) :
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((∑ q ∈ (u.gcd v).divisors, T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤
      (∑ q ∈ Finset.Icc 1 (min A D), T q*(q:ℝ)⁻¹^2) *
        (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹) * (∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹) := by
  have he (u v : ℕ) (hu : u ∈ Finset.Icc 1 A) (hv : v ∈ Finset.Icc 1 D) :
      (∑ q ∈ (u.gcd v).divisors, T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹
        = ∑ q ∈ Finset.Icc 1 (min A D), T q * invHit q u * invHit q v := by
    have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
    have hv0 : 0 < v := (Finset.mem_Icc.mp hv).1
    have hu2 : u ≤ A := (Finset.mem_Icc.mp hu).2
    have hv2 : v ≤ D := (Finset.mem_Icc.mp hv).2
    have hg0 : 0 < u.gcd v := Nat.gcd_pos_of_pos_left _ hu0
    have hdiv : (u.gcd v).divisors
        = (Finset.Icc 1 (min A D)).filter (fun q => q ∣ u ∧ q ∣ v) := by
      ext q
      rw [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · intro h
        have hqu : q ∣ u := h.1.trans (Nat.gcd_dvd_left u v)
        have hqv : q ∣ v := h.1.trans (Nat.gcd_dvd_right u v)
        refine ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hqu hu0, ?_⟩, hqu, hqv⟩
        exact le_min ((Nat.le_of_dvd hu0 hqu).trans hu2) ((Nat.le_of_dvd hv0 hqv).trans hv2)
      · intro h
        exact ⟨Nat.dvd_gcd h.2.1 h.2.2, hg0.ne'⟩
    rw [hdiv, Finset.sum_filter, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases ha : q ∣ u <;> by_cases hb : q ∣ v <;> simp [invHit, ha, hb]
  calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
          ((∑ q ∈ (u.gcd v).divisors, T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹))
      = ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
          ∑ q ∈ Finset.Icc 1 (min A D), T q * invHit q u * invHit q v :=
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => he u v hu hv
    _ = ∑ u ∈ Finset.Icc 1 A, ∑ q ∈ Finset.Icc 1 (min A D),
          ∑ v ∈ Finset.Icc 1 D, T q * invHit q u * invHit q v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 (min A D), ∑ u ∈ Finset.Icc 1 A,
          ∑ v ∈ Finset.Icc 1 D, T q * invHit q u * invHit q v := Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 (min A D),
          T q * (∑ u ∈ Finset.Icc 1 A, invHit q u) * (∑ v ∈ Finset.Icc 1 D, invHit q v) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, T q * invHit q u * invHit q v
          = (∑ u ∈ Finset.Icc 1 A, T q * invHit q u) * (∑ v ∈ Finset.Icc 1 D, invHit q v) :=
            (Finset.sum_mul_sum _ _ (fun u => T q * invHit q u) (fun v => invHit q v)).symm
        _ = T q * (∑ u ∈ Finset.Icc 1 A, invHit q u) * (∑ v ∈ Finset.Icc 1 D, invHit q v) := by
            have e : (∑ u ∈ Finset.Icc 1 A, T q * invHit q u)
                = T q * (∑ u ∈ Finset.Icc 1 A, invHit q u) :=
              (Finset.mul_sum _ _ _).symm
            rw [e]
    _ ≤ ∑ q ∈ Finset.Icc 1 (min A D),
          T q * ((q:ℝ)⁻¹ * harmonicBox A) * ((q:ℝ)⁻¹ * harmonicBox D) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hA := hitHarmonic A q hq1
      have hD := hitHarmonic D q hq1
      have hD0 : 0 ≤ ∑ v ∈ Finset.Icc 1 D, invHit q v :=
        Finset.sum_nonneg fun v _ => invHit_nonneg q v
      have hb : 0 ≤ T q * ((q:ℝ)⁻¹ * harmonicBox A) :=
        mul_nonneg (hT q) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q))
          (harmonicBox_nonneg A))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA (hT q)) hD hD0 hb
    _ = (∑ q ∈ Finset.Icc 1 (min A D), T q*(q:ℝ)⁻¹^2) * harmonicBox A * harmonicBox D := by
      have h2 (q : ℕ) (hq : q ∈ Finset.Icc 1 (min A D)) :
          T q * ((q:ℝ)⁻¹ * harmonicBox A) * ((q:ℝ)⁻¹ * harmonicBox D)
            = (T q*(q:ℝ)⁻¹^2) * (harmonicBox A * harmonicBox D) := by ring
      calc ∑ q ∈ Finset.Icc 1 (min A D),
              T q * ((q:ℝ)⁻¹ * harmonicBox A) * ((q:ℝ)⁻¹ * harmonicBox D)
          = ∑ q ∈ Finset.Icc 1 (min A D),
              (T q*(q:ℝ)⁻¹^2) * (harmonicBox A * harmonicBox D) :=
            Finset.sum_congr rfl fun q hq => h2 q hq
        _ = (∑ q ∈ Finset.Icc 1 (min A D), T q*(q:ℝ)⁻¹^2)
              * (harmonicBox A * harmonicBox D) := (Finset.sum_mul _ _ _).symm
        _ = _ := by ring

theorem cardIcc1 (M : ℕ) : ((Finset.Icc 1 M).card : ℝ) = (M:ℝ) := by
  rw [Nat.card_Icc]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · norm_num
  · rw [Nat.add_sub_cancel]

theorem sum_const_card (s : Finset ℕ) (K : ℝ) : (∑ _ ∈ s, K) = (s.card : ℝ) * K := by
  rw [Finset.sum_const, nsmul_eq_mul]

theorem sum_const_Icc (M : ℕ) (K : ℝ) : (∑ _ ∈ Finset.Icc 1 M, K) = (M:ℝ) * K := by
  rw [sum_const_card, cardIcc1]

theorem gcd_sq_le_divisors (g : ℕ) (hg : 0 < g) : (g:ℝ)^2 ≤ ∑ q ∈ g.divisors, (q:ℝ)^2 := by
  have hmem : g ∈ g.divisors := Nat.mem_divisors_self g hg.ne'
  exact Finset.single_le_sum (f := fun q : ℕ => (q:ℝ)^2) (fun _ _ => by positivity)
    (a := g) hmem

theorem gcdSum (A D : ℕ) :
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((u.gcd v:ℕ):ℝ)^2 * (u:ℝ)⁻¹ * (v:ℝ)⁻¹)
      ≤ (min A D : ℝ) * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹)
        * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by
  have hstep : ∀ u ∈ Finset.Icc 1 A, ∀ v ∈ Finset.Icc 1 D,
      ((u.gcd v:ℕ):ℝ)^2 * (u:ℝ)⁻¹ * (v:ℝ)⁻¹
        ≤ (∑ q ∈ (u.gcd v).divisors, (q:ℝ)^2) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹ := by
    intro u hu v hv
    have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
    have hg0 : 0 < u.gcd v := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left u v) hu0
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (gcd_sq_le_divisors _ hg0) (by positivity)) (by positivity)
  calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((u.gcd v:ℕ):ℝ)^2 * (u:ℝ)⁻¹ * (v:ℝ)⁻¹)
      ≤ ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((∑ q ∈ (u.gcd v).divisors, (q:ℝ)^2) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact hstep u hu v hv
    _ ≤ (∑ q ∈ Finset.Icc 1 (min A D), (q:ℝ)^2 * (q:ℝ)⁻¹^2) * harmonicBox A * harmonicBox D :=
        rect A D (fun q => (q:ℝ)^2) (fun q => by positivity)
    _ = (min A D : ℝ) * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹)
        * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by
        have hone : ∀ q ∈ Finset.Icc 1 (min A D), (q:ℝ)^2 * (q:ℝ)⁻¹^2 = 1 := by
          intro q hq
          have hq0 : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
          rw [← mul_pow, mul_inv_cancel₀ hq0.ne', one_pow]
        rw [Finset.sum_congr rfl hone, sum_const_Icc]
        simp only [harmonicBox]
        rw [Nat.cast_min]
        ring

theorem gcdTerm (A D : ℕ) :
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((max A D:ℕ):ℝ) * ((u.gcd v:ℕ):ℝ)^2 / ((u:ℝ)*(v:ℝ)))
      ≤ (A:ℝ) * (D:ℝ) * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹)
        * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by
  have hrw : ∀ u ∈ Finset.Icc 1 A, ∀ v ∈ Finset.Icc 1 D,
      ((max A D:ℕ):ℝ) * ((u.gcd v:ℕ):ℝ)^2 / ((u:ℝ)*(v:ℝ))
        = ((max A D:ℕ):ℝ) * (((u.gcd v:ℕ):ℝ)^2 * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
    intro u _ v _
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hm : ((max A D:ℕ):ℝ) * (min A D:ℝ) = (A:ℝ) * (D:ℝ) := by
    rcases le_total A D with h | h
    · have h' : (A:ℝ) ≤ (D:ℝ) := Nat.cast_le.mpr h
      rw [max_eq_right h, min_eq_left h', mul_comm]
    · have h' : (D:ℝ) ≤ (A:ℝ) := Nat.cast_le.mpr h
      rw [max_eq_left h, min_eq_right h']
  calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((max A D:ℕ):ℝ) * ((u.gcd v:ℕ):ℝ)^2 / ((u:ℝ)*(v:ℝ)))
      = ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((max A D:ℕ):ℝ) * (((u.gcd v:ℕ):ℝ)^2 * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact hrw u hu v hv
    _ = ((max A D:ℕ):ℝ) * (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((u.gcd v:ℕ):ℝ)^2 * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
        simp only [Finset.mul_sum]
    _ ≤ ((max A D:ℕ):ℝ) * ((min A D:ℝ) * harmonicBox A * harmonicBox D) :=
        mul_le_mul_of_nonneg_left (gcdSum A D) (Nat.cast_nonneg _)
    _ = (A:ℝ) * (D:ℝ) * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹)
        * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by
        simp only [harmonicBox]
        calc ((max A D:ℕ):ℝ) * ((min A D:ℝ) * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹)
              * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹))
            = (((max A D:ℕ):ℝ) * (min A D:ℝ))
                * ((∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹) * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹)) := by
              ring
          _ = (A:ℝ) * (D:ℝ) * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹)
                * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by rw [hm]; ring

def divW (n B H q : ℕ) : ℝ :=
  (if q ≤ B then ((q.gcd n:ℕ):ℝ) * (q:ℝ) / (H:ℝ) else 0)
    + (if B < q then ((q.gcd n:ℕ):ℝ) else 0)

theorem divW_nonneg (n B H q : ℕ) : 0 ≤ divW n B H q := by
  unfold divW
  split_ifs <;> positivity

theorem inner_eq (n B H u v : ℕ) :
    (∑ q ∈ (u.gcd v).divisors.filter (· ≤ B), ((q.gcd n:ℕ):ℝ) * (q:ℝ) / (H:ℝ))
      + (∑ q ∈ (u.gcd v).divisors.filter (B < ·), ((q.gcd n:ℕ):ℝ))
      = ∑ q ∈ (u.gcd v).divisors, divW n B H q := by
  unfold divW
  simp only [Finset.sum_filter, Finset.sum_add_distrib]

theorem divW_bound (n B H q : ℕ) (hB : 0 < B) (hBH : B ≤ H) (hq : 0 < q) :
    divW n B H q * ((q:ℝ)⁻¹)^2 ≤ ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹ / (B:ℝ) := by
  have hq0 : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr hq
  have hB0 : (0:ℝ) < (B:ℝ) := Nat.cast_pos.mpr hB
  have hBH0 : (B:ℝ) ≤ (H:ℝ) := Nat.cast_le.mpr hBH
  have hginv : (0:ℝ) ≤ ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹ := by positivity
  have hqinv : (q:ℝ) * ((q:ℝ)⁻¹)^2 = (q:ℝ)⁻¹ := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hq0.ne', one_mul]
  have hHB : (H:ℝ)⁻¹ ≤ (B:ℝ)⁻¹ := inv_anti₀ hB0 hBH0
  unfold divW
  by_cases h1 : q ≤ B
  · rw [if_pos h1, if_neg (by omega), add_zero]
    have hkey : ((q.gcd n:ℕ):ℝ) * (q:ℝ) / (H:ℝ) * ((q:ℝ)⁻¹)^2
        = (((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹) * (H:ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      calc ((q.gcd n:ℕ):ℝ) * (q:ℝ) * (H:ℝ)⁻¹ * ((q:ℝ)⁻¹)^2
          = (H:ℝ)⁻¹ * (((q.gcd n:ℕ):ℝ) * ((q:ℝ) * ((q:ℝ)⁻¹)^2)) := by ring
        _ = (H:ℝ)⁻¹ * (((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹) := by rw [hqinv]
        _ = (((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹) * (H:ℝ)⁻¹ := by ring
    rw [hkey, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hHB hginv
  · rw [if_neg h1, if_pos (by omega), zero_add]
    have hqB : (B:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : B ≤ q)
    have hqBinv : (q:ℝ)⁻¹ ≤ (B:ℝ)⁻¹ := inv_anti₀ hB0 hqB
    have hkey : ((q.gcd n:ℕ):ℝ) * ((q:ℝ)⁻¹)^2
        = (((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹) * (q:ℝ)⁻¹ := by ring
    rw [hkey, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hqBinv hginv

theorem gcd_le_divisors (n q : ℕ) (hn : 0 < n) :
    ((q.gcd n:ℕ):ℝ) ≤ ∑ e ∈ n.divisors.filter (fun e => e ∣ q), (e:ℝ) := by
  have hmem1 : q.gcd n ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q n, hn.ne'⟩
  have hmem2 : q.gcd n ∈ n.divisors.filter (fun e => e ∣ q) :=
    Finset.mem_filter.mpr ⟨hmem1, Nat.gcd_dvd_left q n⟩
  exact Finset.single_le_sum (f := fun e : ℕ => (e:ℝ)) (fun _ _ => Nat.cast_nonneg _)
    (a := q.gcd n) hmem2

theorem gcdHarm (n M : ℕ) (hn : 0 < n) :
    (∑ q ∈ Finset.Icc 1 M, ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹)
      ≤ (n.divisors.card : ℝ) * (∑ q ∈ Finset.Icc 1 M, (q:ℝ)⁻¹) := by
  have hstep : ∀ q ∈ Finset.Icc 1 M, ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹
      ≤ (∑ e ∈ n.divisors.filter (fun e => e ∣ q), (e:ℝ)) * (q:ℝ)⁻¹ := by
    intro q hq
    exact mul_le_mul_of_nonneg_right (gcd_le_divisors n q hn) (by positivity)
  calc (∑ q ∈ Finset.Icc 1 M, ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹)
      ≤ ∑ q ∈ Finset.Icc 1 M, (∑ e ∈ n.divisors.filter (fun e => e ∣ q), (e:ℝ))
          * (q:ℝ)⁻¹ := Finset.sum_le_sum hstep
    _ = ∑ q ∈ Finset.Icc 1 M, ∑ e ∈ n.divisors.filter (fun e => e ∣ q), (e:ℝ) * (q:ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_mul]
    _ = ∑ q ∈ Finset.Icc 1 M, ∑ e ∈ n.divisors,
          (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_filter]
    _ = ∑ e ∈ n.divisors, ∑ q ∈ Finset.Icc 1 M,
          (if e ∣ q then (e:ℝ) * (q:ℝ)⁻¹ else 0) := Finset.sum_comm
    _ = ∑ e ∈ n.divisors, (e:ℝ) * (∑ q ∈ Finset.Icc 1 M, invHit e q) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : e ∣ q <;> simp [invHit, h]
    _ ≤ ∑ e ∈ n.divisors, (e:ℝ) * ((e:ℝ)⁻¹ * harmonicBox M) := by
        apply Finset.sum_le_sum
        intro e he
        have he1 : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 hn
        exact mul_le_mul_of_nonneg_left (hitHarmonic M e he1) (Nat.cast_nonneg e)
    _ = (n.divisors.card : ℝ) * (∑ q ∈ Finset.Icc 1 M, (q:ℝ)⁻¹) := by
        have hcancel : ∀ e ∈ n.divisors, (e:ℝ) * ((e:ℝ)⁻¹ * harmonicBox M)
            = harmonicBox M := by
          intro e he
          have he1 : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 hn
          have he0 : (0:ℝ) < (e:ℝ) := Nat.cast_pos.mpr he1
          rw [← mul_assoc, mul_inv_cancel₀ he0.ne', one_mul]
        rw [Finset.sum_congr rfl hcancel, sum_const_card]
        simp only [harmonicBox]

theorem divTerm (n A D B H : ℕ) (hn : 0 < n) (hB : 0 < B) (hBH : B ≤ H) :
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((n:ℝ)/((u:ℝ)*(v:ℝ)) * ((∑ q ∈ (u.gcd v).divisors.filter (· ≤ B),
          ((q.gcd n:ℕ):ℝ)*(q:ℝ)/(H:ℝ))
          + (∑ q ∈ (u.gcd v).divisors.filter (B < ·), ((q.gcd n:ℕ):ℝ)))))
      ≤ ((n:ℝ)/(B:ℝ)) * (n.divisors.card : ℝ) * (∑ q ∈ Finset.Icc 1 (min A D), (q:ℝ)⁻¹)
        * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹) * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by
  have hrw : ∀ u ∈ Finset.Icc 1 A, ∀ v ∈ Finset.Icc 1 D,
      ((n:ℝ)/((u:ℝ)*(v:ℝ)) * ((∑ q ∈ (u.gcd v).divisors.filter (· ≤ B),
          ((q.gcd n:ℕ):ℝ)*(q:ℝ)/(H:ℝ))
          + (∑ q ∈ (u.gcd v).divisors.filter (B < ·), ((q.gcd n:ℕ):ℝ))))
        = (n:ℝ) * ((∑ q ∈ (u.gcd v).divisors, divW n B H q) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
    intro u _ v _
    rw [inner_eq n B H u v, div_eq_mul_inv, mul_inv]
    ring
  calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((n:ℝ)/((u:ℝ)*(v:ℝ)) * ((∑ q ∈ (u.gcd v).divisors.filter (· ≤ B),
          ((q.gcd n:ℕ):ℝ)*(q:ℝ)/(H:ℝ))
          + (∑ q ∈ (u.gcd v).divisors.filter (B < ·), ((q.gcd n:ℕ):ℝ)))))
      = ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        (n:ℝ) * ((∑ q ∈ (u.gcd v).divisors, divW n B H q) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact hrw u hu v hv
    _ = (n:ℝ) * (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((∑ q ∈ (u.gcd v).divisors, divW n B H q) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹)) := by
        simp only [Finset.mul_sum]
    _ ≤ (n:ℝ) * ((∑ q ∈ Finset.Icc 1 (min A D), divW n B H q * (q:ℝ)⁻¹^2)
        * harmonicBox A * harmonicBox D) :=
        mul_le_mul_of_nonneg_left (rect A D (divW n B H) (fun q => divW_nonneg n B H q))
          (Nat.cast_nonneg n)
    _ ≤ (n:ℝ) * ((∑ q ∈ Finset.Icc 1 (min A D), ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹ / (B:ℝ))
        * harmonicBox A * harmonicBox D) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ?_ (harmonicBox_nonneg A)) (harmonicBox_nonneg D)
        exact Finset.sum_le_sum fun q hq =>
          divW_bound n B H q hB hBH (Finset.mem_Icc.mp hq).1
    _ ≤ (n:ℝ) * (((n.divisors.card : ℝ) * harmonicBox (min A D) / (B:ℝ))
        * harmonicBox A * harmonicBox D) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ?_ (harmonicBox_nonneg A)) (harmonicBox_nonneg D)
        have hsum : (∑ q ∈ Finset.Icc 1 (min A D), ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹ / (B:ℝ))
            = ((∑ q ∈ Finset.Icc 1 (min A D), ((q.gcd n:ℕ):ℝ) * (q:ℝ)⁻¹)) * (B:ℝ)⁻¹ := by
          simp only [div_eq_mul_inv, Finset.sum_mul]
        rw [hsum, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (gcdHarm n (min A D) hn) (by positivity)
    _ = ((n:ℝ)/(B:ℝ)) * (n.divisors.card : ℝ) * (∑ q ∈ Finset.Icc 1 (min A D), (q:ℝ)⁻¹)
        * (∑ q ∈ Finset.Icc 1 A, (q:ℝ)⁻¹) * (∑ q ∈ Finset.Icc 1 D, (q:ℝ)⁻¹) := by
        simp only [harmonicBox]
        ring

theorem sum_split (s t : Finset ℕ) (f g h : ℕ → ℕ → ℝ) :
    (∑ u ∈ s, ∑ v ∈ t, (f u v + g u v + h u v))
      = (∑ u ∈ s, ∑ v ∈ t, f u v) + (∑ u ∈ s, ∑ v ∈ t, g u v)
        + (∑ u ∈ s, ∑ v ∈ t, h u v) := by
  simp only [← Finset.sum_add_distrib]

end

end Conjectures.Goldbach.RectangularCornerBudget_aux

open Conjectures.Goldbach.RectangularCornerBudget_aux
theorem Conjectures.Goldbach.RectangularCornerBudget : ∀ (n A D B H : ℕ), 0<n → 0<B → B≤H → let L := fun N : ℕ => ∑ q ∈ Finset.Icc 1 N,(q:ℝ)⁻¹; let C := fun u v : ℕ => (1+Real.log ((n:ℝ)+2))^2 + ((max A D:ℕ):ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) + (n:ℝ)/((u:ℝ)*v) * ((∑ q ∈ (u.gcd v).divisors.filter (·≤B),(q.gcd n:ℝ)*q/H) + ∑ q ∈ (u.gcd v).divisors.filter (B<·),(q.gcd n:ℝ)); (∑ u ∈ Finset.Icc 1 A,∑ v ∈ Finset.Icc 1 D,C u v) ≤ (A:ℝ)*D*(1+Real.log ((n:ℝ)+2))^2 + (A:ℝ)*D*L A*L D + ((n:ℝ)/B)*n.divisors.card*L (min A D)*L A*L D := by
  intro n A D B H hn hB hBH
  dsimp only
  have h1 : (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((1+Real.log ((n:ℝ)+2))^2))
      = (A:ℝ)*D*(1+Real.log ((n:ℝ)+2))^2 := by
    rw [sum_const_Icc, sum_const_Icc]
    ring
  have h2 := gcdTerm A D
  have h3 := divTerm n A D B H hn hB hBH
  refine (sum_split (Finset.Icc 1 A) (Finset.Icc 1 D)
    (fun _ _ => (1 + Real.log ((n:ℝ) + 2))^2)
    (fun u v => ((max A D:ℕ):ℝ) * ((u.gcd v:ℕ):ℝ)^2 / ((u:ℝ) * (v:ℝ)))
    (fun u v => (n:ℝ) / ((u:ℝ) * (v:ℝ)) *
      ((∑ q ∈ (u.gcd v).divisors.filter (· ≤ B), ((q.gcd n:ℕ):ℝ) * (q:ℝ) / (H:ℝ))
        + (∑ q ∈ (u.gcd v).divisors.filter (B < ·), ((q.gcd n:ℕ):ℝ))))).trans_le ?_
  refine (add_le_add (add_le_add h1.le h2) h3).trans_eq ?_
  ring
