import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

private theorem cosetCardGe (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    (n + 1) / q ≤ ((Finset.range (n+1)).filter (fun k => k % q = r)).card := by
  have h1 : (Finset.range ((n + 1) / q)).card ≤
      ((Finset.range (n+1)).filter (fun k => k % q = r)).card := by
    apply Finset.card_le_card_of_injOn (fun i => r + i * q)
    · intro i hi
      have hi' : i < (n + 1) / q := by simpa using hi
      have h2 : (i + 1) * q ≤ (n + 1) / q * q := Nat.mul_le_mul_right q hi'
      have h3 : (n + 1) / q * q ≤ n + 1 := Nat.div_mul_le_self _ _
      simp only [Finset.coe_filter, Finset.mem_range]
      constructor
      · nlinarith
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    · intro i _ j _ h
      have : i * q = j * q := by simpa using h
      exact Nat.eq_of_mul_eq_mul_right hq this
  simpa using h1

private theorem cosetCardLe (n q r : ℕ) (hq : 0 < q) :
    ((Finset.range (n+1)).filter (fun k => k % q = r)).card ≤ (n + 1) / q + 1 := by
  have h1 : ((Finset.range (n+1)).filter (fun k => k % q = r)).card ≤
      (Finset.range ((n + 1) / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / q)
    · intro k hk
      have hk := Finset.mem_filter.mp (Finset.mem_coe.mp hk)
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range] at hk ⊢
      have : k / q ≤ (n + 1) / q := Nat.div_le_div_right (by omega)
      omega
    · intro k hk l hl h
      have hk := Finset.mem_filter.mp (Finset.mem_coe.mp hk)
      have hl := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      have h' : k / q = l / q := h
      have e1 := Nat.div_add_mod k q
      have e2 := Nat.div_add_mod l q
      rw [h', hk.2] at e1
      rw [hl.2] at e2
      omega
  simpa using h1

private theorem cosetCardDev (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    ((((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ) * q ≤ ((n + 1 : ℕ) : ℝ) + q) ∧
    (((n + 1 : ℕ) : ℝ) ≤ ((((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ) * q + q)) := by
  have h1 := cosetCardGe n q r hq hr
  have h2 := cosetCardLe n q r hq
  have e1 := Nat.div_add_mod (n + 1) q
  have e2 : (n + 1) % q < q := Nat.mod_lt _ hq
  set c := ((Finset.range (n+1)).filter (fun k => k % q = r)).card with hc
  set m := (n + 1) / q with hm
  have a1 : m * q ≤ c * q := Nat.mul_le_mul_right q h1
  have a2 : c * q ≤ (m + 1) * q := Nat.mul_le_mul_right q h2
  have b1 : ((c * q : ℕ) : ℝ) ≤ (((m + 1) * q : ℕ) : ℝ) := by exact_mod_cast a2
  have b2 : ((m * q : ℕ) : ℝ) ≤ ((c * q : ℕ) : ℝ) := by exact_mod_cast a1
  have b3 : ((q * m + (n + 1) % q : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by exact_mod_cast e1
  have b4 : (((n + 1) % q : ℕ) : ℝ) < q := by exact_mod_cast e2
  push_cast at b1 b2 b3 b4 ⊢
  have b5 : (0:ℝ) ≤ (((n + 1) % q : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

private theorem cam_key (n q k l : ℕ) (hq : 0 < q) :
    (k + l) % q = n % q ↔ l % q = (n + q - k % q) % q := by
  have hr : k % q < q := Nat.mod_lt _ hq
  have h1 : k + (n + q - k % q) ≡ n [MOD q] :=
    calc k + (n + q - k % q) ≡ k % q + (n + q - k % q) [MOD q] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq k q).symm
      _ = n + q := by omega
      _ ≡ n [MOD q] := by
          show (n + q) % q = n % q
          exact Nat.add_mod_right n q
  constructor
  · intro h
    have h2 : k + l ≡ k + (n + q - k % q) [MOD q] := Nat.ModEq.trans h h1.symm
    exact Nat.ModEq.add_left_cancel' k h2
  · intro h
    exact Nat.ModEq.trans (Nat.ModEq.add_left k h) h1

private theorem cam_main (w : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q),
        ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n), w k * w (s - k) =
      ∑ r ∈ Finset.range q,
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), w k) *
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), w k) := by
  set P : Finset (ℕ × ℕ) := ((Finset.range (n+1)) ×ˢ (Finset.range (n+1))).filter
    (fun p => (p.1 + p.2) % q = n % q) with hP
  have hL : ∑ p ∈ P, w p.1 * w p.2 =
      ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q),
        ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n), w k * w (s - k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P)
      (t := (Finset.range (2*n+1)).filter (fun s => s % q = n % q)) (g := fun p => p.1 + p.2)]
    · refine Finset.sum_congr rfl ?_
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_range] at hs
      refine Finset.sum_nbij' (fun p => p.1) (fun k => (k, s - k)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hp ⊢
        omega
      · intro k hk
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hk ⊢
        have : k + (s - k) = s := by omega
        exact ⟨⟨⟨by omega, by omega⟩, by rw [this]; exact hs.2⟩, this⟩
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hp
        ext <;> simp only <;> omega
      · intro k hk
        rfl
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hp
        have : p.2 = s - p.1 := by omega
        rw [this]
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
  have hR : ∑ p ∈ P, w p.1 * w p.2 =
      ∑ r ∈ Finset.range q,
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), w k) *
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), w k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.range q)
      (g := fun p => p.1 % q)]
    · refine Finset.sum_congr rfl ?_
      intro r hr
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      rw [Finset.mem_range] at hr
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨⟨h1, h4⟩, h2, ?_⟩
        rw [cam_key n q p.1 p.2 hq] at h3
        rw [h3, h4]
      · rintro ⟨⟨h1, h4⟩, h2, h3⟩
        refine ⟨⟨⟨h1, h2⟩, ?_⟩, h4⟩
        rw [cam_key n q p.1 p.2 hq, h4]
        exact h3
    · intro p hp
      simp only [Finset.mem_range]
      exact Nat.mod_lt _ hq
  rw [← hL, hR]

theorem PEqualNP.Outside.L_goldbach_coset_alias_rounding :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r)%q; let G := fun n q => ∑ r ∈ Finset.range q, A n q r*A n q (j n q r)/((F n q r).card:ℝ); let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q=n % q), B n s; ∀ n q : ℕ, 0<q → |((q:ℝ)/((n+1:ℕ):ℝ))*Z n q-G n q| ≤ ((q:ℝ)/((n+1:ℕ):ℝ))*G n q := by
  intro F w A j G B Z n q hq
  have hZ : Z n q = ∑ r ∈ Finset.range q, A n q r * A n q (j n q r) := cam_main w n q hq
  have hG : G n q = ∑ r ∈ Finset.range q, A n q r * A n q (j n q r) / ((F n q r).card:ℝ) := rfl
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    by_cases hk : k.Prime
    · have : w k = Real.log (k:ℝ) := if_pos hk
      rw [this]
      apply Real.log_nonneg
      exact_mod_cast hk.one_le
    · have : w k = 0 := if_neg hk
      rw [this]
  have hA : ∀ n q r, 0 ≤ A n q r := fun n q r => Finset.sum_nonneg (fun k _ => hw k)
  have hD : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  set t : ℝ := (q:ℝ)/((n+1:ℕ):ℝ) with ht
  have htD : t * ((n+1:ℕ):ℝ) = q := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := by positivity
  rw [hZ, hG, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  have hP : 0 ≤ A n q r * A n q (j n q r) := mul_nonneg (hA _ _ _) (hA _ _ _)
  have hd := cosetCardDev n q r hq hrq
  by_cases hc : ((F n q r).card:ℝ) = 0
  · have hc' : (F n q r).card = 0 := by exact_mod_cast hc
    have hemp : F n q r = ∅ := Finset.card_eq_zero.mp hc'
    have hA0 : A n q r = 0 := by
      show ∑ k ∈ F n q r, w k = 0
      rw [hemp]; simp
    rw [hA0, hc]; simp
  · have hcpos : 0 < ((F n q r).card:ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
    set c : ℝ := ((F n q r).card:ℝ) with hcdef
    set P := A n q r * A n q (j n q r) with hPdef
    set u := P / c with hu
    have hu0 : 0 ≤ u := div_nonneg hP hcpos.le
    have hPu : P = c * u := by rw [hu]; field_simp
    have e1 : t * c * ((n+1:ℕ):ℝ) = q * c := by rw [mul_right_comm, htD]
    have k1 : t * c - 1 ≤ t := by
      refine le_of_mul_le_mul_right ?_ hD
      nlinarith [hd.1, hd.2]
    have k2 : -t ≤ t * c - 1 := by
      refine le_of_mul_le_mul_right ?_ hD
      nlinarith [hd.1, hd.2]
    have : t * P - u = u * (t * c - 1) := by rw [hPu]; ring
    rw [this, abs_le]
    constructor <;> nlinarith
