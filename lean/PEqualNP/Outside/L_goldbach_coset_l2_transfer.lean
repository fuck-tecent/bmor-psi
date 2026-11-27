import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private theorem refl_aux (n q k a : ℕ) (hk : k ≤ n) (ha : a ≤ n + q) (h : k % q = a % q) :
    (n - k) % q = (n + q - a) % q := by
  have h1 : k ≡ a [MOD q] := h
  have h2 : n - k + k ≡ n + q - a + a [MOD q] := by
    have e1 : n - k + k = n := Nat.sub_add_cancel hk
    have e2 : n + q - a + a = n + q := Nat.sub_add_cancel ha
    rw [e1, e2]
    show n % q = (n + q) % q
    simp
  exact Nat.ModEq.add_right_cancel h1 h2

private theorem cardRefl :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let j := fun n q r : ℕ => (n+q-r)%q; ∀ n q r : ℕ, 0<q → r<q → (F n q r).card=(F n q (j n q r)).card := by
  intro F j n q r hq hr
  simp only [F, j]
  apply Finset.card_bij' (fun k _ => n - k) (fun k _ => n - k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨h1, h2⟩ := hk
    refine ⟨by omega, ?_⟩
    have := refl_aux n q k r (by omega) (by omega) (by rw [h2, Nat.mod_eq_of_lt hr])
    exact this
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨h1, h2⟩ := hk
    refine ⟨by omega, ?_⟩
    have := refl_aux n q k (n + q - r) (by omega) (by omega) h2
    rw [this]
    have e : n + q - (n + q - r) = r := by omega
    rw [e, Nat.mod_eq_of_lt hr]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega

private theorem wcs (s : Finset ℕ) (c x y : ℕ → ℝ) (hc : ∀ r ∈ s, 0 ≤ c r)
    (hy : ∀ r ∈ s, c r = 0 → y r = 0) :
    (∑ r ∈ s, x r * y r) ^ 2 ≤ (∑ r ∈ s, c r * x r ^ 2) * (∑ r ∈ s, y r ^ 2 / c r) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun r => Real.sqrt (c r) * x r)
    (fun r => y r / Real.sqrt (c r))
  have e1 : ∑ r ∈ s, (Real.sqrt (c r) * x r) * (y r / Real.sqrt (c r)) = ∑ r ∈ s, x r * y r := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    by_cases h0 : c r = 0
    · rw [hy r hr h0]; simp
    · have : Real.sqrt (c r) ≠ 0 := by
        rw [Ne, Real.sqrt_eq_zero (hc r hr)]; exact h0
      field_simp
  have e2 : ∑ r ∈ s, (Real.sqrt (c r) * x r) ^ 2 = ∑ r ∈ s, c r * x r ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [mul_pow, Real.sq_sqrt (hc r hr)]
  have e3 : ∑ r ∈ s, (y r / Real.sqrt (c r)) ^ 2 = ∑ r ∈ s, y r ^ 2 / c r := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [div_pow, Real.sq_sqrt (hc r hr)]
  rw [e1, e2, e3] at h
  exact h

private theorem jMod (n q r : ℕ) (hr : r < q) : (n + q - (n + q - r) % q) % q = r := by
  have hq : 0 < q := by omega
  have ha : (n + q - r) % q < q := Nat.mod_lt _ hq
  have h1 : (n + q - r) % q ≡ n + q - r [MOD q] := Nat.mod_modEq _ _
  have h3 : r + (n + q - r) % q ≡ r + (n + q - r) [MOD q] := Nat.ModEq.add_left r h1
  have h4 : r + (n + q - r) = n + q := by omega
  have h5 : (n + q - (n + q - r) % q) + (n + q - r) % q ≡ r + (n + q - r) % q [MOD q] := by
    rw [show n + q - (n + q - r) % q + (n + q - r) % q = n + q by omega]
    rw [h4] at h3
    exact h3.symm
  have h6 := Nat.ModEq.add_right_cancel' ((n + q - r) % q) h5
  have h7 : (n + q - (n + q - r) % q) % q = r % q := h6
  rw [h7, Nat.mod_eq_of_lt hr]

theorem PEqualNP.Outside.L_goldbach_coset_l2_transfer :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r)%q; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let v := fun n q r : ℕ => A n q r-((F n q r).card:ℝ)*μ q r; let G := fun n q => ∑ r ∈ Finset.range q, A n q r*A n q (j n q r)/((F n q r).card:ℝ); let U := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*(μ q r)^2; let E := fun n q => ∑ r ∈ Finset.range q, (v n q r)^2/((F n q r).card:ℝ); let K := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*μ q r*μ q (j n q r); ∀ n q : ℕ, 0<q → |G n q-K n q| ≤ 2*Real.sqrt (U n q*E n q)+E n q := by
  intro F w A j μ v G U E K n q hq
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ r, c r = ((F n q r).card:ℝ) := ⟨_, fun _ => rfl⟩
  have hc0 : ∀ r, 0 ≤ c r := fun r => by rw [hc]; exact Nat.cast_nonneg _
  have hjq : ∀ r, j n q r < q := fun r => Nat.mod_lt _ hq
  have hjj : ∀ r, r < q → j n q (j n q r) = r := fun r hr => jMod n q r hr
  have hcj : ∀ r, r < q → c (j n q r) = c r := by
    intro r hr
    rw [hc, hc]
    exact_mod_cast (cardRefl n q r hq hr).symm
  have hcj' : ∀ r ∈ Finset.range q, c (j n q r) = c r := fun r hr => hcj r (Finset.mem_range.mp hr)
  have reidx : ∀ f : ℕ → ℝ, ∑ r ∈ Finset.range q, f (j n q r) = ∑ r ∈ Finset.range q, f r := by
    intro f
    refine Finset.sum_nbij' (fun r => j n q r) (fun r => j n q r) ?_ ?_ ?_ ?_ ?_
    · intro r _; exact Finset.mem_range.mpr (hjq r)
    · intro r _; exact Finset.mem_range.mpr (hjq r)
    · intro r hr; exact hjj r (Finset.mem_range.mp hr)
    · intro r hr; exact hjj r (Finset.mem_range.mp hr)
    · intro r _; rfl
  have hA0 : ∀ r, c r = 0 → A n q r = 0 := by
    intro r h0
    rw [hc] at h0
    have h1 : F n q r = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast h0)
    show ∑ k ∈ F n q r, w k = 0
    rw [h1]; simp
  have hvdef : ∀ r, v n q r = A n q r - c r * μ q r := fun r => by rw [hc]
  have hv0 : ∀ r, c r = 0 → v n q r = 0 := by
    intro r h0
    rw [hvdef, hA0 r h0, h0]; simp
  have hG : G n q = ∑ r ∈ Finset.range q, A n q r * A n q (j n q r) / c r := by
    simp only [hc]; rfl
  have hK : K n q = ∑ r ∈ Finset.range q, c r * μ q r * μ q (j n q r) := by
    simp only [hc]; rfl
  have hU : U n q = ∑ r ∈ Finset.range q, c r * (μ q r) ^ 2 := by
    simp only [hc]; rfl
  have hE : E n q = ∑ r ∈ Finset.range q, (v n q r) ^ 2 / c r := by
    simp only [hc]; rfl
  have hEj : ∑ r ∈ Finset.range q, (v n q (j n q r)) ^ 2 / c r = E n q := by
    rw [hE, ← reidx (fun s => (v n q s) ^ 2 / c s)]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [hcj' r hr]
  have hUj : ∑ r ∈ Finset.range q, c r * (μ q (j n q r)) ^ 2 = U n q := by
    rw [hU, ← reidx (fun s => c s * (μ q s) ^ 2)]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [hcj' r hr]
  have hterm : ∀ r ∈ Finset.range q,
      A n q r * A n q (j n q r) / c r - c r * μ q r * μ q (j n q r) =
        μ q r * v n q (j n q r) + v n q r * μ q (j n q r) + v n q r * v n q (j n q r) / c r := by
    intro r hr
    by_cases h0 : c r = 0
    · have h1 : c (j n q r) = 0 := by rw [hcj' r hr]; exact h0
      rw [hv0 r h0, hv0 _ h1, hA0 r h0, h0]; simp
    · rw [hvdef r, hvdef (j n q r), hcj' r hr]
      field_simp
      ring
  have hsum : G n q - K n q = (∑ r ∈ Finset.range q, μ q r * v n q (j n q r)) +
      (∑ r ∈ Finset.range q, v n q r * μ q (j n q r)) +
      (∑ r ∈ Finset.range q, v n q r * v n q (j n q r) / c r) := by
    rw [hG, hK, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have hy1 : ∀ r ∈ Finset.range q, c r = 0 → v n q (j n q r) = 0 := by
    intro r hr h0
    exact hv0 _ (by rw [hcj' r hr]; exact h0)
  have hy2 : ∀ r ∈ Finset.range q, c r = 0 → v n q r = 0 := fun r _ h0 => hv0 r h0
  have hT1 : |∑ r ∈ Finset.range q, μ q r * v n q (j n q r)| ≤ Real.sqrt (U n q * E n q) := by
    apply Real.abs_le_sqrt
    have := wcs (Finset.range q) c (fun r => μ q r) (fun r => v n q (j n q r)) (fun r _ => hc0 r) hy1
    rw [← hU, hEj] at this
    exact this
  have hT2 : |∑ r ∈ Finset.range q, v n q r * μ q (j n q r)| ≤ Real.sqrt (U n q * E n q) := by
    apply Real.abs_le_sqrt
    have := wcs (Finset.range q) c (fun r => μ q (j n q r)) (fun r => v n q r) (fun r _ => hc0 r) hy2
    rw [hUj, ← hE] at this
    have e : ∑ r ∈ Finset.range q, v n q r * μ q (j n q r) =
        ∑ r ∈ Finset.range q, μ q (j n q r) * v n q r :=
      Finset.sum_congr rfl (fun r _ => mul_comm _ _)
    rw [e]
    exact this
  have hT3 : |∑ r ∈ Finset.range q, v n q r * v n q (j n q r) / c r| ≤ E n q := by
    have hb : ∀ r ∈ Finset.range q,
        |v n q r * v n q (j n q r) / c r| ≤ (v n q r ^ 2 / c r + v n q (j n q r) ^ 2 / c r) / 2 := by
      intro r _
      by_cases h0 : c r = 0
      · rw [h0]; simp
      · have hpos : 0 < c r := lt_of_le_of_ne (hc0 r) (Ne.symm h0)
        have p1 : 0 ≤ (v n q r - v n q (j n q r)) ^ 2 / c r := div_nonneg (sq_nonneg _) hpos.le
        have p2 : 0 ≤ (v n q r + v n q (j n q r)) ^ 2 / c r := div_nonneg (sq_nonneg _) hpos.le
        have q1 : (v n q r - v n q (j n q r)) ^ 2 / c r =
            v n q r ^ 2 / c r - 2 * (v n q r * v n q (j n q r) / c r) + v n q (j n q r) ^ 2 / c r := by
          ring
        have q2 : (v n q r + v n q (j n q r)) ^ 2 / c r =
            v n q r ^ 2 / c r + 2 * (v n q r * v n q (j n q r) / c r) + v n q (j n q r) ^ 2 / c r := by
          ring
        rw [abs_le]
        constructor <;> linarith
    calc |∑ r ∈ Finset.range q, v n q r * v n q (j n q r) / c r|
        ≤ ∑ r ∈ Finset.range q, |v n q r * v n q (j n q r) / c r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.range q, (v n q r ^ 2 / c r + v n q (j n q r) ^ 2 / c r) / 2 :=
          Finset.sum_le_sum hb
      _ = E n q := by
          have e : ∀ r ∈ Finset.range q, (v n q r ^ 2 / c r + v n q (j n q r) ^ 2 / c r) / 2 = (v n q r ^ 2 / c r + v n q (j n q r) ^ 2 / c r) * (1/2) := fun r _ => by ring
          rw [Finset.sum_congr rfl e, ← Finset.sum_mul, Finset.sum_add_distrib, hEj, ← hE]
          ring
  rw [hsum]
  have h12 := abs_add_le (∑ r ∈ Finset.range q, μ q r * v n q (j n q r) +
      ∑ r ∈ Finset.range q, v n q r * μ q (j n q r)) (∑ r ∈ Finset.range q, v n q r * v n q (j n q r) / c r)
  have h11 := abs_add_le (∑ r ∈ Finset.range q, μ q r * v n q (j n q r))
      (∑ r ∈ Finset.range q, v n q r * μ q (j n q r))
  linarith
