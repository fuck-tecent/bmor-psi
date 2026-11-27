import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

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

theorem PEqualNP.Outside.L_goldbach_coset_prime_gram :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r)%q; ∀ n q : ℕ, 0<q → let b := fun k => A n q (k % q)/((F n q (k % q)).card:ℝ); (∑ k ∈ Finset.range (n+1), b k*b (n-k)) = ∑ r ∈ Finset.range q, A n q r*A n q (j n q r)/((F n q r).card:ℝ) := by
  intro w F A j n q hq b
  have hmaps : ∀ k ∈ Finset.range (n+1), k % q ∈ Finset.range q := by
    intro k _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  have hcard : (F n q (j n q r)).card = (F n q r).card := (cardRefl n q r hq hrq).symm
  have hterm : ∀ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r),
      b k * b (n - k) = A n q r / ((F n q r).card:ℝ) * (A n q (j n q r) / ((F n q r).card:ℝ)) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk'.1; omega
    have e1 : k % q = r := hk'.2
    have e2 : (n - k) % q = j n q r := by
      show (n - k) % q = (n + q - r) % q
      exact refl_aux n q k r hkn (by omega) (by rw [e1, Nat.mod_eq_of_lt hrq])
    have h1 : b k = A n q r / ((F n q r).card:ℝ) := by
      show A n q (k % q) / ((F n q (k % q)).card:ℝ) = _
      rw [e1]
    have h2 : b (n - k) = A n q (j n q r) / ((F n q r).card:ℝ) := by
      show A n q ((n - k) % q) / ((F n q ((n - k) % q)).card:ℝ) = _
      rw [e2, hcard]
    rw [h1, h2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : ((F n q r).card:ℝ) = 0
  · rw [hc]; simp
  · field_simp
    show ((F n q r).card:ℝ) * A n q r * A n q (j n q r) = A n q r * ((F n q r).card:ℝ) * A n q (j n q r)
    ring
