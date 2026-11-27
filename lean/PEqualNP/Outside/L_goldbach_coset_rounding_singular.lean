import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

private theorem fiber_card (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    ((Finset.range (n+1)).filter (fun k => k % q = r)).card = (n + q - r) / q := by
  have hset : (Finset.range (n+1)).filter (fun k => k % q = r)
      = (Finset.range ((n + q - r) / q)).image (fun j => r + q * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hkr⟩
      refine ⟨k / q, ?_, ?_⟩
      · have hd := Nat.mod_add_div k q
        rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hq]
        have : (k / q + 1) * q = q * (k / q) + q := by ring
        omega
      · have := Nat.mod_add_div k q
        omega
    · rintro ⟨j, hj, rfl⟩
      have h1 : (j + 1) * q ≤ n + q - r := (Nat.le_div_iff_mul_le hq).1 hj
      have h2 : (j + 1) * q = q * j + q := by ring
      refine ⟨by omega, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [hset, Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  have : q * a = q * b := by simpa using hab
  exact Nat.eq_of_mul_eq_mul_left hq this

private theorem fiber_real (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    |(((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ) - ((n+1:ℕ):ℝ) / q| ≤ 1 := by
  rw [fiber_card n q r hq hr]
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hd := Nat.div_add_mod (n + q - r) q
  have hm := Nat.mod_lt (n + q - r) hq
  have h1 : ((n + q - r) / q) * q ≤ n + q := by
    have := Nat.mul_comm q ((n + q - r) / q)
    omega
  have h2 : n + 1 ≤ (n + q - r) / q * q + q := by
    have := Nat.mul_comm q ((n + q - r) / q)
    omega
  have h1' : (((n + q - r) / q : ℕ) : ℝ) * q ≤ n + q := by exact_mod_cast h1
  have h2' : (n:ℝ) + 1 ≤ (((n + q - r) / q : ℕ) : ℝ) * q + q := by exact_mod_cast h2
  generalize (((n + q - r) / q : ℕ) : ℝ) = m at h1' h2' ⊢
  push_cast
  have hA : ((n:ℝ) + 1) / q ≤ m + 1 := by
    rw [div_le_iff₀ hqr]
    nlinarith
  have hB : m - 1 ≤ ((n:ℝ) + 1) / q := by
    rw [le_div_iff₀ hqr]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

theorem PEqualNP.Outside.L_goldbach_coset_rounding_singular :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let j := fun n q r : ℕ => (n+q-r) % q; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let K := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*μ q r*μ q (j n q r); let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n q : ℕ, 0<q → |K n q - ((n+1:ℕ):ℝ)*(q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2| ≤ ((q:ℝ)/(q.totient:ℝ))^2*(R n q:ℝ) := by
  intro F j μ K R n q hq
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  set S := (Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q) with hS
  have hR : (R n q : ℝ) = (S.card : ℝ) := rfl
  have hK : K n q = ∑ r ∈ S, ((F n q r).card : ℝ) * ((q:ℝ) / (q.totient:ℝ))^2 := by
    show ∑ r ∈ Finset.range q, ((F n q r).card:ℝ) * μ q r * μ q (j n q r) = _
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h1 : r.Coprime q
    · by_cases h2 : ((n+q-r) % q).Coprime q
      · simp only [μ, j]
        rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
        ring
      · simp only [μ, j]
        have h3 : ¬ (r.Coprime q ∧ ((n+q-r) % q).Coprime q) := fun h => h2 h.2
        rw [if_neg h2, if_neg h3]
        simp
    · simp only [μ, j]
      have h3 : ¬ (r.Coprime q ∧ ((n+q-r) % q).Coprime q) := fun h => h1 h.1
      rw [if_neg h1, if_neg h3]
      simp
  have hT : ((n+1:ℕ):ℝ)*(q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2
      = ∑ r ∈ S, (((n+1:ℕ):ℝ) / q) * ((q:ℝ) / (q.totient:ℝ))^2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hR]
    field_simp
  rw [hK, hT, ← Finset.sum_sub_distrib]
  have hsq : 0 ≤ ((q:ℝ) / (q.totient:ℝ))^2 := by positivity
  calc |∑ r ∈ S, (((F n q r).card : ℝ) * ((q:ℝ) / (q.totient:ℝ))^2
          - (((n+1:ℕ):ℝ) / q) * ((q:ℝ) / (q.totient:ℝ))^2)|
      ≤ ∑ r ∈ S, |((F n q r).card : ℝ) * ((q:ℝ) / (q.totient:ℝ))^2
          - (((n+1:ℕ):ℝ) / q) * ((q:ℝ) / (q.totient:ℝ))^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ S, ((q:ℝ) / (q.totient:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro r hr
        have hrq : r < q := Finset.mem_range.1 (Finset.mem_filter.1 hr).1
        have hf := fiber_real n q r hq hrq
        rw [← sub_mul, abs_mul, abs_of_nonneg hsq]
        have : |((F n q r).card : ℝ) - ((n+1:ℕ):ℝ) / q| ≤ 1 := hf
        nlinarith
    _ = ((q:ℝ) / (q.totient:ℝ))^2 * (R n q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hR]
        ring
