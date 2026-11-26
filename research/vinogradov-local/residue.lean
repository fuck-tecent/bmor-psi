import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)

lemma E_add (x y : ℝ) : E x * E y = E (x + y) := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma S_residue_decomp (n q : ℕ) (hq : 0 < q) (u : ℕ → ℝ) (t : ℝ) :
    S n u t =
      ∑ r ∈ Finset.range (min q (n + 1)),
        E ((r : ℝ) * t) *
          ∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) * t) := by
  classical
  rw [S]
  let s : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (min q (n + 1))).sigma
      (fun r => Finset.range ((n - r) / q + 1))
  let f : (Σ _ : ℕ, ℕ) → ℂ := fun p =>
    (u (p.1 + p.2 * q) : ℂ) * E (((p.1 + p.2 * q : ℕ) : ℝ) * t)
  have hR : (∑ r ∈ Finset.range (min q (n + 1)),
        E ((r : ℝ) * t) *
          ∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) * t)) =
      ∑ p ∈ s, f p := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [f]
    have hE : E ((r : ℝ) * t) * E (((j * q : ℕ) : ℝ) * t) =
        E (((r + j * q : ℕ) : ℝ) * t) := by
      rw [E_add]
      congr 1
      push_cast
      ring
    calc
      E ((r : ℝ) * t) * ((u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) * t))
          = (u (r + j * q) : ℂ) *
              (E ((r : ℝ) * t) * E (((j * q : ℕ) : ℝ) * t)) := by ring
      _ = (u (r + j * q) : ℂ) * E (((r + j * q : ℕ) : ℝ) * t) := by rw [hE]
  rw [hR]
  symm
  refine Finset.sum_bij' (s := s) (t := Finset.range (n + 1))
    (fun p _ => p.1 + p.2 * q)
    (fun k _ => ⟨k % q, k / q⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [s, Finset.mem_sigma, Finset.mem_range] at hp
    rcases hp with ⟨hrq, hrj⟩
    have hrmin : p.1 < min q (n + 1) := hrq
    have hrn : p.1 ≤ n := by
      have : p.1 < n + 1 := lt_of_lt_of_le hrmin (min_le_right _ _)
      omega
    have hj : p.2 ≤ (n - p.1) / q := by omega
    have hk : p.1 + p.2 * q ≤ n := by
      have h1 : p.2 * q ≤ ((n - p.1) / q) * q := Nat.mul_le_mul_right _ hj
      have h2 : ((n - p.1) / q) * q ≤ n - p.1 := Nat.div_mul_le_self _ _
      omega
    exact Finset.mem_range.mpr (by omega)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [s, Finset.mem_sigma, Finset.mem_range]
    constructor
    · exact lt_min (Nat.mod_lt k hq) (lt_of_le_of_lt (Nat.mod_le k q) hk)
    · have hdecomp : k % q + q * (k / q) = k := Nat.mod_add_div k q
      have hk' : k ≤ n := by omega
      have hqk : q * (k / q) = k - k % q := by omega
      have hle : q * (k / q) ≤ n - k % q := by
        calc
          q * (k / q) = k - k % q := hqk
          _ ≤ n - k % q := Nat.sub_le_sub_right hk' _
      have hquot : k / q ≤ (n - k % q) / q := by
        rw [Nat.le_div_iff_mul_le hq]
        simpa [mul_comm] using hle
      rw [Nat.div_lt_iff_lt_mul hq]
      have hmodlt : k % q < q := Nat.mod_lt _ hq
      have hmul : q * (k / q) ≤ q * ((n - k % q) / q) :=
        Nat.mul_le_mul_left q hquot
      calc
        k = k % q + q * (k / q) := hdecomp.symm
        _ < q + q * ((n - k % q) / q) := by omega
        _ = ((n - k % q) / q + 1) * q := by ring
  · intro p hp
    simp only [s, Finset.mem_sigma, Finset.mem_range] at hp
    rcases hp with ⟨hrq, hrj⟩
    have hrlt : p.1 < q := lt_of_lt_of_le hrq (min_le_left _ _)
    cases p with
    | mk r j =>
      rw [Sigma.mk.injEq]
      constructor
      · rw [mul_comm j q, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
      · simp only [Sigma.mk.injEq]
        rw [mul_comm j q, Nat.add_mul_div_left _ _ hq]
        simp [Nat.div_eq_of_lt hrlt]
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    simpa [mul_comm] using Nat.mod_add_div k q
  · intro p hp
    rfl

end

end PEqualNP.Outside
