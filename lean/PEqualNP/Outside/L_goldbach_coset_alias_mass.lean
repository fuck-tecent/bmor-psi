import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

open scoped BigOperators

namespace PEqualNP.Outside

private def pairsWithTargetResidue (n q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => (p.1 + p.2) % q = n % q)

private theorem partner_residue (n q a b : ℕ) (hq : 0 < q) :
    (a + b) % q = n % q ↔ b % q = (n + q - a % q) % q := by
  have ha := Nat.mod_lt a hq
  have hsum : a % q + (n + q - a % q) = n + q := by omega
  have partner : a + (n + q - a % q) ≡ n [MOD q] := calc
    a + (n + q - a % q) ≡ a % q + (n + q - a % q) [MOD q] :=
      (Nat.mod_modEq a q).symm.add_right _
    _ = n + q := hsum
    _ ≡ n [MOD q] := by simp
  change (a + b ≡ n [MOD q]) ↔ (b ≡ n + q - a % q [MOD q])
  exact ⟨fun h => Nat.ModEq.add_left_cancel' a (h.trans partner.symm),
    fun h => (h.add_left a).trans partner⟩

-- On a fixed diagonal the first coordinate uniquely determines the ordered pair.
private theorem sum_at_total (w : ℕ → ℝ) (n q s : ℕ) (hs : s % q = n % q) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ s ∧ s - k ≤ n),
      w k * w (s - k)) =
    ∑ p ∈ (pairsWithTargetResidue n q).filter (fun p => p.1 + p.2 = s),
      w p.1 * w p.2 := by
  refine Finset.sum_bij' (fun k _ => (k, s - k)) (fun p _ => p.1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk, hks, hkn⟩ := Finset.mem_filter.mp hk
    have heq : k + (s - k) = s := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, heq⟩
    · exact Finset.mem_product.mpr ⟨hk, Finset.mem_range.mpr (by omega)⟩
    · change (k + (s - k)) % q = n % q
      rw [heq, hs]
  · rintro ⟨a, b⟩ hp
    obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hbox, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hbox
    have hb' : b < n + 1 := Finset.mem_range.mp hb
    change a + b = s at heq
    exact Finset.mem_filter.mpr ⟨ha, by omega, by omega⟩
  · intro k _
    rfl
  · rintro ⟨a, b⟩ hp
    have heq : a + b = s := (Finset.mem_filter.mp hp).2
    change (a, s - a) = (a, b)
    rw [show s - a = b by omega]
  · intro k _
    rfl

-- Within a fixed first residue the two coordinates range independently.
private theorem residue_fiber (n q r : ℕ) (hq : 0 < q) :
    (pairsWithTargetResidue n q).filter (fun p => p.1 % q = r) =
    (Finset.range (n + 1)).filter (fun a => a % q = r) ×ˢ
      (Finset.range (n + 1)).filter (fun b => b % q = (n + q - r) % q) := by
  ext ⟨a, b⟩
  simp only [pairsWithTargetResidue, Finset.mem_filter, Finset.mem_product]
  rw [partner_residue n q a b hq]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, h⟩, hr⟩
    exact ⟨⟨ha, hr⟩, hb, by simpa only [hr] using h⟩
  · rintro ⟨⟨ha, hr⟩, hb, h⟩
    exact ⟨⟨⟨ha, hb⟩, by simpa only [hr] using h⟩, hr⟩

theorem L_goldbach_coset_alias_mass :
    let F := fun n q r : ℕ =>
      (Finset.range (n + 1)).filter (fun k => k % q = r)
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k
    let j := fun n q r : ℕ => (n + q - r) % q
    let B := fun n s : ℕ =>
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ s ∧ s - k ≤ n), w k * w (s - k)
    let Z := fun n q : ℕ =>
      ∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q), B n s
    ∀ n q : ℕ, 0 < q → Z n q = ∑ r ∈ Finset.range q, A n q r * A n q (j n q r) := by
  dsimp only
  intro n q hq
  let w (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0
  let totals := (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q)
  let pairs := pairsWithTargetResidue n q
  let weight (p : ℕ × ℕ) := w p.1 * w p.2
  have byTotal : ∀ p ∈ pairs, p.1 + p.2 ∈ totals := by
    rintro ⟨a, b⟩ hp
    obtain ⟨hab, hmod⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have ha' : a < n + 1 := Finset.mem_range.mp ha
    have hb' : b < n + 1 := Finset.mem_range.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change a + b < 2 * n + 1; omega), hmod⟩
  have byResidue : ∀ p ∈ pairs, p.1 % q ∈ Finset.range q :=
    fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ hq)
  calc
    _ = ∑ s ∈ totals, ∑ p ∈ pairs.filter (fun p => p.1 + p.2 = s), weight p := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      exact sum_at_total w n q s (Finset.mem_filter.mp hs).2
    _ = ∑ p ∈ pairs, weight p := Finset.sum_fiberwise_of_maps_to byTotal weight
    _ = ∑ r ∈ Finset.range q, ∑ p ∈ pairs.filter (fun p => p.1 % q = r), weight p :=
      (Finset.sum_fiberwise_of_maps_to byResidue weight).symm
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro r _
      change (∑ p ∈ (pairsWithTargetResidue n q).filter (fun p => p.1 % q = r), w p.1 * w p.2) = _
      rw [residue_fiber n q r hq, Finset.sum_product, Finset.sum_mul_sum]

end PEqualNP.Outside
