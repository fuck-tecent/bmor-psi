import Mathlib

open Finset Filter
open scoped Topology

namespace PEqualNP.Outside

private noncomputable def weight (p : ℕ) : ℝ := if p.Prime then Real.log (p : ℝ) else 0

private theorem weight_nonneg (p : ℕ) : 0 ≤ weight p := by
  by_cases hp : p.Prime
  · simpa [weight, hp] using (Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_le))
  · simp [weight, hp]

/-- Primes in the window. Its endpoints make both the size and the parity argument exact. -/
private def windowPrimes (k : ℕ) : Finset ℕ := (Ioc (2 * k) (3 * k)).filter Nat.Prime

private theorem window_mass (k : ℕ) :
    ∑ p ∈ windowPrimes k, weight p = Chebyshev.theta (3 * k : ℕ) - Chebyshev.theta (2 * k : ℕ) := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) = ∑ p ∈ Ioc 0 n, weight p := by
    simp [Chebyshev.theta, weight, sum_filter]
  have split := Finset.sum_union (f := weight)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := 2 * k) (c := 2 * k) (d := 3 * k) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)] at split
  have drop : ∑ p ∈ windowPrimes k, weight p = ∑ p ∈ Ioc (2 * k) (3 * k), weight p := by
    rw [windowPrimes, sum_filter]
    refine sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p.Prime <;> simp [weight, hp]
  rw [drop, expand, expand, split]
  abel

/-- Two fixed relative-error bounds for the Chebyshev function, from Mathlib's PNT.
See https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/WeakPNT.html#Chebyshev.tendsto_theta_div_atTop. -/
private theorem theta_bounds : ∃ K : ℕ, ∀ n ≥ K,
    (19/20 : ℝ) * n < Chebyshev.theta n ∧ Chebyshev.theta n < (21/20 : ℝ) * n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show (19/20 : ℝ) < 1 by norm_num),
    limN.eventually_lt_const (show (1 : ℝ) < 21/20 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨(lt_div_iff₀ hn').mp hlo, (div_lt_iff₀ hn').mp hhi⟩

private theorem eventually_large_mass : ∃ K : ℕ, ∀ k ≥ K,
    (k : ℝ)/2 < ∑ p ∈ windowPrimes k, weight p := by
  obtain ⟨K, hK⟩ := theta_bounds
  refine ⟨max K 1, fun k hk ↦ ?_⟩
  have hthree := (hK (3*k) (by omega)).1
  have htwo := (hK (2*k) (by omega)).2
  rw [window_mass]
  push_cast at hthree htwo ⊢
  linarith

private noncomputable def central (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n+1)).filter (fun p ↦ n ≤ 3*p ∧ 3*p ≤ 2*n), weight p * weight (n-p)

private def evenBlock (x : ℕ) : Finset ℕ := (Icc x (2*x)).filter Even

/-- Each ordered prime pair in `(2k,3k]` contributes to the central coefficient at its sum. -/
private theorem central_block_mass (x k : ℕ) (hk : 1 ≤ k) (hlo : x ≤ 4*k) (hhi : 3*k ≤ x) :
    (∑ p ∈ windowPrimes k, weight p)^2 ≤ ∑ n ∈ evenBlock x, central n := by
  classical
  let P := windowPrimes k
  let index (z : ℕ × ℕ) : ℕ × ℕ := (z.1 + z.2, z.1)
  let term (y : ℕ × ℕ) : ℝ := if y.1 ≤ 3*y.2 ∧ 3*y.2 ≤ 2*y.1 then
    weight y.2 * weight (y.1-y.2) else 0
  have bounds {p : ℕ} (hp : p ∈ P) : 2*k < p ∧ p ≤ 3*k := mem_Ioc.mp (mem_filter.mp hp).1
  have oddP {p : ℕ} (hp : p ∈ P) : Odd p :=
    (mem_filter.mp hp).2.odd_of_ne_two (by have := (bounds hp).1; omega)
  have term_nonneg (y : ℕ × ℕ) : 0 ≤ term y := by
    dsimp [term]
    split_ifs
    · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)
    · exact le_rfl
  have inj : Set.InjOn index (↑(P ×ˢ P) : Set (ℕ × ℕ)) := by
    intro z _ v _ he
    have hp : z.1 = v.1 := congrArg Prod.snd he
    have hs : z.1 + z.2 = v.1 + v.2 := congrArg Prod.fst he
    exact Prod.ext hp (by omega)
  have image_subset : (P ×ˢ P).image index ⊆ evenBlock x ×ˢ P := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨hp, hq⟩ := mem_product.mp hz
    have hp' := bounds hp
    have hq' := bounds hq
    refine mem_product.mpr ⟨?_, hp⟩
    change z.1 + z.2 ∈ evenBlock x
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (oddP hp).add_odd (oddP hq)⟩
  calc
    (∑ p ∈ P, weight p)^2 = ∑ z ∈ P ×ˢ P, weight z.1 * weight z.2 := by
      rw [Finset.sum_product P P (fun z ↦ weight z.1 * weight z.2), pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ ≤ ∑ y ∈ evenBlock x ×ˢ P, term y := by
      apply Finset.sum_le_sum_of_injOn index inj image_subset
      · intro z hz
        obtain ⟨hp, hq⟩ := mem_product.mp hz
        have hp' := bounds hp
        have hq' := bounds hq
        have hc : z.1 + z.2 ≤ 3*z.1 ∧ 3*z.1 ≤ 2*(z.1+z.2) := ⟨by omega, by omega⟩
        simp [index, term, hc]
      · exact fun y _ _ ↦ term_nonneg y
    _ = ∑ n ∈ evenBlock x, ∑ p ∈ P, term (n,p) := Finset.sum_product (evenBlock x) P term
    _ ≤ ∑ n ∈ evenBlock x, central n := by
      refine sum_le_sum fun n hn ↦ ?_
      have hxn := (mem_Icc.mp (mem_filter.mp hn).1).1
      change (∑ p ∈ P, term (n,p)) ≤ ∑ p ∈ (range (n+1)).filter _, _
      rw [sum_filter]
      change (∑ p ∈ P, term (n,p)) ≤ ∑ p ∈ range (n+1), term (n,p)
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact mem_range.mpr (by have := (bounds hp).2; omega)
      · exact fun p _ _ ↦ term_nonneg (n,p)

/-- Central first moment from the unconditional prime number theorem and ordered-pair counting. -/
theorem L_goldbach_central_first_moment :
    let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0; let C := fun n : ℕ => ∑ p ∈ (Finset.range (n+1)).filter (fun p => n≤3*p ∧ 3*p≤2*n), w p*w (n-p); let I := fun x : ℕ => (Finset.Icc x (2*x)).filter (fun n => Even n); ∃ c : ℝ, 0<c ∧ ∃ X : ℕ, ∀ x≥X, c*(x:ℝ)^2 ≤ ∑ n ∈ I x, C n := by
  change ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x ≥ X, c*(x : ℝ)^2 ≤ ∑ n ∈ evenBlock x, central n
  obtain ⟨K, hK⟩ := eventually_large_mass
  refine ⟨1/64, by norm_num, 4*K+16, fun x hx ↦ ?_⟩
  let k := x/4 + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hlo : x ≤ 4*k := by dsimp [k]; omega
  have hhi : 3*k ≤ x := by dsimp [k]; omega
  have hmass := hK k (by dsimp [k]; omega)
  have hxR : (x : ℝ) ≤ 4*k := by exact_mod_cast hlo
  have hlin : (x : ℝ)/8 ≤ ∑ p ∈ windowPrimes k, weight p := by linarith
  have hsquare := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ x/8) hlin
  exact le_trans (by nlinarith only [hsquare]) (central_block_mass x k hk hlo hhi)

end PEqualNP.Outside
