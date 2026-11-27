import Mathlib

open Finset Filter
open scoped Topology

namespace DynFirstMassAux

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

private theorem window_le (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p:ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union (f := fun p : ℕ => if p.Prime then Real.log (p:ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := a) (c := a) (d := b) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab] at split
  have h1 : Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [h1]
  calc ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ)
      ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b:ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp' := mem_filter.mp hp
        have h2 := (mem_Ioc.mp hp'.1)
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast h2.2)
    _ = _ := by simp

private theorem count_nat (X : ℕ) (hX : 16 ≤ X) :
    (((Ioc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card *
      ((Ioc X (X + X / 2)).filter Nat.Prime).card) ≤
    ∑ n ∈ (Icc X (2 * X)).filter Even,
      (((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ Nat.Prime (n - p))).card := by
  set s := Nat.sqrt X with hs
  have hs4 : 4 ≤ s := by
    rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ X := Nat.sqrt_le X
  have h4s : 4 * s ≤ X := by nlinarith
  set P := (Ioc s (2 * s)).filter Nat.Prime
  set Q := (Ioc X (X + X / 2)).filter Nat.Prime
  have hcard : P.card * Q.card = (P ×ˢ Q).card := by rw [card_product]
  rw [hcard]
  simp_rw [card_filter]
  rw [← sum_product' (f := fun n p => if p ≤ n ∧ Nat.Prime (n - p) then 1 else 0)]
  have := Finset.sum_le_sum_of_injOn
    (s := P ×ˢ Q) (t := ((Icc X (2 * X)).filter Even) ×ˢ ((Icc s (2 * s)).filter Nat.Prime))
    (e := fun z : ℕ × ℕ => (z.1 + z.2, z.1))
    (f := fun _ => 1)
    (g := fun z : ℕ × ℕ => if z.2 ≤ z.1 ∧ Nat.Prime (z.1 - z.2) then 1 else 0)
    ?_ ?_ ?_ ?_
  · simpa using this
  · intro z _ v _ he
    have h1 : z.1 = v.1 := congrArg Prod.snd he
    have h2 : z.1 + z.2 = v.1 + v.2 := congrArg Prod.fst he
    exact Prod.ext h1 (by omega)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨hp, hq⟩ := mem_product.mp hz
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    obtain ⟨hp3, hp4⟩ := mem_Ioc.mp hp1
    obtain ⟨hq3, hq4⟩ := mem_Ioc.mp hq1
    have hpodd : Odd z.1 := hp2.odd_of_ne_two (by omega)
    have hqodd : Odd z.2 := hq2.odd_of_ne_two (by omega)
    refine mem_product.mpr ⟨?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hpodd.add_odd hqodd⟩
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hp2⟩
  · intro z hz
    obtain ⟨hp, hq⟩ := mem_product.mp hz
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    obtain ⟨hp3, hp4⟩ := mem_Ioc.mp hp1
    obtain ⟨hq3, hq4⟩ := mem_Ioc.mp hq1
    have h1 : z.1 ≤ z.1 + z.2 := by omega
    have h2 : z.1 + z.2 - z.1 = z.2 := by omega
    simp [h1, h2, hq2]
  · intro a _ _
    exact Nat.zero_le _

set_option maxHeartbeats 1000000 in
private theorem main_ineq : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    c * (X:ℝ) * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2) ≤
    ∑ n ∈ (Icc X (2 * X)).filter Even,
      ((((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ Nat.Prime (n - p))).card : ℝ) := by
  obtain ⟨K, hK⟩ := theta_bounds
  refine ⟨1/20, by norm_num, (K+16)^2, fun X hX => ?_⟩
  have hX16 : 16 ≤ X := by nlinarith [Nat.zero_le K]
  have hnat := count_nat X hX16
  set s := Nat.sqrt X with hs
  have hsK : K ≤ s := by
    rw [hs]; exact le_trans (by omega) (Nat.le_sqrt.mpr (by nlinarith [hX] : (K+16)*(K+16) ≤ X))
  have hs4 : 4 ≤ s := by
    rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ X := Nat.sqrt_le X
  have hsl : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have h4s : 4 * s ≤ X := by nlinarith
  set P := (Ioc s (2 * s)).filter Nat.Prime
  set Q := (Ioc X (X + X / 2)).filter Nat.Prime
  have hcast : ((P.card * Q.card : ℕ) : ℝ) ≤
      ((∑ n ∈ (Icc X (2 * X)).filter Even,
      (((Icc s (2 * s)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ Nat.Prime (n - p))).card : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at hcast
  refine le_trans ?_ hcast
  have hx16 : (16:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX16
  set r := Real.sqrt (X:ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = (X:ℝ) := Real.mul_self_sqrt (by linarith)
  have hsr : (s:ℝ) * (s:ℝ) ≤ (X:ℝ) := by exact_mod_cast hss
  have hsl' : (X:ℝ) < ((s:ℝ)+1)*((s:ℝ)+1) := by exact_mod_cast hsl
  have hs4' : (4:ℝ) ≤ s := by exact_mod_cast hs4
  have hsle : (s:ℝ) ≤ r := by nlinarith
  have hrs : r ≤ (s:ℝ) + 1 := by nlinarith
  have hr2 : r ≤ 2 * (s:ℝ) := by linarith
  have hL : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  set L := Real.log (X:ℝ) with hLdef
  -- P count
  have hP1 := window_le s (2*s) (by omega)
  have hbs := hK s hsK
  have hb2s := hK (2*s) (by omega)
  push_cast at hb2s hP1
  have hlog2s : Real.log (2 * (s:ℝ)) ≤ L := by
    apply Real.log_le_log (by linarith)
    have : (4 * s : ℝ) ≤ (X:ℝ) := by exact_mod_cast h4s
    linarith
  have hPc : (0:ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hP2 : (17/20 : ℝ) * s ≤ (P.card : ℝ) * L := by
    have h1 : (P.card : ℝ) * Real.log (2 * (s:ℝ)) ≤ (P.card : ℝ) * L :=
      mul_le_mul_of_nonneg_left hlog2s hPc
    linarith [hbs.2, hb2s.1]
  -- Q count
  have hQ1 := window_le X (X + X/2) (by omega)
  have hbX := hK X (by nlinarith [hX])
  have hbQ := hK (X + X/2) (by omega)
  push_cast at hQ1 hbQ
  have hdiv : (X:ℝ) ≤ 2 * ((X/2 : ℕ) : ℝ) + 1 := by
    have : X ≤ 2 * (X/2) + 1 := by omega
    exact_mod_cast this
  have hQc : (0:ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
  have hlogQ : Real.log ((X:ℝ) + ((X/2 : ℕ) : ℝ)) ≤ 2 * L := by
    have h1 : Real.log ((X:ℝ) + ((X/2 : ℕ) : ℝ)) ≤ Real.log ((X:ℝ) * (X:ℝ)) := by
      apply Real.log_le_log (by linarith)
      have : ((X/2 : ℕ) : ℝ) ≤ (X:ℝ) := by exact_mod_cast Nat.div_le_self X 2
      nlinarith
    rw [Real.log_mul (by linarith) (by linarith)] at h1
    linarith
  have hQ2 : (3/20 : ℝ) * (X:ℝ) ≤ (Q.card : ℝ) * L := by
    have h1 : (Q.card : ℝ) * Real.log ((X:ℝ) + ((X/2 : ℕ) : ℝ)) ≤ (Q.card : ℝ) * (2 * L) :=
      mul_le_mul_of_nonneg_left hlogQ hQc
    have hh : ((X/2 : ℕ) : ℝ) ≥ (X:ℝ) / 2 - 1 / 2 := by linarith
    nlinarith [hbX.2, hbQ.1]
  have hx0 : (0:ℝ) ≤ (X:ℝ) := by linarith
  have key : (1/20 : ℝ) * (X:ℝ) * r ≤ ((P.card : ℝ) * (Q.card : ℝ)) * (L * L) := by
    have h3 : ((17/20 : ℝ) * s) * ((3/20 : ℝ) * (X:ℝ)) ≤ ((P.card : ℝ) * L) * ((Q.card : ℝ) * L) :=
      mul_le_mul hP2 hQ2 (by linarith) (mul_nonneg hPc hL.le)
    have h4 := mul_nonneg hx0 (sub_nonneg.2 hr2)
    have h5 : (1/20 : ℝ) * (X:ℝ) * r ≤ ((17/20 : ℝ) * s) * ((3/20 : ℝ) * (X:ℝ)) := by
      have h7 : 0 ≤ (s:ℝ) * (X:ℝ) := mul_nonneg (by linarith) hx0
      nlinarith
    have h6 : ((P.card : ℝ) * L) * ((Q.card : ℝ) * L) = ((P.card : ℝ) * (Q.card : ℝ)) * (L * L) := by
      ring
    linarith
  have hfe : (1/20 : ℝ) * (X:ℝ) * (r / L^2) = ((1/20 : ℝ) * (X:ℝ) * r) / (L * L) := by
    field_simp
  rw [hfe, div_le_iff₀ (by positivity)]
  linarith

end DynFirstMassAux

theorem Conjectures.Goldbach.DynFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, c*(X:ℝ)*M X ≤ ∑ n ∈ E X, (H X n:ℝ) := by
  intro E P H M
  exact DynFirstMassAux.main_ineq
