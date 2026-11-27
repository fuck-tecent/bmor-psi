import Mathlib

/-!
# PREPUB goldbach: `L-goldbach-farey-inverse-full-weight`

Sum over the inverse graph: `Σ_{a} Σ_{u : a*u ≡ 1 mod n} w u = Σ_{u coprime n} w u`
(the inverse map is a bijection of the reduced residue classes). Self-contained, Mathlib only.
-/

namespace PEqualNP.Outside

end PEqualNP.Outside

open PEqualNP.Outside

theorem Conjectures.Goldbach.FareyInverseFullWeight :
    ∀ (n : ℕ) (w : ℕ → ℝ), 1 < n →
      (∑ a ∈ Finset.Ico 1 n,
          ∑ u ∈ (Finset.Ico 1 n).filter (fun u => (a * u) % n = 1), w u) =
        (∑ u ∈ (Finset.Ico 1 n).filter (fun u => u.Coprime n), w u) := by
  intro n w hn
  classical
  -- 引理 1：若 `(b*u)%n = 1` 则 `u` 与 `n` 互素。
  have unit_of_mod : ∀ b u : ℕ, (b * u) % n = 1 → u.Coprime n := by
    intro b u hmod
    have hb1 : 1 ≤ b * u := by
      by_contra h
      push_neg at h
      have hzero : b * u = 0 := by omega
      rw [hzero] at hmod
      simp at hmod
    have hdiv : n ∣ b * u - 1 := by
      set q := (b * u) / n with hq_def
      have hq : n * q + (b * u) % n = b * u := Nat.div_add_mod (b * u) n
      rw [hmod] at hq
      refine ⟨q, ?_⟩
      omega
    have hdvd : Nat.gcd u n ∣ b * u := dvd_mul_of_dvd_right (Nat.gcd_dvd_left u n) b
    have hdvd' : Nat.gcd u n ∣ b * u - 1 := (Nat.gcd_dvd_right u n).trans hdiv
    have h1 : Nat.gcd u n ∣ 1 := by
      have hsub := Nat.dvd_sub hdvd hdvd'
      have hval : b * u - (b * u - 1) = 1 := by omega
      rwa [hval] at hsub
    exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h1)
  -- 引理 2：互素时模逆在 `[1,n)` 中唯一。
  have inv_unique' : ∀ (u a b : ℕ), u.Coprime n → a < n → b < n →
      (a * u) % n = 1 → (b * u) % n = 1 → a = b := by
    intro u a b hcop ha_lt hb_lt ha hb
    have hZa : (a : ZMod n) = (b : ZMod n) := by
      have h1 : ((a * u : ℕ) : ZMod n) = ((b * u : ℕ) : ZMod n) := by
        rw [ZMod.natCast_eq_natCast_iff' _ _ n]
        rw [ha, hb]
      push_cast at h1
      have hw : (u : ZMod n) * (u : ZMod n)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one u hcop
      calc (a : ZMod n) = (a : ZMod n) * (u : ZMod n) * (u : ZMod n)⁻¹ := by
              rw [mul_assoc, hw, mul_one]
        _ = (b : ZMod n) * (u : ZMod n) * (u : ZMod n)⁻¹ := by rw [h1]
        _ = (b : ZMod n) := by rw [mul_assoc, hw, mul_one]
    have hmod := (ZMod.natCast_eq_natCast_iff' a b n).mp hZa
    rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod
    exact hmod
  set U := Finset.Ico 1 n with hU
  -- 第一步：内层 filter 换成 if
  have step1 : (∑ a ∈ U,
        ∑ u ∈ U.filter (fun u => (a * u) % n = 1), w u)
      = ∑ a ∈ U, ∑ u ∈ U, if (a * u) % n = 1 then w u else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_filter]
  rw [step1, Finset.sum_comm]
  -- 第二步：对每个 u 求内层和
  have step2 : ∀ u ∈ U,
      (∑ a ∈ U, if (a * u) % n = 1 then w u else 0) = if u.Coprime n then w u else 0 := by
    intro u hu
    by_cases hc : u.Coprime n
    · rw [if_pos hc]
      obtain ⟨a0, ha0_lt, ha0_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hn
      have ha0_mod' : (a0 * u) % n = 1 := by
        rw [Nat.mul_comm]
        exact ha0_mod
      have ha0_pos : 0 < a0 := by
        rcases Nat.eq_zero_or_pos a0 with h0 | hpos
        · rw [h0] at ha0_mod'
          simp at ha0_mod'
        · exact hpos
      have ha0_mem : a0 ∈ U := by
        rw [hU]
        exact Finset.mem_Ico.mpr ⟨ha0_pos, ha0_lt⟩
      refine (Finset.sum_eq_single a0 ?_ ?_).trans ?_
      · intro b hb hbne
        have hbmod : (b * u) % n ≠ 1 := by
          intro hb1
          have hb_lt : b < n := by
            rw [hU] at hb
            exact (Finset.mem_Ico.mp hb).2
          exact hbne (inv_unique' u b a0 hc hb_lt ha0_lt hb1 ha0_mod')
        simp [hbmod]
      · intro hnotin
        exact absurd ha0_mem hnotin
      · simp [ha0_mod']
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro b _
      have hbmod : (b * u) % n ≠ 1 := by
        intro hb1
        exact hc (unit_of_mod b u hb1)
      simp [hbmod]
  rw [Finset.sum_congr rfl step2]
  rw [← Finset.sum_filter]
