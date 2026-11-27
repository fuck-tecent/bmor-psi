import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace GoldbachRoughSquare

private theorem code_bounds {N q k : ℕ} (hq : 2 ≤ q) (hk : 0 < k)
    (hm : k * (q * q) ≤ N) :
    N / q < N / q + k ∧ N / q + k ≤ N / (q-1) := by
  refine ⟨by omega, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩
  have hkq : k*q ≤ N/q := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [Nat.mul_assoc] using hm)
  have hpred : k*(q-1) ≤ N/q := (Nat.mul_le_mul_left k (Nat.sub_le q 1)).trans hkq
  calc
    (N/q + k)*(q-1) = (N/q)*(q-1) + k*(q-1) := Nat.add_mul ..
    _ ≤ (N/q)*(q-1) + N/q := Nat.add_le_add_left hpred _
    _ = (N/q)*q := by rw [← Nat.mul_succ, show (q-1).succ = q by omega]
    _ ≤ N := Nat.div_mul_le_self _ _

private theorem square_count (N z : ℕ) (hz : 1 ≤ z) (D : Finset ℕ)
    (h : ∀ p ∈ D, p ≤ N ∧ ∃ q k : ℕ, z < q ∧ 0 < k ∧ N-p = k*(q*q)) :
    z*D.card ≤ N := by
  classical
  have hdata (p : D) := (h p p.property).2
  choose q k hq hk heq using hdata
  let code (p : D) := N / q p + k p
  have bounds (p : D) : N / q p < code p ∧ code p ≤ N / (q p - 1) := by
    exact code_bounds (by have := hq p; omega) (hk p) (by rw [← heq]; exact Nat.sub_le ..)
  have top (p : D) : code p ≤ N / z := (bounds p).2.trans
    (Nat.div_le_div_left (by have := hq p; omega) (by omega))
  have sep {p r : D} (hlt : q p < q r) : code r < code p := by
    have hdiv : N / (q r - 1) ≤ N / q p :=
      Nat.div_le_div_left (by omega) (by have := hq p; omega)
    exact ((bounds r).2.trans hdiv).trans_lt (bounds p).1
  have positive (p : D) : 0 < code p := Nat.zero_lt_of_lt (bounds p).1
  let f (p : D) : Fin (N/z) := ⟨code p - 1, by have := top p; have := positive p; omega⟩
  have hinj : Function.Injective f := by
    intro p r hpr
    have he : code p = code r := by
      have he' : code p - 1 = code r - 1 := congrArg Fin.val hpr
      have := positive p
      have := positive r
      omega
    have hqr : q p = q r := by
      rcases lt_trichotomy (q p) (q r) with hlt|same|hgt
      · have := sep hlt; omega
      · exact same
      · have := sep hgt; omega
    have hkr : k p = k r := by
      change N / q p + k p = N / q r + k r at he
      rw [hqr] at he
      omega
    apply Subtype.ext
    have ee := heq p
    rw [hqr, hkr, ← heq r] at ee
    have := (h p p.property).1
    have := (h r r.property).1
    omega
  have hc : D.card ≤ N/z := by simpa using Fintype.card_le_of_injective f hinj
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < z)).1 hc

end GoldbachRoughSquare

theorem PEqualNP.Outside.L_goldbach_rough_fifth_square_error :
    let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∀ N z : ℕ, 1 ≤ z → z^5 ≤ N → z*((C N).filter (fun p => ¬ Squarefree (N-p))).card ≤ N := by
  dsimp only
  intro N z hz hzN
  apply GoldbachRoughSquare.square_count N z hz
  intro p hp
  obtain ⟨hc, hsq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr, _, _, _, hm, hmin⟩ := Finset.mem_filter.mp hc
  refine ⟨(Finset.mem_range.mp hr).le, ?_⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨q, hprime, hdiv⟩ := hsq
  have hminq := Nat.minFac_le_of_dvd hprime.two_le ((Nat.dvd_mul_right q q).trans hdiv)
  have hzq : z < q := by
    by_contra! hle
    have := Nat.pow_le_pow_left (hminq.trans hle) 5
    omega
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨q, k, hzq, ?_, by simpa [Nat.mul_comm] using hk⟩
  by_contra! hzero
  have : k = 0 := by omega
  simp [this] at hk
  omega
