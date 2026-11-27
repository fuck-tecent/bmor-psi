import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open ArithmeticFunction

theorem PEqualNP.Outside.L_goldbach_primitive_ramified_total :
    ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), ArithmeticFunction.vonMangoldt k) ≤ 2*Real.log (n:ℝ) := by
  intro n hn
  classical
  let S := (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n)
  let T := S.filter IsPrimePow
  have hfilter : ∑ k ∈ T, vonMangoldt k = ∑ k ∈ S, vonMangoldt k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkt
    exact vonMangoldt_eq_zero_iff.mpr (fun h => hkt (Finset.mem_filter.mpr ⟨hk, h⟩))
  have hdata (k : ℕ) (hk : k ∈ T) :
      k.minFac ∈ n.primeFactors ∧ 0 < k.factorization k.minFac ∧
        k.minFac ^ k.factorization k.minFac = k := by
    obtain ⟨hs, hpp⟩ := Finset.mem_filter.mp hk
    have hp := Nat.minFac_prime (by exact hpp.ne_one)
    have he := hpp.minFac_pow_factorization_eq
    have ha : 0 < k.factorization k.minFac := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, pow_zero] at he
      exact hpp.ne_one he.symm
    have hnc := (Finset.mem_filter.mp hs).2.2.2
    have hd : k.minFac ∣ n := by
      by_contra h
      apply hnc
      rw [← he]
      exact (Nat.coprime_pow_left_iff ha _ _).mpr (hp.coprime_iff_not_dvd.mpr h)
    exact ⟨hp.mem_primeFactors hd (by omega), ha, he⟩
  have hwindow (k : ℕ) (hk : k ∈ T) : n ≤ 3*k ∧ 3*k ≤ 2*n := by
    have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    exact ⟨h.1, h.2.1⟩
  have hfiber (p : ℕ) (hp : p ∈ n.primeFactors) :
      (T.filter (fun k => k.minFac = p)).card ≤ 2 := by
    let F := T.filter (fun k => k.minFac = p)
    by_cases hF : F.Nonempty
    · let m := F.min' hF
      have hm := F.min'_mem hF
      obtain ⟨hmt, hmp⟩ := Finset.mem_filter.mp hm
      let a := m.factorization m.minFac
      have hma : p ^ a = m := by
        change m.minFac = p at hmp
        dsimp [a]
        simpa only [hmp] using (hdata m hmt).2.2
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have hh : F ⊆ {m, p^(a+1)} := by
        intro k hk
        obtain ⟨hkt, hkp⟩ := Finset.mem_filter.mp hk
        let b := k.factorization k.minFac
        have hkb : p ^ b = k := by
          dsimp [b]
          simpa only [hkp] using (hdata k hkt).2.2
        have hmk := F.min'_le k hk
        have hab : a ≤ b := by
          by_contra! h
          have hh := Nat.pow_lt_pow_right hp2 h
          rw [hma, hkb] at hh
          omega
        have hba : b ≤ a+1 := by
          by_contra! h
          have hh : p^(a+2) ≤ p^b := Nat.pow_le_pow_right (by omega) (by omega)
          rw [pow_add, hma, hkb] at hh
          have hp4 : 4 ≤ p^2 := by nlinarith
          have h4 := Nat.mul_le_mul_left m hp4
          have hw₁ := hwindow m hmt
          have hw₂ := hwindow k hkt
          omega
        have hx : b = a ∨ b = a+1 := by omega
        rcases hx with h | h
        · have he : k = m := by rw [← hkb, h, hma]
          simp [he]
        · have he : k = p^(a+1) := by rw [← hkb, h]
          simp [he]
      exact (Finset.card_le_card hh).trans Finset.card_le_two
    · change F.card ≤ 2
      rw [Finset.not_nonempty_iff_eq_empty.mp hF]
      simp
  change (∑ k ∈ S, vonMangoldt k) ≤ _
  rw [← hfilter]
  rw [← Finset.sum_fiberwise_of_maps_to (fun k hk => (hdata k hk).1)]
  calc
    _ ≤ ∑ p ∈ n.primeFactors, 2 * vonMangoldt p := by
      apply Finset.sum_le_sum
      intro p hp
      have hconst : ∀ k ∈ T.filter (fun k => k.minFac = p), vonMangoldt k = vonMangoldt p := by
        intro k hk
        obtain ⟨ht, he⟩ := Finset.mem_filter.mp hk
        have hpp := (Finset.mem_filter.mp ht).2
        rw [vonMangoldt_apply, ite_eq_left hpp, he, vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp)]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber p hp) vonMangoldt_nonneg
    _ ≤ 2 * Real.log (n:ℝ) := by
      rw [← Finset.mul_sum, ← vonMangoldt_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, by omega⟩
      · intro p _ _
        exact vonMangoldt_nonneg
