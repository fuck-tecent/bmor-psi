import Mathlib

/-- 固定短窗口 `[l, u]` 内，`n ^ 2 + a` 的大于 `x` 的不同素因子与整数 `n` 组成的对数
至多是窗口长度的两倍。逐点看：`n ≤ u ≤ 3 * x` 与 `a ≤ x`、`10 ≤ x` 给出
`n ^ 2 + a ≤ 9 * x ^ 2 + x ≤ x ^ 3`；而同一个 `n` 若有三个不同的大于 `x` 的素因子，
两两互素故其积整除 `n ^ 2 + a`，于是积不超过 `n ^ 2 + a`，可是积又至少
`(x + 1) ^ 3`，严格大于 `x ^ 3`，矛盾。故每个 `n` 至多贡献 `2`，求和即得结论。
-/
theorem PEqualNP.Outside.L_quadratic_primes_fixed_offset_endpoint_count :
    ∀ a x l u : ℕ, 10 ≤ x → 1 ≤ a → a ≤ x → u ≤ 3 * x →
      (∑ n ∈ Finset.Icc l u, (((n ^ 2 + a).primeFactors.filter (fun p => x < p)).card)) ≤
        2 * (u + 1 - l) := by
  intro a x l u hx ha hax hu
  refine (Finset.sum_le_card_nsmul (Finset.Icc l u) _ 2 (fun n hn => ?_)).trans ?_
  · set S := (n ^ 2 + a).primeFactors.filter (fun p => x < p) with hS
    have hbnd : n ^ 2 + a ≤ x ^ 3 := by
      have hn : n ≤ 3 * x := Nat.le_trans (Finset.mem_Icc.mp hn).2 hu
      have hx2 : x ≤ x ^ 2 := Nat.le_self_pow (by omega : 2 ≠ 0) x
      calc n ^ 2 + a ≤ (3 * x) ^ 2 + x := Nat.add_le_add (pow_le_pow_left' hn 2) hax
        _ = 9 * x ^ 2 + x := by ring
        _ ≤ 9 * x ^ 2 + x ^ 2 := Nat.add_le_add (Nat.le_refl _) hx2
        _ = 10 * x ^ 2 := by ring
        _ ≤ x * x ^ 2 := Nat.mul_le_mul hx (Nat.le_refl _)
        _ = x ^ 3 := by ring
    have hle2 : S.card ≤ 2 := by
      by_contra hne
      have hpos : 0 < S.card := by omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      obtain ⟨q, hqe⟩ :=
        Finset.card_pos.mp (show 0 < (S.erase p).card from by
          rw [Finset.card_erase_of_mem hp]
          omega)
      have hq : q ∈ S := (Finset.mem_erase.mp hqe).2
      have hq_ne : q ≠ p := (Finset.mem_erase.mp hqe).1
      obtain ⟨r, rhe⟩ :=
        Finset.card_pos.mp (show 0 < ((S.erase p).erase q).card from by
          rw [Finset.card_erase_of_mem hqe, Finset.card_erase_of_mem hp]
          omega)
      have hpe := Finset.mem_erase.mp (Finset.mem_erase.mp rhe).2
      have hr : r ∈ S := hpe.2
      have hrp : r ≠ p := hpe.1
      have hrq : r ≠ q := (Finset.mem_erase.mp rhe).1
      have hbig : ∀ t ∈ ({p, q, r} : Finset ℕ), Nat.Prime t ∧ t ∣ n ^ 2 + a ∧ x < t := by
        intro t ht
        have htS : t ∈ S := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · exact hp
          · exact hq
          · exact hr
        have hf := Finset.mem_filter.mp htS
        have hm := Nat.mem_primeFactors.mp hf.1
        exact ⟨hm.1, hm.2.1, hf.2⟩
      have hpp := hbig p (by simp)
      have hpq := hbig q (by simp)
      have hrr := hbig r (by simp)
      have cpq : Nat.Coprime p q := (Nat.coprime_primes hpp.1 hpq.1).mpr (Ne.symm hq_ne)
      have cpr : Nat.Coprime p r := (Nat.coprime_primes hpp.1 hrr.1).mpr (Ne.symm hrp)
      have cqr : Nat.Coprime q r := (Nat.coprime_primes hpq.1 hrr.1).mpr (Ne.symm hrq)
      have hd2 : p * q ∣ n ^ 2 + a :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq hpp.2.1 hpq.2.1
      have hd3 : p * q * r ∣ n ^ 2 + a :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_left cpr cqr) hd2 hrr.2.1
      have hprod_le : p * q * r ≤ n ^ 2 + a :=
        Nat.le_of_dvd (by omega : 0 < n ^ 2 + a) hd3
      have hprod_gt : x ^ 3 < p * q * r := by
        have h1 : x + 1 ≤ p := by omega
        have h2 : x + 1 ≤ q := by omega
        have h3 : x + 1 ≤ r := by omega
        calc x ^ 3 < (x + 1) ^ 3 := Nat.pow_lt_pow_left (by omega : x < x + 1) (by omega : 3 ≠ 0)
          _ = (x + 1) * (x + 1) * (x + 1) := by ring
          _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      exact lt_irrefl _ (hprod_gt.trans_le (hprod_le.trans hbnd))
    exact hle2
  · rw [Nat.card_Icc, Nat.nsmul_eq_mul, Nat.mul_comm]
