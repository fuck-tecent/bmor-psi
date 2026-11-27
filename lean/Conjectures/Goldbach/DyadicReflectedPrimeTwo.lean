import Mathlib

open scoped BigOperators

lemma arith_key (N q : ℕ) (h4 : 4 ≤ N) (hq4 : 4 ≤ q) :
    (if (N+q-2)%q = 2 then (if (N+2*q-2)%(2*q) < q then (1:ℝ) else -1) else 0)
      = (if N %(2*q)=4 %(2*q) then (1:ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) := by
  have hqpos : 0 < q := by omega
  have harg : (N+q-2)%q = (N-2)%q := by
    have h1 : N + q - 2 = (N-2) + q*1 := by
      rw [Nat.sub_eq_iff_eq_add (by omega : 2 ≤ N + q)]
      omega
    rw [h1, Nat.add_mul_mod_self_left]
  obtain ⟨c, r0, hr0lt, hN⟩ : ∃ c r0, r0 < q ∧ N - 4 = c*q + r0 := by
    refine ⟨(N-4)/q, (N-4)%q, Nat.mod_lt _ hqpos, ?_⟩
    rw [Nat.mul_comm ((N-4)/q) q, add_comm]
    exact (Nat.mod_add_div (N-4) q).symm
  have hN4 : N = 4 + c*q + r0 := by omega
  have harg2 : ((N+q-2)%q = 2) ↔ (r0 = 0) := by
    have harg' : (N+q-2)%q = (r0+2)%q := by
      have h1 : N + q - 2 = (r0 + 2) + (c+1)*q := by
        rw [hN4, Nat.sub_eq_iff_eq_add (by omega : 2 ≤ 4 + c*q + r0 + q)]
        ring
      rw [h1, Nat.mul_comm (c+1) q]
      exact Nat.add_mul_mod_self_left (r0+2) q (c+1)
    rw [harg']
    constructor
    · intro h
      by_cases hc : r0 + 2 < q
      · rw [Nat.mod_eq_of_lt hc] at h; omega
      · push_neg at hc
        rw [Nat.mod_eq_sub_mod hc] at h
        have h1 : r0 + 2 - q < q := by omega
        rw [Nat.mod_eq_of_lt h1] at h
        omega
    · intro h
      subst h
      rw [Nat.mod_eq_of_lt (by omega : 0 + 2 < q)]
  have hpar : c % 2 = 0 ∨ c % 2 = 1 := by
    have := Nat.mod_lt c (by norm_num : 0 < 2); omega
  have hq_dvd_2q : q ∣ 2*q := by
    rw [Nat.mul_comm 2 q]; exact dvd_mul_right q 2
  have hcond1 : (N %(2*q) = 4 %(2*q)) ↔ (r0 = 0 ∧ c % 2 = 0) := by
    have h4lt : 4 < 2*q := by omega
    constructor
    · intro hmod
      have hmodeq : N ≡ 4 [MOD (2*q)] := by
        unfold Nat.ModEq
        rw [hmod, Nat.mod_eq_of_lt h4lt]
      have hdvd : (2*q) ∣ N - 4 := (Nat.modEq_iff_dvd' (by omega : 4 ≤ N)).mp hmodeq.symm
      rw [hN] at hdvd
      have hq_dvd : q ∣ c*q + r0 := dvd_trans hq_dvd_2q hdvd
      have hq_r0 : q ∣ r0 := by
        have h1 : q ∣ r0 + q*c := by
          have h2 := hq_dvd
          simpa [mul_comm, add_comm] using h2
        exact (Nat.dvd_add_iff_left (dvd_mul_right q c)).mpr h1
      have hr0 : r0 = 0 := Nat.eq_zero_of_dvd_of_lt hq_r0 hr0lt
      have hc2 : 2 ∣ c := by
        have h : (2*q) ∣ c*q := by rw [hr0, add_zero] at hdvd; exact hdvd
        have h' : 2*q ∣ c*q := h
        rw [Nat.mul_comm 2 q, Nat.mul_comm c q] at h'
        exact (Nat.mul_dvd_mul_iff_left hqpos).mp h'
      exact ⟨hr0, Nat.dvd_iff_mod_eq_zero.mp hc2⟩
    · rintro ⟨rfl, hc2⟩
      obtain ⟨d, rfl⟩ := Nat.dvd_iff_mod_eq_zero.mpr hc2
      have hNc : N = 4 + d*(2*q) := by rw [hN4]; ring
      rw [hNc, Nat.mul_comm d (2*q)]
      exact Nat.add_mul_mod_self_left 4 (2*q) d
  have hcond2 : (N %(2*q) = (4+q)%(2*q)) ↔ (r0 = 0 ∧ c % 2 = 1) := by
    constructor
    · intro hmod
      by_cases hc0 : c = 0
      · have hNc : N = 4 + r0 := by rw [hN4, hc0]; ring
        have hNlt : N < 2*q := by omega
        have hNm : N % (2*q) = N := Nat.mod_eq_of_lt hNlt
        rw [hNm] at hmod
        have hv : (4+q) % (2*q) = 0 ∨ (4+q) % (2*q) = 4+q := by
          by_cases hq : q = 4
          · left; subst hq; norm_num
          · right; exact Nat.mod_eq_of_lt (by omega)
        rcases hv with hv | hv
        · rw [hv] at hmod; omega
        · rw [hv] at hmod; omega
      · have hc1 : 1 ≤ c := by omega
        have hge : 4 + q ≤ N := by
          rw [hN4]
          have h1 : 1*q ≤ c*q := Nat.mul_le_mul_right q hc1
          have h2 : q ≤ c*q := by simpa using h1
          omega
        have hmodeq : N ≡ (4+q) [MOD (2*q)] := by
          unfold Nat.ModEq
          rw [hmod]
        have hdvd : (2*q) ∣ N - (4+q) := (Nat.modEq_iff_dvd' hge).mp hmodeq.symm
        have hsub : N - (4+q) = (c-1)*q + r0 := by
          have hc' : c = (c-1) + 1 := by omega
          have h1 : N = 4 + ((c-1)+1)*q + r0 := by
            have h2 : c*q = ((c-1)+1)*q := by
              conv_lhs => rw [hc']
            omega
          rw [h1]
          have hexp : ((c-1)+1)*q = (c-1)*q + q := by ring
          rw [hexp]
          omega
        rw [hsub] at hdvd
        have hq_dvd : q ∣ (c-1)*q + r0 := dvd_trans hq_dvd_2q hdvd
        have hq_r0 : q ∣ r0 := by
          have h1 : q ∣ r0 + q*(c-1) := by
            have h2 := hq_dvd
            rw [mul_comm (c-1) q, add_comm] at h2
            exact h2
          exact (Nat.dvd_add_iff_left (dvd_mul_right q (c-1))).mpr h1
        have hr0 : r0 = 0 := Nat.eq_zero_of_dvd_of_lt hq_r0 hr0lt
        have hc_odd : c % 2 = 1 := by
          have h : (2*q) ∣ (c-1)*q := by rw [hr0, add_zero] at hdvd; exact hdvd
          have h' : 2*q ∣ (c-1)*q := h
          rw [Nat.mul_comm 2 q, Nat.mul_comm (c-1) q] at h'
          have h2 : 2 ∣ c-1 := (Nat.mul_dvd_mul_iff_left hqpos).mp h'
          have hmod2 : (c-1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
          have hlt := Nat.mod_lt c (by norm_num : 0 < 2)
          omega
        exact ⟨hr0, hc_odd⟩
    · rintro ⟨rfl, hcodd⟩
      obtain ⟨d, hc⟩ : ∃ d, c = 2*d + 1 := by
        refine ⟨c/2, ?_⟩
        have h1 := Nat.div_add_mod c 2
        omega
      have hNc : N = (4+q) + d*(2*q) := by rw [hN4, hc]; ring
      rw [hNc, Nat.mul_comm d (2*q)]
      exact Nat.add_mul_mod_self_left (4+q) (2*q) d
  have hsign_even : r0 = 0 → c % 2 = 0 → (N+2*q-2)%(2*q) < q := by
    intro hr hr2
    obtain ⟨d, hc⟩ : ∃ d, c = 2*d := Nat.dvd_iff_mod_eq_zero.mpr hr2
    have hNc : N = 4 + d*(2*q) := by rw [hN4, hr, hc]; ring
    have h1 : N + 2*q - 2 = 2 + (d+1)*(2*q) := by
      rw [hNc, Nat.sub_eq_iff_eq_add (by omega : 2 ≤ 4 + d*(2*q) + 2*q)]
      ring
    rw [h1, Nat.mul_comm (d+1) (2*q)]
    rw [Nat.add_mul_mod_self_left]
    have h2 : 2 % (2*q) = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2]; omega
  have hsign_odd : r0 = 0 → c % 2 = 1 → ¬ ((N+2*q-2)%(2*q) < q) := by
    intro hr hr2
    obtain ⟨d, hc⟩ : ∃ d, c = 2*d + 1 := by
      refine ⟨c/2, ?_⟩
      have h1 := Nat.div_add_mod c 2
      omega
    have hNc : N = 4 + (2*d+1)*q := by rw [hN4, hr, hc]; ring
    have h1 : N + 2*q - 2 = (q+2) + (d+1)*(2*q) := by
      rw [hNc, Nat.sub_eq_iff_eq_add (by omega : 2 ≤ 4 + (2*d+1)*q + 2*q)]
      ring
    rw [h1, Nat.mul_comm (d+1) (2*q)]
    rw [Nat.add_mul_mod_self_left]
    have h2 : (q+2) % (2*q) = q+2 := Nat.mod_eq_of_lt (by omega)
    rw [h2]; omega
  by_cases hr0 : r0 = 0
  · have hargval : (N+q-2)%q = 2 := harg2.mpr hr0
    rw [if_pos hargval]
    rcases hpar with hc2 | hc1
    · have hs : (N+2*q-2)%(2*q) < q := hsign_even hr0 hc2
      have hc1v : N %(2*q) = 4 %(2*q) := hcond1.mpr ⟨hr0, hc2⟩
      have hc2v : ¬ (N %(2*q) = (4+q)%(2*q)) := by
        intro hh
        have := (hcond2.mp hh).2
        omega
      rw [if_pos hs, if_pos hc1v]
    · have hs : ¬ ((N+2*q-2)%(2*q) < q) := hsign_odd hr0 hc1
      have hc2v : N %(2*q) = (4+q)%(2*q) := hcond2.mpr ⟨hr0, hc1⟩
      have hc1v : ¬ (N %(2*q) = 4 %(2*q)) := by
        intro hh
        have := (hcond1.mp hh).2
        omega
      rw [if_neg hs, if_neg hc1v, if_pos hc2v]
  · have hargval : ¬ ((N+q-2)%q = 2) := fun hh => hr0 (harg2.mp hh)
    rw [if_neg hargval]
    have hc1v : ¬ (N %(2*q) = 4 %(2*q)) := fun hh => hr0 (hcond1.mp hh).1
    have hc2v : ¬ (N %(2*q) = (4+q)%(2*q)) := fun hh => hr0 (hcond2.mp hh).1
    rw [if_neg hc1v, if_neg hc2v]

namespace PEqualNP.Outside


theorem L_goldbach_dyadic_reflected_prime_two :
    ∀ (N k : ℕ), 4 ≤ N → Even N → 1 ≤ k →
    let q : ℕ := 2^k
    let A := fun r : ℕ => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime), Real.log (n : ℝ)
    let D := fun r : ℕ => A r - A (r+q)
    (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)) =
      (if N %(2*q)=4 %(2*q) then (1 : ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) * (Real.log 2)^2 := by
  intro N k h4 hEven hk
  let q : ℕ := 2^k
  let A : ℕ → ℝ := fun r => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime), Real.log (n : ℝ)
  let D : ℕ → ℝ := fun r => A r - A (r+q)
  have hq_even : Even q := by
    change Even (2^k)
    obtain ⟨j, hjk⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hjk]
    refine ⟨2^j, ?_⟩
    rw [pow_succ]
    ring
  have hq2 : 2 ≤ q := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hN2 : Even (N-2) := by
    rw [Nat.even_iff]
    have h1 : N % 2 = 0 := Nat.even_iff.mp hEven
    have h2 : ((N-2) + 2*1) % 2 = (N-2) % 2 := Nat.add_mul_mod_self_left (N-2) 2 1
    have h3 : (N-2) + 2*1 = N := by omega
    rw [h3] at h2
    rw [← h2]
    exact h1
  have hprime_even : ∀ n, n.Prime → Even n → n = 2 := by
    intro n hp hn
    rcases hp.eq_two_or_odd with h | h
    · exact h
    · have : n % 2 = 0 := Nat.even_iff.mp hn
      omega
  have heven_of_mod : ∀ n r, Even r → n % (2*q) = r → Even n := by
    intro n r hr hmod
    rw [Nat.even_iff] at hr ⊢
    have h1 : n % 2 = (n % (2*q)) % 2 := (Nat.mod_mod_of_dvd n (dvd_mul_right 2 q)).symm
    rw [h1, hmod, hr]
  have h2q2 : 2 < 2*q := by omega
  have hA_even : ∀ r, Even r → A r = if r = 2 then Real.log 2 else 0 := by
    intro r hr
    have hmem2 : (2:ℕ) ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=2 ∧ n.Prime) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, Nat.prime_two⟩
      exact Nat.mod_eq_of_lt h2q2
    have hfilter2 : (Finset.range (N+1)).filter (fun n => n %(2*q)=2 ∧ n.Prime) = {2} := by
      ext n
      constructor
      · intro hn
        obtain ⟨-, hmod, hp⟩ := Finset.mem_filter.mp hn
        have he : Even n := heven_of_mod n 2 even_two hmod
        rw [Finset.mem_singleton]
        exact hprime_even n hp he
      · intro hn
        rw [Finset.mem_singleton] at hn
        subst hn
        exact hmem2
    by_cases h2 : r = 2
    · subst h2
      change (∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=2 ∧ n.Prime), Real.log (n:ℝ)) = _
      rw [hfilter2]
      simp
    · have hempty : (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨-, hmod, hp⟩ := Finset.mem_filter.mp hn
        have he : Even n := heven_of_mod n r hr hmod
        have hn2 : n = 2 := hprime_even n hp he
        subst hn2
        rw [Nat.mod_eq_of_lt h2q2] at hmod
        exact h2 hmod.symm
      change (∑ n ∈ (Finset.range (N+1)).filter (fun n => n %(2*q)=r ∧ n.Prime), Real.log (n:ℝ)) = _
      rw [hempty]
      simp [h2]
  have hD_even : ∀ r, Even r → D r = (if r = 2 then Real.log 2 else 0) - (if r+q = 2 then Real.log 2 else 0) := by
    intro r hr
    change A r - A (r+q) = _
    rw [hA_even r hr, hA_even (r+q) (hr.add hq_even)]
  have hD_k4 : 4 ≤ q → ∀ r, Even r → D r = if r = 2 then Real.log 2 else 0 := by
    intro hq4 r hr
    rw [hD_even r hr]
    have h1 : ¬ (r + q = 2) := by omega
    rw [if_neg h1]
    ring
  -- ===== k = 1 case =====
  have hk1case : k = 1 → (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)) =
      (if N %(2*q)=4 %(2*q) then (1 : ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) * (Real.log 2)^2 := by
    intro hk1
    have hq2 : q = 2 := by
      change 2^k = 2
      rw [hk1]
      norm_num
    rw [hq2] at hD_even ⊢
    have hfilter : (Finset.range 2).filter (fun r => Even r) = {0} := by decide
    rw [hfilter, Finset.sum_singleton]
    have hD0 : D 0 = - Real.log 2 := by
      rw [hD_even 0 (show Even 0 from ⟨0, by norm_num⟩)]
      norm_num
    have hNmod : (N + 2*2 - 0) % (2*2) = N % 4 := by
      have h : N + 2*2 - 0 = N + (2*2)*1 := by norm_num
      rw [h, Nat.add_mul_mod_self_left]
    have harg0 : (N+2-0)%2 = 0 := by
      have h1 : N % 2 = 0 := Nat.even_iff.mp hEven
      have h2 : (N + 2*1) % 2 = N % 2 := Nat.add_mul_mod_self_left N 2 1
      show (N+2) % 2 = 0
      rw [show N + 2 = N + 2*1 from rfl, h2, h1]
    rw [harg0, hD0]
    have hcases : N % 4 = 0 ∨ N % 4 = 2 := by
      have hlt : N % 4 < 4 := Nat.mod_lt N (by norm_num)
      have hmod : (N % 4) % 2 = N % 2 := Nat.mod_mod_of_dvd N (by norm_num : 2 ∣ 4)
      have hNm : N % 2 = 0 := Nat.even_iff.mp hEven
      rw [hNm] at hmod
      omega
    rcases hcases with h0 | h2
    · have hs : (N + 2*2 - 0) % (2*2) < 2 := by rw [hNmod, h0]; norm_num
      have hr1 : N % 4 = 4 % 4 := by rw [h0]
      rw [if_pos hs, if_pos hr1]
      ring
    · have hs : ¬ ((N + 2*2 - 0) % (2*2) < 2) := by rw [hNmod, h2]; norm_num
      have hr1 : N % 4 ≠ 4 % 4 := by rw [h2]; norm_num
      have hr2 : N % 4 = (4+2) % (2*2) := by rw [h2]
      rw [if_neg hs, if_neg hr1, if_pos hr2]
      ring
  -- ===== k ≥ 2 case =====
  have hk2case : 2 ≤ k → (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)) =
      (if N %(2*q)=4 %(2*q) then (1 : ℝ) else if N %(2*q)=(4+q)%(2*q) then -1 else 0) * (Real.log 2)^2 := by
    intro hk2
    have hq4 : 4 ≤ q := by
      calc 4 = 2^2 := by norm_num
        _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk2
    have hqpos : 0 < q := by omega
    have hD_k2 := hD_k4 hq4
    have hmem2 : (2:ℕ) ∈ (Finset.range q).filter (fun r => Even r) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), even_two⟩
    have hsingle : (∑ r ∈ (Finset.range q).filter (fun r => Even r),
        (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q))
        = (if (N+2*q-2)%(2*q) < q then (1 : ℝ) else -1) * D 2 * D ((N+q-2)%q) := by
      refine Finset.sum_eq_single 2 ?_ ?_
      · intro r hr hne
        obtain ⟨-, hre⟩ := Finset.mem_filter.mp hr
        have hDr : D r = 0 := by
          rw [hD_k2 r hre]
          exact if_neg hne
        simp [hDr]
      · intro hnot
        exact absurd hmem2 hnot
    rw [hsingle]
    have hD2 : D 2 = Real.log 2 := by
      rw [hD_k2 2 even_two]
      norm_num
    rw [hD2]
    have hargEven : Even ((N+q-2)%q) := by
      have harg_eq : (N+q-2)%q = (N-2)%q := by
        have h1 : N + q - 2 = (N-2) + q*1 := by
          rw [Nat.sub_eq_iff_eq_add (by omega : 2 ≤ N + q)]
          omega
        rw [h1, Nat.add_mul_mod_self_left]
      rw [harg_eq, Nat.even_iff]
      rw [Nat.mod_mod_of_dvd (N-2) (even_iff_two_dvd.mp hq_even), Nat.even_iff.mp hN2]
    rw [hD_k2 ((N+q-2)%q) hargEven]
    have hL : (if (N+2*q-2)%(2*q) < q then (1 : ℝ) else -1) * Real.log 2 *
        (if ((N+q-2)%q = 2) then Real.log 2 else 0)
        = (if ((N+q-2)%q = 2) then (if (N+2*q-2)%(2*q) < q then (1 : ℝ) else -1) else 0) *
          (Real.log 2)^2 := by
      by_cases ha : (N+q-2)%q = 2
      · rw [if_pos ha, if_pos ha]; ring
      · rw [if_neg ha, if_neg ha]; ring
    rw [hL, arith_key N q h4 hq4]
  by_cases hk1 : k = 1
  · exact hk1case hk1
  · exact hk2case (by omega)

end PEqualNP.Outside

/-- Canonical module-named statement (the platform checker requires a declaration named
exactly after the gap module: `Conjectures.Goldbach.DyadicReflectedPrimeTwo`). -/
theorem Conjectures.Goldbach.DyadicReflectedPrimeTwo :
    ∀ (N k : ℕ), 4 ≤ N → Even N → 1 ≤ k →
    let q : ℕ := 2^k
    let A := fun r : ℕ => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % (2*q) = r ∧ n.Prime), Real.log (n : ℝ)
    let D := fun r : ℕ => A r - A (r+q)
    (∑ r ∈ (Finset.range q).filter (fun r => Even r),
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)) =
      (if N % (2*q) = 4 % (2*q) then (1 : ℝ) else if N % (2*q) = (4+q) % (2*q) then -1 else 0) * (Real.log 2)^2 :=
  PEqualNP.Outside.L_goldbach_dyadic_reflected_prime_two
