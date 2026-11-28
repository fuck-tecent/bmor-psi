import Mathlib
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio

open Finset

-- child 1 zh: 对每个充分大的偶数 n，中央窗内满足 u 为两个均大于立方根截点的素数之积且 n-u 为素数的 u 数目，至多为终筛体积的 16/25。允许两个素因子相等。
-- child 1 en: For every sufficiently large even n, the number of central u such that u is a product of two primes above the cube-root cutoff and n-u is prime is at most 16/25 times the terminal sieve volume. The two factors of u may coincide.
-- child 2 zh: 对每个充分大的偶数 n，中央窗内满足 u 和 n-u 各为两个均大于立方根截点的素数之积的 u 数目，至多为终筛体积的 23/50。允许每一侧的两个素因子相等。
-- child 2 en: For every sufficiently large even n, the number of central u such that u and n-u are each products of two primes above the cube-root cutoff is at most 23/50 times the terminal sieve volume. The two factors on either side may coincide.
theorem Conjectures.Cuts.Cute010fd32aed746d33789f2a9
    (hmixed :
      let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
      let Z := fun n : ℕ => ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊
      let A := fun n : ℕ => (I n).filter fun u =>
        Z n < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime
      let V := fun n : ℕ => ((I n).card : ℝ) * (n.totient : ℝ) / n *
        ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2/(p : ℝ))
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        (((A n).filter fun u => (n-u).Prime).card : ℝ) ≤ (16/25 : ℝ) * V n)
    (hdouble :
      let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
      let Z := fun n : ℕ => ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊
      let A := fun n : ℕ => (I n).filter fun u =>
        Z n < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime
      let V := fun n : ℕ => ((I n).card : ℝ) * (n.totient : ℝ) / n *
        ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2/(p : ℝ))
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        (((A n).filter fun u => n-u ∈ A n).card : ℝ) ≤ (23/50 : ℝ) * V n) :
    (let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Z₂ := Nat.sqrt; ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → let L := ((I n).filter (fun u => u.Coprime n ∧ Z₁ n < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ Z₂ n)).card; (L:ℝ) ≤ V n (Z₁ n) - V n (Z₂ n) + V n (Z₂ n)/2) := by
  let centralInterval (n : ℕ) : Finset ℕ := Icc ((n+2)/3) ((2*n)/3)

  let cubeCutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊

  let sieveVolume (n z : ℕ) : ℝ :=
    ((centralInterval n).card : ℝ) * (n.totient : ℝ) / n *
      ∏ p ∈ ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2/(p : ℝ))

  let semiprimes (n : ℕ) : Finset ℕ :=
    (centralInterval n).filter fun u =>
      cubeCutoff n < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime

  let mixedCount (n : ℕ) : ℕ :=
    ((semiprimes n).filter fun u => (n-u).Prime).card

  let doubleCount (n : ℕ) : ℕ :=
    ((semiprimes n).filter fun u => n-u ∈ semiprimes n).card

  let lateHits (n : ℕ) : Finset ℕ :=
    (centralInterval n).filter fun u => u.Coprime n ∧ cubeCutoff n < (u*(n-u)).minFac ∧
      (u*(n-u)).minFac ≤ n.sqrt

  have cubeCutoff_lt (n p : ℕ) : cubeCutoff n < p ↔ n < p^3 := by
    dsimp only [cubeCutoff]
    rw [Nat.floor_lt (by positivity)]
    have hpow : (((n : ℝ) ^ (1/3 : ℝ)) ^ (3 : ℕ)) = n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ))]
      norm_num
    calc
      (n : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ↔
          ((n : ℝ) ^ (1/3 : ℝ)) ^ (3 : ℕ) < (p : ℝ) ^ (3 : ℕ) :=
        (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).symm
      _ ↔ n < p^3 := by rw [hpow]; norm_cast

  have bounds_of_mem_central {n u : ℕ} (hn : 64 ≤ n) (hu : u ∈ centralInterval n) :
      22 ≤ u ∧ u < n ∧ 22 ≤ n-u ∧ n-u < n ∧ n ≤ 3*u ∧ n ≤ 3*(n-u) := by
    obtain ⟨hl, hh⟩ := mem_Icc.mp hu
    have hl' := (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 3)).mp hl
    have hh' := (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp hh
    omega

  have reflect_mem_central {n u : ℕ} (hu : u ∈ centralInterval n) :
      n-u ∈ centralInterval n := by
    obtain ⟨hl, hh⟩ := mem_Icc.mp hu
    have hl' := (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 3)).mp hl
    have hh' := (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp hh
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · exact (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 3)).mpr (by omega)
    · exact (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr (by omega)

  have prime_or_mem_semiprimes {n m p : ℕ} (hm : m ∈ centralInterval n)
      (hm₂ : 2 ≤ m) (hcut : cubeCutoff n < p) (hmin : p ≤ m.minFac) (hcube : m < p^3) :
      m.Prime ∨ m ∈ semiprimes n := by
    by_cases hprime : m.Prime
    · exact Or.inl hprime
    · refine Or.inr (mem_filter.mpr ⟨hm, hcut.trans_le hmin, Nat.minFac_prime (by omega), ?_⟩)
      let q := m / m.minFac
      change q.Prime
      have hmul : q * m.minFac = m := Nat.div_mul_cancel (Nat.minFac_dvd m)
      have hq_pos : 0 < q := by
        apply Nat.pos_of_ne_zero
        intro h
        rw [h, zero_mul] at hmul
        omega
      have hq_ne_one : q ≠ 1 := by
        intro hq
        rw [hq, one_mul] at hmul
        exact hprime (hmul ▸ Nat.minFac_prime (by omega : m ≠ 1))
      by_contra hnq
      have hqm : q ∣ m := ⟨m.minFac, hmul.symm⟩
      have hqmin := Nat.minFac_prime hq_ne_one
      have hmin_le : m.minFac ≤ q.minFac :=
        Nat.minFac_le_of_dvd hqmin.two_le ((Nat.minFac_dvd q).trans hqm)
      have hsq : p^2 ≤ q := (Nat.pow_le_pow_left (hmin.trans hmin_le) 2).trans
        (Nat.minFac_sq_le_self hq_pos hnq)
      apply (not_le_of_gt hcube)
      rw [pow_succ, ← hmul]
      exact Nat.mul_le_mul hsq hmin

  have central_exceeds_terminal {n m : ℕ} (hm : 22 ≤ m) (hbound : n ≤ 3*m) :
      n.sqrt < m := by
    apply Nat.sqrt_lt.mpr
    exact hbound.trans_lt (Nat.mul_lt_mul_of_pos_right (by omega) (by omega))

  have card_lateHits_le (n : ℕ) (hn : 64 ≤ n) :
      (lateHits n).card ≤ 2 * mixedCount n + doubleCount n := by
    let mixed := (semiprimes n).filter fun u => (n-u).Prime
    let reflected := mixed.image fun u => n-u
    let double := (semiprimes n).filter fun u => n-u ∈ semiprimes n
    have hsub : lateHits n ⊆ mixed ∪ reflected ∪ double := by
      intro u hu
      obtain ⟨huI, _, hlo, hhi⟩ := mem_filter.mp hu
      obtain ⟨hu₂, hu_lt, hv₂, hv_lt, hnu, hnv⟩ := bounds_of_mem_central hn huI
      have hvI := reflect_mem_central huI
      let p := (u*(n-u)).minFac
      have hp := Nat.minFac_prime (show u*(n-u) ≠ 1 by
        have := Nat.mul_le_mul (show 2 ≤ u by omega) (show 2 ≤ n-u by omega)
        omega)
      have hpcube : n < p^3 := (cubeCutoff_lt n p).mp hlo
      have hleft : p ≤ u.minFac := Nat.minFac_le_of_dvd
        (Nat.minFac_prime (by omega : u ≠ 1)).two_le (dvd_mul_of_dvd_left (Nat.minFac_dvd u) _)
      have hright : p ≤ (n-u).minFac := Nat.minFac_le_of_dvd
        (Nat.minFac_prime (by omega : n-u ≠ 1)).two_le
        (dvd_mul_of_dvd_right (Nat.minFac_dvd (n-u)) _)
      have hclassLeft := prime_or_mem_semiprimes huI (by omega) hlo hleft (hu_lt.trans hpcube)
      have hclassRight := prime_or_mem_semiprimes hvI (by omega) hlo hright (hv_lt.trans hpcube)
      rcases hclassLeft with huP | huA <;> rcases hclassRight with hvP | hvA
      · change p.Prime at hp
        have hp_le : p ≤ n.sqrt := hhi
        rcases hp.dvd_mul.mp (Nat.minFac_dvd (u*(n-u))) with hd | hd
        · have heq : p = u := ((Nat.dvd_prime huP).mp hd).resolve_left hp.ne_one
          exact ((not_le_of_gt (central_exceeds_terminal hu₂ hnu)) (heq ▸ hp_le)).elim
        · have heq : p = n-u := ((Nat.dvd_prime hvP).mp hd).resolve_left hp.ne_one
          exact ((not_le_of_gt (central_exceeds_terminal hv₂ hnv)) (heq ▸ hp_le)).elim
      · refine mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨n-u, ?_, Nat.sub_sub_self hu_lt.le⟩))
        exact mem_filter.mpr ⟨hvA, (Nat.sub_sub_self hu_lt.le).symm ▸ huP⟩
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨huA, hvP⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨huA, hvA⟩)
    calc
      (lateHits n).card ≤ (mixed ∪ reflected ∪ double).card := card_le_card hsub
      _ ≤ (mixed ∪ reflected).card + double.card := card_union_le _ _
      _ ≤ (mixed.card + reflected.card) + double.card :=
        Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ 2 * mixedCount n + doubleCount n := by
        rw [two_mul]
        exact Nat.add_le_add_right (Nat.add_le_add_left card_image_le _) _

  have sieveVolume_pos {n : ℕ} (hn : 64 ≤ n) (he : Even n) (z : ℕ) :
      0 < sieveVolume n z := by
    have hP : (Icc 2 z).filter Nat.Prime = ErdosStraus.PrimeEstimates.Mertens.primesUpTo z := by
      ext p
      simp only [mem_filter, mem_Icc, ErdosStraus.PrimeEstimates.Mertens.mem_primesUpTo]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.two_le, h.2⟩, h.1⟩⟩
    dsimp only [sieveVolume]
    rw [hP]
    exact GoldbachLateDensity.vol_pos n z hn he

  change ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n →
    ((lateHits n).card : ℝ) ≤ sieveVolume n (cubeCutoff n) - sieveVolume n n.sqrt +
      sieveVolume n n.sqrt / 2
  obtain ⟨Nm, hNm⟩ := hmixed
  obtain ⟨Nd, hNd⟩ := hdouble
  obtain ⟨Nr, hr64, hr⟩ := Conjectures.Goldbach.FareyCubeSqrtDensityRatio (1/100) (by norm_num)
  refine ⟨max Nr (max Nm Nd), hr64.trans (le_max_left _ _), ?_⟩
  intro n hn he
  have hnr := (le_max_left Nr (max Nm Nd)).trans hn
  have hnm := ((le_max_left Nm Nd).trans (le_max_right Nr (max Nm Nd))).trans hn
  have hnd := ((le_max_right Nm Nd).trans (le_max_right Nr (max Nm Nd))).trans hn
  have hn64 := hr64.trans hnr
  have hcount : ((lateHits n).card : ℝ) ≤ 2 * (mixedCount n : ℝ) + doubleCount n := by
    exact_mod_cast card_lateHits_le n hn64
  have hm : (mixedCount n : ℝ) ≤ (16/25 : ℝ) * sieveVolume n n.sqrt := hNm n hnm he
  have hd : (doubleCount n : ℝ) ≤ (23/50 : ℝ) * sieveVolume n n.sqrt := hNd n hnd he
  have hratio : |sieveVolume n (cubeCutoff n) / sieveVolume n n.sqrt - 9/4| ≤ 1/100 :=
    hr n hnr he
  have hlower : (56/25 : ℝ) ≤ sieveVolume n (cubeCutoff n) / sieveVolume n n.sqrt := by
    linarith only [(abs_le.mp hratio).1]
  have hv := (le_div_iff₀ (sieveVolume_pos hn64 he _)).mp hlower
  linarith only [hcount, hm, hd, hv]
