import Mathlib

/-!
# PREPUB goldbach gap: `L-goldbach-farey-sieve-terminal-floor`

On the Farey middle third the normalized sieve mass `V n z` dominates `(2/3)·|I|·M(z)²`.
The proof splits the prime factors `p ≤ √n` into those dividing `n` (local factor
`1 - 1/p`) and those not dividing `n` (local factor `(1 - 1/p)²/(1 - 2/p)`), then bounds

* `∏_{p ∣ n, p ≤ √n} (1 - 1/p) ≤ 1/2` (the prime `2` divides the even number `n`),
* `∏_{p ≤ √n, p ∤ n} (1 - 1/p)²/(1 - 2/p) ≤ 2` (a Wallis-type telescoping product),
* `∏_{p ∣ n, p > √n} (1 - 1/p) ≥ 4/5` (at most one such prime, and it is at least `5`).
-/


open scoped BigOperators
open Finset

namespace PEqualNP.Outside

/-- The Wallis-type factor `m²/((m-1)(m+1)) = 1 + 1/(m²-1)`. -/
noncomputable def wallisFac (m : ℕ) : ℝ := (m:ℝ)^2 / (((m:ℝ)-1)*((m:ℝ)+1))

/-- Wallis-type telescoping product: `∏_{m=2}^{M} wallisFac m = 2M/(M+1)`. -/
theorem wallis_telescope : ∀ M : ℕ, 1 ≤ M →
    ∏ m ∈ Finset.Icc 2 M, wallisFac m = 2*(M:ℝ)/((M:ℝ)+1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => norm_num [wallisFac]
  | succ M hM ih =>
      rw [Finset.prod_Icc_succ_top (f := wallisFac) (by omega : 2 ≤ M + 1)]
      rw [ih]
      have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      have h1 : (M:ℝ) + 1 ≠ 0 := by positivity
      have h2 : (M:ℝ) + 2 ≠ 0 := by positivity
      simp only [wallisFac]
      push_cast
      field_simp [hM0, h1, h2]
      ring

/- PREPUB frozen statement `L-goldbach-farey-sieve-terminal-floor`. -/
set_option maxHeartbeats 1000000 in
theorem L_goldbach_farey_sieve_terminal_floor :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹);
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    ∀ n : ℕ, 12 ≤ n → Even n → (2/3:ℝ)*((I n).card:ℝ)*(M (Nat.sqrt n))^2 ≤ V n (Nat.sqrt n) := by
  dsimp only
  classical
  intro n hn hEven
  set z : ℕ := Nat.sqrt n with hz
  set Pz : Finset ℕ := (Finset.Icc 2 z).filter Nat.Prime with hPz
  set Sz : Finset ℕ := Pz.filter (fun p => p ∣ n) with hSz
  set Tz : Finset ℕ := Pz.filter (fun p => ¬ p ∣ n) with hTz
  set Iz : Finset ℕ := Finset.Icc ((n+2)/3) ((2*n)/3) with hIz
  set Es : Finset ℕ := n.primeFactors.filter (fun p => z < p) with hEs
  set A : ℝ := ∏ p ∈ Sz, (1 - (p:ℝ)⁻¹) with hA
  set B : ℝ := ∏ p ∈ Tz, (1 - (p:ℝ)⁻¹) with hB
  set Tp : ℝ := ∏ p ∈ Tz, (1 - 2/(p:ℝ)) with hTp
  set E : ℝ := ∏ p ∈ Es, (1 - (p:ℝ)⁻¹) with hE
  have hn0 : n ≠ 0 := by omega
  have hz3 : 3 ≤ z := by
    rw [hz, Nat.le_sqrt']
    omega
  have hz_sq : z ^ 2 ≤ n := by rw [hz]; exact Nat.sqrt_le' n
  have hz_succ_sq : n < (z + 1) ^ 2 := by rw [hz]; exact Nat.lt_succ_sqrt' n
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp hEven
  -- |I| > 0
  have hIfact : Iz.card = (2*n)/3 + 1 - ((n+2)/3) := by rw [hIz]; exact Nat.card_Icc _ _
  have hIpos : (0:ℝ) < (Iz.card:ℝ) := by
    have hle : ((n+2)/3) ≤ ((2*n)/3) := by
      apply Nat.div_le_div_right; omega
    have hpos : 0 < Iz.card := by rw [hIfact]; omega
    exact_mod_cast hpos
  -- membership characterisations
  have hmemP : ∀ p : ℕ, p ∈ Pz ↔ p.Prime ∧ p ≤ z := by
    intro p
    rw [hPz, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hpz⟩, hpp⟩; exact ⟨hpp, hpz⟩
    · rintro ⟨hpp, hpz⟩; exact ⟨⟨hpp.two_le, hpz⟩, hpp⟩
  have hmemS : ∀ p : ℕ, p ∈ Sz ↔ p.Prime ∧ p ∣ n ∧ p ≤ z := by
    intro p
    rw [hSz, Finset.mem_filter, hmemP]
    constructor
    · rintro ⟨⟨hpp, hpz⟩, hdvd⟩; exact ⟨hpp, hdvd, hpz⟩
    · rintro ⟨hpp, hdvd, hpz⟩; exact ⟨⟨hpp, hpz⟩, hdvd⟩
  have hmemT : ∀ p : ℕ, p ∈ Tz ↔ p.Prime ∧ ¬ p ∣ n ∧ p ≤ z := by
    intro p
    rw [hTz, Finset.mem_filter, hmemP]
    constructor
    · rintro ⟨⟨hpp, hpz⟩, hnd⟩; exact ⟨hpp, hnd, hpz⟩
    · rintro ⟨hpp, hnd, hpz⟩; exact ⟨⟨hpp, hpz⟩, hnd⟩
  have hmemE : ∀ p : ℕ, p ∈ Es ↔ p.Prime ∧ p ∣ n ∧ z < p := by
    intro p
    rw [hEs, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpp, hdvd, -⟩, hzp⟩; exact ⟨hpp, hdvd, hzp⟩
    · rintro ⟨hpp, hdvd, hzp⟩; exact ⟨⟨hpp, hdvd, hn0⟩, hzp⟩
  have hdisj : Disjoint Sz Tz := by
    rw [hSz, hTz]
    exact Finset.disjoint_filter_filter_not _ _ _
  have hPsplit : Pz = Sz ∪ Tz := by
    rw [hSz, hTz]
    exact (Finset.filter_union_filter_not_eq (p := fun p => p ∣ n) Pz).symm
  -- `p ∈ Tz` is odd and at least 3
  have hT_three : ∀ p ∈ Tz, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := ((hmemT p).mp hp).1
    have hnd : ¬ p ∣ n := ((hmemT p).mp hp).2.1
    have hp2 : 2 ≤ p := hpp.two_le
    have hne2 : p ≠ 2 := by intro h; exact hnd (h ▸ h2dvd)
    have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hne2
    omega
  -- `Tp ≥ 0`
  have hTp_nonneg : 0 ≤ Tp := by
    rw [hTp]
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : 3 ≤ p := hT_three p hp
    have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hpos : (0:ℝ) < (p:ℝ) := by linarith
    rw [sub_nonneg, div_le_one hpos]
    linarith
  -- the Wallis-type bound: `∏ (1-1/p)²/(1-2/p) ≤ 2`
  have hQ : (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ)))) ≤ 2 := by
    have hfac : ∀ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ))) = wallisFac (p - 1) := by
      intro p hp
      have hp3 : 3 ≤ p := hT_three p hp
      have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hp0
      have hp2a : (p:ℝ) - 2 ≠ 0 := by intro h; linarith
      have hp2b : (-2 + (p:ℝ)) ≠ 0 := by intro h; linarith
      have hA1 : (p:ℝ) - 1 - 1 ≠ 0 := by intro h; linarith
      have hA2 : (p:ℝ) - 1 + 1 ≠ 0 := by intro h; linarith
      have hden : (1:ℝ) - 2/(p:ℝ) ≠ 0 := by
        have hlt : (2:ℝ)/(p:ℝ) < 1 := by
          rw [div_lt_one hp0]; linarith
        linarith
      have h1 : (((p - 1 : ℕ)) : ℝ) = (p:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
      simp only [wallisFac]
      rw [h1]
      field_simp
      ring
    have hstep : (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ))))
        = ∏ p ∈ Tz, wallisFac (p - 1) := Finset.prod_congr rfl hfac
    rw [hstep]
    have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑Tz : Set ℕ) := by
      intro a ha b hb hab
      have ha3 : 3 ≤ a := hT_three a ha
      have hb3 : 3 ≤ b := hT_three b hb
      have hab' : a - 1 = b - 1 := hab
      omega
    have hsubimg : (Tz.image (fun p => p - 1)) ⊆ Finset.Icc 2 (z - 1) := by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      have hp3 : 3 ≤ p := hT_three p hp
      have hpz : p ≤ z := ((hmemT p).mp hp).2.2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfac1 : ∀ m ∈ Finset.Icc 2 (z - 1), (1:ℝ) ≤ wallisFac m := by
      intro m hm
      obtain ⟨hm2, -⟩ := Finset.mem_Icc.mp hm
      have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      have hpos : (0:ℝ) < ((m:ℝ)-1)*((m:ℝ)+1) := by nlinarith
      simp only [wallisFac]
      rw [le_div_iff₀ hpos]
      nlinarith
    have hfac0 : ∀ m ∈ Finset.Icc 2 (z - 1), (0:ℝ) ≤ wallisFac m := by
      intro m hm
      obtain ⟨hm2, -⟩ := Finset.mem_Icc.mp hm
      have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      have hpos : (0:ℝ) < ((m:ℝ)-1)*((m:ℝ)+1) := by nlinarith
      simp only [wallisFac]
      exact div_nonneg (sq_nonneg _) hpos.le
    calc ∏ p ∈ Tz, wallisFac (p - 1)
        = ∏ m ∈ Tz.image (fun p => p - 1), wallisFac m :=
          (Finset.prod_image (f := wallisFac) (g := fun p : ℕ => p - 1) hinj).symm
      _ ≤ ∏ m ∈ Finset.Icc 2 (z - 1), wallisFac m := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ hsubimg
          · intro m hm
            exact hfac0 m (hsubimg hm)
          · intro m hm _
            exact hfac1 m hm
      _ = 2*(((z - 1 : ℕ)):ℝ)/((((z - 1 : ℕ)):ℝ)+1) := wallis_telescope (z - 1) (by omega)
      _ ≤ 2 := by
          have hz1 : (1:ℝ) ≤ (((z - 1 : ℕ)):ℝ) := by exact_mod_cast (by omega : 1 ≤ z - 1)
          have hden : (0:ℝ) < (((z - 1 : ℕ)):ℝ) + 1 := by linarith
          rw [div_le_iff₀ hden]
          nlinarith
  have hB2 : B ^ 2 ≤ 2 * Tp := by
    have heq : B ^ 2 = (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ)))) * Tp := by
      rw [hB, hTp, sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp3 : 3 ≤ p := hT_three p hp
      have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      have hden : (1:ℝ) - 2/(p:ℝ) ≠ 0 := by
        have hlt : (2:ℝ)/(p:ℝ) < 1 := by
          rw [div_lt_one hp0]; linarith
        linarith
      have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hp0
      have hp2a : (p:ℝ) - 2 ≠ 0 := by intro h; linarith
      have hp2b : (-2 + (p:ℝ)) ≠ 0 := by intro h; linarith
      have hA1 : (p:ℝ) - 1 - 1 ≠ 0 := by intro h; linarith
      have hA2 : (p:ℝ) - 1 + 1 ≠ 0 := by intro h; linarith
      field_simp
    rw [heq]
    nlinarith [hQ, hTp_nonneg]
  -- `A ≤ 1/2`: the prime `2` divides the even number `n`
  have h2S : (2:ℕ) ∈ Sz := (hmemS 2).mpr ⟨by norm_num, h2dvd, by omega⟩
  have hA2 : A ≤ 1/2 := by
    rw [hA]
    have heq : (∏ p ∈ Sz, (1 - (p:ℝ)⁻¹))
        = (∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹)) * (1 - (2:ℝ)⁻¹) :=
      Finset.prod_eq_prod_sdiff_singleton_mul h2S _
    rw [heq]
    have hrest_nonneg : 0 ≤ ∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hp
      have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
      have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
      have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
      linarith
    have hrest_le : (∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
        linarith
      · intro p hp
        have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        have hinv : 0 ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr hp1.le
        linarith
    have hconst : (1 - (2:ℝ)⁻¹) = 1/2 := by norm_num
    rw [hconst]
    nlinarith [hrest_nonneg, hrest_le]
  -- `E ≥ 4/5`: at most one prime factor of `n` exceeds `√n`, and it is at least 5
  have hEs_card : Es.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hne
    have hpp : p.Prime := ((hmemE p).mp hp).1
    have hqp : q.Prime := ((hmemE q).mp hq).1
    have hpd : p ∣ n := ((hmemE p).mp hp).2.1
    have hqd : q ∣ n := ((hmemE q).mp hq).2.1
    have hzp : z < p := ((hmemE p).mp hp).2.2
    have hzq : z < q := ((hmemE q).mp hq).2.2
    have hcop : p.Coprime q := (Nat.coprime_primes hpp hqp).mpr hne
    have hpqdvd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hpqle : p * q ≤ n := Nat.le_of_dvd (by omega) hpqdvd
    have hpq_ge : (z + 1) ^ 2 ≤ p * q := by
      rw [pow_two]
      apply Nat.mul_le_mul <;> omega
    omega
  have hE_ge : (4/5:ℝ) ≤ E := by
    rw [hE]
    have hfac : ∀ p ∈ Es, (4/5:ℝ) ≤ (1 - (p:ℝ)⁻¹) := by
      intro p hp
      have hpp : p.Prime := ((hmemE p).mp hp).1
      have hzp : z < p := ((hmemE p).mp hp).2.2
      have hne2 : p ≠ 2 := by omega
      have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hne2
      have hp5 : 5 ≤ p := by omega
      have hp5r : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp5
      have hinv : (p:ℝ)⁻¹ ≤ 1/5 := by
        have h5 : ((5:ℝ))⁻¹ = 1/5 := by norm_num
        rw [← h5]
        exact (inv_le_inv₀ (by linarith : (0:ℝ) < (p:ℝ)) (by norm_num : (0:ℝ) < 5)).mpr hp5r
      linarith
    have hc : Es.card = 0 ∨ Es.card = 1 := by omega
    rcases hc with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]
      norm_num
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      rw [hp, Finset.prod_singleton]
      exact hfac p (by rw [hp]; exact Finset.mem_singleton_self p)
  -- the totient factorisation `φ(n)/n = A · E`
  have hphi : ((n.totient:ℝ)/(n:ℝ)) = A * E := by
    have htot : ((n.totient:ℝ)/(n:ℝ)) = ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹) := by
      have hcast : (n.totient:ℝ) * (∏ p ∈ n.primeFactors, (p:ℝ))
          = (n:ℝ) * (∏ p ∈ n.primeFactors, ((p:ℝ) - 1)) := by
        have hnat := Nat.totient_mul_prod_primeFactors n
        have h1 := congrArg (fun m : ℕ => (m:ℝ)) hnat
        push_cast at h1
        have hprod : (∏ p ∈ n.primeFactors, (((p - 1 : ℕ)) : ℝ))
            = ∏ p ∈ n.primeFactors, ((p:ℝ) - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)), Nat.cast_one]
        rw [hprod] at h1
        exact h1
      have hn0' : (n:ℝ) ≠ 0 := by positivity
      have hPne : (∏ p ∈ n.primeFactors, (p:ℝ)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro p hp
        have hpos : (0:ℝ) < (p:ℝ) := by
          have := (Nat.prime_of_mem_primeFactors hp).pos
          exact_mod_cast this
        linarith
      have hQP : ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹)
          = (∏ p ∈ n.primeFactors, ((p:ℝ) - 1)) / (∏ p ∈ n.primeFactors, (p:ℝ)) := by
        have hfac : ∀ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹) = ((p:ℝ) - 1) / (p:ℝ) := by
          intro p hp
          have hpos : (0:ℝ) < (p:ℝ) := by
            have := (Nat.prime_of_mem_primeFactors hp).pos
            exact_mod_cast this
          have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hpos
          field_simp
        rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib]
      rw [hQP, div_eq_div_iff hn0' hPne]
      simpa [mul_comm] using hcast
    rw [htot, hA, hE, hEs]
    have hprod := Finset.prod_filter_mul_prod_filter_not (s := n.primeFactors)
      (p := fun p => p ≤ z) (f := fun p => (1 - (p:ℝ)⁻¹))
    have hnotle : n.primeFactors.filter (fun p => ¬ p ≤ z)
        = n.primeFactors.filter (fun p => z < p) := by
      apply Finset.filter_congr
      intro p _
      exact Nat.not_le
    rw [← hprod, hnotle]
    have hSz_eq : n.primeFactors.filter (fun p => p ≤ z) = Sz := by
      ext p
      rw [Finset.mem_filter, hmemS]
      constructor
      · rintro ⟨hp, hpz⟩
        obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
        exact ⟨hpp, hdvd, hpz⟩
      · rintro ⟨hpp, hdvd, hpz⟩
        exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hn0⟩, hpz⟩
    rw [hSz_eq]
  -- `A ≥ 0`
  have hA0 : 0 ≤ A := by
    rw [hA]
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := ((hmemS p).mp hp).1
    have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
    linarith
  -- assembly
  have hMz : (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹)) = A * B := by
    rw [hPsplit, Finset.prod_union hdisj, hA, hB]
  have hcore : (2/3:ℝ) * A^2 * B^2 ≤ A * E * Tp := by
    have h1 : (2/3:ℝ) * A^2 * B^2 ≤ (4/3) * A^2 * Tp := by
      have h := mul_le_mul_of_nonneg_left hB2 (by positivity : (0:ℝ) ≤ (2/3) * A^2)
      nlinarith [h]
    have h2 : (4/3:ℝ) * A^2 * Tp ≤ (2/3) * A * Tp := by
      have hAA : A^2 ≤ A * (1/2) := by nlinarith [hA0, hA2]
      have h := mul_le_mul_of_nonneg_right hAA hTp_nonneg
      nlinarith [h]
    have h3 : (2/3:ℝ) * A * Tp ≤ A * E * Tp := by
      have hAT : 0 ≤ A * Tp := mul_nonneg hA0 hTp_nonneg
      have h := mul_le_mul_of_nonneg_right hE_ge hAT
      nlinarith [h]
    linarith
  have hmain : (2/3:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2
      ≤ ((n.totient:ℝ)/(n:ℝ)) * (∏ p ∈ Tz, (1 - 2/(p:ℝ))) := by
    rw [hMz, hphi]
    calc (2/3:ℝ) * (A * B)^2 = (2/3:ℝ) * A^2 * B^2 := by ring
      _ ≤ A * E * Tp := hcore
      _ = (A * E) * Tp := by ring
  calc (2/3:ℝ) * (Iz.card:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2
      = (Iz.card:ℝ) * ((2/3:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2) := by ring
    _ ≤ (Iz.card:ℝ) * (((n.totient:ℝ)/(n:ℝ)) * (∏ p ∈ Tz, (1 - 2/(p:ℝ)))) :=
        mul_le_mul_of_nonneg_left hmain hIpos.le
    _ = (Iz.card:ℝ) * (n.totient:ℝ) / (n:ℝ) * (∏ p ∈ Tz, (1 - 2/(p:ℝ))) := by ring

end PEqualNP.Outside


/-! ## Platform module-name alias (the live guard requires the theorem named `<module>`) -/

/- PREPUB frozen statement `L-goldbach-farey-sieve-terminal-floor`, under its platform
module name. -/
set_option maxHeartbeats 1000000 in
theorem Conjectures.Goldbach.FareySieveTerminalFloor :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹);
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    ∀ n : ℕ, 12 ≤ n → Even n → (2/3:ℝ)*((I n).card:ℝ)*(M (Nat.sqrt n))^2 ≤ V n (Nat.sqrt n) :=
  PEqualNP.Outside.L_goldbach_farey_sieve_terminal_floor
