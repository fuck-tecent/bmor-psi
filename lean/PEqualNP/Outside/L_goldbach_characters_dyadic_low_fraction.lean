import Mathlib

private lemma oddCount {n : ℕ} [NeZero n] (hn : 2 < n) :
    2*((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).card = n.totient := by
  classical
  let X := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)
  have hne : (-1 : ZMod n) ≠ 1 := by
    intro h
    rcases ZMod.neg_one_eq_one_iff.mp h with h | h <;> omega
  have hz := DirichletCharacter.sum_characters_eq_zero ℂ hne
  have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n
  have hcard : (Fintype.card (DirichletCharacter ℂ n):ℂ) = (n.totient:ℂ) := by
    exact_mod_cast (Nat.card_eq_fintype_card.symm.trans hc)
  have h : (2:ℂ)*(X.card:ℂ) = (n.totient:ℂ) := by
    calc
      _ = ∑ _χ ∈ X, (2:ℂ) := by simp [mul_comm]
      _ = ∑ χ : DirichletCharacter ℂ n, (1 - χ (-1)) := by
        dsimp only [X]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro χ _
        rcases χ.even_or_odd with he | ho
        · rw [show χ (-1) = 1 from he]
          norm_num
        · rw [show χ (-1) = -1 from ho]
          norm_num
      _ = _ := by rw [Finset.sum_sub_distrib,hz]; simpa using hcard
  change 2 * X.card = n.totient
  exact_mod_cast h

private lemma lowCount :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d : ℕ, d∣n → 2<d → 2*(odd.filter (fun χ => χ.conductor ∣ d)).card = d.totient := by
  intro n _ _ odd d hd hd2
  classical
  let _ : NeZero d := ⟨by omega⟩
  let Y := (Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ (-1) = -1)
  let lift : DirichletCharacter ℂ d ↪ DirichletCharacter ℂ n :=
    ⟨_, DirichletCharacter.changeLevel_injective hd⟩
  have parity (ψ : DirichletCharacter ℂ d) : lift ψ (-1) = ψ (-1) := by
    simpa [lift] using ψ.changeLevel_eq_cast_of_dvd' hd (a := (-1:ℤ)) ⟨-1, 0, by ring⟩
  have bij : odd.filter (fun χ => χ.conductor ∣ d) = Y.map lift := by
    ext χ
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hχ,hcon⟩
      have hf := (χ.mem_conductorSet_iff_conductor_dvd hd).2 hcon
      obtain ⟨_,ψ,rfl⟩ := hf
      refine ⟨ψ,Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,rfl⟩
      exact (parity ψ).symm.trans (Finset.mem_filter.mp hχ).2
    · rintro ⟨ψ,hψ,rfl⟩
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(parity ψ).trans (Finset.mem_filter.mp hψ).2⟩,?_⟩
      change (DirichletCharacter.changeLevel hd ψ).conductor ∣ d
      rw [ψ.conductor_changeLevel hd]
      exact ψ.conductor_dvd_level
  rw [bij, Finset.card_map]
  exact oddCount hd2

theorem PEqualNP.Outside.L_goldbach_characters_dyadic_low_fraction :
    ∀ k : ℕ, 4≤k → let n := 2^k; let X := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); 2^(k/4)*(X.filter (fun χ => χ.conductor^4 ≤ n^3)).card ≤ X.card := by
  intro k hk n X
  let t := 3*k/4
  let d := 2^t
  have ht : 2 ≤ t := by dsimp [t]; omega
  have htk : t ≤ k := by dsimp [t]; omega
  have hd : 2 < d := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).2 (show 1<t by omega)
  have hn : 2 < n := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).2 (show 1<k by omega)
  have hdiv : d ∣ n := Nat.pow_dvd_pow 2 htk
  have hsub : (X.filter (fun χ => χ.conductor^4 ≤ n^3)) ⊆ X.filter (fun χ => χ.conductor ∣ d) := by
    intro χ hχ
    obtain ⟨hx,hsize⟩ := Finset.mem_filter.mp hχ
    obtain ⟨i,_,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 χ.conductor_dvd_level
    change χ.conductor^4 ≤ (2^k)^3 at hsize
    rw [he, ← pow_mul, ← pow_mul, Nat.pow_le_pow_iff_right (by decide : 1<2)] at hsize
    exact Finset.mem_filter.mpr ⟨hx, he ▸ Nat.pow_dvd_pow 2 (show i≤t by dsimp [t]; omega)⟩
  have all : 2*X.card = n.totient := oddCount hn
  have low := lowCount n hn d hdiv hd
  change 2*(X.filter (fun χ => χ.conductor∣d)).card = d.totient at low
  have le := Finset.card_le_card hsub
  have cn : n.totient = 2^(k-1) := by
    change (2^k).totient = _
    simp [Nat.totient_prime_pow Nat.prime_two (by omega : 0<k)]
  have cd : d.totient = 2^(t-1) := by
    change (2^t).totient = _
    simp [Nat.totient_prime_pow Nat.prime_two (by omega : 0<t)]
  rw [cn] at all
  rw [cd] at low
  have hexp : k/4 + (t-1) ≤ k-1 := by dsimp [t]; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<2) hexp
  rw [pow_add, ← low, ← all] at hpow
  nlinarith [Nat.mul_le_mul_left (2^(k/4)) le]
