import Mathlib

private lemma sc_aux (K m : ℕ) (hm2 : 2 ≤ m) (hlo : Nat.sqrt K < m) (hhi : m ≤ K) :
    Nat.Coprime m (((Finset.range (Nat.sqrt K+1)).filter Nat.Prime).prod id) ↔ m.Prime := by
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h
    by_contra hnp
    have hmf : (Nat.minFac m).Prime := Nat.minFac_prime (by omega)
    have hsq : (Nat.minFac m)^2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    have hle : Nat.minFac m ≤ Nat.sqrt K := Nat.le_sqrt'.mpr (le_trans hsq hhi)
    have hmem : Nat.minFac m ∈ (Finset.range (Nat.sqrt K+1)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hmf⟩
    have hc := h _ hmem
    simp only [id] at hc
    exact (Nat.Prime.coprime_iff_not_dvd hmf).mp hc.symm (Nat.minFac_dvd m)
  · intro hp q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    simp only [id]
    rw [Nat.coprime_primes hp hq.2]
    omega

theorem PEqualNP.Outside.L_twin_primes_sifted_correlation :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ X : ℕ, 9 ≤ X → let Q := ((Finset.range (Nat.sqrt (2*X+2)+1)).filter Nat.Prime).prod id; ((w X).filter (fun n => Nat.Coprime n Q ∧ Nat.Coprime (n+2) Q)) = ((w X).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
  dsimp only
  intro X hX
  apply Finset.filter_congr
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  have hsq : Nat.sqrt (2*X+2) < X + 1 := by
    rw [Nat.sqrt_lt']
    nlinarith
  rw [sc_aux (2*X+2) n (by omega) (by omega) (by omega),
    sc_aux (2*X+2) (n+2) (by omega) (by omega) (by omega)]
