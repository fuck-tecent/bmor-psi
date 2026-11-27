import Mathlib

/-!
# PREPUB goldbach: `L-goldbach-dyadic-sum-avoiding-mask`

New route · Odd-character interference · OC-0107: a positive-density periodic support whose
pairwise sums avoid every power of two.

Pick a prime `s > max W 5`, put `L = 2^(s-3)`, `M = 2^s - 1 = 8L - 1` and
`S = Finset.Ico (3L) (4L)`.  Then `S ⊆ Finset.range M`, `S.card = L` and `M ≤ 8 * S.card`.
Because `2^s ≡ 1 [MOD M]`, the doubling orbit folds back with period `s`, so every power of two
has residue `≤ 2^(s-1) = 4L`, while sums of two elements of `S` lie in `[6L, 8L-2] ⊂ [0, M)`.
Hence no sum meets a power-of-two residue.  Coprimality: an odd prime `p` dividing `M` has
`orderOf (2 : ZMod p) ∣ s` and `∣ p - 1`; as `s` is prime and `p - 1 < p ≤ W < s` the order is
forced to be `1`, i.e. `2 ≡ 1 [MOD p]`, impossible.  Self-contained, Mathlib only.
-/

namespace Conjectures.Goldbach.DyadicSumAvoidingMask_aux

private theorem coprime_mersenne {W s : ℕ} (hW : 0 < W)
    (hsprime : Nat.Prime s) (hWs : W < s) :
    Nat.Coprime W (2 ^ s - 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpW hpM
  have hpWs : p ≤ W := Nat.le_of_dvd hW hpW
  have hps : p < s := lt_of_le_of_lt hpWs hWs
  have hspos : 0 < s := hsprime.pos
  have hp2le : 2 ≤ p := hp.two_le
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    have hsone : 1 ≤ s := hspos
    have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hsone, pow_succ]
    rw [hpow, Nat.mul_comm] at hpM
    exact Nat.two_not_dvd_two_mul_sub_one (Nat.two_pow_pos (s - 1)) hpM
  have hp2lt : 2 < p := by omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)
  letI : Fact p.Prime := ⟨hp⟩
  have hz : ((2 ^ s - 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (2 ^ s - 1) p).mpr hpM
  have hpow : (2 : ZMod p) ^ s = 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  have hordS : orderOf (2 : ZMod p) ∣ s :=
    orderOf_dvd_of_pow_eq_one hpow
  have hordP : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one htwo
  rcases hsprime.eq_one_or_self_of_dvd _ hordS with hord | hord
  · have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp hord
    have h21' : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h21
    have hmod : 2 % p = 1 % p :=
      (ZMod.natCast_eq_natCast_iff 2 1 p).mp h21'
    rw [Nat.mod_eq_of_lt hp2lt,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod
    omega
  · have hordP' : s ∣ p - 1 := by
      rw [← hord]
      exact hordP
    have hle : s ≤ p - 1 := Nat.le_of_dvd (by omega) hordP'
    omega

private theorem power_residue_bound {s k : ℕ} (hs : 5 < s) :
    (2 ^ k) % (2 ^ s - 1) ≤ 2 ^ (s - 1) := by
  let M := 2 ^ s - 1
  have hspos : 0 < s := by omega
  have hMpos : 0 < M := by
    dsimp [M]
    have hpow : 1 < 2 ^ s := by
      calc
        1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hbase : 2 ^ s ≡ 1 [MOD M] := by
    show (2 ^ s) % M = 1 % M
    have hsum : 2 ^ s = M + 1 := by dsimp [M]; omega
    rw [hsum, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  have hdecomp : 2 ^ k = (2 ^ s) ^ (k / s) * 2 ^ (k % s) := by
    calc
      2 ^ k = 2 ^ (s * (k / s) + k % s) := by rw [Nat.div_add_mod]
      _ = 2 ^ (s * (k / s)) * 2 ^ (k % s) := by rw [pow_add]
      _ = (2 ^ s) ^ (k / s) * 2 ^ (k % s) := by rw [pow_mul]
  have hmod : 2 ^ k ≡ 2 ^ (k % s) [MOD M] := by
    rw [hdecomp]
    simpa using Nat.ModEq.mul_right (2 ^ (k % s)) (Nat.ModEq.pow (k / s) hbase)
  have hrlt : k % s < s := Nat.mod_lt _ hspos
  have hrle : k % s ≤ s - 1 := by omega
  have hpowle : 2 ^ (k % s) ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by omega) hrle
  have hbound : 2 ^ (s - 1) < M := by
    dsimp [M]
    have hsone : 1 ≤ s := by omega
    have hhalf : 2 ^ (s - 1) * 2 = 2 ^ s := by
      conv_rhs => rw [← Nat.sub_add_cancel hsone, pow_succ]
    have hpos : 0 < 2 ^ (s - 1) := Nat.two_pow_pos _
    have h2 : 2 ≤ 2 ^ (s - 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  exact (Nat.mod_eq_of_modEq hmod (lt_of_le_of_lt hpowle hbound)).trans_le hpowle

end Conjectures.Goldbach.DyadicSumAvoidingMask_aux

theorem Conjectures.Goldbach.DyadicSumAvoidingMask :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a+b)%M ≠ (2^k)%M := by
  intro W hW
  obtain ⟨s, hsle, hsprime⟩ := Nat.exists_infinite_primes (max W 5 + 1)
  have hsW : W < s := by omega
  have hs5 : 5 < s := by omega
  let L := 2 ^ (s - 3)
  let M := 2 ^ s - 1
  let S := Finset.Ico (3 * L) (4 * L)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.two_pow_pos _
  have hsdecomp : s = (s - 3) + 3 := by omega
  have hpow : 2 ^ s = 8 * L := by
    dsimp [L]
    rw [hsdecomp, pow_add]
    norm_num [Nat.mul_comm]
  have hM8 : M = 8 * L - 1 := by
    dsimp [M]
    rw [hpow]
  have hMone : 1 < M := by
    rw [hM8]
    omega
  have hcop : Nat.Coprime W M := by
    dsimp [M]
    exact Conjectures.Goldbach.DyadicSumAvoidingMask_aux.coprime_mersenne hW hsprime hsW
  refine ⟨M, hMone, hcop, S, ?_, ?_, ?_⟩
  · intro a ha
    have ha' := Finset.mem_Ico.mp ha
    apply Finset.mem_range.mpr
    rw [hM8]
    omega
  · have hcard : S.card = L := by
      dsimp [S]
      rw [Nat.card_Ico]
      omega
    rw [hcard, hM8]
    omega
  · intro a b k ha hb
    have ha' := Finset.mem_Ico.mp ha
    have hb' := Finset.mem_Ico.mp hb
    have hsumlt : a + b < M := by
      rw [hM8]
      omega
    have hfour : 2 ^ (s - 1) = 4 * L := by
      dsimp [L]
      rw [show s - 1 = (s - 3) + 2 by omega, pow_add]
      norm_num [Nat.mul_comm]
    have horbit : (2 ^ k) % M ≤ 4 * L := by
      calc
        (2 ^ k) % M = (2 ^ k) % (2 ^ s - 1) := by rfl
        _ ≤ 2 ^ (s - 1) :=
          Conjectures.Goldbach.DyadicSumAvoidingMask_aux.power_residue_bound hs5
        _ = 4 * L := hfour
    rw [Nat.mod_eq_of_lt hsumlt]
    intro heq
    omega

