import Mathlib

namespace Conjectures.Goldbach.DyadicProgressionCountermodel_aux

def MaskAssumption : Prop :=
  ∀ W : ℕ, 0 < W →
    ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧
        ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a + b) % M ≠ (2 ^ k) % M

noncomputable def maskedWeight (M : ℕ) (S : Finset ℕ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % M ∈ S then ((M : ℝ) / (S.card : ℝ)) * u n else 0

private theorem value_periodic {W : ℕ} {u : ℕ → ℝ}
    (hu : ∀ x, u (x + W) = u x) (x j : ℕ) :
    u (x + j * W) = u x := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        u (x + (j + 1) * W) = u ((x + j * W) + W) := by
          rw [Nat.succ_mul, Nat.add_assoc]
        _ = u (x + j * W) := hu _
        _ = u x := ih

private theorem mask_periodic (M W x : ℕ) (S : Finset ℕ) :
    Function.Periodic (fun j => (x + j * W) % M ∈ S) M := by
  intro j
  simp only
  congr 1
  have hinner : ((j + M) * W) % M = (j * W) % M := by
    rw [Nat.add_mul]
    exact Nat.add_mul_mod_self_left (j * W) M W
  calc
    (x + (j + M) * W) % M = (x % M + ((j + M) * W) % M) % M :=
      Nat.add_mod _ _ _
    _ = (x % M + (j * W) % M) % M := by rw [hinner]
    _ = (x + j * W) % M := (Nat.add_mod _ _ _).symm

private theorem residue_injective {M W x j l : ℕ}
    (hcop : Nat.Coprime W M) (hj : j < M) (hl : l < M)
    (heq : (x + j * W) % M = (x + l * W) % M) :
    j = l := by
  have hxy : j * W + x ≡ l * W + x [MOD M] := by
    change (j * W + x) % M = (l * W + x) % M
    simpa only [Nat.add_comm] using heq
  have hmul : j * W ≡ l * W [MOD M] :=
    Nat.ModEq.add_right_cancel' x hxy
  have hmod : j ≡ l [MOD M] :=
    Nat.ModEq.cancel_right_of_coprime hcop.symm hmul
  exact hmod.eq_of_lt_of_lt hj hl

private theorem residue_surjective {M W x s : ℕ}
    (hM : 0 < M) (hcop : Nat.Coprime W M) (hs : s < M) :
    ∃ j < M, (x + j * W) % M = s := by
  let r := s + M - x % M
  obtain ⟨j, hj, hjmod⟩ :=
    Nat.exists_mul_mod_eq_of_coprime r hcop hM.ne'
  refine ⟨j, hj, ?_⟩
  have hx : x % M < M := Nat.mod_lt x hM
  have hsum : x % M + r = s + M := by
    dsimp [r]
    omega
  calc
    (x + j * W) % M = (x % M + (j * W) % M) % M := Nat.add_mod _ _ _
    _ = (x % M + r % M) % M := by rw [Nat.mul_comm j W, hjmod]
    _ = (x % M + r) % M := by simp only [Nat.add_mod, Nat.mod_mod]
    _ = (s + M) % M := by rw [hsum]
    _ = s % M := Nat.add_mod_right _ _
    _ = s := Nat.mod_eq_of_lt hs

private theorem full_period_card {M W x : ℕ} (S : Finset ℕ)
    (hM : 0 < M) (hcop : Nat.Coprime W M) (hS : S ⊆ Finset.range M) :
    ((Finset.range M).filter (fun j => (x + j * W) % M ∈ S)).card = S.card := by
  classical
  apply Finset.card_bij (fun j _ => (x + j * W) % M)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro j hj l hl heq
    exact residue_injective hcop
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hl).1) heq
  · intro s hs
    have hsM : s < M := Finset.mem_range.mp (hS hs)
    obtain ⟨j, hj, hjs⟩ := residue_surjective hM hcop hsM
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ?_⟩, hjs⟩
    simpa [hjs] using hs

private theorem periodic_count_mul {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (q : ℕ) :
    Nat.count p (q * d) = q * Nat.count p d := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Nat.count_add']
      have hshift : (fun k => p (k + d)) = p := by
        funext k
        exact hp k
      simp only [hshift, ih]
      ring

private theorem periodic_count_div_mod {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (N : ℕ) :
    Nat.count p N = (N / d) * Nat.count p d + Nat.count p (N % d) := by
  conv_lhs => rw [← Nat.mod_add_div N d]
  rw [Nat.count_add']
  have hshift : (fun k => p (k + d * (N / d))) = p := by
    funext k
    simpa [Nat.mul_comm] using hp.nsmul (N / d) k
  simp only [hshift]
  rw [Nat.mul_comm d, periodic_count_mul hp]
  ring

private theorem indicator_sum (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (∑ j ∈ Finset.range N, if p j then (1 : ℝ) else 0) = Nat.count p N := by
  rw [Finset.sum_boole, Nat.count_eq_card_filter_range]

private theorem maskedWeight_bounds {M : ℕ} {S : Finset ℕ} {u : ℕ → ℝ}
    (hM : 0 < M) (hcard : M ≤ 8 * S.card) (hu : ∀ x, 0 ≤ u x) (n : ℕ) :
    0 ≤ maskedWeight M S u n ∧ maskedWeight M S u n ≤ 8 * u n := by
  have hScard : 0 < S.card := by omega
  have hScardR : (0 : ℝ) < S.card := by exact_mod_cast hScard
  have hcardR : (M : ℝ) ≤ 8 * S.card := by exact_mod_cast hcard
  have hscale : (M : ℝ) / S.card ≤ 8 := by
    exact (div_le_iff₀ hScardR).2 hcardR
  constructor
  · by_cases hn : n % M ∈ S
    · simp only [maskedWeight, hn, if_true]
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hu n)
    · simp [maskedWeight, hn]
  · by_cases hn : n % M ∈ S
    · simp only [maskedWeight, hn, if_true]
      exact mul_le_mul_of_nonneg_right hscale (hu n)
    · simp only [maskedWeight, hn, if_false]
      exact mul_nonneg (by norm_num) (hu n)

private theorem maskedWeight_dyadic {M : ℕ} {S : Finset ℕ} {u : ℕ → ℝ}
    (havoid : ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a + b) % M ≠ (2 ^ k) % M)
    (a b k : ℕ) (hsum : a + b = 2 ^ k) :
    maskedWeight M S u a * maskedWeight M S u b = 0 := by
  by_cases ha : a % M ∈ S
  · by_cases hb : b % M ∈ S
    · exfalso
      apply havoid (a % M) (b % M) k ha hb
      calc
        (a % M + b % M) % M = (a + b) % M := (Nat.add_mod _ _ _).symm
        _ = (2 ^ k) % M := by rw [hsum]
    · simp [maskedWeight, hb]
  · simp [maskedWeight, ha]

private theorem maskedWeight_sum_bound
    {M W : ℕ} (hM : 0 < M) (hcop : Nat.Coprime W M)
    {S : Finset ℕ} (hS : S ⊆ Finset.range M) (hScard : 0 < S.card)
    {u : ℕ → ℝ} (hu : ∀ x, 0 ≤ u x)
    (hper : ∀ x, u (x + W) = u x) (x H : ℕ) :
    |(∑ j ∈ Finset.range H, maskedWeight M S u (x + j * W)) -
        (H : ℝ) * u x| ≤ (M : ℝ) * u x := by
  classical
  let p : ℕ → Prop := fun j => (x + j * W) % M ∈ S
  have hp : Function.Periodic p M := by
    exact mask_periodic M W x S
  have hcountM : Nat.count p M = S.card := by
    rw [Nat.count_eq_card_filter_range]
    exact full_period_card S hM hcop hS
  have hcount : Nat.count p H =
      (H / M) * S.card + Nat.count p (H % M) := by
    simpa only [hcountM] using periodic_count_div_mod hp H
  have htail : Nat.count p (H % M) ≤ S.card := by
    calc
      Nat.count p (H % M) ≤ Nat.count p M :=
        Nat.count_monotone p (Nat.mod_lt H hM).le
      _ = S.card := hcountM
  have hsum :
      (∑ j ∈ Finset.range H, maskedWeight M S u (x + j * W)) =
        (Nat.count p H : ℝ) * ((M : ℝ) / S.card) * u x := by
    calc
      (∑ j ∈ Finset.range H, maskedWeight M S u (x + j * W)) =
          ∑ j ∈ Finset.range H, if p j then ((M : ℝ) / S.card) * u x else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [maskedWeight, p, value_periodic hper x j]
      _ = (∑ j ∈ Finset.range H, if p j then (1 : ℝ) else 0) *
          (((M : ℝ) / S.card) * u x) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hjp : p j <;> simp [hjp]
      _ = (Nat.count p H : ℝ) * (((M : ℝ) / S.card) * u x) := by
            rw [indicator_sum]
      _ = (Nat.count p H : ℝ) * ((M : ℝ) / S.card) * u x := by ring
  have hcountR :
      (Nat.count p H : ℝ) =
        (H / M : ℕ) * (S.card : ℝ) + Nat.count p (H % M) := by
    exact_mod_cast hcount
  have hHdecomp : (H : ℝ) = (H / M : ℕ) * (M : ℝ) + (H % M : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' H M).symm
  have hScardR : (0 : ℝ) < S.card := by exact_mod_cast hScard
  have hScardNe : (S.card : ℝ) ≠ 0 := hScardR.ne'
  have htailR : (Nat.count p (H % M) : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast htail
  have hremR : ((H % M : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.mod_lt H hM).le
  have hscaleNonneg : (0 : ℝ) ≤ (M : ℝ) / S.card :=
    div_nonneg (Nat.cast_nonneg _) hScardR.le
  have htailWeight :
      ((M : ℝ) / S.card) * Nat.count p (H % M) ≤ (M : ℝ) := by
    calc
      ((M : ℝ) / S.card) * Nat.count p (H % M) ≤
          ((M : ℝ) / S.card) * S.card :=
        mul_le_mul_of_nonneg_left htailR hscaleNonneg
      _ = (M : ℝ) := by field_simp
  have htailWeightNonneg :
      (0 : ℝ) ≤ ((M : ℝ) / S.card) * Nat.count p (H % M) :=
    mul_nonneg hscaleNonneg (Nat.cast_nonneg _)
  have htailError :
      |((M : ℝ) / S.card) * Nat.count p (H % M) - (H % M : ℕ)| ≤ (M : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  have herr :
      (Nat.count p H : ℝ) * ((M : ℝ) / S.card) * u x - (H : ℝ) * u x =
        (((M : ℝ) / S.card) * Nat.count p (H % M) - (H % M : ℕ)) * u x := by
    rw [hcountR, hHdecomp]
    push_cast
    field_simp [hScardNe]
    <;> ring
  rw [hsum, herr, abs_mul, abs_of_nonneg (hu x)]
  exact mul_le_mul_of_nonneg_right htailError (hu x)

private lemma two_pow_pred_cycle (s k : ℕ) (hs : 2 < s) :
    (2 ^ k) % (2 ^ s - 1) = 2 ^ (k % s) := by
  have htwo : 0 < 2 ^ k := pow_pos (by norm_num) _
  have hpowlarge : 2 < 2 ^ s := by
    calc
      2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ s)
  have hM : 0 < 2 ^ s - 1 := by
    omega
  have hM1 : 1 < 2 ^ s - 1 := by omega
  have hr : k % s < s := Nat.mod_lt _ (by omega)
  have hrpow : 2 ^ (k % s) < 2 ^ s - 1 := by
    have hle : k % s + 1 ≤ s := hr
    have hpow : 2 ^ (k % s) * 2 ≤ 2 ^ s := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hle
    have hpowpos : 0 < 2 ^ (k % s) := pow_pos (by norm_num) _
    omega
  calc
    (2 ^ k) % (2 ^ s - 1) = ((2 ^ k - 1 + 1) % (2 ^ s - 1)) := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow k 2 (by norm_num))]
    _ = (((2 ^ k - 1) % (2 ^ s - 1) + 1) % (2 ^ s - 1)) := by
      calc
        ((2 ^ k - 1 + 1) % (2 ^ s - 1)) =
            ((2 ^ k - 1) % (2 ^ s - 1) + 1 % (2 ^ s - 1)) %
              (2 ^ s - 1) := Nat.add_mod _ _ _
        _ = ((2 ^ k - 1) % (2 ^ s - 1) + 1) % (2 ^ s - 1) := by
          rw [Nat.mod_eq_of_lt hM1]
    _ = ((2 ^ (k % s) - 1 + 1) % (2 ^ s - 1)) := by
      rw [Nat.pow_sub_one_mod_pow_sub_one]
    _ = (2 ^ (k % s)) % (2 ^ s - 1) := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow (k % s) 2 (by norm_num))]
    _ = 2 ^ (k % s) := Nat.mod_eq_of_lt hrpow

private theorem mask_exists (W : ℕ) (hW : 0 < W) :
    ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧
        ∀ a b k : ℕ, a ∈ S → b ∈ S →
          (a + b) % M ≠ (2 ^ k) % M := by
  obtain ⟨s, hsle, hsprime⟩ :=
    Nat.exists_infinite_primes (max W 5 + 1)
  have hsW : W < s := by omega
  have hs5 : 5 < s := by omega
  let L : ℕ := 2 ^ (s - 3)
  let M : ℕ := 8 * L - 1
  let S : Finset ℕ :=
    (Finset.range L).map (addLeftEmbedding (3 * L))
  have hLpos : 0 < L := by
    dsimp [L]
    exact pow_pos (by norm_num) _
  have hs3 : 3 ≤ s := by omega
  have hpow : 2 ^ s = 8 * L := by
    calc
      2 ^ s = 2 ^ ((s - 3) + 3) := by rw [Nat.sub_add_cancel hs3]
      _ = 2 ^ (s - 3) * 2 ^ 3 := by rw [pow_add]
      _ = 8 * L := by norm_num [L, Nat.mul_comm]
  have hMeq : M = 2 ^ s - 1 := by
    dsimp [M]
    omega
  have hMgt : 1 < M := by
    dsimp [M]
    omega
  have hModd : Odd M := by
    refine ⟨4 * L - 1, ?_⟩
    dsimp [M]
    omega
  have hcop : Nat.Coprime W M := by
    apply Nat.coprime_of_dvd
    intro p hp hpW hpM
    have hpodd : Odd p := hModd.of_dvd_nat hpM
    have h2p : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
    have hpWle : p ≤ W := Nat.le_of_dvd hW hpW
    have hp1lt : p - 1 < s := by omega
    have hscop : Nat.Coprime s (p - 1) := by
      apply hsprime.coprime_iff_not_dvd.mpr
      exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) hp1lt
    have hfermat : p ∣ 2 ^ (p - 1) - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact Nat.pow_card_sub_one_sub_one_mod_card hp h2p
    have hpdvd : p ∣ 2 ^ (Nat.gcd s (p - 1)) - 1 := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one]
      exact dvd_gcd (hMeq ▸ hpM) hfermat
    have hgcd : Nat.gcd s (p - 1) = 1 := hscop
    have : p ∣ 1 := by
      simpa [hgcd] using hpdvd
    exact hp.not_dvd_one this
  refine ⟨M, hMgt, hcop, S, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_map.mp ha with ⟨j, hj, rfl⟩
    have hjlt : j < L := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    simp only [addLeftEmbedding_apply]
    dsimp [M]
    omega
  · have hcard : S.card = L := by
      dsimp [S]
      simp
    dsimp [M]
    omega
  · intro a b k ha hb
    rcases Finset.mem_map.mp ha with ⟨i, hi, rfl⟩
    rcases Finset.mem_map.mp hb with ⟨j, hj, rfl⟩
    have hilt : i < L := Finset.mem_range.mp hi
    have hjlt : j < L := Finset.mem_range.mp hj
    simp only [addLeftEmbedding_apply] at *
    have hsumlt : (3 * L + i) + (3 * L + j) < M := by
      dsimp [M]
      omega
    have hsumlo : 6 * L ≤ (3 * L + i) + (3 * L + j) := by omega
    have hr : k % s < s := Nat.mod_lt _ (by omega)
    have hpowle : 2 ^ (k % s) ≤ 4 * L := by
      have hle : k % s ≤ s - 1 := by omega
      have hp : 2 ^ (k % s) ≤ 2 ^ (s - 1) :=
        Nat.pow_le_pow_right (by norm_num) hle
      have heq : 2 ^ (s - 1) = 4 * L := by
        calc
          2 ^ (s - 1) = 2 ^ ((s - 3) + 2) := by
            congr 1
            omega
          _ = 2 ^ (s - 3) * 2 ^ 2 := by rw [pow_add]
          _ = 4 * L := by norm_num [L, Nat.mul_comm]
      omega
    intro heqmod
    have hpowmod : (2 ^ k) % M = 2 ^ (k % s) := by
      rw [hMeq]
      exact two_pow_pred_cycle s k (by omega)
    rw [Nat.mod_eq_of_lt hsumlt, hpowmod] at heqmod
    omega

end Conjectures.Goldbach.DyadicProgressionCountermodel_aux

open Conjectures.Goldbach.DyadicProgressionCountermodel_aux

private theorem countermodel_of_mask
    (hmask : MaskAssumption) :
    ∀ W : ℕ, 0 < W → ∀ u : ℕ → ℝ, (∀ x, 0 ≤ u x) →
      (∀ x, u (x + W) = u x) →
      ∃ (f : ℕ → ℝ) (C : ℝ),
        0 < C ∧
        (∀ x, 0 ≤ f x ∧ f x ≤ 8 * u x) ∧
        (∀ x H : ℕ,
          |(∑ j ∈ Finset.range H, f (x + j * W)) - (H : ℝ) * u x| ≤ C * u x) ∧
        ∀ a b k : ℕ, a + b = 2 ^ k → f a * f b = 0 := by
  intro W hW u hu hper
  obtain ⟨M, hM1, hcop, S, hS, hcard, havoid⟩ := hmask W hW
  have hM : 0 < M := by omega
  have hScard : 0 < S.card := by omega
  let f : ℕ → ℝ := maskedWeight M S u
  refine ⟨f, (M : ℝ), ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hM
  · intro x
    simpa only [f] using maskedWeight_bounds hM hcard hu x
  · intro x H
    simpa only [f] using
      maskedWeight_sum_bound hM hcop hS hScard hu hper x H
  · intro a b k hsum
    simpa only [f] using maskedWeight_dyadic havoid a b k hsum

theorem Conjectures.Goldbach.DyadicProgressionCountermodel : ∀ W : ℕ, 0 < W → ∀ u : ℕ → ℝ, (∀ x, 0 ≤ u x) → (∀ x, u (x+W) = u x) → ∃ (f : ℕ → ℝ) (C : ℝ), 0 < C ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 8 * u x) ∧ (∀ x H : ℕ, |(∑ j ∈ Finset.range H, f (x+j*W)) - (H:ℝ)*u x| ≤ C*u x) ∧ ∀ a b k : ℕ, a+b = 2^k → f a * f b = 0 := by
  apply countermodel_of_mask
  intro W hW
  exact mask_exists W hW
