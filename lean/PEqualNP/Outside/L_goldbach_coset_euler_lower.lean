import Mathlib

namespace PEqualNP.Outside.CosetEulerLowerAux

def localCount (n q : ℕ) : ℕ :=
  ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n + q - r) % q).Coprime q)).card

open Classical in
noncomputable def zmodSet (n q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter (fun x : ZMod q => IsUnit x ∧ IsUnit ((n : ZMod q) - x))

private theorem mem_zmodSet_iff (n q : ℕ) [NeZero q] (x : ZMod q) :
    x ∈ zmodSet n q ↔ IsUnit x ∧ IsUnit ((n : ZMod q) - x) := by
  classical
  simp [zmodSet]

private theorem pred_iff_zmod (n q r : ℕ) (hr : r < q) :
    (r.Coprime q ∧ ((n + q - r) % q).Coprime q) ↔
      (IsUnit (r : ZMod q) ∧ IsUnit ((n : ZMod q) - (r : ZMod q))) := by
  rw [← ZMod.isUnit_iff_coprime r q, ← ZMod.isUnit_iff_coprime ((n + q - r) % q) q]
  have hcast : (((n + q - r) % q : ℕ) : ZMod q) = (n : ZMod q) - (r : ZMod q) := by
    rw [ZMod.natCast_mod]
    have hle : r ≤ n + q := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [hcast]

private theorem localCount_eq_zmod (n q : ℕ) (hq : 0 < q) :
    localCount n q =
      (letI : NeZero q := ⟨hq.ne'⟩; (zmodSet n q).card) := by
  have : NeZero q := ⟨hq.ne'⟩
  dsimp [localCount]
  refine Finset.card_bij (fun r _ => (r : ZMod q)) ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [mem_zmodSet_iff]
    exact (pred_iff_zmod n q r hr.1).mp hr.2
  · intro r₁ hr₁ r₂ hr₂ heq
    rw [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    have hv := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt hr₁.1, ZMod.val_natCast_of_lt hr₂.1] at hv
  · intro x hx
    rw [mem_zmodSet_iff] at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [pred_iff_zmod n q x.val (ZMod.val_lt x), ZMod.natCast_zmod_val]
    exact hx

private theorem ringEquiv_isUnit_iff {A B : Type*} [Semiring A] [Semiring B]
    (e : A ≃+* B) (x : A) : IsUnit (e x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map e.symm.toMonoidHom, fun h => h.map e.toMonoidHom⟩

private theorem localCount_mul (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    localCount n (a * b) = localCount n a * localCount n b := by
  have hab_pos : 0 < a * b := Nat.mul_pos ha hb
  rw [localCount_eq_zmod n (a * b) hab_pos, localCount_eq_zmod n a ha, localCount_eq_zmod n b hb]
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have : NeZero (a * b) := ⟨hab_pos.ne'⟩
  let e : ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder hab
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    rw [mem_zmodSet_iff] at hx
    rw [Finset.mem_product, mem_zmodSet_iff, mem_zmodSet_iff]
    have hu1 : IsUnit (e x) := (ringEquiv_isUnit_iff e x).mpr hx.1
    rw [Prod.isUnit_iff] at hu1
    have hu2 : IsUnit (e ((n : ZMod (a * b)) - x)) :=
      (ringEquiv_isUnit_iff e ((n : ZMod (a * b)) - x)).mpr hx.2
    have hmap : e ((n : ZMod (a * b)) - x) = ((n : ZMod a) - (e x).1, (n : ZMod b) - (e x).2) := by
      rw [map_sub, map_natCast]
      rfl
    rw [hmap, Prod.isUnit_iff] at hu2
    exact ⟨⟨hu1.1, hu2.1⟩, ⟨hu1.2, hu2.2⟩⟩
  · intro x₁ _ x₂ _ heq
    exact e.injective heq
  · intro y hy
    rw [Finset.mem_product, mem_zmodSet_iff, mem_zmodSet_iff] at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_zmodSet_iff]
    have hu1 : IsUnit (e (e.symm y)) := by
      rw [e.apply_symm_apply, Prod.isUnit_iff]
      exact ⟨hy.1.1, hy.2.1⟩
    have hu2 : IsUnit (e ((n : ZMod (a * b)) - e.symm y)) := by
      have hmap : e ((n : ZMod (a * b)) - e.symm y) = ((n : ZMod a) - y.1, (n : ZMod b) - y.2) := by
        rw [map_sub, map_natCast, e.apply_symm_apply]
        rfl
      rw [hmap, Prod.isUnit_iff]
      exact ⟨hy.1.2, hy.2.2⟩
    exact ⟨(ringEquiv_isUnit_iff e _).mp hu1, (ringEquiv_isUnit_iff e _).mp hu2⟩

private theorem localCount_prime (n p : ℕ) (hp : p.Prime) :
    localCount n p = if p ∣ n then p - 1 else p - 2 := by
  classical
  rw [localCount_eq_zmod n p hp.pos]
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hset : zmodSet n p =
      (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ x ≠ (n : ZMod p)) := by
    ext x
    rw [mem_zmodSet_iff, Finset.mem_filter]
    simp [isUnit_iff_ne_zero, sub_ne_zero, ne_comm]
  rw [hset]
  by_cases hpn : p ∣ n
  · simp only [hpn, ↓reduceIte]
    have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    have heq : (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ x ≠ (n : ZMod p)) =
        (Finset.univ : Finset (ZMod p)).erase 0 := by
      ext x
      simp [hn0]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  · simp only [hpn, ↓reduceIte]
    have hn0 : (n : ZMod p) ≠ 0 := fun h => hpn ((ZMod.natCast_eq_zero_iff n p).mp h)
    have heq : (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ x ≠ (n : ZMod p)) =
        ((Finset.univ : Finset (ZMod p)).erase (n : ZMod p)).erase 0 := by
      ext x
      simp [and_comm]
    have hmem0 : (0 : ZMod p) ∈ (Finset.univ : Finset (ZMod p)).erase (n : ZMod p) := by
      simp [hn0.symm]
    rw [heq, Finset.card_erase_of_mem hmem0, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
    omega

private theorem mod_pow_cast_eq (a p k : ℕ) (hk : 0 < k) :
    (((a % (p ^ k)) : ℕ) : ZMod p) = (a : ZMod p) := by
  have hdiv := Nat.div_add_mod a (p ^ k)
  have hcast := congrArg (fun m : ℕ => (m : ZMod p)) hdiv
  have hp0 : ((p ^ k : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (p ^ k) p).mpr (dvd_pow_self p hk.ne')
  simpa [Nat.cast_add, Nat.cast_mul, hp0] using hcast

private theorem localCount_prime_pow (n p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    localCount n (p ^ k) = p ^ (k - 1) * localCount n p := by
  dsimp [localCount]
  rw [← Finset.card_range (p ^ (k - 1)), ← Finset.card_product]
  have hpk : p ^ k = p * p ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have hpred : ∀ r : ℕ, r < p ^ k →
      ((r.Coprime (p ^ k) ∧ ((n + p ^ k - r) % (p ^ k)).Coprime (p ^ k)) ↔
        ((r % p).Coprime p ∧ ((n + p - r % p) % p).Coprime p)) := by
    intro r hr
    rw [Nat.coprime_pow_right_iff hk, Nat.coprime_pow_right_iff hk]
    rw [← ZMod.isUnit_iff_coprime r p, ← ZMod.isUnit_iff_coprime (r % p) p,
      ← ZMod.isUnit_iff_coprime ((n + p ^ k - r) % (p ^ k)) p,
      ← ZMod.isUnit_iff_coprime ((n + p - r % p) % p) p]
    have hc1 : ((r % p : ℕ) : ZMod p) = (r : ZMod p) := ZMod.natCast_mod r p
    have hc2 : (((n + p ^ k - r) % (p ^ k) : ℕ) : ZMod p) =
        (((n + p - r % p) % p : ℕ) : ZMod p) := by
      rw [mod_pow_cast_eq _ p k hk, ZMod.natCast_mod]
      have hle1 : r ≤ n + p ^ k := by omega
      have hrmod : r % p < p := Nat.mod_lt r hp.pos
      have hle2 : r % p ≤ n + p := by omega
      have hp0 : ((p ^ k : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (p ^ k) p).mpr (dvd_pow_self p hk.ne')
      rw [Nat.cast_sub hle1, Nat.cast_sub hle2, Nat.cast_add, Nat.cast_add,
        hp0, ZMod.natCast_self, ZMod.natCast_mod]
    rw [hc1, hc2]
  refine Finset.card_bij (fun r _ => (r / p, r % p)) ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
    have hdiv_lt : r / p < p ^ (k - 1) := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      linarith
    exact ⟨hdiv_lt, Nat.mod_lt r hp.pos, (hpred r hr.1).mp hr.2⟩
  · intro r₁ _ r₂ _ heq
    rw [Prod.mk.injEq] at heq
    have h1 := Nat.div_add_mod r₁ p
    have h2 := Nat.div_add_mod r₂ p
    rw [heq.1, heq.2] at h1
    exact h1.symm.trans h2
  · intro y hy
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_range] at hy
    rcases y with ⟨q₀, c⟩
    dsimp at hy
    have hr_lt : c + p * q₀ < p ^ k := by
      rw [hpk]
      nlinarith [hy.1, hy.2.1]
    have hmod : (c + p * q₀) % p = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy.2.1]
    have hdiv : (c + p * q₀) / p = q₀ := by
      rw [Nat.add_mul_div_left c q₀ hp.pos, Nat.div_eq_of_lt hy.2.1, zero_add]
    refine ⟨c + p * q₀, ?_, Prod.ext hdiv hmod⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hr_lt, ?_⟩
    rw [hpred (c + p * q₀) hr_lt, hmod]
    exact hy.2.2

noncomputable def factorFloor (p : ℕ) : ℝ :=
  if 3 ≤ p then (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 else 1

private theorem factorFloor_nonneg (p : ℕ) : 0 ≤ factorFloor p := by
  dsimp [factorFloor]
  split_ifs with hp
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (0 : ℝ) ≤ (p : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
    exact div_nonneg (mul_nonneg h1 h2) (sq_nonneg _)
  · norm_num

private theorem factorFloor_le_one (p : ℕ) : factorFloor p ≤ 1 := by
  dsimp [factorFloor]
  split_ifs with hp
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hden : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1
    rw [div_le_one hden]
    nlinarith
  · norm_num

private theorem prime_pow_local_bound (n p k : ℕ) (hn : Even n) (hp : p.Prime) (hk : 0 < k) :
    factorFloor p ≤
      ((p ^ k : ℕ) : ℝ) * (localCount n (p ^ k) : ℝ) / ((p ^ k).totient : ℝ) ^ 2 := by
  rw [localCount_prime_pow n p k hp hk, Nat.totient_prime_pow hp hk]
  have hpk : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpow_ne : (p : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero (k - 1) hp_ne
  have hp1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have : p - 1 ≠ 0 := by have := hp.two_le; omega
    exact Nat.cast_ne_zero.mpr this
  have hsimp :
      ((p ^ k : ℕ) : ℝ) * ((p ^ (k - 1) * localCount n p : ℕ) : ℝ) /
          ((p ^ (k - 1) * (p - 1) : ℕ) : ℝ) ^ 2 =
        (p : ℝ) * (localCount n p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
    rw [hpk]
    push_cast
    field_simp
  rw [hsimp, localCount_prime n p hp]
  by_cases hp3 : 3 ≤ p
  · have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp1_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have : 1 ≤ p := by omega
      rw [Nat.cast_sub this, Nat.cast_one]
    have hge : p - 2 ≤ (if p ∣ n then p - 1 else p - 2) := by
      split_ifs <;> omega
    have hge_r : (p : ℝ) - 2 ≤ ((if p ∣ n then p - 1 else p - 2 : ℕ) : ℝ) := by
      have h2 : 2 ≤ p := by omega
      calc
        (p : ℝ) - 2 = ((p - 2 : ℕ) : ℝ) := by rw [Nat.cast_sub h2, Nat.cast_ofNat]
        _ ≤ ((if p ∣ n then p - 1 else p - 2 : ℕ) : ℝ) := by exact_mod_cast hge
    simp only [factorFloor, hp3, ↓reduceIte, hp1_cast]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hge_r (by linarith)
  · have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    have h2n : 2 ∣ n := even_iff_two_dvd.mp hn
    simp [factorFloor, h2n]

private theorem euler_prod_lower (n : ℕ) (hn : Even n) :
    ∀ q : ℕ, 0 < q →
      (∏ p ∈ q.primeFactors, factorFloor p) ≤
        (q : ℝ) * (localCount n q : ℝ) / (q.totient : ℝ) ^ 2 := by
  intro q
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ q
  · intro p k hp hk _
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
    exact prime_pow_local_bound n p k hn hp hk
  · intro h0
    exact False.elim (lt_irrefl 0 h0)
  · intro _
    simp [localCount]
  · intro a b ha hb hab iha ihb _
    have ha0 : 0 < a := by omega
    have hb0 : 0 < b := by omega
    rw [Nat.primeFactors_mul ha0.ne' hb0.ne',
      Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab),
      localCount_mul n a b ha0 hb0 hab, Nat.totient_mul hab]
    have hsplit :
        ((a * b : ℕ) : ℝ) * ((localCount n a * localCount n b : ℕ) : ℝ) /
            ((a.totient * b.totient : ℕ) : ℝ) ^ 2 =
          ((a : ℝ) * (localCount n a : ℝ) / (a.totient : ℝ) ^ 2) *
            ((b : ℝ) * (localCount n b : ℝ) / (b.totient : ℝ) ^ 2) := by
      push_cast
      ring
    rw [hsplit]
    exact mul_le_mul (iha ha0) (ihb hb0)
      (Finset.prod_nonneg (fun p _ => factorFloor_nonneg p))
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))

private theorem prod_range_factorFloor_shift (d : ℕ) :
    (∏ k ∈ Finset.range (d + 3), factorFloor k) =
      ((d + 2 : ℕ) : ℝ) / (2 * (((d + 2 : ℕ) : ℝ) - 1)) := by
  induction d with
  | zero =>
    simp [Finset.prod_range_succ, factorFloor]
    norm_num
  | succ d ih =>
    have hstep : d + 1 + 3 = (d + 3) + 1 := by omega
    rw [hstep, Finset.prod_range_succ, ih]
    have h3 : 3 ≤ d + 3 := by omega
    dsimp [factorFloor]
    have hd1 : (((d + 2 : ℕ) : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ d + 2)
      linarith
    have hd2 : (((d + 3 : ℕ) : ℝ) - 1) ≠ 0 := by
      have : (3 : ℝ) ≤ ((d + 3 : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    have hd3 : (((d + 1 + 2 : ℕ) : ℝ) - 1) ≠ 0 := by
      have : (3 : ℝ) ≤ ((d + 1 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ d + 1 + 2)
      linarith
    push_cast at hd1 hd2 hd3 ⊢
    field_simp
    ring

private theorem prod_range_mono (f g : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (hfg : ∀ k, f k ≤ g k) :
    ∀ m : ℕ, (∏ k ∈ Finset.range m, f k) ≤ ∏ k ∈ Finset.range m, g k
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    exact mul_le_mul (prod_range_mono f g hf hfg m) (hfg m) (hf m)
      (Finset.prod_nonneg (fun k _ => le_trans (hf k) (hfg k)))

private theorem half_le_prod_factorFloor (s : Finset ℕ) :
    (1 : ℝ) / 2 ≤ ∏ k ∈ s, factorFloor k := by
  classical
  let d : ℕ := s.sup id + 1
  have hsub : s ⊆ Finset.range (d + 3) := by
    intro k hk
    rw [Finset.mem_range]
    have hle : k ≤ s.sup id := Finset.le_sup (f := id) hk
    omega
  have hfilt : (Finset.range (d + 3)).filter (fun k => k ∈ s) = s := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun hk => ⟨hsub hk, hk⟩⟩
  have hprod_eq :
      (∏ k ∈ s, factorFloor k) =
        ∏ k ∈ Finset.range (d + 3), (if k ∈ s then factorFloor k else 1) := by
    rw [← Finset.prod_filter, hfilt]
  rw [hprod_eq]
  have hmono :
      (∏ k ∈ Finset.range (d + 3), factorFloor k) ≤
        ∏ k ∈ Finset.range (d + 3), (if k ∈ s then factorFloor k else 1) := by
    refine prod_range_mono factorFloor (fun k => if k ∈ s then factorFloor k else 1)
      factorFloor_nonneg (fun k => ?_) (d + 3)
    split_ifs
    · exact le_rfl
    · exact factorFloor_le_one k
  refine le_trans ?_ hmono
  rw [prod_range_factorFloor_shift d]
  have hd_ge : (2 : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ d + 2)
  have hden : (0 : ℝ) < 2 * (((d + 2 : ℕ) : ℝ) - 1) := by linarith
  rw [div_le_div_iff₀ (by norm_num) hden]
  linarith

end PEqualNP.Outside.CosetEulerLowerAux

theorem PEqualNP.Outside.L_goldbach_coset_euler_lower :
    let R := fun n q : ℕ =>
      ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n + q - r) % q).Coprime q)).card
    ∀ n q : ℕ, Even n → 0 < q → (1 : ℝ) / 2 ≤ (q : ℝ) * (R n q : ℝ) / (q.totient : ℝ) ^ 2 := by
  intro R n q hn hq
  exact le_trans
    (PEqualNP.Outside.CosetEulerLowerAux.half_le_prod_factorFloor q.primeFactors)
    (PEqualNP.Outside.CosetEulerLowerAux.euler_prod_lower n hn q hq)
