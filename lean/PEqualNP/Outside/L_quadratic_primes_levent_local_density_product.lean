import Mathlib

private lemma coprime_mod {a m : ℕ} : Nat.Coprime (a % m) m ↔ Nat.Coprime a m := by
  simp only [Nat.coprime_iff_gcd_eq_one]
  rw [Nat.gcd_comm a m, Nat.gcd_rec m a]

private lemma coprime_of_modEq {a b m : ℕ} (h : a ≡ b [MOD m]) (hb : Nat.Coprime b m) :
    Nat.Coprime a m := by
  rw [← coprime_mod (a := a)]
  show Nat.Coprime (a % m) m
  rw [show a % m = b % m from h]
  exact (coprime_mod (a := b)).2 hb

private lemma coprime_sq_add_one_mod {k m : ℕ} :
    Nat.Coprime ((k % m)^2+1) m ↔ Nat.Coprime (k^2+1) m := by
  rw [← coprime_mod (a := (k % m)^2+1), ← coprime_mod (a := k^2+1),
    show ((k % m)^2+1) % m = (k^2+1) % m from
      (Nat.mod_modEq k m).pow 2 |>.add (Nat.ModEq.refl 1)]

private lemma card_coprime_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hco : m.Coprime n) :
    ((Finset.range (m*n)).filter (fun k => Nat.Coprime (k^2+1) (m*n))).card
      = ((Finset.range m).filter (fun k => Nat.Coprime (k^2+1) m)).card
        * ((Finset.range n).filter (fun k => Nat.Coprime (k^2+1) n)).card := by
  classical
  rw [← Finset.card_product]
  refine Finset.card_bij (fun k _ => (k % m, k % n)) ?_ ?_ ?_
  · rintro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hk ⊢
    obtain ⟨hklt, hkc⟩ := hk
    obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.1 hkc
    exact ⟨⟨Nat.mod_lt _ hm, coprime_sq_add_one_mod.2 h1⟩,
      ⟨Nat.mod_lt _ hn, coprime_sq_add_one_mod.2 h2⟩⟩
  · rintro k1 hk1 k2 hk2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2
    simp only [Prod.mk.injEq] at heq
    have h3 : k1 ≡ k2 [MOD m*n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hco).1 ⟨heq.1, heq.2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h3 hk1.1 hk2.1
  · rintro ⟨u, v⟩ hb
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨⟨hu1, huc⟩, ⟨hv1, hvc⟩⟩ := hb
    have hlt : (Nat.chineseRemainder hco u v).1 < m*n :=
      Nat.chineseRemainder_lt_mul hco u v hm.ne' hn.ne'
    have hmu : (Nat.chineseRemainder hco u v).1 ≡ u [MOD m] :=
      (Nat.chineseRemainder hco u v).2.1
    have hmv : (Nat.chineseRemainder hco u v).1 ≡ v [MOD n] :=
      (Nat.chineseRemainder hco u v).2.2
    refine ⟨(Nat.chineseRemainder hco u v).1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt, ?_⟩
      rw [Nat.coprime_mul_iff_right]
      exact ⟨coprime_of_modEq (hmu.pow 2 |>.add (Nat.ModEq.refl 1)) huc,
        coprime_of_modEq (hmv.pow 2 |>.add (Nat.ModEq.refl 1)) hvc⟩
    · have e1 : (Nat.chineseRemainder hco u v).1 % m = u := by
        rw [show (Nat.chineseRemainder hco u v).1 % m = u % m from hmu, Nat.mod_eq_of_lt hu1]
      have e2 : (Nat.chineseRemainder hco u v).1 % n = v := by
        rw [show (Nat.chineseRemainder hco u v).1 % n = v % n from hmv, Nat.mod_eq_of_lt hv1]
      simp only [e1, e2]

private lemma card_filter_coprime_prime {p : ℕ} (hp : p.Prime) :
    ((Finset.range p).filter (fun n => Nat.Coprime (n^2+1) p)).card
      = p - ((Finset.range p).filter (fun r => p ∣ r^2+1)).card := by
  classical
  have hiff : ∀ r : ℕ, (p ∣ r^2+1) ↔ ¬ Nat.Coprime (r^2+1) p := by
    intro r
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    simp
  have hcompl : (Finset.range p) \ ((Finset.range p).filter (fun n => Nat.Coprime (n^2+1) p))
      = (Finset.range p).filter (fun r => p ∣ r^2+1) := by
    ext r
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, hiff r]
    tauto
  have hR : ((Finset.range p).filter (fun r => p ∣ r^2+1)).card
      = p - ((Finset.range p).filter (fun n => Nat.Coprime (n^2+1) p)).card := by
    rw [← hcompl, Finset.card_sdiff,
      Finset.inter_eq_left.2 (Finset.filter_subset _ _), Finset.card_range]
  rw [hR, Nat.sub_sub_self]
  have h1 : ((Finset.range p).filter (fun n => Nat.Coprime (n^2+1) p)).card ≤ (Finset.range p).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa using h1

private lemma card_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ((Finset.range (∏ p ∈ S, p)).filter (fun n => Nat.Coprime (n^2+1) (∏ p ∈ S, p))).card
      = ∏ p ∈ S, ((Finset.range p).filter (fun n => Nat.Coprime (n^2+1) p)).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p T hpT ih =>
    rw [Finset.prod_insert hpT, Finset.prod_insert hpT]
    have hp : Nat.Prime p := hS p (Finset.mem_insert_self p T)
    have hT : ∀ q ∈ T, Nat.Prime q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hco : p.Coprime (∏ q ∈ T, q) := by
      refine Nat.Coprime.prod_right (fun q hq => ?_)
      rw [Nat.coprime_primes hp (hT q hq)]
      intro hpq
      exact hpT (hpq ▸ hq)
    have hpos : 0 < ∏ q ∈ T, q := Finset.prod_pos (fun q hq => (hT q hq).pos)
    rw [card_coprime_mul hp.pos hpos hco, ih hT]

theorem PEqualNP.Outside.L_quadratic_primes_levent_local_density_product :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → let Q := ∏ p ∈ S, p; (((Finset.range Q).filter (fun n => Nat.Coprime (n^2+1) Q)).card : ℝ) / Q = ∏ p ∈ S, (1-((roots 1 p).card : ℝ)/p) := by
  dsimp only
  intro S hS
  classical
  have hle : ∀ p ∈ S, ((Finset.range p).filter (fun r => p ∣ r^2+1)).card ≤ p := by
    intro p _
    have h1 : ((Finset.range p).filter (fun r => p ∣ r^2+1)).card ≤ (Finset.range p).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa using h1
  have hcard := card_prod_primes S hS
  rw [Finset.prod_congr rfl (fun p hp => card_filter_coprime_prime (hS p hp))] at hcard
  rw [hcard]
  simp only [Nat.cast_prod]
  rw [Finset.prod_congr rfl (fun p hp => Nat.cast_sub (hle p hp))]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp0 : (p:ℝ) ≠ 0 := by
    have := (hS p hp).pos
    positivity
  field_simp
