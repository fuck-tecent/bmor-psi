import Mathlib

namespace PEqualNP.Outside

private lemma w11b_mod_sq_add_dvd {r q a : ℕ} :
    q ∣ r ^ 2 + a ↔ q ∣ (r % q) ^ 2 + a := by
  have hdiv : q * (r / q) + r % q = r := Nat.div_add_mod r q
  have h_id : r ^ 2 + a = q * (q * (r / q) ^ 2 + 2 * (r / q) * (r % q)) + ((r % q) ^ 2 + a) := by
    calc r ^ 2 + a = (q * (r / q) + r % q) ^ 2 + a := by rw [hdiv]
      _ = q * (q * (r / q) ^ 2 + 2 * (r / q) * (r % q)) + ((r % q) ^ 2 + a) := by ring
  rw [h_id]
  exact Nat.dvd_add_right (dvd_mul_right q _)

private lemma w11b_roots_mul_coprime {a q m : ℕ} (hq : 0 < q) (hm : 0 < m) (hcop : Nat.Coprime q m) :
    (((Finset.range (q * m)).filter (fun r => q * m ∣ r ^ 2 + a)).card) =
      (((Finset.range q).filter (fun r => q ∣ r ^ 2 + a)).card) *
      (((Finset.range m).filter (fun r => m ∣ r ^ 2 + a)).card) := by
  rw [← Finset.card_product]
  refine Finset.card_bij (fun r _ => (r % q, r % m)) ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt r hq, w11b_mod_sq_add_dvd.mp (dvd_trans (dvd_mul_right q m) hr.2)⟩,
      ⟨Nat.mod_lt r hm, w11b_mod_sq_add_dvd.mp (dvd_trans (dvd_mul_left m q) hr.2)⟩⟩
  · intro r₁ hr₁ r₂ hr₂ h_eq
    rw [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    rw [Prod.mk.injEq] at h_eq
    have hmod_qm : r₁ ≡ r₂ [MOD q * m] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h_eq.1, h_eq.2⟩
    change r₁ % (q * m) = r₂ % (q * m) at hmod_qm
    rwa [Nat.mod_eq_of_lt hr₁.1, Nat.mod_eq_of_lt hr₂.1] at hmod_qm
  · intro p hp
    rcases p with ⟨u, v⟩
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨hu_lt, hu_dvd⟩, ⟨hv_lt, hv_dvd⟩⟩ := hp
    let crt := Nat.chineseRemainder hcop u v
    let r : ℕ := crt.val % (q * m)
    have hr_lt : r < q * m := Nat.mod_lt _ (Nat.mul_pos hq hm)
    have hr_q : r % q = u := by
      calc r % q = (crt.val % (q * m)) % q := rfl
        _ = crt.val % q := Nat.mod_mod_of_dvd crt.val (dvd_mul_right q m)
        _ = u % q := crt.prop.1
        _ = u := Nat.mod_eq_of_lt hu_lt
    have hr_m : r % m = v := by
      calc r % m = (crt.val % (q * m)) % m := rfl
        _ = crt.val % m := Nat.mod_mod_of_dvd crt.val (dvd_mul_left m q)
        _ = v % m := crt.prop.2
        _ = v := Nat.mod_eq_of_lt hv_lt
    refine ⟨r, ?_, Prod.ext hr_q hr_m⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hr_lt, hcop.mul_dvd_of_dvd_of_dvd ?_ ?_⟩
    · rw [w11b_mod_sq_add_dvd, hr_q]; exact hu_dvd
    · rw [w11b_mod_sq_add_dvd, hr_m]; exact hv_dvd

private lemma w11b_roots_prime {p : ℕ} (hp : p.Prime) :
    ((Finset.range p).filter (fun r => p ∣ r ^ 2 + 1)).card =
      if p = 2 then 1 else if p % 4 = 1 then 2 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · have h_eq : (Finset.range 2).filter (fun r => 2 ∣ r ^ 2 + 1) = {1} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hr_lt, hdvd⟩
        rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
        · norm_num at hdvd
        · rfl
      · rintro rfl
        norm_num
    rw [h_eq, Finset.card_singleton]
    simp
  · simp only [hp2, ↓reduceIte]
    have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with hp1 | hp3
    · simp only [hp1, ↓reduceIte]
      have hp_ne3 : p % 4 ≠ 3 := by omega
      obtain ⟨u, hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr hp_ne3
      have hu_sq : u ^ 2 = -1 := by simpa [sq] using hu.symm
      have hu_ne : u ≠ -u := by
        intro h_eq
        have h2u : (2 : ZMod p) * u = 0 := by linear_combination h_eq
        have h2_nz : (2 : ZMod p) ≠ 0 := by
          intro h0
          have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
          have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
          have hge : 2 ≤ p := hp.two_le
          omega
        have hu0 : u = 0 := (mul_eq_zero.mp h2u).resolve_left h2_nz
        rw [hu0] at hu_sq
        norm_num at hu_sq
      have hval_ne : u.val ≠ (-u).val := by
        intro h
        have hc := congr_arg (fun n : ℕ => (n : ZMod p)) h
        simp only [ZMod.natCast_zmod_val] at hc
        exact hu_ne hc
      have h_set : (Finset.range p).filter (fun r => p ∣ r ^ 2 + 1) = {u.val, (-u).val} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr_lt, hr_dvd⟩
          have hz0 : ((r ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff _ p).mpr hr_dvd
          push_cast at hz0
          have hfac : ((r : ZMod p) - u) * ((r : ZMod p) + u) = 0 := by
            linear_combination hz0 - hu_sq
          rcases mul_eq_zero.mp hfac with h1 | h2
          · left
            have hru : (r : ZMod p) = u := sub_eq_zero.mp h1
            rw [← hru, ZMod.val_natCast_of_lt hr_lt]
          · right
            have hru : (r : ZMod p) = -u := eq_neg_of_add_eq_zero_left h2
            rw [← hru, ZMod.val_natCast_of_lt hr_lt]
        · rintro (rfl | rfl)
          · refine ⟨ZMod.val_lt u, (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
            push_cast
            rw [ZMod.natCast_zmod_val, hu_sq, neg_add_cancel]
          · refine ⟨ZMod.val_lt (-u), (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
            push_cast
            rw [ZMod.natCast_zmod_val, neg_sq, hu_sq, neg_add_cancel]
      rw [h_set, Finset.card_pair hval_ne]
    · have hp_not1 : p % 4 ≠ 1 := by omega
      simp only [hp_not1, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _ hr_dvd
      have hz0 : ((r ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ p).mpr hr_dvd
      push_cast at hz0
      have h_ex : IsSquare (-1 : ZMod p) := ⟨(r : ZMod p), by linear_combination -hz0⟩
      have hp_ne3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp h_ex
      exact hp_ne3 hp3

theorem L_quadratic_primes_levent_root_count_multiplicative :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ q : ℕ, 0<q → Squarefree q → (roots 1 q).card = ∏ p ∈ q.primeFactors, (if p=2 then 1 else if p % 4 = 1 then 2 else 0) := by
  intro roots q hq hsq
  have h_prod_eq : ∏ p ∈ q.primeFactors, p = q := Nat.prod_primeFactors_of_squarefree hsq
  have h_finset : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      (roots 1 (∏ p ∈ S, p)).card = ∏ p ∈ S, (roots 1 p).card := by
    intro S hS
    induction S using Finset.induction_on with
    | empty =>
      dsimp only [roots]
      rw [Finset.prod_empty, Finset.prod_empty]
      have h1 : (Finset.range 1).filter (fun r => 1 ∣ r ^ 2 + 1) = {0} := by
        ext r; simp
      rw [h1, Finset.card_singleton]
    | @insert p s hp_not ih =>
      have hp : p.Prime := hS p (Finset.mem_insert_self p s)
      have hs : ∀ r ∈ s, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
      have hM_pos : 0 < ∏ r ∈ s, r := Finset.prod_pos fun r hr => (hs r hr).pos
      have hcop : Nat.Coprime p (∏ r ∈ s, r) :=
        Nat.Coprime.prod_right fun r hr => (hp.coprime_iff_not_dvd).mpr fun hdvd =>
          hp_not (((Nat.prime_dvd_prime_iff_eq hp (hs r hr)).mp hdvd) ▸ hr)
      rw [Finset.prod_insert hp_not, Finset.prod_insert hp_not, ← ih hs]
      exact w11b_roots_mul_coprime hp.pos hM_pos hcop
  have h_pf_prime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  calc (roots 1 q).card
    _ = (roots 1 (∏ p ∈ q.primeFactors, p)).card := by rw [h_prod_eq]
    _ = ∏ p ∈ q.primeFactors, (roots 1 p).card := h_finset q.primeFactors h_pf_prime
    _ = ∏ p ∈ q.primeFactors, (if p = 2 then 1 else if p % 4 = 1 then 2 else 0) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        exact w11b_roots_prime (h_pf_prime p hp)

end PEqualNP.Outside
