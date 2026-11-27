import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith

private theorem R_eq (n q : ℕ) : (Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q) = (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q) := by
  apply Finset.filter_congr
  intro r _
  have h : Nat.Coprime ((n+q-r) % q) q ↔ Nat.Coprime (n+q-r) q := by
    unfold Nat.Coprime
    rw [(Nat.mod_modEq _ _).gcd_eq]
  rw [h]

private theorem powlift_aux :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ p k n, Nat.Prime p → (U (p^(k+1)) n).card=p^k*(U p n).card := by
  intro U p k n hp
  have hp0 : 0 < p := hp.pos
  have hpow : p^(k+1) = p * p^k := by ring
  have helper : ∀ b j : ℕ, b < p → j < p^k →
      (Nat.Coprime (b + p*j) (p^(k+1)) ↔ Nat.Coprime b p) ∧
      (Nat.Coprime (n + p^(k+1) - (b + p*j)) (p^(k+1)) ↔ Nat.Coprime (n + p - b) p) := by
    intro b j hb hj
    obtain ⟨m, hm⟩ : ∃ m, p^k = j + 1 + m := ⟨p^k - j - 1, by omega⟩
    have e : p^(k+1) = p*j + p + p*m := by rw [hpow, hm]; ring
    have e2 : n + p^(k+1) - (b + p*j) = (n + p - b) + p*m := by omega
    constructor
    · rw [Nat.coprime_pow_right_iff (Nat.succ_pos k), Nat.coprime_add_mul_left_left]
    · rw [Nat.coprime_pow_right_iff (Nat.succ_pos k), e2, Nat.coprime_add_mul_left_left]
  have hmem : ∀ q a : ℕ, a ∈ U q n ↔ a < q ∧ Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q := by
    intro q a
    simp only [U, Finset.mem_filter, Finset.mem_range]
  have hk : (U p n ×ˢ Finset.range (p^k)).card = (U (p^(k+1)) n).card := by
    apply Finset.card_bij (fun x _ => x.1 + p * x.2)
    · intro x hx
      rw [Finset.mem_product, hmem, Finset.mem_range] at hx
      obtain ⟨⟨hb, hc1, hc2⟩, hj⟩ := hx
      have h := helper x.1 x.2 hb hj
      rw [hmem]
      refine ⟨?_, h.1.2 hc1, h.2.2 hc2⟩
      have : p * (x.2 + 1) ≤ p * p^k := Nat.mul_le_mul_left p hj
      rw [hpow]
      nlinarith
    · intro x hx y hy hxy
      rw [Finset.mem_product, hmem, Finset.mem_range] at hx hy
      have hb1 := hx.1.1
      have hb2 := hy.1.1
      have hxy : x.1 + p * x.2 = y.1 + p * y.2 := hxy
      have m1 : (x.1 + p * x.2) % p = x.1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb1]
      have m2 : (y.1 + p * y.2) % p = y.1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb2]
      have d1 : (x.1 + p * x.2) / p = x.2 := by
        rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hb1]; simp
      have d2 : (y.1 + p * y.2) / p = y.2 := by
        rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hb2]; simp
      rw [hxy] at m1 d1
      exact Prod.ext (m1.symm.trans m2) (d1.symm.trans d2)
    · intro a ha
      rw [hmem] at ha
      obtain ⟨ha1, ha2, ha3⟩ := ha
      have hb : a % p < p := Nat.mod_lt _ hp0
      have hj : a / p < p^k := by
        apply Nat.div_lt_of_lt_mul
        rw [← hpow]; exact ha1
      have hdecomp : a % p + p * (a / p) = a := Nat.mod_add_div a p
      have h := helper (a % p) (a / p) hb hj
      rw [hdecomp] at h
      refine ⟨(a % p, a / p), ?_, hdecomp⟩
      rw [Finset.mem_product, hmem, Finset.mem_range]
      exact ⟨⟨hb, h.1.1 ha2, h.2.1 ha3⟩, hj⟩
  rw [← hk, Finset.card_product, Finset.card_range, mul_comm]

private theorem cnt_prime (n p : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p)).card = if p ∣ n then p - 1 else p - 2 := by
  have hp0 : 0 < p := hp.pos
  have mem : ∀ a, a < p → ((Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p) ↔ (a ≠ 0 ∧ a ≠ n % p)) := by
    intro a ha
    have c1 : Nat.Coprime a p ↔ a ≠ 0 := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      constructor
      · intro h h0
        subst h0
        exact h (dvd_zero p)
      · intro h hd
        exact h (Nat.eq_zero_of_dvd_of_lt hd ha)
    have c2 : Nat.Coprime (n+p-a) p ↔ a ≠ n % p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      have h1 := Nat.modEq_iff_dvd' (show a ≤ n + p by omega) (n := p)
      have h2 : p ∣ n + p - a ↔ a = n % p := by
        rw [← h1]
        unfold Nat.ModEq
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
      rw [h2]
    rw [c1, c2]
  by_cases hd : p ∣ n
  · have hn0 : n % p = 0 := Nat.mod_eq_zero_of_dvd hd
    have hs : (Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p) = Finset.Ico 1 p := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        have := (mem a h1).1 h2
        omega
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (mem a h2).2 ⟨by omega, by omega⟩⟩
    rw [hs, Nat.card_Ico]
    simp [hd]
  · have hn : n % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    have hlt : n % p < p := Nat.mod_lt _ hp0
    have hs : (Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p) = ((Finset.range p).erase 0).erase (n % p) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        have := (mem a h1).1 h2
        omega
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3, (mem a h3).2 ⟨h2, h1⟩⟩
    have hm1 : n % p ∈ (Finset.range p).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨hn, hlt⟩
    rw [hs, Finset.card_erase_of_mem hm1, Finset.card_erase_of_mem (by simp [hp0]), Finset.card_range]
    simp [hd]
    omega

theorem PEqualNP.Outside.L_goldbach_coset_primepower_lift :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q)).card; ∀ n p a : ℕ, p.Prime → 0<a → R n (p^a)=p^(a-1)*(if p∣n then p-1 else p-2) := by
  intro R n p a hp ha
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  show ((Finset.range (p^(k+1))).filter (fun r => r.Coprime (p^(k+1)) ∧ ((n+p^(k+1)-r)%(p^(k+1))).Coprime (p^(k+1)))).card = p^(k+1-1)*(if p∣n then p-1 else p-2)
  rw [R_eq n (p^(k+1)), powlift_aux p k n hp, cnt_prime n p hp, Nat.add_sub_cancel]
