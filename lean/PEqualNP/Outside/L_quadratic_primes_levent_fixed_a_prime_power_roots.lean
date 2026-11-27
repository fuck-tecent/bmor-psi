import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_prime_power_roots :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ p k a : ℕ, p.Prime → Nat.Coprime p (2*a) → 0<k → (roots a (p^k)).card = (roots a p).card := by
  intro roots p k a hp hc hk
  have _ : NeZero p := ⟨hp.ne_zero⟩
  have _ : Fact p.Prime := ⟨hp⟩
  -- the abbreviation unpacked, and membership in a filtered range
  have hroots : ∀ x q : ℕ, roots x q = Finset.filter (fun r => q ∣ r^2+x) (Finset.range q) :=
    fun x q => rfl
  have hmem : ∀ q r : ℕ, r ∈ roots a q ↔ r < q ∧ q ∣ r^2+a := by
    intro q r
    rw [hroots]
    simp
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_mul_iff_right.mp hc).1
  have hna : ¬ p ∣ a := (hp.coprime_iff_not_dvd).mp ((Nat.coprime_mul_iff_right.mp hc).2)
  have hpown : ∀ j : ℕ, 1 ≤ j → p ∣ p^j := by
    intro j hj
    have h : p^1 ∣ p^j := pow_dvd_pow p hj
    rwa [pow_one] at h
  have hpowj : ∀ j : ℕ, p^j ∣ p^(j+1) := fun j => pow_dvd_pow p (Nat.lt_succ_self j).le
  -- a root of X^2+a modulo p^j is never divisible by p
  have hndvd : ∀ j r : ℕ, 1 ≤ j → p^j ∣ r^2+a → ¬ p ∣ r := by
    intro j r hj h hr
    have hr2 : p ∣ r^2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_left hr r
    have hsum : p ∣ a + r^2 := by
      rw [add_comm]
      exact dvd_trans (hpown j hj) h
    exact hna ((Nat.dvd_add_left hr2).mp hsum)
  -- reducing a solution modulo n gives a solution modulo n
  have hdown : ∀ n r : ℕ, n ∣ r^2+a → n ∣ (r % n)^2+a := by
    intro n r h
    rw [← Nat.modEq_zero_iff_dvd] at h ⊢
    exact Nat.ModEq.trans (Nat.ModEq.add_right a (Nat.ModEq.pow 2 (Nat.mod_modEq r n))) h
  -- divisibility by p, read as a cast being zero in the field with p elements
  have hcast2 : ∀ x : ℕ, ((2*x : ℕ) : ZMod p) = (2 : ZMod p) * (x : ZMod p) := by
    intro x
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hne2 : ∀ x : ℕ, Nat.Coprime p (2*x) → (2 : ZMod p) * (x : ZMod p) ≠ 0 := by
    intro x hx hcon
    rw [← hcast2 x] at hcon
    exact ((hp.coprime_iff_not_dvd).mp hx)
      ((ZMod.natCast_eq_zero_iff (2*x) p).mp hcon)
  -- the linear congruence c + 2*r*t ≡ 0 modulo p, once p does not divide r
  have solve : ∀ r c : ℕ, ¬ p ∣ r → ∃ t : ℕ, t < p ∧ p ∣ c + 2*r*t := by
    intro r c hr
    have hcr : Nat.Coprime p (2*r) :=
      Nat.coprime_mul_iff_right.mpr ⟨hcop2, (hp.coprime_iff_not_dvd).mpr hr⟩
    have hne : (2 : ZMod p) * (r : ZMod p) ≠ 0 := hne2 r hcr
    let t₀ : ZMod p := -((c : ZMod p)) / (2 * (r : ZMod p))
    have hkey : (2 : ZMod p) * (r : ZMod p) * t₀ = -(c : ZMod p) := by
      have h1 : (-((c : ZMod p)) / (2 * (r : ZMod p))) * (2 * (r : ZMod p)) = -(c : ZMod p) :=
        div_mul_cancel₀ _ hne
      show (2 : ZMod p) * (r : ZMod p) * (-((c : ZMod p)) / (2 * (r : ZMod p))) = -(c : ZMod p)
      rw [mul_comm, h1]
    have hsum : (c : ZMod p) + (2 : ZMod p) * (r : ZMod p) * (t₀.val : ZMod p) = 0 := by
      rw [ZMod.natCast_zmod_val, hkey]
      abel
    refine ⟨t₀.val, ZMod.val_lt t₀, ?_⟩
    have hsim : ((c + 2*r*t₀.val : ℕ) : ZMod p) =
        (c : ZMod p) + (2 : ZMod p) * (r : ZMod p) * (t₀.val : ZMod p) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [← ZMod.natCast_eq_zero_iff (c + 2*r*t₀.val) p, hsim]
    exact hsum
  -- the shape of the binomial expansion used by the lift
  have hexp : ∀ j s x : ℕ, s^2+a = ((s^2+a) / p^j) * p^j →
      (s + x * p^j)^2 + a = p^j * (((s^2+a) / p^j) + 2*s*x + x^2 * p^j) := by
    intro j s x hcf
    have h1 : (s + x*p^j)^2 + a = ((s^2+a)/p^j) * p^j + (2*s*x*p^j + x^2*(p^j)^2) := by
      have h2 : (s + x*p^j)^2 + a = s^2 + a + (2*s*x*p^j + x^2*(p^j)^2) := by ring
      rw [hcf] at h2
      exact h2
    rw [h1]
    ring
  -- surjectivity of the restriction: every root modulo p^j lifts, and stays in the range
  have hlift : ∀ j s : ℕ, 1 ≤ j → s < p^j → p^j ∣ s^2+a →
      ∃ t : ℕ, t < p ∧ s + t * p^j < p^(j+1) ∧ p^(j+1) ∣ (s + t * p^j)^2+a ∧
        (s + t * p^j) % p^j = s := by
    intro j s hj hs hsd
    have hpj : 0 < p^j := pow_pos hp.pos j
    have hcf : s^2+a = ((s^2+a) / p^j) * p^j := (Nat.div_mul_cancel hsd).symm
    obtain ⟨t, ht, hdiv⟩ := solve s ((s^2+a) / p^j) (hndvd j s hj hsd)
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · rw [pow_succ']
      have h1 : s + t*p^j < p^j + t*p^j := Nat.add_lt_add_right hs (t*p^j)
      have hle : p^j + t*p^j ≤ p * p^j := by
        have h2 : p^j + t*p^j = (t+1)*p^j := by ring
        rw [h2]
        exact Nat.mul_le_mul_right (p^j) (Nat.succ_le_of_lt ht)
      exact Nat.lt_of_lt_of_le h1 hle
    · rw [hexp j s t hcf, pow_succ', mul_comm p (p^j), Nat.mul_dvd_mul_iff_left hpj]
      rw [Nat.dvd_add_left (dvd_mul_of_dvd_right (hpown j hj) (t^2))]
      exact hdiv
    · rw [mul_comm t (p^j), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  -- injectivity of the restriction: two lifts of one root share their multiplier
  have huniq : ∀ j s t₁ t₂ : ℕ, 1 ≤ j → s < p^j → p^j ∣ s^2+a →
      p^(j+1) ∣ (s + t₁ * p^j)^2+a → p^(j+1) ∣ (s + t₂ * p^j)^2+a → t₁ < p → t₂ < p → t₁ = t₂ := by
    intro j s t₁ t₂ hj hs hsd h1 h2 ht1 ht2
    have hpj : 0 < p^j := pow_pos hp.pos j
    have hcf : s^2+a = ((s^2+a) / p^j) * p^j := (Nat.div_mul_cancel hsd).symm
    have lin : ∀ x : ℕ, p^(j+1) ∣ (s + x * p^j)^2+a → p ∣ ((s^2+a) / p^j) + 2*s*x := by
      intro x hx
      rw [hexp j s x hcf, pow_succ', mul_comm p (p^j)] at hx
      rw [Nat.mul_dvd_mul_iff_left hpj] at hx
      rw [Nat.dvd_add_left (dvd_mul_of_dvd_right (hpown j hj) (x^2))] at hx
      exact hx
    have hnd : ¬ p ∣ s := hndvd j s hj hsd
    have hcr : Nat.Coprime p (2*s) :=
      Nat.coprime_mul_iff_right.mpr ⟨hcop2, (hp.coprime_iff_not_dvd).mpr hnd⟩
    have hne : (2 : ZMod p) * (s : ZMod p) ≠ 0 := hne2 s hcr
    have e1 : (((s^2+a)/p^j : ℕ) : ZMod p) + (2 : ZMod p) * (s : ZMod p) * (t₁ : ZMod p) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (ZMod.natCast_eq_zero_iff (((s^2+a)/p^j : ℕ) + 2*s*t₁) p).mpr (lin t₁ h1)
    have e2 : (((s^2+a)/p^j : ℕ) : ZMod p) + (2 : ZMod p) * (s : ZMod p) * (t₂ : ZMod p) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (ZMod.natCast_eq_zero_iff (((s^2+a)/p^j : ℕ) + 2*s*t₂) p).mpr (lin t₂ h2)
    have hx1 : (2 : ZMod p) * (s : ZMod p) * (t₁ : ZMod p) = -(((s^2+a)/p^j : ℕ) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      rw [add_comm]
      exact e1
    have hx2 : (2 : ZMod p) * (s : ZMod p) * (t₂ : ZMod p) = -(((s^2+a)/p^j : ℕ) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      rw [add_comm]
      exact e2
    have hcong : (t₁ : ZMod p) = (t₂ : ZMod p) :=
      mul_left_cancel₀ hne (hx1.trans hx2.symm)
    have hval : (t₁ : ZMod p).val = (t₂ : ZMod p).val := congrArg ZMod.val hcong
    rwa [ZMod.val_natCast_of_lt ht1, ZMod.val_natCast_of_lt ht2] at hval
  -- one induction step: restriction modulo p^j is a bijection of root sets
  have step : ∀ j : ℕ, 1 ≤ j → (roots a (p^(j+1))).card = (roots a (p^j)).card := by
    intro j hj
    have hpj : 0 < p^j := pow_pos hp.pos j
    refine Finset.card_bij (fun r _ => r % p^j) ?_ ?_ ?_
    · intro r hr
      obtain ⟨hlt, hdvd⟩ := (hmem (p^(j+1)) r).mp hr
      rw [hmem]
      exact ⟨Nat.mod_lt r hpj, hdown (p^j) r (dvd_trans (hpowj j) hdvd)⟩
    · intro r₁ hr₁ r₂ hr₂ he
      obtain ⟨h₁, hd₁⟩ := (hmem (p^(j+1)) r₁).mp hr₁
      obtain ⟨h₂, hd₂⟩ := (hmem (p^(j+1)) r₂).mp hr₂
      have hd₁₀ : p^j ∣ r₁^2+a := dvd_trans (hpowj j) hd₁
      have hlt₁ : r₁ / p^j < p := Nat.div_lt_of_lt_mul (by rw [← pow_succ p j]; exact h₁)
      have hlt₂ : r₂ / p^j < p := Nat.div_lt_of_lt_mul (by rw [← pow_succ p j]; exact h₂)
      have hm₁ : r₁ % p^j + (r₁ / p^j) * p^j = r₁ := by rw [mul_comm, Nat.mod_add_div]
      have hm₂ : r₂ % p^j + (r₂ / p^j) * p^j = r₂ := by rw [mul_comm, Nat.mod_add_div]
      have hA : p^(j+1) ∣ (r₁ % p^j + (r₁ / p^j) * p^j)^2 + a := by rw [hm₁]; exact hd₁
      have hB : p^(j+1) ∣ (r₂ % p^j + (r₂ / p^j) * p^j)^2 + a := by rw [hm₂]; exact hd₂
      rw [← he] at hB
      have hdiv : r₁ / p^j = r₂ / p^j :=
        huniq j (r₁ % p^j) (r₁ / p^j) (r₂ / p^j) hj (Nat.mod_lt r₁ hpj)
          (hdown (p^j) r₁ hd₁₀) hA hB hlt₁ hlt₂
      rw [← hm₁, ← hm₂]
      rw [he, hdiv]
    · intro s hs
      obtain ⟨hs₁, hsd⟩ := (hmem (p^j) s).mp hs
      obtain ⟨t, ht, hsize, hdvd, hmod⟩ := hlift j s hj hs₁ hsd
      exact ⟨s + t * p^j, (hmem (p^(j+1)) (s + t * p^j)).mpr ⟨hsize, hdvd⟩, hmod⟩
  have main : ∀ n : ℕ, 0 < n → (roots a (p^n)).card = (roots a p).card := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact absurd hn (Nat.not_lt_zero 0)
    | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · rw [Nat.zero_add, pow_one]
      · rw [step n hn']
        exact ih hn'
  exact main k hk
