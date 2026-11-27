import Mathlib

private lemma quad_pow_root_iff (p k : ℕ) (hp : p.Prime) (r : ℕ) :
    p^k ∣ r^2 ↔ p^(k - k/2) ∣ r := by
  by_cases hr : r = 0
  · subst hr; simp
  · rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hr),
        hp.pow_dvd_iff_le_factorization hr, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    omega

private lemma quad_count_multiples (p k : ℕ) (hp : p.Prime) :
    ((Finset.range (p^k)).filter (fun r => p^(k - k/2) ∣ r)).card = p^(k/2) := by
  have hsplit : k - k/2 + k/2 = k := by omega
  have hpoweq : p^k = p^(k - k/2) * p^(k/2) := by
    rw [← pow_add, hsplit]
  rw [hpoweq]
  have hpos : 0 < p^(k - k/2) := pow_pos hp.pos _
  rw [show (Finset.range (p^(k - k/2) * p^(k/2))).filter (fun r => p^(k - k/2) ∣ r)
        = (Finset.range (p^(k/2))).image (fun i => p^(k - k/2) * i) from by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hlt, ⟨i, rfl⟩⟩
      exact ⟨i, (Nat.mul_lt_mul_left hpos).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hpos).mpr hi, dvd_mul_right _ _⟩]
  rw [Finset.card_image_of_injective _ (fun a b h => Nat.mul_left_cancel hpos h)]
  simp

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_bad_roots :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ p a k : ℕ, p.Prime → 0<k → p^k ∣ a → (roots a (p^k)).card = p^(k/2) := by
  dsimp only
  intro p a k hp hk hdiv
  have hdvd (r : ℕ) : p^k ∣ r^2 + a ↔ p^k ∣ r^2 := by
    constructor
    · intro h
      have := Nat.dvd_sub h hdiv
      simpa [Nat.add_sub_cancel] using this
    · intro h
      exact dvd_add h hdiv
  have hfilter : (Finset.range (p^k)).filter (fun r => p^k ∣ r^2 + a)
      = (Finset.range (p^k)).filter (fun r => p^(k - k/2) ∣ r) := by
    apply Finset.filter_congr
    intro r _
    rw [hdvd r]
    exact quad_pow_root_iff p k hp r
  rw [hfilter]
  exact quad_count_multiples p k hp
