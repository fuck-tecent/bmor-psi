import Mathlib

private def base (j : Fin 6) : ℕ := [13,47,71,127,23,199].getD j 0
private def cand (j : Fin 6) (i : Fin 5) : ℕ := base j + 210 * i
private def modp (k : Fin 4) : ℕ := [11,13,17,19].getD k 0

set_option maxRecDepth 20000 in
private theorem base_cover : ∀ t : Fin 210, t.val % 2 = 0 → ∃ j : Fin 6,
    t.val % 2 ≠ base j % 2 ∧ t.val % 3 ≠ base j % 3 ∧
    t.val % 5 ≠ base j % 5 ∧ t.val % 7 ≠ base j % 7 := by decide

set_option maxRecDepth 20000 in
private theorem wheel (n : ℕ) (hn : 1041 ≤ n) (he : Even n) :
    ∃ p : ℕ, p.Prime ∧ 2 ≤ n-p ∧ ∀ d ∈ (n-p).primeFactorsList, 23 ≤ d := by
  let t : Fin 210 := ⟨n % 210, Nat.mod_lt _ (by decide)⟩
  obtain ⟨j,h₂,h₃,h₅,h₇⟩ := base_cover t (by rcases he with ⟨m, hm⟩; dsimp [t]; omega)
  let bad (k : Fin 4) (i : Fin 5) : Prop := n % modp k = cand j i % modp k
  classical
  let avoid (k : Fin 4) : Fin 5 := if h : ∃ i, bad k i then h.choose else 0
  have hf : ¬ Function.Surjective avoid := fun hs => by
    have hh := Fintype.card_le_of_surjective avoid hs
    simp at hh
  obtain ⟨i,hi⟩ : ∃ i, ∀ k, avoid k ≠ i := by simpa [Function.Surjective] using hf
  have hinj : ∀ (a : Fin 6) (k : Fin 4) (u v : Fin 5),
      cand a u % modp k = cand a v % modp k → u = v := by decide
  have hg (k : Fin 4) : ¬ bad k i := by
    intro h
    have hx : ∃ u, bad k u := ⟨i,h⟩
    apply hi k
    dsimp only [avoid]
    rw [dite_eq_left hx]
    exact hinj j k _ _ (hx.choose_spec.symm.trans h)
  have ht : ∀ (a : Fin 6) (u : Fin 5), (cand a u).Prime ∧ cand a u ≤ 1039 := by decide
  have hp := ht j i
  refine ⟨cand j i,hp.1,by omega,?_⟩
  intro d hd
  have hprime := Nat.prime_of_mem_primeFactorsList hd
  have hdiv := Nat.dvd_of_mem_primeFactorsList hd
  have hmod : cand j i % d = n % d := (Nat.modEq_iff_dvd' (by omega)).2 hdiv
  by_contra! hlt
  have hsmall : d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 11 ∨ d = 13 ∨ d = 17 ∨ d = 19 := by
    have small : ∀ z : Fin 23, z.val.Prime → z.val = 2 ∨ z.val = 3 ∨ z.val = 5 ∨
        z.val = 7 ∨ z.val = 11 ∨ z.val = 13 ∨ z.val = 17 ∨ z.val = 19 := by decide
    exact small ⟨d,hlt⟩ hprime
  rcases hsmall with h|h|h|h|h|h|h|h <;> subst d
  · dsimp [cand] at hmod; dsimp [t] at h₂; omega
  · dsimp [cand] at hmod; dsimp [t] at h₃; omega
  · dsimp [cand] at hmod; dsimp [t] at h₅; omega
  · dsimp [cand] at hmod; dsimp [t] at h₇; omega
  · exact hg 0 hmod.symm
  · exact hg 1 hmod.symm
  · exact hg 2 hmod.symm
  · exact hg 3 hmod.symm

private theorem list_pow (c : ℕ) (l : List ℕ) (h : ∀ d ∈ l, c ≤ d) :
    c ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact Nat.mul_le_mul (h x (by simp)) (ih (fun d hd => h d (by simp [hd])))

private theorem exp_nat_bound (k : ℕ) :
    Real.exp (k : ℝ) ≤ (2719/1000 : ℝ)^k := by
  rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by simp]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans (by norm_num)) _

private theorem cutoffs :
    Real.exp (Real.exp 5) < (23:ℝ)^48 ∧ Real.exp (Real.exp (19/5)) < (23:ℝ)^15 := by
  have h5 : Real.exp 5 < 149 := (exp_nat_bound 5).trans_lt (by norm_num)
  have h19 : Real.exp (19/5) < 46 := by
    by_contra! h
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 46) h 5
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    exact (not_le_of_gt ((exp_nat_bound 19).trans_lt (by norm_num : (2719/1000:ℝ)^19 < 46^5))) (by norm_num at *; assumption)
  constructor
  · exact (Real.exp_lt_exp.mpr h5).trans ((exp_nat_bound 149).trans_lt (by norm_num))
  · exact (Real.exp_lt_exp.mpr h19).trans ((exp_nat_bound 46).trans_lt (by norm_num))

theorem PEqualNP.Outside.L_goldbach_finite_rough_fourteen_fortyseven :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp 5) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 47 ∧ ((n:ℝ) < Real.exp (Real.exp (19/5)) → (n-p).primeFactorsList.length ≤ 14) := by
  intro n hn he hmax
  by_cases hlarge : 1041 ≤ n
  · obtain ⟨p,hp,hd,hrough⟩ := wheel n hlarge he
    have hb := list_pow 23 _ hrough
    rw [Nat.prod_primeFactorsList (by omega)] at hb
    have hb' : 23 ^ (n-p).primeFactorsList.length ≤ n := hb.trans (Nat.sub_le _ _)
    have bound (k : ℕ) (hk : (n:ℝ) < 23^k) : (n-p).primeFactorsList.length < k := by
      by_contra! h
      have hbad := (Nat.pow_le_pow_right (by decide : 0 < 23) h).trans hb'
      exact hk.not_ge (by exact_mod_cast hbad)
    exact ⟨p,hp,hd,by have := bound 48 (hmax.trans cutoffs.1); omega,
      fun hx => by have := bound 15 (hx.trans cutoffs.2); omega⟩
  · refine ⟨2,by decide,by omega,?_⟩
    have hb := list_pow 2 (n-2).primeFactorsList (fun d hd => (Nat.prime_of_mem_primeFactorsList hd).two_le)
    rw [Nat.prod_primeFactorsList (by omega)] at hb
    have hh : (n-2).primeFactorsList.length ≤ 14 := by
      by_contra! h
      have hbad := (Nat.pow_le_pow_right (by decide : 0 < 2) h).trans hb
      norm_num at hbad
      omega
    exact ⟨by omega, fun _ => hh⟩
