import Mathlib

private def squarePair (m : ℕ) := m.sqrt.Prime ∧ m.sqrt^2 = m
private instance (m : ℕ) : Decidable (squarePair m) := inferInstanceAs (Decidable (m.sqrt.Prime ∧ m.sqrt^2 = m))
private def mixedPair (m : ℕ) := ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a < b ∧ a*b=m

private theorem twoLength {a b : ℕ} (ha : a.Prime) (hb : b.Prime) :
    (a*b).primeFactorsList.length = 2 := by
  simpa [Nat.primeFactorsList_prime ha, Nat.primeFactorsList_prime hb] using
    (Nat.perm_primeFactorsList_mul ha.ne_zero hb.ne_zero).length_eq

private theorem smallCases {m : ℕ} (hm : 0 < m) (hl : m.primeFactorsList.length ≤ 2) :
    m=1 ∨ m.Prime ∨ squarePair m ∨ mixedPair m := by
  have prod := Nat.prod_primeFactorsList hm.ne'
  have primes := @Nat.prime_of_mem_primeFactorsList m
  cases h : m.primeFactorsList with
  | nil => simp [h] at prod; exact Or.inl prod.symm
  | cons a l =>
    have ha := primes (show a ∈ m.primeFactorsList by simp [h])
    cases l with
    | nil => simp [h] at prod; exact Or.inr (Or.inl (prod ▸ ha))
    | cons b l =>
      have hb := primes (show b ∈ m.primeFactorsList by simp [h])
      have he : l = [] := by simpa [h] using hl
      subst l
      simp [h] at prod
      by_cases hab : a=b
      · subst b
        exact Or.inr (Or.inr (Or.inl (by simpa [squarePair, ← prod, Nat.sqrt_eq, sq] using ha)))
      · right; right; right
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · exact ⟨a,b,ha,hb,hlt,prod⟩
        · exact ⟨b,a,hb,ha,hgt,by simpa [Nat.mul_comm] using prod⟩

private theorem disjointPairs {m : ℕ} (hs : squarePair m) (hd : mixedPair m) : False := by
  obtain ⟨hc,he⟩ := hs
  obtain ⟨a,b,ha,hb,hab,he'⟩ := hd
  have f (p : ℕ) (hp : p.Prime) (hdvd : p ∣ a*b) : p=m.sqrt := by
    rw [he',← he,sq] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hc).mp ((hp.dvd_mul.mp hdvd).elim id id)
  exact hab.ne ((f a ha (dvd_mul_right ..)).trans (f b hb (dvd_mul_left ..)).symm)

open scoped Classical in
private theorem indicators (m : ℕ) :
    (if 0 < m ∧ m.primeFactorsList.length≤2 then 1 else 0 : ℕ) =
    (if m.Prime then 1 else 0) + (if squarePair m then 1 else 0) +
    (if mixedPair m then 1 else 0) + (if m=1 then 1 else 0) := by
  classical
  have hprime (h : m.Prime) : 0 < m ∧ m.primeFactorsList.length=1 := by
    simp [h.pos, Nat.primeFactorsList_prime h]
  have hsquare (h : squarePair m) : 1 < m ∧ m.primeFactorsList.length=2 := by
    obtain ⟨hc,he⟩ := h
    have hu := twoLength hc hc
    rw [← sq,he] at hu
    exact ⟨by have := hc.two_le; nlinarith [he],hu⟩
  have hmix (h : mixedPair m) : 1 < m ∧ m.primeFactorsList.length=2 := by
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := h
    exact ⟨by have := ha.two_le; have := hb.two_le; nlinarith, twoLength ha hb⟩
  by_cases h : m=1
  · subst m
    have hn : ¬ squarePair 1 := fun t => by have := (hsquare t).1; omega
    have hm : ¬ mixedPair 1 := fun t => by have := (hmix t).1; omega
    simp [hn,hm,Nat.not_prime_one]
  · have hcases := @smallCases m
    have hdis := @disjointPairs m
    split_ifs <;> first | rfl | (exfalso; grind)

theorem Conjectures.Goldbach.FiniteChenUnweightedCountPartition :
    ∀ n : ℕ, let P := (Finset.range (n+1)).filter Nat.Prime; let C := P.filter (fun p => 0<n-p ∧ (n-p).primeFactorsList.length≤2); let G := P.filter (fun p => (n-p).Prime); let S := P.filter (fun p => (Nat.sqrt (n-p)).Prime ∧ (Nat.sqrt (n-p))^2=n-p); let D := P.filter (fun p => ((Finset.Icc 2 n).filter (fun r => r.Prime ∧ ((Finset.Ioc r n).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty); C.card = G.card + S.card + D.card + (if (n-1).Prime then 1 else 0) := by
  classical
  intro n P C G S D
  let small := fun p => 0 < n-p ∧ (n-p).primeFactorsList.length ≤ 2
  have mix (p : ℕ) (hp : p ∈ P) :
      ((Finset.Icc 2 n).filter (fun r => r.Prime ∧ ((Finset.Ioc r n).filter
      (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty ↔ mixedPair (n-p) := by
    have hpn := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    simp only [Finset.filter_nonempty_iff,Finset.mem_Icc,Finset.mem_Ioc]
    constructor
    · rintro ⟨r,hr,hrp,v,hv,hvp,he⟩
      exact ⟨r,v,hrp,hvp,hv.1,by omega⟩
    · rintro ⟨r,v,hr,hv,hrv,he⟩
      have hvn := (Nat.le_mul_of_pos_left v hr.pos)
      exact ⟨r,⟨hr.two_le,by omega⟩,hr,v,⟨hrv,by omega⟩,hv,by omega⟩
  have hD : D = P.filter (fun p => mixedPair (n-p)) := by
    ext p
    simp only [D,Finset.mem_filter]
    exact and_congr_right fun hp => mix p hp
  have hone : (P.filter (fun p => n-p=1)).card = (if (n-1).Prime then 1 else 0) := by
    by_cases h : (n-1).Prime
    · have H : P.filter (fun p => n-p=1) = {n-1} := by
        ext p
        simp only [P,Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
        have := h.two_le
        constructor <;> intro t
        · omega
        · subst p; exact ⟨⟨by omega,h⟩,by omega⟩
      simp [H,h]
    · have H : P.filter (fun p => n-p=1) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
        have hpn : p=n-1 := by omega
        exact h (hpn ▸ (Finset.mem_filter.mp hp).2)
      simp [H,h]
  rw [hD,← hone]
  simp only [C,G,S,Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hi := indicators (n-p)
  unfold squarePair at hi
  by_cases h₁ : 0 < n-p ∧ (n-p).primeFactorsList.length ≤ 2 <;>
    by_cases h₂ : (n-p).Prime <;>
    by_cases h₃ : (n-p).sqrt.Prime ∧ (n-p).sqrt^2 = n-p <;>
    by_cases h₄ : mixedPair (n-p) <;>
    by_cases h₅ : n-p=1 <;>
    simpa only [h₁,h₂,h₃,h₄,h₅,if_true,if_false] using hi
