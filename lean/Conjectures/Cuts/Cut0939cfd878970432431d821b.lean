import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

-- Exact CRT identity: TwistedGoldbachLocalProduct.full_product,
-- from the accepted SharpSingularSeriesRatios module (board L-goldbach-sharp-singular-series-ratios).
-- The different-conductor common-lift injectivity follows the method of Qmhou in #4164.

open Finset DirichletCharacter
open scoped BigOperators




open DirichletCharacter Finset
open scoped BigOperators
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct


-- child 1 zh: 素数 p 整除偶数目标 m 时，在任意素数幂模数上证明归一化 Jacobi 和一行的三次矩至多为 1。
-- child 1 en: When p divides the even target, the normalized cubic Jacobi row moment at every power of p is at most one.
-- child 2 zh: 素数 p 不整除偶数目标 m 时，在任意素数幂模数上证明归一化 Jacobi 和一行的三次矩至多为 1 + 1/(p-2)^2。
-- child 2 en: When p does not divide the even target, bound the normalized cubic Jacobi row moment at every power of p by 1 + 1/(p-2)^2.
theorem Conjectures.Cuts.Cut0939cfd878970432431d821b
    (hDiv : ∀ (p e m : ℕ) [NeZero (p ^ e)], p.Prime → 0 < e → Even m → p ∣ m →
      ∀ (a : DirichletCharacter ℂ (p ^ e)) (T : Finset (DirichletCharacter ℂ (p ^ e))),
      let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
        ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
      (∑ b ∈ T, ‖Jm a b / Jm 1 1‖^3) ≤ 1)
    (hUnit : ∀ (p e m : ℕ) [NeZero (p ^ e)], p.Prime → 0 < e → Even m → ¬p ∣ m →
      ∀ (a : DirichletCharacter ℂ (p ^ e)) (T : Finset (DirichletCharacter ℂ (p ^ e))),
      let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
        ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
      (∑ b ∈ T, ‖Jm a b / Jm 1 1‖^3) ≤ 1 + (((p : ℝ) - 2)^2)⁻¹)
    : (by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) →
    (∑ b ∈ F, ‖S α b.2 m‖^3) ≤ 3 * ‖O m‖^3) := by
  classical
  let w (p : ℕ) : ℝ :=
    if p = 3 then 2 else if 5 ≤ p then ((p : ℝ) - 2)^2 / (((p : ℝ) - 2)^2 - 1) else 1

  have w_pos (p : ℕ) : 0 < w p := by
    unfold w
    split_ifs with h₁ h₂
    · norm_num
    · have hp : (5 : ℝ) ≤ p := by exact_mod_cast h₂
      apply div_pos <;> nlinarith [sq_nonneg ((p : ℝ) - 5)]
    · norm_num

  have one_le_w (p : ℕ) : 1 ≤ w p := by
    unfold w
    split_ifs with h₁ h₂
    · norm_num
    · have hp : (5 : ℝ) ≤ p := by exact_mod_cast h₂
      have h : 0 < ((p : ℝ) - 2)^2 - 1 := by nlinarith [sq_nonneg ((p : ℝ) - 5)]
      rw [le_div_iff₀ h]
      linarith
    · norm_num

  have local_weight_le {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
      1 + (((p : ℝ) - 2)^2)⁻¹ ≤ w p := by
    by_cases e : p = 3
    · subst p
      norm_num [w]
    · have b : 5 ≤ p := by
        have h := hp.two_le
        obtain ⟨k,hk⟩ := hp.odd_of_ne_two h2
        omega
      have b' : (5 : ℝ) ≤ p := by exact_mod_cast b
      have A : 0 < ((p : ℝ) - 2)^2 := pow_pos (by linarith) 2
      have B : 0 < ((p : ℝ) - 2)^2 - 1 := by nlinarith [sq_nonneg ((p : ℝ) - 5)]
      simp only [w, ite_eq_right e, ite_eq_left b, ← one_div]
      have H := one_div_le_one_div_of_le B (show ((p : ℝ) - 2)^2 - 1 ≤ ((p : ℝ) - 2)^2 by linarith)
      calc
        _ ≤ 1 + 1 / (((p : ℝ) - 2)^2 - 1) := by linarith
        _ = _ := by field_simp <;> ring

  have prefix_prod (n : ℕ) :
      (∏ k ∈ range n, w (k + 5)) = 3 * ((n : ℝ) + 2) / (2 * ((n : ℝ) + 3)) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [prod_range_succ, ih]
      have h0 : n + 5 ≠ 3 := by omega
      have h5 : 5 ≤ n + 5 := by omega
      simp only [w, ite_eq_right h0, ite_eq_left h5]
      push_cast
      change 3 * ((n:ℝ)+2) / (2*((n:ℝ)+3)) * (((n:ℝ)+5-2)^2 / (((n:ℝ)+5-2)^2-1)) =
        3 * ((n:ℝ)+1+2)/(2*((n:ℝ)+1+3))
      have a : 0 < (n : ℝ) + 2 := by positivity
      have b : 0 < (n : ℝ) + 3 := by positivity
      have c : 0 < (n : ℝ) + 4 := by positivity
      have fac : ((n : ℝ) + 5 - 2)^2 - 1 = ((n : ℝ) + 2)*((n : ℝ) + 4) := by ring
      rw [fac]
      have e : (n : ℝ) + 1 + 3 = (n : ℝ) + 4 := by ring
      rw [e]
      field_simp [a.ne',b.ne',c.ne']
      <;> ring

  have range_le (n : ℕ) : (∏ k ∈ range (n + 5), w k) ≤ 3 := by
    rw [Nat.add_comm, prod_range_add]
    simp_rw [Nat.add_comm 5]
    rw [prefix_prod]
    have h : (∏ k ∈ range 5, w k) = 2 := by norm_num [w, prod_range_succ]
    rw [h, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).2
    linarith

  have prod_le_three (S : Finset ℕ) : (∏ p ∈ S, w p) ≤ 3 := by
    classical
    let n := S.sup id
    have hSub : S ⊆ range (n + 5) := by
      intro a ha
      refine mem_range.mpr ((le_sup (f := id) ha).trans_lt ?_)
      change n < n + 5
      omega
    exact (prod_le_prod_of_subset_of_one_le₀ hSub (fun p _ => (w_pos p).le) (fun p _ _ => one_le_w p)).trans (range_le n)



  have lift_injective {q : ℕ} [NeZero q]
      {a b : Σ s : ℕ, DirichletCharacter ℂ s} (ha : a.2.IsPrimitive)
      (hb : b.2.IsPrimitive) (da : a.1 ∣ q) (db : b.1 ∣ q)
      (h : changeLevel da a.2 = changeLevel db b.2) : a = b := by
    obtain ⟨r,A⟩ := a
    obtain ⟨s,B⟩ := b
    have hcond := congrArg DirichletCharacter.conductor h
    rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at hcond
    change r = s at hcond
    subst s
    have hab := changeLevel_injective da h
    cases hab
    rfl

  have family_sum_le_product {ι : Type} [Fintype ι] [DecidableEq ι]
      {C : ι → Type} [∀ i, Fintype (C i)]
      (F : Type) [Fintype F] (f : F → ∀ i, C i) (inj : Function.Injective f)
      (g : ∀ i, C i → ℝ) (hg : ∀ i x, 0 ≤ g i x) :
      (∑ b : F, ∏ i, g i (f b i)) ≤ ∏ i, ∑ c : C i, g i c := by
    classical
    let W (v : ∀ i, C i) := ∏ i, g i (v i)
    rw [Fintype.prod_sum]
    change (∑ b : F, W (f b)) ≤ ∑ c, W c
    calc
      _ = ∑ c ∈ Finset.univ.image f, W c := by
        rw [Finset.sum_image (fun _ _ _ _ he => inj he)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ =>
        Finset.prod_nonneg (fun i _ => hg i (b i)))
  have cubic_at_common_level
      (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive)
      (m : ℕ) (hm : 0 < m) (he : Even m)
      (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
      (hF : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) :
      (∑ b ∈ F, ‖series α b.2 m‖^3) ≤
        3 * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖^3 := by
    classical
    let Q := r * ∏ b ∈ F, b.1
    letI : NeZero Q := ⟨mul_ne_zero (NeZero.ne r)
      (Finset.prod_ne_zero_iff.mpr (fun b hb => (hF b hb).1))⟩
    have hr : r ∣ Q := dvd_mul_right _ _
    have hs (b : F) : b.1.1 ∣ Q :=
      (Finset.dvd_prod_of_mem (fun b : Σ s : ℕ, DirichletCharacter ℂ s => b.1) b.2).trans
        (dvd_mul_left _ _)
    let q (i : Q.primeFactors) := (i : ℕ) ^ Q.factorization i
    have hp (i : Q.primeFactors) : Nat.Prime (i : ℕ) :=
      Nat.prime_of_mem_primeFactors i.2
    letI (i : Q.primeFactors) : NeZero (q i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
    letI (i : Q.primeFactors) : Fintype (DirichletCharacter ℂ (q i)) := Fintype.ofFinite _
    let E := ZMod.equivPi Q (NeZero.ne Q)
    let A (i : Q.primeFactors) := component E (changeLevel hr α) i
    let B (b : F) (i : Q.primeFactors) := component E (changeLevel (hs b) b.1.2) i
    let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖^3
    let G (i : Q.primeFactors) (χ : DirichletCharacter ℂ (q i)) :=
      ‖J (A i) χ (m : ZMod (q i)) / J 1 1 (m : ZMod (q i))‖^3
    have B_inj : Function.Injective B := by
      intro b c equality
      apply Subtype.ext
      apply lift_injective (hF _ b.2).2 (hF _ c.2).2 (hs b) (hs c)
      apply MulChar.ext
      intro u
      rw [reassemble E (changeLevel (hs b) b.1.2), reassemble E (changeLevel (hs c) c.1.2)]
      exact Finset.prod_congr rfl (fun i _ => congrArg (fun v => v i (E ↑u i)) equality)
    have point (b : F) : ‖series α b.1.2 m‖^3 = O * ∏ i, G i (B b i) := by
      letI : NeZero b.1.1 := ⟨(hF _ b.2).1⟩
      rw [full_product E hα (hF _ b.2).2 hr (hs b) m hm he, norm_mul, norm_prod, mul_pow]
      simp only [O, G, A, B, Finset.prod_pow]
    have nonneg (i : Q.primeFactors) (χ : DirichletCharacter ℂ (q i)) : 0 ≤ G i χ :=
      pow_nonneg (norm_nonneg _) _
    have local_bound (i : Q.primeFactors) : (∑ χ, G i χ) ≤ w i := by
      have epos : 0 < Q.factorization i := (hp i).factorization_pos_of_dvd (NeZero.ne Q) (Nat.dvd_of_mem_primeFactors i.2)
      by_cases h : (i : ℕ) ∣ m
      · exact (hDiv i (Q.factorization i) m (hp i) epos he h (A i) Finset.univ).trans
          (one_le_w i)
      · have h2 : (i : ℕ) ≠ 2 := fun h2 => h (h2 ▸ even_iff_two_dvd.mp he)
        exact (hUnit i (Q.factorization i) m (hp i) epos he h (A i) Finset.univ).trans
          (local_weight_le (hp i) h2)
    have product : (∏ i : Q.primeFactors, ∑ χ, G i χ) ≤ 3 := by
      calc
        _ ≤ ∏ i : Q.primeFactors, w i :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun x _ => nonneg i x))
            (fun i _ => local_bound i)
        _ = ∏ p ∈ Q.primeFactors, w p := by
          rw [← Finset.prod_attach Q.primeFactors w]
          rfl
        _ ≤ 3 := prod_le_three _
    calc
      _ = ∑ b : F, ‖series α b.1.2 m‖^3 := by
        rw [← Finset.sum_attach F (fun b => ‖series α b.2 m‖^3)]
        rfl
      _ = O * ∑ b : F, ∏ i, G i (B b i) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => point b)
      _ ≤ O * 3 := mul_le_mul_of_nonneg_left
        ((family_sum_le_product F B B_inj G nonneg).trans product) (by dsimp [O]; positivity)
      _ = _ := mul_comm _ _
  exact cubic_at_common_level
