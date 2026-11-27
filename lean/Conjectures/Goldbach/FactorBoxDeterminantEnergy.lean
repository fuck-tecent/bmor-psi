import Mathlib

private def determinant (x y : ℕ × ℕ) : ℤ := (x.1:ℤ)*y.2-(y.1:ℤ)*x.2

private theorem degreeBound (a b n H : ℕ) (hn : 0 < n) (ha : 0 < a)
    (F : Finset (ℕ × ℕ)) (fiber : ∀ z ∈ F, a*z.1 + b*z.2 = n) {x} (hx : x ∈ F) :
    (F.filter (fun y => x ≠ y ∧ (determinant x y).natAbs ≤ H)).card ≤
      2*(H * a.gcd b / n) := by
  classical
  let k := H * a.gcd b / n
  let t := fun y : ℕ × ℕ => a.gcdA b * ((y.2:ℤ)-x.2) + a.gcdB b * ((x.1:ℤ)-y.1)
  have eqn (z) (hz : z ∈ F) : (a:ℤ)*z.1 + (b:ℤ)*z.2 = n := by exact_mod_cast fiber z hz
  have d₁ (y) (hy : y ∈ F) : (n:ℤ)*((y.2:ℤ)-x.2) = a * determinant x y := by
    dsimp [determinant]
    linear_combination (x.2:ℤ) * eqn y hy - (y.2:ℤ) * eqn x hx
  have d₂ (y) (hy : y ∈ F) : (n:ℤ)*((x.1:ℤ)-y.1) = b * determinant x y := by
    dsimp [determinant]
    linear_combination (y.1:ℤ) * eqn x hx - (x.1:ℤ) * eqn y hy
  have scaled (y) (hy : y ∈ F) : (n:ℤ)*t y = a.gcd b * determinant x y := by
    dsimp [t]
    rw [Nat.gcd_eq_gcd_ab]
    linear_combination a.gcdA b * d₁ y hy + a.gcdB b * d₂ y hy
  have ng : (a.gcd b : ℤ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left b ha).ne'
  have nn : (n:ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have inj : (F : Set (ℕ × ℕ)).InjOn t := by
    intro y hy z hz heq
    have eqd : determinant x y = determinant x z := mul_left_cancel₀ ng <|
      (scaled y hy).symm.trans ((congrArg ((n:ℤ)*·) heq).trans (scaled z hz))
    have eq1 := mul_left_cancel₀ nn ((d₂ y hy).trans ((congrArg ((b:ℤ)*·) eqd).trans (d₂ z hz).symm))
    have eq2 := mul_left_cancel₀ nn ((d₁ y hy).trans ((congrArg ((a:ℤ)*·) eqd).trans (d₁ z hz).symm))
    exact Prod.ext (by omega) (by omega)
  have htx : t x = 0 := by simp [t]
  let I := (Finset.Icc (-(k:ℤ)) k).erase 0
  calc
    _ ≤ I.card := by
      apply Finset.card_le_card_of_injOn t
      · intro y hy
        obtain ⟨hy,hne,hle⟩ := Finset.mem_filter.mp hy
        have ht : t y ≠ 0 := fun h => hne (inj hx hy (htx.trans h.symm))
        have habs := congrArg Int.natAbs (scaled y hy)
        simp only [Int.natAbs_mul,Int.natAbs_natCast] at habs
        have hh : (t y).natAbs ≤ k := (Nat.le_div_iff_mul_le hn).mpr (by
          calc
            _ = a.gcd b * (determinant x y).natAbs := (Nat.mul_comm ..).trans habs
            _ ≤ H * a.gcd b := (Nat.mul_le_mul_left _ hle).trans_eq (Nat.mul_comm ..))
        apply Finset.mem_erase.mpr
        exact ⟨ht,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
      · exact fun _ hy _ hz => inj (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hz).1
    _ = _ := by
      rw [show I = (Finset.Icc (-(k:ℤ)) k).erase 0 from rfl,Finset.card_erase_of_mem (by simp),Int.card_Icc]
      change ((k : ℤ) + 1 - -(k:ℤ)).toNat - 1 = 2*k
      omega

private theorem graphBound {α : Type*} (F : Finset α) (R : α → α → Prop)
    [DecidableRel R] (hsym : ∀ x y, R x y ↔ R y x) (w : α → ℝ) (k : ℕ)
    (degree : ∀ x ∈ F, (F.filter (R x)).card ≤ k) :
    |∑ x ∈ F, ∑ y ∈ F.filter (R x), w x*w y| ≤ k * ∑ x ∈ F, (w x)^2 := by
  classical
  have swap : (∑ x ∈ F, ∑ y ∈ F.filter (R x), (w y)^2) =
      ∑ x ∈ F, ∑ _y ∈ F.filter (R x), (w x)^2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : R x y
    · simp [h, (hsym x y).mp h]
    · simp [h, (hsym y x).not.mpr h]
  have mass : (∑ x ∈ F, ∑ _y ∈ F.filter (R x), (w x)^2) ≤ k * ∑ x ∈ F, (w x)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    simp only [Finset.sum_const,nsmul_eq_mul]
    gcongr
    exact_mod_cast degree x hx
  have hpoint (x y : α) : |w x*w y| ≤ ((w x)^2 + (w y)^2)/2 := by
    rw [abs_mul]; nlinarith [sq_nonneg (|w x|-|w y|),sq_abs (w x),sq_abs (w y)]
  calc
    _ ≤ ∑ x ∈ F, ∑ y ∈ F.filter (R x), |w x*w y| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x ∈ F, ∑ y ∈ F.filter (R x), ((w x)^2 + (w y)^2)/2 :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpoint x y
    _ ≤ _ := by
      simp only [← Finset.sum_div,Finset.sum_add_distrib]
      rw [swap]
      linarith

theorem Conjectures.Goldbach.FactorBoxDeterminantEnergy :
    ∀ (n U A B H : ℕ), 0 < n → 0 < A → A ≤ B →
let F := fun (a b : ℕ) => ((Finset.Icc (U+1) (n/a)).product (Finset.Icc (U+1) (n/b))).filter (fun z => a*z.1 + b*z.2 = n)
let c := fun a : ℕ => ∑ d ∈ (Nat.divisors a).filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)
let w := fun (a b : ℕ) (z : ℕ × ℕ) => c a * ArithmeticFunction.vonMangoldt z.1 * (c b * ArithmeticFunction.vonMangoldt z.2)
let det := fun (x y : ℕ × ℕ) => ((x.1 : ℤ) * y.2 - (y.1 : ℤ) * x.2).natAbs
|∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, ∑ x ∈ F a b, ∑ y ∈ (F a b).filter (fun y => x ≠ y ∧ det x y ≤ H), w a b x * w a b y| ≤
∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, 2 * ((H * Nat.gcd a b / n : ℕ) : ℝ) * (∑ x ∈ F a b, (w a b x)^2) := by
  intro n U A B H hn hA hAB F c w det
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  have ha' := (Finset.mem_Icc.mp ha).1
  have sym (x y : ℕ × ℕ) : (x ≠ y ∧ det x y ≤ H) ↔ (y ≠ x ∧ det y x ≤ H) := by
    dsimp only [det]
    rw [ne_comm, ← Int.natAbs_neg ((x.1:ℤ)*y.2-(y.1:ℤ)*x.2),neg_sub]
  have hg := graphBound (F a b) _ sym (w a b) (2*(H*a.gcd b/n))
    (fun _ hx => degreeBound a b n H hn (by omega) (F a b)
      (fun _ hz => (Finset.mem_filter.mp hz).2) hx)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hg
