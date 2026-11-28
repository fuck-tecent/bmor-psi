import Mathlib

-- child 1 zh: 在每个对数平方短窗内，按目标归一化的奇素数对对数权总质量至少为 a(log x)²，其中 a>0 与起点无关。
-- child 1 en: Give a uniform positive lower first moment for the normalized odd-prime-pair logarithmic weights in every log-square window.
-- child 2 zh: 在每个同样的短窗内，归一化奇素数对权重的平方和至多为 b(log x)²，其中 b 与起点无关。
-- child 2 en: Bound the second moment of the normalized odd-prime-pair logarithmic weights uniformly in every such window.
-- child 3 zh: 对任意有限目标集，用按目标归一化的奇素数对对数权的一阶、二阶矩给出可表示目标数的柯西下界。
-- child 3 en: On every finite set of targets, bound the squared total normalized odd-prime-pair mass by the number of represented targets times the second moment.

theorem Conjectures.Cuts.Cut430ae16fb1dea113d8ccee8e
    (h₁ : let R := fun n : ℕ =>
      (∑ p ∈ (Finset.range (n+1)).filter (fun p =>
        Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p)),
        Real.log (p:ℝ) * Real.log ((n-p:ℕ):ℝ)) / (n:ℝ)
    ∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 2 ≤ x →
    let h := (Real.log x)^2
    let W := Finset.Ioc ⌊x⌋₊ ⌊x + 123*h⌋₊
    a*h ≤ ∑ n ∈ W, R n)
    (h₂ : let R := fun n : ℕ =>
      (∑ p ∈ (Finset.range (n+1)).filter (fun p =>
        Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p)),
        Real.log (p:ℝ) * Real.log ((n-p:ℕ):ℝ)) / (n:ℝ)
    ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, 2 ≤ x →
    let h := (Real.log x)^2
    let W := Finset.Ioc ⌊x⌋₊ ⌊x + 123*h⌋₊
    (∑ n ∈ W, (R n)^2) ≤ b*h)
    (h₃ : let R := fun n : ℕ =>
      (∑ p ∈ (Finset.range (n+1)).filter (fun p =>
        Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p)),
        Real.log (p:ℝ) * Real.log ((n-p:ℕ):ℝ)) / (n:ℝ)
    let represented := fun n : ℕ => 0 < ((Finset.range (n+1)).filter (fun p =>
      Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p))).card
    ∀ W : Finset ℕ, (∑ n ∈ W, R n)^2 ≤
      ((W.filter represented).card : ℝ) *
        ∑ n ∈ W, (R n)^2) :
    (let good := fun n : ℕ => ∃ p q : ℕ, Nat.Prime p ∧ Odd p ∧ Nat.Prime q ∧ Odd q ∧ p + q = n
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x →
    let h := (Real.log x)^2
    let W := Finset.Ioc ⌊x⌋₊ ⌊x + 123*h⌋₊
    1 + ⌊c*h⌋₊ ≤ (@Finset.filter ℕ good (Classical.decPred good) W).card) := by
  classical
  intro good
  obtain ⟨a, ha, haW⟩ := h₁
  obtain ⟨b, hb, hbW⟩ := h₂
  refine ⟨a^2 / (2*b), by positivity, ?_⟩
  intro x hx h W
  let R := fun n : ℕ =>
      (∑ p ∈ (Finset.range (n+1)).filter (fun p =>
        Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p)),
        Real.log (p:ℝ) * Real.log ((n-p:ℕ):ℝ)) / (n:ℝ)
  let T := W.filter good
  have hh : 0 < h := sq_pos_of_pos (Real.log_pos (by linarith : 1 < x))
  have low : a*h ≤ ∑ n ∈ W, R n := haW x hx
  have high : (∑ n ∈ W, (R n)^2) ≤ b*h := hbW x hx
  let represented := fun n : ℕ => 0 < ((Finset.range (n+1)).filter (fun p =>
      Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p))).card
  have eq_support : W.filter represented = T := by
    ext n
    simp only [T, Finset.mem_filter]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · intro hn
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hn
      obtain ⟨hr, hprime, hodd, hq, ho⟩ := Finset.mem_filter.mp hp
      have := Finset.mem_range.mp hr
      exact ⟨p, n-p, hprime, hodd, hq, ho, by omega⟩
    · rintro ⟨p, q, hprime, hodd, hq, ho, rfl⟩
      apply Finset.card_pos.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime, hodd, ?_⟩⟩
      simpa using And.intro hq ho
  have cs : (∑ n ∈ W, R n)^2 ≤ (T.card:ℝ) * ∑ n ∈ W, (R n)^2 := by
    rw [← eq_support]
    exact h₃ W
  have est : (a*h)^2 ≤ (T.card:ℝ)*(b*h) :=
    ((pow_le_pow_left₀ (mul_nonneg ha.le hh.le) low 2).trans cs).trans
      (mul_le_mul_of_nonneg_left high (Nat.cast_nonneg ..))
  have density : a^2*h ≤ (T.card:ℝ)*b := by
    apply le_of_mul_le_mul_right (a := h) _ hh
    linarith only [show a^2*h*h = (a*h)^2 by ring, est,
      show (T.card:ℝ)*b*h = (T.card:ℝ)*(b*h) by ring]
  have strict : a^2/(2*b)*h < (T.card:ℝ) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2*b)]
    nlinarith [mul_pos (sq_pos_of_pos ha) hh]
  have hfloor : ⌊a^2/(2*b)*h⌋₊ < T.card := (Nat.floor_lt (by positivity)).mpr strict
  change 1 + ⌊a^2/(2*b)*h⌋₊ ≤ T.card
  omega
