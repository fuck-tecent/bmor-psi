import Mathlib

-- child 1 zh: 在无界素数边长上，对四条纵移抛物线的竖直及割线判别式候选，截断所有实际整数共线三元组，删点数比边长的 5/2 倍少固定比例。
-- child 1 en: Along unbounded primes, hit all actual collinear triples among the vertical and secant-discriminant candidates on four shifted parabolas, with a fixed margin below five halves of the side length.
-- child 2 zh: 四条纵移抛物线的实际共线三元组必在竖直与割线判别式候选中。截断后余点有效，余点数加删点数恰为边长的四倍。
-- child 2 en: The vertical and secant-discriminant candidates include every actual collinear triple on four shifted parabolas. Hitting them leaves a valid grid set, with retained and deleted counts summing to four times the side length.
theorem Conjectures.Cuts.Cut656b7b66e6dd8e42525a4df9
    (budget : ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
  ∃ A b : ZMod p, A ≠ 0 ∧ ∃ L : Fin 4 → ZMod p, Function.Injective L ∧
  ∃ D : Finset (Fin p × Fin 4), (D.card : ℝ) ≤ (5/2-d)*(p : ℝ) ∧ (let X := fun (u : Fin p × Fin 4) => (u.1.val : ZMod p);
let Y := fun (u : Fin p × Fin 4) => A * (X u)^2 + b * X u + L u.2;
let pt := fun (u : Fin p × Fin 4) => (u.1.val, (Y u).val);
let col := fun (x y z : ℕ × ℕ) =>
  ((y.1 : ℤ) - x.1) * ((z.2 : ℤ) - x.2) = ((y.2 : ℤ) - x.2) * ((z.1 : ℤ) - x.1);
let shadow := fun (i j k : Fin p × Fin 4) =>
  if i.1 = j.1 then k.1 = i.1 else
    let m := (Y j - Y i) * (X j - X i)⁻¹;
    let v := Y i - m*X i;
    (2*A*X k + b-m)^2 = (b-m)^2 - 4*A*(L k.2-v);∀ i j k : Fin p × Fin 4, i ≠ j → i ≠ k → j ≠ k → shadow i j k →
    col (pt i) (pt j) (pt k) → i ∈ D ∨ j ∈ D ∨ k ∈ D))
    (support : ∀ (p : ℕ), p.Prime → ∀ A b : ZMod p, ∀ L : Fin 4 → ZMod p, Function.Injective L →
  ∀ D : Finset (Fin p × Fin 4), let X := fun (u : Fin p × Fin 4) => (u.1.val : ZMod p);
let Y := fun (u : Fin p × Fin 4) => A * (X u)^2 + b * X u + L u.2;
let pt := fun (u : Fin p × Fin 4) => (u.1.val, (Y u).val);
let col := fun (x y z : ℕ × ℕ) =>
  ((y.1 : ℤ) - x.1) * ((z.2 : ℤ) - x.2) = ((y.2 : ℤ) - x.2) * ((z.1 : ℤ) - x.1);
let shadow := fun (i j k : Fin p × Fin 4) =>
  if i.1 = j.1 then k.1 = i.1 else
    let m := (Y j - Y i) * (X j - X i)⁻¹;
    let v := Y i - m*X i;
    (2*A*X k + b-m)^2 = (b-m)^2 - 4*A*(L k.2-v);(∀ i j k : Fin p × Fin 4, i ≠ j → i ≠ k → j ≠ k → shadow i j k →
    col (pt i) (pt j) (pt k) → i ∈ D ∨ j ∈ D ∨ k ∈ D) →
    let S := (Finset.univ \ D).image pt;
    ((∀ u ∈ S, u.1 < p ∧ u.2 < p) ∧
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k → ¬col i j k)) ∧
      S.card + D.card = 4*p) :
  (let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ S : Finset (ℕ × ℕ), valid n S ∧ (3/2+d)*(n:ℝ) ≤ (S.card:ℝ)) := by
  obtain ⟨d, hd, w⟩ := budget
  refine ⟨d, hd, ?_⟩
  intro B
  obtain ⟨p, hBp, hp, A, b, _, L, hL, D, hD, hHit⟩ := w B
  obtain ⟨hValid, hCard⟩ := support p hp A b L hL D hHit
  refine ⟨p, hBp, _, hValid, ?_⟩
  have hCast := congrArg (fun n : ℕ => (n : ℝ)) hCard
  push_cast at hCast
  nlinarith only [hCast,hD]
