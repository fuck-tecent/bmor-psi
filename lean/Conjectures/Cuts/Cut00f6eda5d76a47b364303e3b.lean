import Mathlib

-- child 1 zh: 对每个偶数目标，精确计数任意多个完整模 18 周期的可配对剩余类，并给出每周期至少一个的下界。
-- child 1 en: Count admissible paired residues across arbitrary complete periods modulo 18 and give a uniform lower bound for every even target.
-- child 2 zh: 在五种允许的模 18 进程上，将剥去强制因子 3 的移位素数条件等价化为整系数线性形式的几乎素数条件。
-- child 2 en: Identify the normalized affine almost-prime condition after stripping the forced factor of three on each admissible progression modulo 18.
-- child 3 zh: 对每个至少为 5 的素数与每个目标剩余类，证明四个反射配对的筛线性形式能同时避开零。
-- child 3 en: Establish simultaneous nonvanishing of the four reflected sieve forms for every prime at least five and every target residue.
-- child 4 zh: 对局部可行的固定剩余类，证明归一化线性形式的素数与几乎素数配对只有给定幂次的例外。
-- child 4 en: Bound the exceptional set for reflected prime and normalized almost-prime affine pairs on locally admissible residue progressions with the specified power saving.

theorem Conjectures.Cuts.Cut00f6eda5d76a47b364303e3b
    (h₁ : by
  classical
  let R : Finset ℕ := {1,5,11,13,17}
  let B := fun m k : ℕ => ((Finset.range (18*k)).filter (fun t => t % 18 ∈ R ∧ (m % 18+18-t % 18) % 18 ∈ R)).card
  exact ∀ m k : ℕ, Even m → k ≤ B m k ∧ B m k = k * B m 1)
    (h₂ : by
  classical
  let R : Finset ℕ := {1,5,11,13,17}
  let s : ℕ → ℕ := fun a => if a % 3 = 1 then 6 else 18
  let c : ℕ → ℕ := fun a => if a % 3 = 1 then (a+2)/3 else a+2
  let ok := fun p : ℕ => 3 < p ∧ Nat.Prime p ∧ ¬ 9 ∣ p+2 ∧ ((p+2)/(if 3 ∣ p+2 then 3 else 1)).primeFactorsList.length ≤ 2
  let A := fun a u : ℕ => 3 < 18*u+a ∧ Nat.Prime (18*u+a) ∧ (s a*u+c a).primeFactorsList.length ≤ 2
  exact ∀ a ∈ R, ∀ u : ℕ, ok (18*u+a) ↔ A a u)
    (h₃ : by
  classical
  let R : Finset ℕ := {1,5,11,13,17}
  let s : ℕ → ℕ := fun a => if a % 3 = 1 then 6 else 18
  let c : ℕ → ℕ := fun a => if a % 3 = 1 then (a+2)/3 else a+2
  let F := fun (ℓ a : ℕ) (u : ZMod ℓ) => (18*u+a)*(s a*u+c a)
  exact ∀ a ∈ R, ∀ b ∈ R, ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ∀ z : ZMod ℓ, ∃ t : ZMod ℓ, F ℓ a t * F ℓ b (z-t) ≠ 0)
    (h₄ : by
  classical
  let R : Finset ℕ := {1,5,11,13,17}
  let s : ℕ → ℕ := fun a => if a % 3 = 1 then 6 else 18
  let c : ℕ → ℕ := fun a => if a % 3 = 1 then (a+2)/3 else a+2
  let A := fun a u : ℕ => 3 < 18*u+a ∧ Nat.Prime (18*u+a) ∧ (s a*u+c a).primeFactorsList.length ≤ 2
  let F := fun (ℓ a : ℕ) (u : ZMod ℓ) => (18*u+a)*(s a*u+c a)
  exact ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → ∃ E : Finset ℕ,
    (E.card : ℝ) ≤ C*(X:ℝ)^(1-(1/10000:ℝ)) ∧ ∀ m ∈ Finset.Icc 4 X, m ∉ E → Even m →
    ∀ a ∈ R, ∀ b ∈ R, (a+b) % 18=m % 18 → (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ∀ z : ZMod ℓ, ∃ t : ZMod ℓ, F ℓ a t * F ℓ b (z-t) ≠ 0) →
    ∃ u v : ℕ, A a u ∧ A b v ∧ (18*u+a)+(18*v+b)=m)
    : (by
  classical
  let ok := fun p : ℕ => 3 < p ∧ Nat.Prime p ∧ ¬ 9 ∣ p+2 ∧ ((p+2)/(if 3 ∣ p+2 then 3 else 1)).primeFactorsList.length ≤ 2
  exact ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → (((Finset.Icc 4 X).filter (fun m => Even m ∧ ¬ ∃ p q : ℕ, ok p ∧ ok q ∧ p+q=m)).card : ℝ) ≤ C*(X : ℝ)^(1-(1/10000 : ℝ))) := by
  classical
  rcases h₄ with ⟨C, hC, h⟩
  refine ⟨C, hC, fun X hX => ?_⟩
  obtain ⟨E, hE, hm⟩ := h X hX
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hE
  intro m hbad
  obtain ⟨hmX, hem, hn⟩ := Finset.mem_filter.mp hbad
  by_contra hme
  have hp := (h₁ m 1 hem).1
  have hh := Finset.card_pos.mp (show 0 < _ from hp)
  obtain ⟨a, ha⟩ := hh
  obtain ⟨ha0, ha1, hb⟩ := Finset.mem_filter.mp ha
  have haLt : a < 18 := Finset.mem_range.mp ha0
  rw [Nat.mod_eq_of_lt haLt] at ha1 hb
  let b := (m % 18 + 18 - a) % 18
  have hab : (a+b) % 18 = m % 18 := by dsimp [b]; omega
  obtain ⟨u,v,hu,hv,heq⟩ := hm m hmX hme hem a ha1 b hb hab (h₃ a ha1 b hb)
  exact hn ⟨_, _, (h₂ a ha1 u).2 hu, (h₂ b hb v).2 hv, heq⟩
