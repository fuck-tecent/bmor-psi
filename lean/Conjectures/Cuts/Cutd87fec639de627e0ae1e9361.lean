import Mathlib

open scoped BigOperators

theorem Conjectures.Cuts.Cutd87fec639de627e0ae1e9361
    (h₁ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let rho := fun h : ℕ => (2:ℝ)^(if 3∣h then 1 else 0) * (3*(if 5∣h then (0:ℝ) else 1) + 4*(if 5∣h then (1:ℝ) else 0)); let P := fun n : ℕ => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, (A n h (high n) - (n-h:ℝ)*((15:ℝ)/32)*rho h)*V n h); ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → P n ≤ ((1:ℝ)/250)*(n:ℝ))
    (h₂ : let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let rho := fun h : ℕ => (2:ℝ)^(if 3∣h then 1 else 0) * (3*(if 5∣h then (0:ℝ) else 1) + 4*(if 5∣h then (1:ℝ) else 0)); let Qpiece := fun n : ℕ => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, ((n-h:ℝ)*((15:ℝ)/32)*rho h - A n h model)*V n h); ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → Qpiece n ≤ (-((1:ℝ)/312))*(n:ℝ)) :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → long n (high n) - long n model ≤ (n:ℝ)/1152 := by

  classical
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  let E : ℝ → ℂ := fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let S : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun n u t => ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let low : ℕ → ℕ → ℝ := fun n k => if k ^ 3 ≤ n then w k else 0
  let high : ℕ → ℕ → ℝ := fun n k => w k - low n k
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let P : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, (A n h (high n) - (n - h : ℝ) * ((15 : ℝ) / 32) * rho h) * V n h)
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  let long : ℕ → (ℕ → ℝ) → ℝ := fun n a => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, A n h a * V n h)

  obtain ⟨N₁, hP⟩ := h₁
  obtain ⟨N₂, hQ⟩ := h₂
  have hPn : ∀ n : ℕ, N₁ ≤ n → Even n → P n ≤ ((1 : ℝ) / 250) * (n : ℝ) := by
    intro n hn hEven
    have h := hP n hn hEven
    simpa only [P] using h
  have hQn : ∀ n : ℕ, N₂ ≤ n → Even n → Q n ≤ (-((1 : ℝ) / 312)) * (n : ℝ) := by
    intro n hn hEven
    have h := hQ n hn hEven
    simpa only [Q] using h
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn hEven
  change long n (high n) - long n model ≤ (n : ℝ) / 1152
  have h1n : P n ≤ ((1 : ℝ) / 250) * (n : ℝ) := hPn n (le_trans (le_max_left N₁ N₂) hn) hEven
  have h2n : Q n ≤ (-((1 : ℝ) / 312)) * (n : ℝ) := hQn n (le_trans (le_max_right N₁ N₂) hn) hEven
  have hid : long n (high n) - long n model = P n + Q n := by
    dsimp only [long, P, Q]
    rw [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hid]
  have hconst : ((1 : ℝ) / 250 - (1 : ℝ) / 312) ≤ (1 : ℝ) / 1152 := by norm_num
  have hsum : P n + Q n ≤ ((1 : ℝ) / 250 - (1 : ℝ) / 312) * (n : ℝ) := by linarith
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : ((1 : ℝ) / 250 - (1 : ℝ) / 312) * (n : ℝ) ≤ ((1 : ℝ) / 1152) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hconst hnonneg
  linarith
