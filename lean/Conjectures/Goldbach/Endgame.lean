import Mathlib

theorem Conjectures.Goldbach.Endgame :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun t => (S n w t)^2*E (-(n:ℝ)*t)) t) (0:ℝ) 1 MeasureTheory.volume; let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re) → (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re) → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)) → ((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re)) → (∀ n:ℕ, I n w w=I n (low n) (low n)+2*I n (low n) (high n)+I n (high n) (high n)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (low n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (high n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → -(e*(n:ℝ))≤(I n (high n) (high n)).re) → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → ∃ p q:ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := by
  intro w E S Q arcs low high f I minor major htransfer hmajorfloor hsplit hsmallsmall
    hsmallbulk hbulkfloor
  have hminor_eq : ∀ n : ℕ, minor n = I n w w := by
    intro n
    dsimp only [minor, I]
    simp only [pow_two]
  refine htransfer hmajorfloor ?_
  intro e he
  have he4 : (0 : ℝ) < e / 4 := by linarith
  obtain ⟨N₁, hN₁⟩ := hsmallsmall (e / 4) he4
  obtain ⟨N₂, hN₂⟩ := hsmallbulk (e / 4) he4
  obtain ⟨N₃, hN₃⟩ := hbulkfloor (e / 4) he4
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn hEven
  have hn₁ : N₁ ≤ n := (le_max_left N₁ (max N₂ N₃)).trans hn
  have hn₂₃ : max N₂ N₃ ≤ n := (le_max_right N₁ (max N₂ N₃)).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left N₂ N₃).trans hn₂₃
  have hn₃ : N₃ ≤ n := (le_max_right N₂ N₃).trans hn₂₃
  have hLL := hN₁ n hn₁
  have hLH := hN₂ n hn₂
  have hHH := hN₃ n hn₃ hEven
  have hre : ∀ z : ℂ, -‖z‖ ≤ z.re := fun z => neg_le_of_abs_le (Complex.abs_re_le_norm z)
  have htwo : ∀ z : ℂ, ((2 : ℂ) * z).re = 2 * z.re := by
    intro z
    simp [Complex.mul_re]
  have b1 : -(e / 4 * (n : ℝ)) ≤ (I n (low n) (low n)).re := (neg_le_neg hLL).trans (hre _)
  have b2 : -(e / 4 * (n : ℝ)) ≤ (I n (low n) (high n)).re := (neg_le_neg hLH).trans (hre _)
  have b3 : -(e / 4 * (n : ℝ)) ≤ (I n (high n) (high n)).re := hHH
  have h4 : (4 : ℝ) * (e / 4 * (n : ℝ)) = e * (n : ℝ) := by ring
  rw [hminor_eq n, hsplit n]
  simp only [Complex.add_re, htwo]
  linarith [b1, b2, b3, h4]
