import Mathlib

theorem PEqualNP.Outside.L_goldbach_frontier_spatial_assembly_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let L₀ := fun n : ℕ => Nat.log 2 (n + 2); let M₀ := fun n : ℕ => ⌊(n:ℝ) / Real.sqrt (L₀ n : ℝ)⌋₊; let diagTerm := fun n : ℕ => (MeasureTheory.volume ((arcs n)ᶜ ∩ Set.Ioc (0:ℝ) 1)).toReal * (∑ p ∈ Finset.range (n+1), w p * w (n - p)); let sincKernel := fun (n q : ℕ) (m : ℤ) => (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Real.cos (2 * Real.pi * (m:ℝ) * (a:ℝ) / (q:ℝ))) * (Real.sin (2 * Real.pi * (m:ℝ) * ((Q n:ℝ) / ((q:ℝ)*(n:ℝ)))) / (Real.pi * (m:ℝ))); let offLowNear := fun n : ℕ => ∑ j ∈ Finset.range (n+1), ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => j + k ≠ n ∧ Int.natAbs ((j:ℤ) + (k:ℤ) - (n:ℤ)) ≤ M₀ n), w j * w k * ∑ q ∈ Finset.Icc 1 (L₀ n), sincKernel n q ((j:ℤ) + (k:ℤ) - (n:ℤ)); let offLowFar := fun n : ℕ => ∑ j ∈ Finset.range (n+1), ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => M₀ n < Int.natAbs ((j:ℤ) + (k:ℤ) - (n:ℤ))), w j * w k * ∑ q ∈ Finset.Icc 1 (L₀ n), sincKernel n q ((j:ℤ) + (k:ℤ) - (n:ℤ)); let offHighMod := fun n : ℕ => ∑ j ∈ Finset.range (n+1), ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => j + k ≠ n), w j * w k * ∑ q ∈ Finset.Ioc (L₀ n) (Q n), sincKernel n q ((j:ℤ) + (k:ℤ) - (n:ℤ)); let seriesLow := fun n : ℕ => (n:ℝ) * ∑ q ∈ Finset.Icc 1 (L₀ n), ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) / ((Nat.totient q : ℝ) ^ 2)) * (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Real.cos (2 * Real.pi * (n:ℝ) * (a:ℝ) / (q:ℝ))); (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (minor n).re = diagTerm n - offLowNear n - offLowFar n - offHighMod n) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → |offLowFar n| ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → |offLowNear n - seriesLow n| ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → offHighMod n + seriesLow n - diagTerm n ≤ e * (n : ℝ)) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (minor n).re := by
  intro _w _E _S _Q _arcs _f minor _L0 _M0 diagTerm _sincKernel offLowNear offLowFar offHighMod seriesLow hsplit hfar hnear hhigh e he
  obtain ⟨N₀, hN₀⟩ := hsplit
  obtain ⟨N₁, hN₁⟩ := hfar (e / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hnear (e / 3) (by positivity)
  obtain ⟨N₃, hN₃⟩ := hhigh (e / 3) (by positivity)
  refine ⟨N₀ + N₁ + N₂ + N₃, ?_⟩
  intro n hn heven
  have hn0 : N₀ ≤ n := by omega
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hn3 : N₃ ≤ n := by omega
  have h0 : (minor n).re = diagTerm n - offLowNear n - offLowFar n - offHighMod n := hN₀ n hn0
  have h2 : |offLowFar n| ≤ e / 3 * (n : ℝ) := hN₁ n hn1 heven
  have h3 : |offLowNear n - seriesLow n| ≤ e / 3 * (n : ℝ) := hN₂ n hn2 heven
  have h4 : offHighMod n + seriesLow n - diagTerm n ≤ e / 3 * (n : ℝ) := hN₃ n hn3 heven
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  rw [h0]
  linarith [h2'.1, h2'.2, h3'.1, h3'.2, h4]
