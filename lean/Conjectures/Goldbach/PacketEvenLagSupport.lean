import Mathlib

open scoped Classical

theorem Conjectures.Goldbach.PacketEvenLagSupport :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ n : ℕ, 8 ≤ n → ∀ h : ℕ, Odd h → A n h (high n) = 0 ∧ A n h model = 0 := by
  intro w E S Q arcs low high I L K B U V A model short long n hn h hh
  have kill (a : ℕ → ℝ) (ha : ∀ k, k % 2 = 0 → a k = 0) : A n h a = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    obtain ⟨j, hj⟩ := hh
    by_cases hk : k % 2 = 0
    · rw [ha k hk, zero_mul]
    · rw [ha (k+h) (by omega), mul_zero]
  constructor
  · apply kill
    intro k hk
    by_cases hp : k.Prime
    · have h₂ : k = 2 := hp.eq_two_or_odd.resolve_right (by omega)
      subst k
      simp [high, low, hn]
    · simp [high, low, w, hp]
  · apply kill
    intro k hk
    have hd : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk
    have hncp := Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) hd (by decide : 2 ∣ 30)
    simp [model, hncp]
