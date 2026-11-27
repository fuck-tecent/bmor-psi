import Mathlib

theorem PEqualNP.Outside.L_goldbach_frontier_medium_assembly_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Qqp := fun n : ℕ => ⌊Real.exp (Real.sqrt (Real.log (n:ℝ)))⌋₊; let Qzf := fun n : ℕ => ⌊(n:ℝ)^(1/10:ℝ)⌋₊; let K := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.range (n+1), E ((k:ℝ)*β); let medCoreBand := fun (n A B : ℕ) => intervalIntegral (fun t => {u : ℝ | ∃ q a : ℕ, A < q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧ |u - (a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let modelBand := fun (n A B : ℕ) => ∑ q ∈ Finset.Ioc A B, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), intervalIntegral (fun t => (((∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) * K n (t - (a:ℝ)/(q:ℝ)))^2 * E (-(n:ℝ)*t)) ((a:ℝ)/(q:ℝ) - (Q n:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q n:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let remSkirt := fun n : ℕ => intervalIntegral (fun t => ((wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → medCore n = medCoreBand n (Q n) (Qqp n) + medCoreBand n (Qqp n) (Qzf n) + medCoreBand n (Qzf n) (Q₁ n) ∧ modelBand n (Q n) (Q₁ n) = modelBand n (Q n) (Qqp n) + modelBand n (Qqp n) (Qzf n) + modelBand n (Qzf n) (Q₁ n) ∧ medSkirt n = lowSkirt n + remSkirt n) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (modelBand n (Q n) (Q₁ n)).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Q n) (Qqp n) - modelBand n (Q n) (Qqp n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qqp n) (Qzf n) - modelBand n (Qqp n) (Qzf n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qzf n) (Q₁ n) - modelBand n (Qzf n) (Q₁ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (remSkirt n).re) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (medCore n + medSkirt n).re := by
  intro w E S Q arcs f Q₁ H midArcs wideArcs medCore medSkirt Qqp Qzf K medCoreBand modelBand lowWideArcs lowSkirt remSkirt
  intro ⟨N₀,hdecomp⟩ hmodel hfirst hsecond hthird hlow hrem e he
  obtain ⟨N₁,h₁⟩ := hmodel (e/6) (by positivity)
  obtain ⟨N₂,h₂⟩ := hfirst (e/6) (by positivity)
  obtain ⟨N₃,h₃⟩ := hsecond (e/6) (by positivity)
  obtain ⟨N₄,h₄⟩ := hthird (e/6) (by positivity)
  obtain ⟨N₅,h₅⟩ := hlow (e/6) (by positivity)
  obtain ⟨N₆,h₆⟩ := hrem (e/6) (by positivity)
  refine ⟨N₀+N₁+N₂+N₃+N₄+N₅+N₆, ?_⟩
  intro n hn hEven
  obtain ⟨hc,hm,hs⟩ := hdecomp n (by omega)
  have b₁ := h₁ n (by omega) hEven
  have b₂ := h₂ n (by omega) hEven
  have b₃ := h₃ n (by omega) hEven
  have b₄ := h₄ n (by omega) hEven
  have b₅ := h₅ n (by omega) hEven
  have b₆ := h₆ n (by omega) hEven
  have a₂ := Complex.abs_re_le_norm (medCoreBand n (Q n) (Qqp n) - modelBand n (Q n) (Qqp n))
  have a₃ := Complex.abs_re_le_norm (medCoreBand n (Qqp n) (Qzf n) - modelBand n (Qqp n) (Qzf n))
  have a₄ := Complex.abs_re_le_norm (medCoreBand n (Qzf n) (Q₁ n) - modelBand n (Qzf n) (Q₁ n))
  have hcRe := congrArg Complex.re hc
  have hmRe := congrArg Complex.re hm
  have hsRe := congrArg Complex.re hs
  simp only [Complex.sub_re, Complex.add_re] at hcRe hmRe hsRe a₂ a₃ a₄ ⊢
  have e₂ := neg_abs_le ((medCoreBand n (Q n) (Qqp n)).re - (modelBand n (Q n) (Qqp n)).re)
  have e₃ := neg_abs_le ((medCoreBand n (Qqp n) (Qzf n)).re - (modelBand n (Qqp n) (Qzf n)).re)
  have e₄ := neg_abs_le ((medCoreBand n (Qzf n) (Q₁ n)).re - (modelBand n (Qzf n) (Q₁ n)).re)
  linarith
