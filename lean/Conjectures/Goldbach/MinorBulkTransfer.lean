import Mathlib

/-! A one-sided bound at every sufficiently large even target survives the two
small terms in the catalogue's three-term minor-arc decomposition. -/

private theorem of_minor_parts {total low mixed bulk : ℕ → ℂ}
    (split : ∀ n, total n = low n + 2 * mixed n + bulk n)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖low n‖ ≤ ε * (n : ℝ))
    (hm : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖mixed n‖ ≤ ε * (n : ℝ))
    (hb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n → -(ε * (n : ℝ)) ≤ (bulk n).re) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n → -(ε * (n : ℝ)) ≤ (total n).re := by
  intro ε hε
  have hpos : 0 < ε / 4 := by positivity
  obtain ⟨L, hL⟩ := hl (ε / 4) hpos
  obtain ⟨M, hM⟩ := hm (ε / 4) hpos
  obtain ⟨B, hB⟩ := hb (ε / 4) hpos
  refine ⟨max L (max M B), ?_⟩
  intro n hn heven
  have hlower := (abs_le.mp ((Complex.abs_re_le_norm (low n)).trans (hL n (by omega)))).1
  have hmixed := (abs_le.mp ((Complex.abs_re_le_norm (mixed n)).trans (hM n (by omega)))).1
  have hbulk := hB n (by omega) heven
  rw [split n]
  simp only [two_mul, Complex.add_re]
  linarith

theorem Conjectures.Goldbach.MinorBulkTransfer :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
    let high := fun (n k : ℕ) => w k-low n k;
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t);
    let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume;
    (∀ n:ℕ,I n w w=I n (low n) (low n)+2*I n (low n) (high n)+I n (high n) (high n)) →
    (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (low n)‖≤e*(n:ℝ)) →
    (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (high n)‖≤e*(n:ℝ)) →
    (∀ e:ℝ,0<e → ∃ N:ℕ,∀ n≥N, Even n → -(e*(n:ℝ))≤(I n (high n) (high n)).re) →
    ∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re := by
  dsimp only
  intro split low mixed bulk
  simpa only [pow_two] using of_minor_parts split low mixed bulk
