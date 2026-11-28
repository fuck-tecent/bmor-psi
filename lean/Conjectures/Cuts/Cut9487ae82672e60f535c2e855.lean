import Mathlib

-- child 1 zh: 对首项和总和均为平方的本原三元组 u²+(v²−u²)=v²，证明每个正 ε 的统一 abc 高度上界。
-- child 1 en: Establish the uniform abc height bound for every positive epsilon on the primitive square triples u²+(v²−u²)=v² with coprime roots u<v.
-- child 2 zh: 将非相等的互素正加数提升为这种平方三元组，使总和至少为原和平方的四分之一，根基至多为原根基乘四倍原和。
-- child 2 en: Lift any pair of unequal positive coprime summands to a square triple whose sum is at least one quarter of the square of the old sum and whose radical is at most four times the old sum times the old radical.

theorem Conjectures.Cuts.Cut9487ae82672e60f535c2e855
    (hRestricted : let rad := fun (n : ℕ) => n.primeFactors.prod id;
      ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, ∀ u v : ℕ, 0 < u → u < v → u.Coprime v →
      Real.log ((v^2 : ℕ):ℝ) ≤ (1+δ) * Real.log ((rad (u^2*(v^2-u^2)*v^2):ℕ):ℝ) + K)
    (hLift : let rad := fun (n : ℕ) => n.primeFactors.prod id;
      ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → a ≠ b →
      ∃ u v : ℕ, 0 < u ∧ u < v ∧ u.Coprime v ∧
        (a+b)^2 ≤ 4*v^2 ∧
        rad (u^2*(v^2-u^2)*v^2) ≤ 4*(a+b)*rad (a*b*(a+b))) :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → h a b ≤ (1+ε)*r a b+C) := by
  classical
  dsimp only
  intro ε hε
  let δ := ε/(ε+2)
  have hDen : 0 < ε+2 := by linarith
  have hδ : 0 < δ := div_pos hε hDen
  have hδOne : δ < 1 := by
    dsimp [δ]; apply (div_lt_one hDen).2; linarith
  have hCoeff : (1-δ)*(1+ε) = 1+δ := by
    dsimp [δ]; field_simp; ring
  obtain ⟨K,hSquare⟩ := hRestricted δ hδ
  let C := max (Real.log 2) ((K+(2+δ)*Real.log 4)/(1-δ))
  refine ⟨C,?_⟩
  intro a b ha hb hCop
  let c := a+b
  let rad (n : ℕ) := n.primeFactors.prod id
  let R := rad (a*b*c)
  have hc : 0 < (c:ℝ) := by dsimp [c]; push_cast; positivity
  have radPos (n : ℕ) : 0 < rad n := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hR : 0 < (R:ℝ) := by exact_mod_cast radPos _
  change Real.log ((a:ℝ)+b) ≤ (1+ε)*Real.log (R:ℝ)+C
  rw [show (a:ℝ)+b = (c:ℝ) by simp [c]]
  by_cases heq : a=b
  · subst b
    have h1 : a = 1 := by simpa [Nat.Coprime] using hCop
    have hlogR : 0 ≤ Real.log (R:ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ R from radPos _)
    have hc2 : c=2 := by simp [c,h1]
    rw [hc2]
    norm_num only [Nat.cast_ofNat]
    exact (le_max_left _ _).trans (le_add_of_nonneg_left (mul_nonneg (by linarith) hlogR))
  obtain ⟨u,v,hu,huv,huvCop,hHeight,hRad⟩ := hLift a b ha hb hCop heq
  let R' := rad (u^2*(v^2-u^2)*v^2)
  have hvR : 0 < (v:ℝ) := by exact_mod_cast (hu.trans huv)
  have hR' : 0 < (R':ℝ) := by exact_mod_cast radPos _
  have hHeightR : (c:ℝ)^2 ≤ 4 * (v:ℝ)^2 := by exact_mod_cast hHeight
  have hRadR : (R':ℝ) ≤ 4 * (c:ℝ) * (R:ℝ) := by exact_mod_cast hRad
  have hHeightLog := Real.log_le_log (pow_pos hc 2) hHeightR
  rw [Real.log_mul (by norm_num) (pow_pos hvR 2).ne', Real.log_pow] at hHeightLog
  norm_num only [Nat.cast_ofNat] at hHeightLog
  have hRadLog := Real.log_le_log hR' hRadR
  rw [Real.log_mul (mul_pos (by norm_num) hc).ne' hR.ne',Real.log_mul (by norm_num) hc.ne'] at hRadLog
  have hBound := hSquare u v hu huv huvCop
  change Real.log ((v^2:ℕ):ℝ) ≤ (1+δ)*Real.log (R':ℝ)+K at hBound
  push_cast at hBound
  have hBig : (1-δ)*Real.log (c:ℝ) ≤ (1+δ)*Real.log (R:ℝ)+K+(2+δ)*Real.log 4 := by
    have hWeight := mul_le_mul_of_nonneg_left hRadLog (show 0 ≤ 1+δ by linarith)
    linarith only [hHeightLog,hBound,hWeight]
  have hConst : K+(2+δ)*Real.log 4 ≤ (1-δ)*C := by
    have hMax : (K+(2+δ)*Real.log 4)/(1-δ) ≤ C := le_max_right _ _
    have hStep := (div_le_iff₀ (show 0 < 1-δ by linarith)).1 hMax
    simpa only [mul_comm C (1-δ)] using hStep
  apply (le_of_mul_le_mul_left ?_ (show 0 < 1-δ by linarith))
  rw [mul_add, ← mul_assoc, hCoeff]
  linarith only [hBig,hConst]
