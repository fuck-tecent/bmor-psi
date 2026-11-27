import Mathlib

open scoped Classical

private theorem oddMixedMoment : ∀ (N : ℕ) [NeZero N] (F G : (ZMod N)ˣ → ℂ), let oddChars := @Finset.filter (DirichletCharacter ℂ N) (fun χ => χ.Odd) (fun χ => Classical.propDecidable χ.Odd) Finset.univ; let T := fun (W : (ZMod N)ˣ → ℂ) (χ : DirichletCharacter ℂ N) => Finset.univ.sum (fun a : (ZMod N)ˣ => W a * χ (a : ZMod N)); 2 * oddChars.sum (fun χ => star (T F χ) * T G χ) = (N.totient : ℂ) * Finset.univ.sum (fun a : (ZMod N)ˣ => star (F a) * (G a - G (-a))) := by
  classical
  intro N _ F G oddChars T
  have orth (a b : (ZMod N)ˣ) :
      (∑ χ : DirichletCharacter ℂ N, star (χ (a:ZMod N))*χ (b:ZMod N)) =
      if a=b then (N.totient:ℂ) else 0 := by
    have hca (χ : DirichletCharacter ℂ N) : star (χ (a:ZMod N)) = χ ((a:ZMod N)⁻¹) := by
      rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit]
    simp_rw [hca]
    simpa only [Units.val_inj] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b:ZMod N)
  have parseval (W : (ZMod N)ˣ → ℂ) :
      ∑ χ : DirichletCharacter ℂ N, star (T F χ) * T W χ =
        (N.totient:ℂ)*∑ a, star (F a)*W a := by
    let k (χ : DirichletCharacter ℂ N) (a b : (ZMod N)ˣ) :=
      (star (F a)*W b) * (star (χ (a:ZMod N))*χ (b:ZMod N))
    have hex (χ : DirichletCharacter ℂ N) : star (T F χ)*T W χ = ∑ a,∑ b,k χ a b := by
      dsimp only [T,k]; rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum, star_mul]
      apply Finset.sum_congr rfl; intro b _; ring
    simp_rw [hex]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]; dsimp only [k]
    simp_rw [← Finset.mul_sum,orth]
    simp [Finset.sum_ite_eq, mul_comm]
  let W := fun a : (ZMod N)ˣ => G a-G (-a)
  have hhalf (χ : DirichletCharacter ℂ N) : T W χ = if χ.Odd then 2*T G χ else 0 := by
    have href : (∑ a : (ZMod N)ˣ,G (-a)*χ (a:ZMod N)) = ∑ a : (ZMod N)ˣ,G a*χ ((-a: (ZMod N)ˣ):ZMod N) := by
      have he := Equiv.sum_comp (Equiv.neg ((ZMod N)ˣ)) (fun a : (ZMod N)ˣ => G a*χ ((-a:(ZMod N)ˣ):ZMod N))
      simpa using he
    dsimp only [T,W]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,href]
    rcases χ.even_or_odd with h | h
    · simp [h.not_odd, Units.val_neg,h.eval_neg]
    · simp [h, Units.val_neg,h.eval_neg,Finset.sum_neg_distrib]; ring
  have h := parseval W
  rw [← h]
  simp_rw [hhalf]
  dsimp only [oddChars]
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hχ : χ.Odd
  · simp [hχ]; ring
  · simp [hχ]


theorem PEqualNP.Outside.L_goldbach_characters_odd_parseval :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ f : (ZMod n)ˣ → ℝ, (2/(n.totient : ℝ))*(∑ χ ∈ odd, ‖∑ a : (ZMod n)ˣ, (f a : ℂ)*χ (a : ZMod n)‖^2) = (∑ a : (ZMod n)ˣ, (f a)^2) - ∑ a : (ZMod n)ˣ, f a*f (-a) := by
  intro n _ hn odd f
  let F := fun a : (ZMod n)ˣ => (f a : ℂ)
  have h := oddMixedMoment n F F
  dsimp only at h
  have hp : 0 < n.totient := Nat.totient_pos.mpr (NeZero.pos n)
  have hv (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp_rw [hv] at h
  simp only [F, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum] at h
  have h' : 2 * (∑ χ ∈ odd, ‖∑ a : (ZMod n)ˣ, (f a : ℂ) * χ (a : ZMod n)‖ ^ 2) =
    (n.totient : ℝ) * ∑ a, f a * (f a - f (-a)) := by exact_mod_cast h
  simp_rw [mul_sub, ← sq, Finset.sum_sub_distrib] at h'
  have hne : (n.totient : ℝ) ≠ 0 := by positivity
  field_simp
  linarith only [h']
