import Mathlib

/-
Dyadic truncation amplitude budget, DR-0019.

The zero sets, multiplicities and finsums are never unfolded; only the two
premises are used. For every primitive character the remainder norm is at most
C times (u (log (m u N))^2 / N + log (m u) + low), and the low zero sum is at
most B log (2m). From u = N + 1/2, 2 <= m <= 2N and 2 <= N one gets
m u N <= (2N)^3, m u <= (2N)^2, 2m <= (2N)^2, u / N <= 5/4 and
1 <= log (2N), hence the bracket is at most 16 (1+B) (log (2N))^2. Dividing
by the square root of the totient, squaring and summing over the primitive
characters uses that there are at most m.totient of them, so the totient
cancels and only the square of 16 C (1+B) (log (2N))^2 remains.
-/


private theorem norm_div_real_sq {a : ℂ} {r : ℝ} (hr : 0 < r) :
    ‖a / (r : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / r ^ 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_pow]

private theorem amp_bound {N m : ℕ} {C B u low : ℝ}
    (hN : 2 ≤ N) (hm : 2 ≤ m) (hmN : m ≤ 2 * N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hu : u = (N : ℝ) + 1 / 2) (hlow : low ≤ B * Real.log (2 * m : ℝ)) :
    C * (u * (Real.log ((m : ℝ) * u * N)) ^ 2 / ↑N + Real.log ((m : ℝ) * u) + low)
      ≤ 16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2 := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmN' : (m : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hmN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hupos : (0 : ℝ) < u := by rw [hu]; linarith
  have hu2 : u ≤ 2 * (N : ℝ) := by rw [hu]; linarith
  have hu54 : u ≤ 5 / 4 * (N : ℝ) := by rw [hu]; linarith
  have h2Npos : (0 : ℝ) < 2 * (N : ℝ) := by linarith
  have h2u : (2 : ℝ) ≤ u := by rw [hu]; linarith
  have hmu : (m : ℝ) * u ≤ 2 * (N : ℝ) * (2 * (N : ℝ)) := by
    calc (m : ℝ) * u ≤ (2 * (N : ℝ)) * u := mul_le_mul_of_nonneg_right hmN' (le_of_lt hupos)
      _ ≤ (2 * (N : ℝ)) * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hu2 (le_of_lt h2Npos)
  have hmun : (m : ℝ) * u * (N : ℝ) ≤ (2 * (N : ℝ)) ^ 3 := by
    calc (m : ℝ) * u * (N : ℝ) ≤ 2 * (N : ℝ) * (2 * (N : ℝ)) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hmu (le_of_lt hNpos)
      _ ≤ (2 * (N : ℝ)) ^ 3 := by
        have h3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := pow_nonneg (le_of_lt hNpos) 3
        nlinarith
  have h8 : (8 : ℝ) ≤ (m : ℝ) * u * (N : ℝ) := by
    have h1 : (2 : ℝ) * 2 ≤ (m : ℝ) * u := by
      calc (2 : ℝ) * 2 ≤ (m : ℝ) * 2 := mul_le_mul_of_nonneg_right hm' (by norm_num)
        _ ≤ (m : ℝ) * u := mul_le_mul_of_nonneg_left h2u (le_of_lt hmpos)
    have h2 : (2 : ℝ) * 2 * 2 ≤ (m : ℝ) * u * (N : ℝ) := by
      calc (2 : ℝ) * 2 * 2 ≤ (m : ℝ) * u * 2 := mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ ≤ (m : ℝ) * u * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hN' (le_of_lt (mul_pos hmpos hupos))
    linarith
  have hL1pos : 0 ≤ Real.log ((m : ℝ) * u * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hL1 : Real.log ((m : ℝ) * u * (N : ℝ)) ≤ 3 * Real.log (2 * (N : ℝ)) := by
    have h := Real.log_le_log (by linarith) hmun
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hsq1 : (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 ≤ 9 * (Real.log (2 * (N : ℝ))) ^ 2 := by
    nlinarith [mul_self_le_mul_self hL1pos hL1]
  have hterm1 : u * (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 / (N : ℝ)
      ≤ 45 / 4 * (Real.log (2 * (N : ℝ))) ^ 2 := by
    have hd : u / (N : ℝ) ≤ 5 / 4 := by
      rw [div_le_iff₀ hNpos]
      linarith
    have h := mul_le_mul hd hsq1 (sq_nonneg _) (by norm_num)
    calc u * (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 / (N : ℝ)
        = (u / (N : ℝ)) * (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 := by ring
      _ ≤ (5 / 4) * (9 * (Real.log (2 * (N : ℝ))) ^ 2) := h
      _ = 45 / 4 * (Real.log (2 * (N : ℝ))) ^ 2 := by ring
  have hL2 : Real.log ((m : ℝ) * u) ≤ 2 * Real.log (2 * (N : ℝ)) := by
    have hmu' : (m : ℝ) * u ≤ (2 * (N : ℝ)) ^ 2 := by
      calc (m : ℝ) * u ≤ 2 * (N : ℝ) * (2 * (N : ℝ)) := hmu
        _ = (2 * (N : ℝ)) ^ 2 := by ring
    have h := Real.log_le_log (mul_pos hmpos hupos) hmu'
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hL3 : Real.log (2 * (m : ℝ)) ≤ 2 * Real.log (2 * (N : ℝ)) := by
    have h2m : (2 : ℝ) * (m : ℝ) ≤ (2 * (N : ℝ)) ^ 2 := by
      have h1 : (2 : ℝ) * (m : ℝ) ≤ 2 * (2 * (N : ℝ)) := by linarith
      have h3 : (2 : ℝ) ≤ 2 * (N : ℝ) := by linarith
      have h4 : (2 * (N : ℝ)) * 2 ≤ (2 * (N : ℝ)) * (2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (le_of_lt h2Npos)
      calc (2 : ℝ) * (m : ℝ) ≤ 2 * (2 * (N : ℝ)) := h1
        _ = (2 * (N : ℝ)) * 2 := by ring
        _ ≤ (2 * (N : ℝ)) * (2 * (N : ℝ)) := h4
        _ = (2 * (N : ℝ)) ^ 2 := by ring
    have h := Real.log_le_log (by linarith) h2m
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hx1 : (1 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [h4]
      have := Real.log_two_gt_d9
      linarith
    have h := Real.log_le_log (by norm_num) (show (4 : ℝ) ≤ 2 * (N : ℝ) by linarith)
    linarith
  have hx : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by linarith
  have hxx : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) * (Real.log (2 * (N : ℝ)) - 1) :=
    mul_nonneg hx (by linarith)
  have hp1 : (45 : ℝ) / 4 * (Real.log (2 * (N : ℝ))) ^ 2 + 2 * Real.log (2 * (N : ℝ))
      ≤ 16 * (Real.log (2 * (N : ℝ))) ^ 2 := by nlinarith [hxx, hx]
  have hp2 : 2 * Real.log (2 * (N : ℝ)) ≤ 16 * (Real.log (2 * (N : ℝ))) ^ 2 := by
    nlinarith [hxx, hx]
  have hA0 : u * (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 / (N : ℝ)
      + Real.log ((m : ℝ) * u) + B * Real.log (2 * (m : ℝ))
      ≤ 16 * (1 + B) * (Real.log (2 * (N : ℝ))) ^ 2 := by
    have h3 : B * Real.log (2 * (m : ℝ)) ≤ B * (2 * Real.log (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hL3 hB
    have h4 : B * (2 * Real.log (2 * (N : ℝ))) ≤ B * (16 * (Real.log (2 * (N : ℝ))) ^ 2) :=
      mul_le_mul_of_nonneg_left hp2 hB
    linarith [hterm1, hL2, h3, h4, hp1]
  calc C * (u * (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 / ↑N + Real.log ((m : ℝ) * u) + low)
      ≤ C * (u * (Real.log ((m : ℝ) * u * (N : ℝ))) ^ 2 / ↑N + Real.log ((m : ℝ) * u)
          + B * Real.log (2 * (m : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (by linarith [hlow]) hC
    _ ≤ C * (16 * (1 + B) * (Real.log (2 * (N : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hA0 hC
    _ = 16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2 := by ring

theorem Conjectures.Goldbach.DyadicTruncationAmplitudeBudget :
    ∀ (N m : ℕ) [NeZero m] (C B : ℝ), 2 ≤ N → 2 ≤ m → m ≤ 2*N → 0 ≤ C → 0 ≤ B →
      let u : ℝ := (N : ℝ) + 1/2
      let zeros := fun (χ : DirichletCharacter ℂ m) (T : ℝ) =>
        {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}
      let ord := fun (χ : DirichletCharacter ℂ m) (ρ : ℂ) => analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
      let low := fun χ : DirichletCharacter ℂ m => ∑ᶠ ρ ∈ zeros χ 1, (ord χ ρ : ℝ) / ‖ρ‖
      let V := fun χ : DirichletCharacter ℂ m =>
        ∑ n ∈ Finset.range (N+1), (ArithmeticFunction.vonMangoldt n : ℂ) * χ⁻¹ (n : ZMod m)
      let Z := fun χ : DirichletCharacter ℂ m =>
        -(∑ᶠ ρ ∈ zeros χ⁻¹ N, (ord χ⁻¹ ρ : ℂ) * ((u : ℂ)^ρ / ρ))
      let s := (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun χ => χ.conductor = m)
      (∀ χ ∈ s, (zeros χ⁻¹ N).Finite ∧
        ‖V χ-Z χ‖ ≤ C * (u * (Real.log ((m : ℝ)*u*N))^2 / N + Real.log ((m : ℝ)*u) + low χ⁻¹)) →
      (∀ χ ∈ s, low χ⁻¹ ≤ B * Real.log (2*m : ℝ)) →
        (∑ χ ∈ s, ‖(V χ-Z χ) / (Real.sqrt (m.totient : ℝ) : ℂ)‖^2) ≤
          (16*C*(1+B)*(Real.log (2*N : ℝ))^2)^2 := by
  intro N m _ C B hN hm hmN hC hB u zeros ord low V Z s hyp1 hyp2
  have hφpos : (0 : ℝ) < (m.totient : ℝ) := by
    have h : 0 < m.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hφne : (m.totient : ℝ) ≠ 0 := hφpos.ne'
  have hsqrtpos : (0 : ℝ) < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.2 hφpos
  have hcard : (s.card : ℝ) ≤ (m.totient : ℝ) := by
    have h1 : s.card ≤ Fintype.card (DirichletCharacter ℂ m) := by
      simpa using Finset.card_le_univ s
    have h2 : Fintype.card (DirichletCharacter ℂ m) = m.totient := by
      simpa only [Nat.card_eq_fintype_card] using
        (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ m)
    exact_mod_cast (h1.trans_eq h2)
  have hkey : ∀ χ ∈ s, ‖(V χ - Z χ) / (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2
      ≤ (16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2) ^ 2 / (m.totient : ℝ) := by
    intro χ hχ
    have h1 : ‖V χ - Z χ‖
        ≤ C * (u * (Real.log ((m : ℝ) * u * N)) ^ 2 / ↑N + Real.log ((m : ℝ) * u)
          + low χ⁻¹) := (hyp1 χ hχ).2
    have h2 : low χ⁻¹ ≤ B * Real.log (2 * m : ℝ) := hyp2 χ hχ
    have h3 : ‖V χ - Z χ‖ ≤ 16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2 :=
      h1.trans (amp_bound hN hm hmN hC hB rfl h2)
    rw [norm_div_real_sq hsqrtpos, Real.sq_sqrt hφpos.le]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hφpos)
    nlinarith [mul_self_le_mul_self (norm_nonneg (V χ - Z χ)) h3]
  calc (∑ χ ∈ s, ‖(V χ - Z χ) / (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ χ ∈ s, ((16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2) ^ 2 / (m.totient : ℝ)) :=
        Finset.sum_le_sum hkey
    _ = (s.card : ℝ) * ((16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2) ^ 2
        / (m.totient : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m.totient : ℝ) * ((16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2) ^ 2
        / (m.totient : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hcard ?_
        exact div_nonneg (sq_nonneg _) (le_of_lt hφpos)
    _ = (16 * C * (1 + B) * (Real.log (2 * N : ℝ)) ^ 2) ^ 2 := by
        rw [mul_comm, div_mul_cancel₀ _ hφne]

