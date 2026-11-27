import Mathlib

private lemma choose_eq_of_mul (n k c : ℕ) (hk : k ≤ n)
    (h : c * (k.factorial * (n - k).factorial) = n.factorial) : Nat.choose n k = c := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have hpos : 0 < k.factorial * (n - k).factorial :=
    Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (n - k))
  have h2 : Nat.choose n k * (k.factorial * (n - k).factorial) = c * (k.factorial * (n - k).factorial) := by
    calc Nat.choose n k * (k.factorial * (n - k).factorial)
        = Nat.choose n k * k.factorial * (n - k).factorial := by ring
      _ = n.factorial := h1
      _ = c * (k.factorial * (n - k).factorial) := h.symm
  exact Nat.eq_of_mul_eq_mul_right hpos h2

private lemma choose_tangent (k t m : ℕ) (hk : 1 ≤ k) :
    Nat.choose t k + Nat.choose t (k - 1) * m ≤ Nat.choose m k + t * Nat.choose t (k - 1) := by
  rcases le_total m t with hmt | htm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmt
    suffices ∀ r, r ≤ d → Nat.choose (m + r) k ≤ Nat.choose m k + r * Nat.choose (m + d) (k - 1) by
      have h := this d le_rfl
      have : (m + d) * Nat.choose (m + d) (k - 1) = Nat.choose (m + d) (k - 1) * m + d * Nat.choose (m + d) (k - 1) := by ring
      omega
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have hrec : Nat.choose (m + r + 1) k = Nat.choose (m + r) k + Nat.choose (m + r) (k - 1) := by
        cases k with
        | zero => omega
        | succ k' =>
          change Nat.choose (m + r + 1) (k' + 1) = Nat.choose (m + r) (k' + 1) + Nat.choose (m + r) k'
          rw [Nat.choose_succ_succ, add_comm]
      have hmono : Nat.choose (m + r) (k - 1) ≤ Nat.choose (m + d) (k - 1) :=
        Nat.choose_le_choose (k - 1) (by omega)
      have ih' := ih (by omega)
      calc Nat.choose (m + (r + 1)) k = Nat.choose (m + r + 1) k := by ring_nf
        _ = Nat.choose (m + r) k + Nat.choose (m + r) (k - 1) := hrec
        _ ≤ (Nat.choose m k + r * Nat.choose (m + d) (k - 1)) + Nat.choose (m + d) (k - 1) := Nat.add_le_add ih' hmono
        _ = Nat.choose m k + (r + 1) * Nat.choose (m + d) (k - 1) := by ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htm
    suffices ∀ r, Nat.choose t k + r * Nat.choose t (k - 1) ≤ Nat.choose (t + r) k by
      have h := this d
      have : Nat.choose t (k - 1) * (t + d) = t * Nat.choose t (k - 1) + d * Nat.choose t (k - 1) := by ring
      omega
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      have hrec : Nat.choose (t + r + 1) k = Nat.choose (t + r) k + Nat.choose (t + r) (k - 1) := by
        cases k with
        | zero => omega
        | succ k' =>
          change Nat.choose (t + r + 1) (k' + 1) = Nat.choose (t + r) (k' + 1) + Nat.choose (t + r) k'
          rw [Nat.choose_succ_succ, add_comm]
      have hmono : Nat.choose t (k - 1) ≤ Nat.choose (t + r) (k - 1) :=
        Nat.choose_le_choose (k - 1) (by omega)
      calc Nat.choose t k + (r + 1) * Nat.choose t (k - 1)
          = (Nat.choose t k + r * Nat.choose t (k - 1)) + Nat.choose t (k - 1) := by ring
        _ ≤ Nat.choose (t + r) k + Nat.choose (t + r) (k - 1) := Nat.add_le_add ih hmono
        _ = Nat.choose (t + r + 1) k := hrec.symm
        _ = Nat.choose (t + (r + 1)) k := by ring_nf

theorem PEqualNP.Outside.L_hash_collision_lab_cert_11_23 :
  ∀ (q:ℕ) (b:Fin q→ℕ), (q*1352078)+1144066*(∑ i,b i)≤(∑ i,Nat.choose (b i) 11)+q*26313518 := by
  intro q b
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin q) _ => choose_tangent 11 23 (b i) (by decide))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at hsum
  have hc1 : Nat.choose 23 11 = 1352078 := choose_eq_of_mul 23 11 1352078 (by omega) (by norm_num [Nat.factorial])
  have hc2 : Nat.choose 23 10 = 1144066 := choose_eq_of_mul 23 10 1144066 (by omega) (by norm_num [Nat.factorial])
  rw [hc1, show (11 : ℕ) - 1 = 10 from rfl, hc2] at hsum
  linarith
