import Mathlib

private lemma choose3_telescope (n d : ℕ) :
    Nat.choose (n + d) 3 = Nat.choose n 3 + ∑ j ∈ Finset.range d, Nat.choose (n + j) 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show n + (d + 1) = n + d + 1 from rfl]
    have h1 : Nat.choose (n + d + 1) 3 = Nat.choose (n + d) 3 + Nat.choose (n + d) 2 := by
      have h2 : Nat.choose (n + d + 1) 3 = Nat.choose (n + d) 2 + Nat.choose (n + d) 3 := by
        simpa using Nat.choose_succ_succ' (n + d) 2
      omega
    rw [h1, ih, Finset.sum_range_succ]
    ring

private lemma choose3_ge_mean (k d : ℕ) :
    Nat.choose k 3 + d * Nat.choose k 2 ≤ Nat.choose (k + d) 3 := by
  have ht := choose3_telescope k d
  have hlow : (∑ j ∈ Finset.range d, Nat.choose k 2)
      ≤ ∑ j ∈ Finset.range d, Nat.choose (k + j) 2 :=
    Finset.sum_le_sum (fun j _ => Nat.choose_le_choose 2 (by omega : k ≤ k + j))
  have hc : (∑ j ∈ Finset.range d, Nat.choose k 2) = d * Nat.choose k 2 := by
    rw [Finset.sum_const_nat (m := Nat.choose k 2) (fun j _ => rfl), Finset.card_range]
  omega

private lemma choose3_le_mean (k e : ℕ) (he : e ≤ k) :
    Nat.choose k 3 ≤ Nat.choose (k - e) 3 + e * Nat.choose k 2 := by
  have ht := choose3_telescope (k - e) e
  rw [Nat.sub_add_cancel he] at ht
  have hup : (∑ j ∈ Finset.range e, Nat.choose (k - e + j) 2)
      ≤ ∑ j ∈ Finset.range e, Nat.choose k 2 := by
    apply Finset.sum_le_sum
    intro j hj
    apply Nat.choose_le_choose 2
    simp only [Finset.mem_range] at hj
    omega
  have hc : (∑ j ∈ Finset.range e, Nat.choose k 2) = e * Nat.choose k 2 := by
    rw [Finset.sum_const_nat (m := Nat.choose k 2) (fun j _ => rfl), Finset.card_range]
  omega

theorem PEqualNP.Outside.L_hash_collision_lab_triple_sharp :
    ∀ (q:ℕ) (b:Fin q→ℕ),0<q → let M:=∑ i,b i; let k:=M/q; let r:=M % q; (q-r)*Nat.choose k 3+r*Nat.choose (k+1) 3≤∑ i,Nat.choose (b i) 3 := by
  intro q b hq
  dsimp only
  set M := ∑ i, b i with hM
  set k := M / q with hk
  set r := M % q with hr
  have hqk : q * k + r = M := by
    rw [hk, hr]
    exact Nat.div_add_mod M q
  have hrq : r ≤ q := by
    rw [hr]
    exact Nat.le_of_lt (Nat.mod_lt M hq)
  set A := (Finset.univ : Finset (Fin q)).filter (fun i => k ≤ b i) with hA
  set B := (Finset.univ : Finset (Fin q)).filter (fun i => ¬ k ≤ b i) with hB
  set D := ∑ i ∈ A, (b i - k) with hD
  set E := ∑ i ∈ B, (k - b i) with hE
  have hAmem : ∀ i : Fin q, i ∈ A → k ≤ b i := by
    intro i hi
    rw [hA] at hi
    simpa using hi
  have hBmem : ∀ i : Fin q, i ∈ B → ¬ k ≤ b i := by
    intro i hi
    rw [hB] at hi
    simpa using hi
  have hcard : A.card + B.card = q := by
    rw [hA, hB, Finset.card_filter_add_card_filter_not]
    simp
  have htermA : ∀ i ∈ A, Nat.choose k 3 + (b i - k) * Nat.choose k 2 ≤ Nat.choose (b i) 3 := by
    intro i hi
    have hki : k ≤ b i := hAmem i hi
    have hb : k + (b i - k) = b i := by omega
    simpa [hb] using choose3_ge_mean k (b i - k)
  have htermB : ∀ i ∈ B, Nat.choose k 3 ≤ Nat.choose (b i) 3 + (k - b i) * Nat.choose k 2 := by
    intro i hi
    have hlt : b i < k := not_le.mp (hBmem i hi)
    have hle : b i ≤ k := Nat.le_of_lt hlt
    have hb : k - (k - b i) = b i := by omega
    have he : k - b i ≤ k := Nat.sub_le k (b i)
    simpa [hb] using choose3_le_mean k (k - b i) he
  have hAineq : A.card * Nat.choose k 3 + D * Nat.choose k 2 ≤ ∑ i ∈ A, Nat.choose (b i) 3 := by
    have h1 : (∑ i ∈ A, (Nat.choose k 3 + (b i - k) * Nat.choose k 2))
        ≤ ∑ i ∈ A, Nat.choose (b i) 3 := Finset.sum_le_sum htermA
    have h2 : (∑ i ∈ A, (Nat.choose k 3 + (b i - k) * Nat.choose k 2))
        = A.card * Nat.choose k 3 + D * Nat.choose k 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const_nat (m := Nat.choose k 3) (fun i _ => rfl)]
      have h2b : (∑ i ∈ A, (b i - k) * Nat.choose k 2) = D * Nat.choose k 2 := by
        rw [hD, Finset.sum_mul]
      rw [h2b]
    calc A.card * Nat.choose k 3 + D * Nat.choose k 2
        = (∑ i ∈ A, (Nat.choose k 3 + (b i - k) * Nat.choose k 2)) := h2.symm
      _ ≤ ∑ i ∈ A, Nat.choose (b i) 3 := h1
  have hBineq : B.card * Nat.choose k 3 ≤ ∑ i ∈ B, Nat.choose (b i) 3 + E * Nat.choose k 2 := by
    have h1 : (∑ i ∈ B, Nat.choose k 3)
        ≤ ∑ i ∈ B, (Nat.choose (b i) 3 + (k - b i) * Nat.choose k 2) :=
      Finset.sum_le_sum htermB
    have h2 : (∑ i ∈ B, Nat.choose k 3) = B.card * Nat.choose k 3 := by
      rw [Finset.sum_const_nat (m := Nat.choose k 3) (fun i _ => rfl)]
    have h3 : (∑ i ∈ B, (Nat.choose (b i) 3 + (k - b i) * Nat.choose k 2))
        = (∑ i ∈ B, Nat.choose (b i) 3) + E * Nat.choose k 2 := by
      rw [Finset.sum_add_distrib]
      have h3b : (∑ i ∈ B, (k - b i) * Nat.choose k 2) = E * Nat.choose k 2 := by
        rw [hE, Finset.sum_mul]
      rw [h3b]
    calc B.card * Nat.choose k 3 = (∑ i ∈ B, Nat.choose k 3) := h2.symm
      _ ≤ (∑ i ∈ B, (Nat.choose (b i) 3 + (k - b i) * Nat.choose k 2)) := h1
      _ = (∑ i ∈ B, Nat.choose (b i) 3) + E * Nat.choose k 2 := h3
  have hAsum : (∑ i ∈ A, b i) = A.card * k + D := by
    have hstep : ∀ i ∈ A, b i = k + (b i - k) := by
      intro i hi
      have hki : k ≤ b i := hAmem i hi
      omega
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
      Finset.sum_const_nat (m := k) (fun i _ => rfl), ← hD]
  have hBsum : (∑ i ∈ B, b i) + E = B.card * k := by
    have hstep : ∀ i ∈ B, b i + (k - b i) = k := by
      intro i hi
      have hle : b i ≤ k := Nat.le_of_lt (not_le.mp (hBmem i hi))
      omega
    have h1 : (∑ i ∈ B, (b i + (k - b i))) = B.card * k := by
      rw [Finset.sum_congr rfl hstep, Finset.sum_const_nat (m := k) (fun i _ => rfl)]
    have h2 : (∑ i ∈ B, (b i + (k - b i))) = (∑ i ∈ B, b i) + E := by
      rw [Finset.sum_add_distrib, ← hE]
    rw [← h2, h1]
  have hbsplit : (∑ i ∈ A, b i) + (∑ i ∈ B, b i) = M := by
    rw [hM, ← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin q)))
      (p := fun i : Fin q => k ≤ b i)]
  have hME : M + E = q * k + D := by
    have h1 : M + E = ((∑ i ∈ A, b i) + ∑ i ∈ B, b i) + E := by rw [hbsplit]
    rw [h1, Nat.add_assoc, hBsum, hAsum]
    calc (A.card * k + D) + B.card * k = (A.card + B.card) * k + D := by ring
      _ = q * k + D := by rw [hcard]
  have hDE : D = r + E := by omega
  have hCsplt : (∑ i ∈ A, Nat.choose (b i) 3) + (∑ i ∈ B, Nat.choose (b i) 3)
      = ∑ i, Nat.choose (b i) 3 := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin q)))
      (p := fun i : Fin q => k ≤ b i)]
  have step : (A.card * Nat.choose k 3 + D * Nat.choose k 2) + B.card * Nat.choose k 3
      ≤ (∑ i, Nat.choose (b i) 3) + E * Nat.choose k 2 := by
    calc (A.card * Nat.choose k 3 + D * Nat.choose k 2) + B.card * Nat.choose k 3
        ≤ (∑ i ∈ A, Nat.choose (b i) 3)
            + ((∑ i ∈ B, Nat.choose (b i) 3) + E * Nat.choose k 2) :=
          Nat.add_le_add hAineq hBineq
      _ = (∑ i, Nat.choose (b i) 3) + E * Nat.choose k 2 := by
          rw [← Nat.add_assoc, hCsplt]
  have hmain : q * Nat.choose k 3 + r * Nat.choose k 2 ≤ ∑ i, Nat.choose (b i) 3 := by
    have hL : (A.card * Nat.choose k 3 + D * Nat.choose k 2) + B.card * Nat.choose k 3
        = q * Nat.choose k 3 + D * Nat.choose k 2 := by
      calc (A.card * Nat.choose k 3 + D * Nat.choose k 2) + B.card * Nat.choose k 3
          = (A.card + B.card) * Nat.choose k 3 + D * Nat.choose k 2 := by ring
        _ = q * Nat.choose k 3 + D * Nat.choose k 2 := by rw [hcard]
    have hR : q * Nat.choose k 3 + (r + E) * Nat.choose k 2
        = q * Nat.choose k 3 + r * Nat.choose k 2 + E * Nat.choose k 2 := by ring
    rw [hL, hDE, hR] at step
    exact Nat.le_of_add_le_add_right step
  have hF6 : (q - r) * Nat.choose k 3 + r * Nat.choose (k + 1) 3
      = q * Nat.choose k 3 + r * Nat.choose k 2 := by
    have hp : Nat.choose (k + 1) 3 = Nat.choose k 3 + Nat.choose k 2 := by
      rw [Nat.choose_succ_succ']
      ring
    have h1 : (q - r) * Nat.choose k 3 + r * Nat.choose k 3 = q * Nat.choose k 3 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hrq]
    have h2 : r * Nat.choose (k + 1) 3 = r * Nat.choose k 3 + r * Nat.choose k 2 := by
      rw [hp, Nat.mul_add]
    omega
  rw [hF6]
  exact hmain
