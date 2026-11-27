import Mathlib

open scoped BigOperators

private lemma cell_identity (H : ℕ) (a b : ℕ → ℝ) :
    (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a s - a t) * (b s - b t))
      = 2 * ((H:ℝ) * (∑ s ∈ Finset.range H, a s * b s)
              - (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t)) := by
  have hexp : ∀ s t : ℕ, (a s - a t) * (b s - b t)
      = a s * b s - a s * b t - a t * b s + a t * b t := by intro s t; ring
  have h1 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a s * b s)
      = (H:ℝ) * ∑ s ∈ Finset.range H, a s * b s := by
    have hinner : ∀ s : ℕ, (∑ t ∈ Finset.range H, a s * b s) = (H:ℝ) * (a s * b s) := by
      intro s
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [hinner]
    rw [← Finset.mul_sum]
  have h2 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a s * b t)
      = (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) := by
    rw [Finset.sum_mul_sum]
  have h3 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a t * b s)
      = (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_mul_sum]
  have h4 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a t * b t)
      = (H:ℝ) * ∑ s ∈ Finset.range H, a s * b s := by
    rw [Finset.sum_comm]
    have hinner : ∀ t : ℕ, (∑ s ∈ Finset.range H, a t * b t) = (H:ℝ) * (a t * b t) := by
      intro t
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [hinner]
    rw [← Finset.mul_sum]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
  ring

private lemma cell_term (H : ℕ) (hH : 0 < H) (a b : ℕ → ℝ) :
    (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a s - a t) * (b s - b t)) / (2 * (H:ℝ))
      = (∑ s ∈ Finset.range H, a s * b s)
        - (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) / (H:ℝ) := by
  rw [cell_identity]
  have hH' : (H:ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

private lemma reflect_sum (H : ℕ) (f : ℕ → ℝ) (x : ℕ) :
    (∑ t ∈ Finset.range H, f (x + (H - 1 - t))) = ∑ t ∈ Finset.range H, f (x + t) :=
  Finset.sum_range_reflect (fun t => f (x + t)) H

private lemma sum_rect (B H : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, g (j*H + s))
      = ∑ m ∈ Finset.range (B*H), g m := by
  induction B generalizing g with
  | zero => rw [Finset.sum_range_zero, Nat.zero_mul, Finset.sum_range_zero]
  | succ B ih =>
    rw [Finset.sum_range_succ, ih]
    have hcomm : Nat.succ B * H = B*H + H := Nat.succ_mul B H
    rw [hcomm, Finset.sum_range_add]

private lemma mass_forward (n H B : ℕ) (w : ℕ → ℝ)
    (hhalf : 2 * (n/2) = n) (hBH8 : B*H*8 = n)
    (hmass : ∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) :
    ∀ j : ℕ, j < B → (H:ℝ)/2 ≤ ∑ s ∈ Finset.range H, w (n/2 + j*H + s) := by
  intro j hj
  have hjm : j*H + H ≤ B*H := by
    have h1 : (j+1)*H ≤ B*H := Nat.mul_le_mul_right H (by omega)
    have h2 : j*H + H = (j+1)*H := by ring
    omega
  generalize j*H = m at *
  have h1 : n ≤ 3 * (n/2 + m) := by omega
  have h2 : 3 * (n/2 + m) ≤ 2*n := by omega
  exact hmass (n/2 + m) h1 h2

private lemma mass_reflect (n H B : ℕ) (w : ℕ → ℝ)
    (hhalf : 2 * (n/2) = n) (hBH8 : B*H*8 = n) (hBHH : B*H ≤ n/2)
    (hmass : ∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) :
    ∀ j : ℕ, j < B → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t)) := by
  intro j hj
  have hjm : j*H + H ≤ B*H := by
    have h1 : (j+1)*H ≤ B*H := Nat.mul_le_mul_right H (by omega)
    have h2 : j*H + H = (j+1)*H := by ring
    omega
  generalize j*H = m at *
  have hje : m + (H-1) ≤ n/2 := by omega
  have hx1 : n ≤ 3 * (n/2 - (m + (H-1))) := by omega
  have hx2 : 3 * (n/2 - (m + (H-1))) ≤ 2*n := by omega
  have hpt : ∀ t : ℕ, t < H → n - (n/2 + m + t) = (n/2 - (m + (H-1))) + (H - 1 - t) := by
    intro t ht
    omega
  have hsum : (∑ t ∈ Finset.range H, w (n - (n/2 + m + t)))
      = ∑ u ∈ Finset.range H, w ((n/2 - (m + (H-1))) + u) := by
    rw [← reflect_sum H w (n/2 - (m + (H-1)))]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hpt t (Finset.mem_range.mp ht)]
  rw [hsum]
  exact hmass _ hx1 hx2

private lemma ab_bound (n H B : ℕ) (w : ℕ → ℝ) (hw : ∀ m : ℕ, 0 ≤ w m)
    (hH0 : (0:ℝ) < H) (hn32 : (B:ℝ) * ((H:ℝ)/4) = (n:ℝ)/32)
    (hA : ∀ j : ℕ, j < B → (H:ℝ)/2 ≤ ∑ s ∈ Finset.range H, w (n/2 + j*H + s))
    (hBm : ∀ j : ℕ, j < B → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) :
    (n:ℝ)/32 ≤ ∑ j ∈ Finset.range B,
      (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
        * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ) := by
  calc (n:ℝ)/32 = (B:ℝ) * ((H:ℝ)/4) := hn32.symm
    _ = ∑ _j ∈ Finset.range B, ((H:ℝ)/4) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
          * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hja := hA j (Finset.mem_range.mp hj)
        have hjb := hBm j (Finset.mem_range.mp hj)
        have hnn : 0 ≤ ∑ s ∈ Finset.range H, w (n/2 + j*H + s) :=
          Finset.sum_nonneg (fun s _ => hw _)
        rw [le_div_iff₀ hH0]
        calc ((H:ℝ)/4) * (H:ℝ) = ((H:ℝ)/2) * ((H:ℝ)/2) := by ring
          _ ≤ (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
                * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) :=
            mul_le_mul hja hjb (by linarith) hnn

private lemma central_bound (n H B : ℕ) (w : ℕ → ℝ) (hw : ∀ m : ℕ, 0 ≤ w m)
    (hhalf : 2 * (n/2) = n) (hBH8 : B*H*8 = n) (hBHH : B*H ≤ n/2) :
    (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
        w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
      ≤ ∑ q ∈ (Finset.range (n+1)).filter (fun q => n ≤ 3*q ∧ 3*q ≤ 2*n), w q * w (n - q) := by
  have hconv : ∀ j : ℕ, (∑ s ∈ Finset.range H, w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
      = ∑ s ∈ Finset.range H, (fun m => w (n/2 + m) * w (n - (n/2 + m))) (j*H + s) := by
    intro j
    apply Finset.sum_congr rfl
    intro s _
    have hring : n/2 + j*H + s = n/2 + (j*H + s) := by ring
    rw [hring]
  have hstep1 : (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
        w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
      = ∑ m ∈ Finset.range (B*H), (fun m => w (n/2 + m) * w (n - (n/2 + m))) m := by
    calc (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
            w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
        = ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
            (fun m => w (n/2 + m) * w (n - (n/2 + m))) (j*H + s) :=
          Finset.sum_congr rfl (fun j _ => hconv j)
      _ = ∑ m ∈ Finset.range (B*H), (fun m => w (n/2 + m) * w (n - (n/2 + m))) m :=
          sum_rect B H (fun m => w (n/2 + m) * w (n - (n/2 + m)))
  rw [hstep1]
  refine Finset.sum_le_sum_of_injOn (fun m => n/2 + m) ?_ ?_ ?_ ?_
  · intro a _ b _ hab
    exact Nat.add_left_cancel hab
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    have hmm : m < B*H := Finset.mem_range.mp hm
    have h2 : n ≤ 3*(n/2 + m) := by omega
    have h3 : 3*(n/2 + m) ≤ 2*n := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨h2, h3⟩⟩
  · intro m _
    exact le_refl _
  · intro q _ _
    exact mul_nonneg (hw _) (hw _)

private lemma assemble (n H B : ℕ) (w : ℕ → ℝ)
    (hcell : ∀ j : ℕ, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2 + j*H + s) - w (n/2 + j*H + t))
          * (w (n - (n/2 + j*H + s)) - w (n - (n/2 + j*H + t)))) / (2*(H:ℝ))
      = (∑ s ∈ Finset.range H, w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
        - (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
            * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ))
    (hsumAB : (n:ℝ)/32 ≤ ∑ j ∈ Finset.range B,
      (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
        * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ))
    (hcentral : (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
        w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
      ≤ ∑ q ∈ (Finset.range (n+1)).filter (fun q => n ≤ 3*q ∧ 3*q ≤ 2*n), w q * w (n - q)) :
    (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2 + j*H + s) - w (n/2 + j*H + t))
          * (w (n - (n/2 + j*H + s)) - w (n - (n/2 + j*H + t)))) / (2*(H:ℝ)))
      ≤ ∑ q ∈ (Finset.range (n+1)).filter (fun q => n ≤ 3*q ∧ 3*q ≤ 2*n), w q * w (n - q) := by
  have hsumcell : (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2 + j*H + s) - w (n/2 + j*H + t))
          * (w (n - (n/2 + j*H + s)) - w (n - (n/2 + j*H + t)))) / (2*(H:ℝ)))
      = ∑ j ∈ Finset.range B, ((∑ s ∈ Finset.range H,
            w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
        - (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
            * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ)) :=
    Finset.sum_congr rfl (fun j _ => hcell j)
  calc (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2 + j*H + s) - w (n/2 + j*H + t))
          * (w (n - (n/2 + j*H + s)) - w (n - (n/2 + j*H + t)))) / (2*(H:ℝ)))
      = (n:ℝ)/32 + ∑ j ∈ Finset.range B, ((∑ s ∈ Finset.range H,
            w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
        - (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
            * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ)) := by
        rw [hsumcell]
    _ = ((n:ℝ)/32 + ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
            w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
        - ∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
            * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ) := by
        rw [Finset.sum_sub_distrib]
        ring
    _ ≤ ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H,
        w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)) := by
        have h := hsumAB
        linarith
    _ ≤ ∑ q ∈ (Finset.range (n+1)).filter (fun q => n ≤ 3*q ∧ 3*q ≤ 2*n), w q * w (n - q) :=
      hcentral

theorem Conjectures.Goldbach.DyadicCellWindowTransfer :
    let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∀ k : ℕ, 12 ≤ k → let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); (∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) → (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ))) ≤ (∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  intro w k hk
  dsimp only
  set n : ℕ := 2^k with hn
  set H : ℕ := 2^(k-k/4) with hH
  set B : ℕ := 2^(k/4-3) with hB
  intro hmass
  have hHpos : 0 < H := by rw [hH]; positivity
  have hH0 : (0:ℝ) < H := by exact_mod_cast hHpos
  have hBH : B * H = 2^(k-3) := by
    rw [hB, hH, ← pow_add]
    congr 1
    omega
  have hn8 : (2:ℕ)^(k-3) * 8 = 2^k := by
    have h : (2:ℕ)^(k-3) * 8 = 2^(k-3) * 2^3 := by norm_num
    rw [h, ← pow_add]
    congr 1
    omega
  have hBH8 : B * H * 8 = n := by rw [hBH, hn8, hn]
  have hdvd : (2:ℕ) ∣ n := by
    refine ⟨2^(k-1), ?_⟩
    have hkk : k = (k-1) + 1 := by omega
    calc n = 2^k := hn
      _ = 2^((k-1)+1) := by congr 1 <;> omega
      _ = 2^(k-1) * 2 := pow_succ 2 (k-1)
      _ = 2 * 2^(k-1) := by ring
  have hhalf : 2 * (n/2) = n := Nat.mul_div_cancel' hdvd
  have hBHH : B * H ≤ n/2 := by omega
  have hBHr : (B:ℝ) * (H:ℝ) = (n:ℝ)/8 := by
    have h : ((B*H*8 : ℕ):ℝ) = (n:ℝ) := by exact_mod_cast hBH8
    push_cast at h
    linarith
  have hn32 : (B:ℝ) * ((H:ℝ)/4) = (n:ℝ)/32 := by
    rw [show (B:ℝ)*((H:ℝ)/4) = (B:ℝ)*(H:ℝ)/4 by ring, hBHr]
    ring
  have hw : ∀ m : ℕ, 0 ≤ w m := by
    intro m
    dsimp [w]
    split_ifs with hm
    · exact Real.log_nonneg (by exact_mod_cast hm.one_le)
    · exact le_rfl
  have hA := mass_forward n H B w hhalf hBH8 hmass
  have hBm := mass_reflect n H B w hhalf hBH8 hBHH hmass
  have hsumAB := ab_bound n H B w hw hH0 hn32 hA hBm
  have hcentral := central_bound n H B w hw hhalf hBH8 hBHH
  have hcell : ∀ j : ℕ, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2 + j*H + s) - w (n/2 + j*H + t))
          * (w (n - (n/2 + j*H + s)) - w (n - (n/2 + j*H + t)))) / (2*(H:ℝ))
      = (∑ s ∈ Finset.range H, w (n/2 + j*H + s) * w (n - (n/2 + j*H + s)))
        - (∑ s ∈ Finset.range H, w (n/2 + j*H + s))
            * (∑ t ∈ Finset.range H, w (n - (n/2 + j*H + t))) / (H:ℝ) :=
    fun j => cell_term H hHpos (fun s => w (n/2 + j*H + s))
      (fun t => w (n - (n/2 + j*H + t)))
  exact assemble n H B w hcell hsumAB hcentral
