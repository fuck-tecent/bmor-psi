import Mathlib

private def wheelTerm (i h : ℕ) : ℕ :=
  if (i % 30).Coprime 30 ∧ ((i + h) % 30).Coprime 30 then 450 else 0

private def wheelMean (h : ℕ) : ℕ :=
  if 2 ∣ h then (15 * (if 3 ∣ h then 2 else 1)) * (if 5 ∣ h then 4 else 3) else 0

private theorem wheelPeriod : ∀ h : Fin 30,
    ∑ i ∈ Finset.range 30, wheelTerm i h = 30 * wheelMean h := by
  decide +kernel

private theorem wheelPrefix (n h : ℕ) (hh : h < 30) :
    let s := ∑ i ∈ Finset.range n, wheelTerm i h
    s ≤ n * wheelMean h + 14400 ∧ n * wheelMean h ≤ s + 14400 := by
  dsimp only
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n < 30
    · have hs : ∑ i ∈ Finset.range n, wheelTerm i h ≤ n * 450 := by
        calc
          _ ≤ ∑ _i ∈ Finset.range n, 450 := Finset.sum_le_sum fun i _ => by
            unfold wheelTerm
            split <;> omega
          _ = _ := by simp
      have hm : wheelMean h ≤ 450 := by
        unfold wheelMean
        split_ifs <;> decide
      have hb := Nat.mul_le_mul_left n hm
      constructor <;> omega
    · let k := n - 30
      have he : n = 30 + k := by dsimp [k]; omega
      have hk := ih k (by dsimp [k]; omega)
      rw [he, Finset.sum_range_add, Nat.add_mul]
      have hs (i : ℕ) : wheelTerm (30 + i) h = wheelTerm i h := by
        unfold wheelTerm
        rw [show (30+i) % 30 = i % 30 by omega,
            show (30+i+h) % 30 = (i+h) % 30 by omega]
      simp only [hs]
      rw [show (∑ i ∈ Finset.range 30, wheelTerm i h) = 30 * wheelMean h from wheelPeriod ⟨h, hh⟩]
      omega

private theorem wheelCoprime (i : ℕ) : i.Coprime 30 ↔ (i % 30).Coprime 30 := by
  change Nat.gcd i 30 = 1 ↔ Nat.gcd (i % 30) 30 = 1
  rw [Nat.gcd_comm i 30, Nat.gcd_rec 30 i]

theorem Conjectures.Cuts.Task97f2f73c3f4d394af1f5c84a : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if x1.Coprime (30 : ℕ) then (30 / 8 : ℝ) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => if (2 : ℕ) ∣ x2 then ((15 / 32 : ℝ) * if (3 : ℕ) ∣ x2 then (2 : ℝ) else (1 : ℝ)) * if (5 : ℕ) ∣ x2 then (4 : ℝ) else (3 : ℝ) else (0 : ℝ); ∀ (x3 x4 : ℕ), |∑ x5 ∈ Finset.range x3, x1 x5 * x1 (x5 + x4) - ↑x3 * x2 x4| ≤ (450 : ℝ)) := by
  dsimp only
  intro n h
  let r := h % 30
  have hr : r < 30 := Nat.mod_lt _ (by decide)
  have hmod (i : ℕ) : (i + r) % 30 = (i + h) % 30 := by dsimp [r]; omega
  have ht (i : ℕ) :
      (if i.Coprime 30 then (30 / 8 : ℝ) else 0) *
      (if (i+h).Coprime 30 then (30 / 8 : ℝ) else 0) =
      (wheelTerm i r : ℝ) / 32 := by
    unfold wheelTerm
    simp only [hmod, ← wheelCoprime]
    split_ifs <;> norm_num <;> tauto
  have hm : (if 2 ∣ h then ((15 / 32 : ℝ) * (if 3 ∣ h then 2 else 1)) *
          (if 5 ∣ h then 4 else 3) else 0) = (wheelMean r : ℝ) / 32 := by
    have h2 : 2 ∣ r ↔ 2 ∣ h := by dsimp [r]; omega
    have h3 : 3 ∣ r ↔ 3 ∣ h := by dsimp [r]; omega
    have h5 : 5 ∣ r ↔ 5 ∣ h := by dsimp [r]; omega
    unfold wheelMean
    simp only [h2, h3, h5]
    split_ifs <;> norm_num
  simp_rw [ht]
  rw [hm, ← Finset.sum_div, ← Nat.cast_sum, abs_le]
  obtain ⟨h₁, h₂⟩ := wheelPrefix n r hr
  have ha : ((∑ i ∈ Finset.range n, wheelTerm i r : ℕ) : ℝ) ≤
      (n : ℝ) * (wheelMean r : ℝ) + 14400 := by exact_mod_cast h₁
  have hb : (n : ℝ) * (wheelMean r : ℝ) ≤
      ((∑ i ∈ Finset.range n, wheelTerm i r : ℕ) : ℝ) + 14400 := by exact_mod_cast h₂
  constructor <;> linarith
