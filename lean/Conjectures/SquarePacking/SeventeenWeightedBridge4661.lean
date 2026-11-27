import Mathlib

theorem Conjectures.SquarePacking.SeventeenWeightedBridge4661 :
    (let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; ∃ (k : ℕ) (X Y : Fin k → ℚ) (w : Fin k → ℕ) (q : ℕ), 0 < q ∧ (∑ j, w j) < 17*q ∧ ∀ x y a b : ℝ, (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧ |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) → q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) → (let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y); ¬ fits 17 (4661/1000)) := by
  intro h
  dsimp only at h ⊢
  obtain ⟨k, X, Y, w, q, hq, hw, hc⟩ := h
  rintro ⟨_, x, y, a, b, hbox, hdisj⟩
  have h1 : ∀ i : Fin 17, q ≤ ∑ j : Fin k, (if |a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2 then w j else 0) :=
    fun i => hc _ _ _ _ (hbox i)
  have h2 : ∀ j : Fin k, ∑ i : Fin 17, (if |a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2 then w j else 0) ≤ w j := by
    intro j
    by_cases hex : ∃ i : Fin 17, |a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2
    · obtain ⟨i0, hi0⟩ := hex
      calc _ ≤ ∑ i : Fin 17, (if i = i0 then w j else 0) := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hp : |a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2
            · have : i = i0 := by
                by_contra hne
                exact hdisj i i0 hne _ _ hp hi0
              subst this
              rw [if_pos hp, if_pos rfl]
            · rw [if_neg hp]; exact Nat.zero_le _
        _ = w j := by simp
    · push_neg at hex
      have : ∀ i : Fin 17, ¬ (|a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2) := fun i hp => by
        have := hex i hp.1
        linarith [hp.2]
      rw [Finset.sum_eq_zero (fun i _ => if_neg (this i))]
      exact Nat.zero_le _
  have h3 : 17 * q ≤ ∑ j : Fin k, w j := by
    calc 17 * q = ∑ _i : Fin 17, q := by simp
      _ ≤ ∑ i : Fin 17, ∑ j : Fin k, (if |a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2 then w j else 0) := Finset.sum_le_sum fun i _ => h1 i
      _ = ∑ j : Fin k, ∑ i : Fin 17, (if |a i*((X j:ℝ)-x i)+b i*((Y j:ℝ)-y i)| < 1/2 ∧ |(-b i)*((X j:ℝ)-x i)+a i*((Y j:ℝ)-y i)| < 1/2 then w j else 0) := Finset.sum_comm
      _ ≤ ∑ j : Fin k, w j := Finset.sum_le_sum fun j _ => h2 j
  omega
