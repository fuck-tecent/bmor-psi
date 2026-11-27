import Mathlib

theorem PEqualNP.Outside.L_goldbach_power_box_card :
    let S := fun n : ℕ => (Finset.range (n+1)) ∩ (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)); ∀ n : ℕ, (S n).card ≤ Nat.sqrt n * Nat.log 2 n := by
  intro S n
  calc
    (S n).card ≤ (((Finset.Icc 2 (Nat.sqrt n)).product
        (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)).card :=
      Finset.card_le_card Finset.inter_subset_right
    _ ≤ ((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).card :=
      Finset.card_image_le
    _ = (Nat.sqrt n + 1 - 2) * (Nat.log 2 n + 1 - 2) := by
      simp [Finset.card_product]
    _ ≤ Nat.sqrt n * Nat.log 2 n := by
      exact Nat.mul_le_mul (by omega) (by omega)
