import Mathlib

open scoped BigOperators

-- child 1 zh: 对充分大的偶数，至少一侧较小素因子超过给定次指数平方根截点的双半素数配对至多占终筛体积的 1/500。
-- child 1 en: Eventually for even targets, pairs with a least prime factor beyond the stated subexponential square-root cutoff contribute at most 1/500 of the terminal volume.
-- child 2 zh: 对充分大的偶数，两侧较小素因子均不超过 n 的 2/5 次幂的双半素数配对至多占终筛体积的 2/25。
-- child 2 en: Eventually for even targets, pairs with both least prime factors at most n to the power 2/5 contribute at most 2/25 of the terminal volume.
-- child 3 zh: 对充分大的偶数，两侧较小素因子均不超过次指数平方根截点且至少一侧超过 n 的 2/5 次幂的双半素数配对至多占终筛体积的 189/500。
-- child 3 en: Eventually for even targets, pairs with both least prime factors at most the stated square-root cutoff and at least one beyond n to the power 2/5 contribute at most 189/500 of the terminal volume.
theorem Conjectures.Cuts.Cutcc1bcaccff92c7623d0cfa07
    (endpoint :
      let I (n : ℕ) := Finset.Icc ((n+2)/3) ((2*n)/3)
      let P (z : ℕ) := (Finset.Icc 2 z).filter Nat.Prime
      let A (n : ℕ) := (I n).filter (fun m =>
        ⌊(n : ℝ)^(1/3:ℝ)⌋₊ < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m/m.minFac))
      let V (n : ℕ) := ((I n).card : ℝ) * (n.totient:ℝ)/n *
        ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
      let B (n : ℕ) := (A n).filter (fun m => n-m ∈ A n)
      let C (n : ℕ) := ⌊Real.exp (Real.log (n:ℝ)/2 - 2*(Real.log (n:ℝ))^(2/3:ℝ))⌋₊
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        (((B n).filter (fun m => C n < m.minFac ∨ C n < (n-m).minFac)).card:ℝ) ≤ (1/500:ℝ)*V n)
    (lower :
      let I (n : ℕ) := Finset.Icc ((n+2)/3) ((2*n)/3)
      let P (z : ℕ) := (Finset.Icc 2 z).filter Nat.Prime
      let A (n : ℕ) := (I n).filter (fun m =>
        ⌊(n : ℝ)^(1/3:ℝ)⌋₊ < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m/m.minFac))
      let V (n : ℕ) := ((I n).card : ℝ) * (n.totient:ℝ)/n *
        ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
      let B (n : ℕ) := (A n).filter (fun m => n-m ∈ A n)
      let D (n : ℕ) := ⌊(n:ℝ)^(2/5:ℝ)⌋₊
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        (((B n).filter (fun m => m.minFac ≤ D n ∧ (n-m).minFac ≤ D n)).card:ℝ) ≤ (2/25:ℝ)*V n)
    (upper :
      let I (n : ℕ) := Finset.Icc ((n+2)/3) ((2*n)/3)
      let P (z : ℕ) := (Finset.Icc 2 z).filter Nat.Prime
      let A (n : ℕ) := (I n).filter (fun m =>
        ⌊(n : ℝ)^(1/3:ℝ)⌋₊ < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m/m.minFac))
      let V (n : ℕ) := ((I n).card : ℝ) * (n.totient:ℝ)/n *
        ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
      let B (n : ℕ) := (A n).filter (fun m => n-m ∈ A n)
      let C (n : ℕ) := ⌊Real.exp (Real.log (n:ℝ)/2 - 2*(Real.log (n:ℝ))^(2/3:ℝ))⌋₊
      let D (n : ℕ) := ⌊(n:ℝ)^(2/5:ℝ)⌋₊
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        (((B n).filter (fun m => m.minFac ≤ C n ∧ (n-m).minFac ≤ C n ∧
          (D n < m.minFac ∨ D n < (n-m).minFac))).card:ℝ) ≤ (189/500:ℝ)*V n) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑{x9 ∈ x3 x6 | x6 - x9 ∈ x3 x6}.card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6) := by
  let I (n : ℕ) := Finset.Icc ((n+2)/3) ((2*n)/3)
  let P (z : ℕ) := (Finset.Icc 2 z).filter Nat.Prime
  let A (n : ℕ) := (I n).filter (fun m =>
    ⌊(n : ℝ)^(1/3:ℝ)⌋₊ < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m/m.minFac))
  let V (n : ℕ) := ((I n).card : ℝ) * (n.totient:ℝ)/n *
    ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
  let B (n : ℕ) := (A n).filter (fun m => n-m ∈ A n)
  let C (n : ℕ) := ⌊Real.exp (Real.log (n:ℝ)/2 - 2*(Real.log (n:ℝ))^(2/3:ℝ))⌋₊
  let D (n : ℕ) := ⌊(n:ℝ)^(2/5:ℝ)⌋₊
  let B₁ (n : ℕ) := (B n).filter (fun m => C n < m.minFac ∨ C n < (n-m).minFac)
  let B₂ (n : ℕ) := (B n).filter (fun m => m.minFac ≤ D n ∧ (n-m).minFac ≤ D n)
  let B₃ (n : ℕ) := (B n).filter (fun m => m.minFac ≤ C n ∧ (n-m).minFac ≤ C n ∧
    (D n < m.minFac ∨ D n < (n-m).minFac))
  change ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ((B n).card : ℝ) ≤ (23/50:ℝ)*V n
  obtain ⟨N₁,hN₁⟩ := endpoint
  obtain ⟨N₂,hN₂⟩ := lower
  obtain ⟨N₃,hN₃⟩ := upper
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn he
  have h1 : ((B₁ n).card:ℝ) ≤ (1/500:ℝ)*V n := hN₁ n ((le_max_left ..).trans hn) he
  have h2 : ((B₂ n).card:ℝ) ≤ (2/25:ℝ)*V n :=
    hN₂ n ((le_max_left N₂ N₃).trans ((le_max_right ..).trans hn)) he
  have h3 : ((B₃ n).card:ℝ) ≤ (189/500:ℝ)*V n :=
    hN₃ n ((le_max_right N₂ N₃).trans ((le_max_right ..).trans hn)) he
  have hcover : B n ⊆ B₁ n ∪ B₂ n ∪ B₃ n := by
    intro m hm
    by_cases hC : C n < m.minFac ∨ C n < (n-m).minFac
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm,hC⟩))
    · obtain ⟨hCL, hCR⟩ := not_or.mp hC
      by_cases hD : m.minFac ≤ D n ∧ (n-m).minFac ≤ D n
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm,hD⟩))
      · have hAbove : D n < m.minFac ∨ D n < (n-m).minFac := by
          by_cases hDL : m.minFac ≤ D n
          · exact Or.inr (lt_of_not_ge (fun hDR => hD ⟨hDL,hDR⟩))
          · exact Or.inl (lt_of_not_ge hDL)
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hm,le_of_not_gt hCL,le_of_not_gt hCR,hAbove⟩)
  have hcounts : (B n).card ≤ (B₁ n).card + (B₂ n).card + (B₃ n).card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le (B₁ n) (B₂ n)) _))
  have hcountsR : ((B n).card:ℝ) ≤ ((B₁ n).card:ℝ) + ((B₂ n).card:ℝ) + ((B₃ n).card:ℝ) := by
    exact_mod_cast hcounts
  linarith only [hcountsR,h1,h2,h3]
