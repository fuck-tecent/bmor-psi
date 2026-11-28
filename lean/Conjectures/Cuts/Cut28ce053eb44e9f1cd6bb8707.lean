import Mathlib

-- child 1 zh: 在无界的二倍区间上，把 n²+1 的质因子重数按对数加权；331/250 阈值以下的部分相对 2x log x 节省一个固定正比例。
-- child 1 en: On unbounded dyadic blocks, the logarithmic contribution of prime factors at or below the 331/250 threshold, counted with multiplicity, saves a fixed positive multiple of x log x from 2x log x.
-- child 2 zh: 对每个 x≥2，二倍区间内 n²+1 的全部质因子按重数计的对数总质量至少为 2x log x。
-- child 2 en: For every x at least two, the total logarithmic prime factor mass of n²+1 on the dyadic block, counted with multiplicity, is at least 2x log x.

theorem Conjectures.Cuts.Cut28ce053eb44e9f1cd6bb8707
    (hSmall : let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p : ℝ);
    ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ x : ℕ, B < x ∧
      (∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors.filter
        (fun p => p^250 ≤ n^331), w n p) ≤ (2-d)*(x:ℝ)*Real.log (x:ℝ))
    (hAll : let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p : ℝ);
    ∀ x : ℕ, 2 ≤ x → 2*(x:ℝ)*Real.log (x:ℝ) ≤
      ∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors, w n p) :
    (∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ n ^ 331 < p ^ 250) := by
  classical
  intro B
  obtain ⟨d, hd, hx⟩ := hSmall
  obtain ⟨x, hX, hS⟩ := hx (max B 2)
  have hBx : B < x := lt_of_le_of_lt (le_max_left ..) hX
  have hxTwo : 2 < x := lt_of_le_of_lt (le_max_right ..) hX
  by_contra hNo
  have hFilter (n : ℕ) (hn : n ∈ Finset.Ioc x (2*x)) :
      (n^2+1).primeFactors.filter (fun p => p^250 ≤ n^331) = (n^2+1).primeFactors := by
    apply Finset.filter_true_of_mem
    intro p hp
    apply le_of_not_gt
    intro hhi
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact hNo ⟨n,p,hBx.trans (Finset.mem_Ioc.mp hn).1,hprime,hdvd,hhi⟩
  let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p:ℝ)
  have hEq :
      (∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors.filter (fun p => p^250 ≤ n^331), w n p) =
      ∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors, w n p := by
    apply Finset.sum_congr rfl; intro n hn; rw [hFilter n hn]
  change (∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors.filter (fun p => p^250 ≤ n^331),
      w n p) ≤ (2-d)*(x:ℝ)*Real.log (x:ℝ) at hS
  rw [hEq] at hS
  have hA := hAll x hxTwo.le
  change 2*(x:ℝ)*Real.log (x:ℝ) ≤
      ∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors, w n p at hA
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hPos : 0 < d * (x:ℝ) * Real.log (x:ℝ) :=
    mul_pos (mul_pos hd (by linarith)) (Real.log_pos hxR)
  nlinarith only [hA.trans hS,hPos]
