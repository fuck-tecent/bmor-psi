import Mathlib

/-!
新路线 · Levent GRH 与自然扩张 · QP-0003 · 从模 4 的累积误差得到倍增区间误差

所用的恒等式：区间 (x, 2x] 上的质量是两个端点累积量之差，
(psi 4 1 (2*x) - psi 4 1 x) - x/2 = (psi 4 1 (2*x) - x/2) - (psi 4 1 x - x/2)，
其中自然数 2*x 的实像除以 2 等于 x 的实像的一半；两端各自的偏差由假设 E 控制，再用三角不等式相加。
量词与假设：E 是任意实值函数，x 是任意自然数；前提是命题里写明的两条端点误差界。
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_dyadic_scale :
    let psi := fun (q a x : ℕ) => ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n; ∀ (E : ℕ → ℝ) (x : ℕ), |psi 4 1 x - (x : ℝ)/2| ≤ E x → |psi 4 1 (2*x) - (2*x : ℕ)/ (2 : ℝ)| ≤ E (2*x) → |(psi 4 1 (2*x) - psi 4 1 x) - (x : ℝ)/2| ≤ E (2*x) + E x := by
  intro psi E x h1 h2
  have hcast : ((2*x : ℕ) : ℝ) / (2 : ℝ) = (x : ℝ) := by
    push_cast
    ring
  rw [hcast] at h2
  have hid : (psi 4 1 (2*x) - psi 4 1 x) - (x : ℝ)/2
      = (psi 4 1 (2*x) - (x : ℝ)) - (psi 4 1 x - (x : ℝ)/2) := by ring
  rw [hid]
  calc |(psi 4 1 (2*x) - (x : ℝ)) - (psi 4 1 x - (x : ℝ)/2)|
      ≤ |psi 4 1 (2*x) - (x : ℝ)| + |psi 4 1 x - (x : ℝ)/2| := abs_sub _ _
    _ ≤ E (2*x) + E x := add_le_add h2 h1
