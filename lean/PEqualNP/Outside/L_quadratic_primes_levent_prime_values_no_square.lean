import Mathlib

/-!
新路线 · Levent GRH 与自然扩张 · QP-0064 · 排除 n²+1 等于平方及偶指数真幂

命题：对任意自然数 n、p、j，在 0 < n 与 0 < j 之下，n²+1 不等于 p^(2*j)。

所用的恒等式与事实：
- 指数拆分 p^(2*j) = (p^j)²，所以偶数次幂是完全平方；
- n² < n²+1 < (n+1)²，即 n²+1 严格落在两个相邻的平方之间；
- 平方在自然数上单调：a ≤ b 推出 a² ≤ b²。

于是若 n²+1 = (p^j)²，由 n² < (p^j)² 与平方的单调性得 n < p^j，由 (p^j)² < (n+1)² 得 p^j < n+1，
两者给出 p^j = n，代回得 n²+1 = n²，矛盾。

量词：n、p、j 全称量词，取遍自然数。仍需的假设：0 < n 与 0 < j。
证明只用到相邻平方之间的间隙与平方的单调性，对 p 没有素数性要求。
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_no_square :
    ∀ n p j : ℕ, 0<n → 0<j → n^2+1 ≠ p^(2*j) := by
  intro n p j hn _hj h
  -- 偶数次幂是完全平方：p^(2*j) = (p^j)²
  have hsq : p ^ (2 * j) = (p ^ j) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hsq] at h
  -- 左端严格大于 n²
  have hlt : n ^ 2 < (p ^ j) ^ 2 := by omega
  -- 平方单调，所以 n < p^j
  have hnm : n < p ^ j := by
    by_contra! hc
    have hle := pow_le_pow_left' hc 2
    omega
  -- 右端不超过 2n，严格小于 (n+1)²
  have hbig : n ^ 2 + 1 < (n + 1) ^ 2 := by
    have hs : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hs]
    omega
  -- 再由平方单调得 p^j < n+1
  have hm : p ^ j < n + 1 := by
    by_contra! hc
    have hle := pow_le_pow_left' hc 2
    omega
  -- 夹在 n 与 n+1 之间，只能是 n，代回矛盾
  have hpn : p ^ j = n := by omega
  rw [hpn] at h
  omega
