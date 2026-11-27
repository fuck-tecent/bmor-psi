import Mathlib

/-!
新路线 · Levent GRH 与自然扩张 · QP-0070 · 从素数质量为正提取区间内的素数值

所用的恒等式：有限和不为零，则其中至少有一项不为零；于是在区间 (x, 2x] 里能找到一个 n，
使 n^2+1 是素数，取 p 等于它即可。
量词与假设：x 是任意自然数，前提是素数质量 primeMass x 为正。
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_cofactor_mass :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let primeMass := fun x : ℕ => ∑ n ∈ (block x).filter (fun n => Nat.Prime (n^2+1)), Real.log ((n^2+1 : ℕ) : ℝ); ∀ x : ℕ, 0 < primeMass x → ∃ n ∈ block x, ∃ p : ℕ, p.Prime ∧ n^2+1=p := by
  intro block primeMass x h
  obtain ⟨n, hn, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  exact ⟨n, (Finset.mem_filter.1 hn).1, n^2+1, (Finset.mem_filter.1 hn).2, rfl⟩
