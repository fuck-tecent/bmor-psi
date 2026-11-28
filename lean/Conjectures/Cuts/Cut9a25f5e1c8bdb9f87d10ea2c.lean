import Mathlib

-- child 1 zh: 对任意长度 M 和位移 h，模 30 轮筛的双点相关和与 M 乘精确周期均值的误差至多 450。奇位移均值为零，偶位移按 3、5 的整除性分组。
-- child 1 en: For every length M and lag h, the two-point correlation of the mod-30 wheel differs from M times its exact period mean by at most 450. The mean vanishes at odd lags and distinguishes divisibility by 3 and 5 at even lags.
-- child 2 zh: 在冻结的正共振次弧集合上，所有长位移余弦系数绝对值的总和为 o(n)，对奇偶 n 均成立。
-- child 2 en: The sum of the absolute values of the long-lag cosine coefficients of the frozen resonant minor arcs is o(n), for both even and odd n.
-- child 3 zh: 对充分大偶数 n，高段素数对相关减去含奇偶限制的模 30 周期均值，按原余弦系数带符号求和后至多为 n/2304。
-- child 3 en: For all sufficiently large even n, the signed long-lag sum of the high-prime correlations after subtracting the parity-sensitive mod-30 mean is at most n/2304, including the factor of two.

theorem Conjectures.Cuts.Cut9a25f5e1c8bdb9f87d10ea2c
    (wheel : let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0;
      let ρ := fun h : ℕ => if 2 ∣ h then (15:ℝ)/32 * (if 3 ∣ h then 2 else 1) * (if 5 ∣ h then 4 else 3) else 0;
      ∀ M h : ℕ, |(∑ k ∈ Finset.range M, model k * model (k+h)) - (M:ℝ) * ρ h| ≤ 450)
    (fourier : let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
      let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
      let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
      let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
      let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume;
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        (∑ h ∈ Finset.Icc ((L n)^2+1) n, |V n h|) ≤ ε * (n:ℝ))
    (prime : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
      let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
      let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
      let high := fun (n k : ℕ) => w k-low n k;
      let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
      let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
      let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
      let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume;
      let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h);
      let ρ := fun h : ℕ => if 2 ∣ h then (15:ℝ)/32 * (if 3 ∣ h then 2 else 1) * (if 5 ∣ h then 4 else 3) else 0;
      ∃ N : ℕ, ∀ n ≥ N, Even n →
        2 * (∑ h ∈ Finset.Icc ((L n)^2+1) n,
          (A n h (high n) - ((n+1-h:ℕ):ℝ) * ρ h) * V n h) ≤ (n:ℝ)/2304) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
     let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
     let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
     let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
     let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
     let high := fun (n k : ℕ) => w k-low n k;
     let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
     let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume;
     let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume;
     let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h);
     let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0;
     let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h);
     let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h);
     ∃ N : ℕ, ∀ n ≥ N, Even n → long n (high n) - long n model ≤ (n:ℝ)/1152) := by
  intro w E S Q arcs low high I L K B U V A model short long
  let ρ := fun h : ℕ => if 2 ∣ h then (15:ℝ)/32 * (if 3 ∣ h then 2 else 1) * (if 5 ∣ h then 4 else 3) else 0
  change ∀ M h : ℕ, |(∑ k ∈ Finset.range M, model k * model (k+h)) - (M:ℝ) * ρ h| ≤ 450 at wheel
  change ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ h ∈ Finset.Icc ((L n)^2+1) n, |V n h|) ≤ ε * (n:ℝ) at fourier
  change ∃ N : ℕ, ∀ n ≥ N, Even n →
    2 * (∑ h ∈ Finset.Icc ((L n)^2+1) n,
      (A n h (high n) - ((n+1-h:ℕ):ℝ) * ρ h) * V n h) ≤ (n:ℝ)/2304 at prime
  obtain ⟨N₁,h₁⟩ := fourier (1 / 2073600) (by norm_num)
  obtain ⟨N₂,h₂⟩ := prime
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn even
  let D := Finset.Icc ((L n)^2+1) n
  let mean := fun h : ℕ => ((n+1-h:ℕ):ℝ) * ρ h
  have err (h : ℕ) : |mean h - A n h model| ≤ 450 := by
    rw [abs_sub_comm]
    exact wheel (n+1-h) h
  have term (h : ℕ) : (mean h - A n h model) * V n h ≤ 450 * |V n h| := by
    calc
      _ ≤ |(mean h - A n h model) * V n h| := le_abs_self _
      _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (err h) (abs_nonneg _)
  have remainder : (∑ h ∈ D, (mean h - A n h model) * V n h) ≤ 450 * ((1/2073600) * n) := by
    calc
      _ ≤ ∑ h ∈ D, 450 * |V n h| := Finset.sum_le_sum (fun h _ => term h)
      _ = _ := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (h₁ n ((le_max_left ..).trans hn)) (by norm_num)
  have main := h₂ n ((le_max_right ..).trans hn) even
  change 2 * (∑ h ∈ D, (A n h (high n) - mean h) * V n h) ≤ (n:ℝ)/2304 at main
  calc
    long n (high n) - long n model =
        2 * (∑ h ∈ D, (A n h (high n) - mean h) * V n h) +
        2 * (∑ h ∈ D, (mean h - A n h model) * V n h) := by
          dsimp only [long, D]
          simp only [sub_mul, Finset.sum_sub_distrib]
          ring
    _ ≤ (n:ℝ)/1152 := by linarith
