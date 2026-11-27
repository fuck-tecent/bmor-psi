import Mathlib

/-!
# E05: 每 105 个连续奇参数的双边局部筛密度

对每个 i 令 x = 2^s * (2*(a+i)+1)。i 取遍 0..104 时，2*(a+i)+1 模 105 取遍全部剩余类，
再乘以与 105 互素的 2^s 仍是一个置换，故所求的计数等于 r 取遍 0..104 时满足
r+104 与 105 互素、且 (n+1+105-r) 模 105 与 105 互素的 r 的个数。
第一条件等价于 r 不同余 1 模 3、5、7，第二条件等价于 r 不同余 n+1 模 3、5、7；
每个素数处至多禁掉两个剩余类，由中国剩余定理计数至少 (3-2)*(5-2)*(7-2) = 15。
形式化路线：先用一个显式双射把 i 换成 r = x 模 105，再把 n 换成 n 模 105，
最后对 105 种情形逐一判定。
-/

namespace Conjectures.Goldbach.Rfc11CmParameterLocalDensity_aux

lemma coprime_shift (x : ℕ) :
    Nat.Coprime (x + 104) 105 ↔ Nat.Coprime (x % 105 + 104) 105 := by
  rw [← ZMod.coprime_mod_iff_coprime (x + 104) 105,
    ← ZMod.coprime_mod_iff_coprime (x % 105 + 104) 105]
  have h : (x + 104) % 105 = (x % 105 + 104) % 105 := by omega
  rw [h]

lemma inj_aux (s a i j : ℕ) (hi : i < 105) (hj : j < 105)
    (h : (2 ^ s * (2 * (a + i) + 1)) % 105 = (2 ^ s * (2 * (a + j) + 1)) % 105) : i = j := by
  have hm : 2 ^ s * (2 * (a + i) + 1) ≡ 2 ^ s * (2 * (a + j) + 1) [MOD 105] := h
  have e1 : 2 ^ s * (2 * (a + i) + 1) = 2 ^ s * (2 * a + 1) + 2 ^ (s + 1) * i := by ring
  have e2 : 2 ^ s * (2 * (a + j) + 1) = 2 ^ s * (2 * a + 1) + 2 ^ (s + 1) * j := by ring
  rw [e1, e2] at hm
  have h2 : 2 ^ (s + 1) * i ≡ 2 ^ (s + 1) * j [MOD 105] := Nat.ModEq.add_left_cancel' _ hm
  have hc : Nat.Coprime 105 (2 ^ (s + 1)) := by
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos s)]
    decide
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    have hd : 105 ∣ 2 ^ (s + 1) * j - 2 ^ (s + 1) * i :=
      (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left _ hlt.le)).mp h2
    rw [← Nat.mul_sub] at hd
    have hd' : 105 ∣ (j - i) * 2 ^ (s + 1) := by rw [mul_comm]; exact hd
    have hz : 105 ∣ j - i := hc.dvd_mul_right.mp hd'
    have hle : 105 ≤ j - i := Nat.le_of_dvd (by omega) hz
    omega
  · exact heq
  · exfalso
    have hd : 105 ∣ 2 ^ (s + 1) * i - 2 ^ (s + 1) * j :=
      (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left _ hgt.le)).mp h2.symm
    rw [← Nat.mul_sub] at hd
    have hd' : 105 ∣ (i - j) * 2 ^ (s + 1) := by rw [mul_comm]; exact hd
    have hz : 105 ∣ i - j := hc.dvd_mul_right.mp hd'
    have hle : 105 ≤ i - j := Nat.le_of_dvd (by omega) hz
    omega

lemma card_reduce (n s a : ℕ) :
    ((Finset.range 105).filter (fun i => let x := 2 ^ s * (2 * (a + i) + 1);
        Nat.Coprime (x + 104) 105 ∧ Nat.Coprime ((n + 1 + 105 - (x % 105)) % 105) 105)).card
      = ((Finset.range 105).filter (fun r =>
        Nat.Coprime (r + 104) 105 ∧ Nat.Coprime ((n + 1 + 105 - r) % 105) 105)).card := by
  classical
  let f : ℕ → ℕ := fun i => (2 ^ s * (2 * (a + i) + 1)) % 105
  have hflt : ∀ i, f i < 105 := fun i => Nat.mod_lt _ (by norm_num)
  have hinj : Set.InjOn f (Finset.range 105 : Set ℕ) := by
    intro i hi j hj h
    exact inj_aux s a i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have himg : (Finset.range 105).image f = Finset.range 105 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact Finset.mem_range.mpr (hflt i)
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hfilter : (Finset.range 105).filter (fun i => let x := 2 ^ s * (2 * (a + i) + 1);
        Nat.Coprime (x + 104) 105 ∧ Nat.Coprime ((n + 1 + 105 - (x % 105)) % 105) 105)
      = (Finset.range 105).filter (fun i =>
        Nat.Coprime (f i + 104) 105 ∧ Nat.Coprime ((n + 1 + 105 - (f i)) % 105) 105) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, f]
    constructor <;> intro h
    · refine ⟨h.1, (coprime_shift _).mp h.2.1, h.2.2⟩
    · refine ⟨h.1, (coprime_shift _).mpr h.2.1, h.2.2⟩
  rw [hfilter]
  refine Finset.card_bij (fun i _ => f i) ?_ ?_ ?_
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hflt i), hi'.2⟩
  · intro i hi j hj h
    exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 h
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbmem : b ∈ (Finset.range 105).image f := by rw [himg]; exact hb'.1
    rw [Finset.mem_image] at hbmem
    obtain ⟨i, hi, hfb⟩ := hbmem
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, hfb⟩
    rw [hfb]
    exact hb'.2

lemma base (k : ℕ) (hk : k < 105) :
    15 ≤ ((Finset.range 105).filter (fun r =>
      Nat.Coprime (r + 104) 105 ∧ Nat.Coprime ((k + 1 + 105 - r) % 105) 105)).card := by
  interval_cases k <;> decide

end Conjectures.Goldbach.Rfc11CmParameterLocalDensity_aux

theorem Conjectures.Goldbach.Rfc11CmParameterLocalDensity :
    ∀ n s a : ℕ, 2∣n → 1 ≤ s → 15 ≤ ((Finset.range 105).filter (fun i => let x := 2^s*(2*(a+i)+1); Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x % 105)) % 105) 105)).card := by
  classical
  intro n s a hn hs
  rw [Conjectures.Goldbach.Rfc11CmParameterLocalDensity_aux.card_reduce]
  have hk : n % 105 < 105 := Nat.mod_lt n (by norm_num)
  have hred : (Finset.range 105).filter (fun r =>
        Nat.Coprime (r + 104) 105 ∧ Nat.Coprime ((n + 1 + 105 - r) % 105) 105)
      = (Finset.range 105).filter (fun r =>
        Nat.Coprime (r + 104) 105 ∧ Nat.Coprime (((n % 105) + 1 + 105 - r) % 105) 105) := by
    refine Finset.filter_congr (fun r hr => ?_)
    simp only [Finset.mem_range] at hr
    have heq : (n + 1 + 105 - r) % 105 = ((n % 105) + 1 + 105 - r) % 105 := by omega
    constructor <;> intro h
    · refine ⟨h.1, ?_⟩
      rw [← heq]; exact h.2
    · refine ⟨h.1, ?_⟩
      rw [heq]; exact h.2
  rw [hred]
  exact Conjectures.Goldbach.Rfc11CmParameterLocalDensity_aux.base (n % 105) hk
