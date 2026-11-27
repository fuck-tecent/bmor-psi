import Mathlib

/-!
把起点条件化为两个坐标各自独立的范围：可行起点集正好是长度 n-42 与 n-2 的两个区间之积。
先证过滤后的乘积等于两个过滤后区间的乘积，再把两个区间分别认成 Finset.range (n-42) 与 Finset.range (n-2)，
最后数出两个区间的长度。
-/

theorem PEqualNP.Outside.L_no_three_in_line_cert_21_1 : ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+42<n ∧ z.2+2<n)).card=(n-42)*(n-2) := by
  intro n
  have hset :
      ((Finset.range n).product (Finset.range n)).filter (fun z => z.1+42<n ∧ z.2+2<n)
        = ((Finset.range n).filter (fun x => x+42<n)).product ((Finset.range n).filter (fun y => y+2<n)) := by
    ext z
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hx : (Finset.range n).filter (fun x => x+42<n) = Finset.range (n-42) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · intro h
      exact ⟨by omega, by omega⟩
  have hy : (Finset.range n).filter (fun y => y+2<n) = Finset.range (n-2) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · intro h
      exact ⟨by omega, by omega⟩
  rw [hset, hx, hy]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
