import Mathlib

-- child 1 zh: 存在固定 d > 0，使对任意边长下界 B，存在边长 n > B 及网格点集 T ⊆ [0, n)²，满足点数减去严格字典序共线三元组数至少为 (3/2 + d)n。
-- child 1 en: There exists a fixed d > 0 such that for every B there is n > B and a grid subset T ⊆ [0, n)² whose cardinality minus the number of lexicographically ordered collinear triples in T is at least (3/2 + d)n.
-- child 2 zh: 通用删点清理引理：对任意有限格点集 T，存在不含严格字典序共线三元组的子集 S ⊆ T，且最多删去不超过 T 中共线三元组数的点。
-- child 2 en: General deletion lemma: every finite set T of lattice points contains a subset S ⊆ T with no lexicographically ordered collinear triples such that |T| ≤ |S| + |collinearTriples(T)|.

theorem Conjectures.Cuts.Cut57ae3db4334bf1e3dc66fdfb
    (h_family :
      ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ T : Finset (ℕ × ℕ),
        (∀ z ∈ T, z.1 < n ∧ z.2 < n) ∧
        (3 / 2 + d) * (n : ℝ) +
          ((((T ×ˢ T) ×ˢ T).filter fun p =>
            (p.1.1.1 < p.1.2.1 ∨ (p.1.1.1 = p.1.2.1 ∧ p.1.1.2 < p.1.2.2)) ∧
            (p.1.2.1 < p.2.1 ∨ (p.1.2.1 = p.2.1 ∧ p.1.2.2 < p.2.2)) ∧
            ((p.1.2.1 : ℤ) - (p.1.1.1 : ℤ)) * ((p.2.2 : ℤ) - (p.1.1.2 : ℤ)) =
              ((p.1.2.2 : ℤ) - (p.1.1.2 : ℤ)) * ((p.2.1 : ℤ) - (p.1.1.1 : ℤ))).card : ℝ)
          ≤ (T.card : ℝ))
    (h_delete :
      ∀ T : Finset (ℕ × ℕ), ∃ S : Finset (ℕ × ℕ), S ⊆ T ∧
        (((S ×ˢ S) ×ˢ S).filter fun p =>
          (p.1.1.1 < p.1.2.1 ∨ (p.1.1.1 = p.1.2.1 ∧ p.1.1.2 < p.1.2.2)) ∧
          (p.1.2.1 < p.2.1 ∨ (p.1.2.1 = p.2.1 ∧ p.1.2.2 < p.2.2)) ∧
          ((p.1.2.1 : ℤ) - (p.1.1.1 : ℤ)) * ((p.2.2 : ℤ) - (p.1.1.2 : ℤ)) =
            ((p.1.2.2 : ℤ) - (p.1.1.2 : ℤ)) * ((p.2.1 : ℤ) - (p.1.1.1 : ℤ))) = ∅ ∧
        T.card ≤ S.card +
          (((T ×ˢ T) ×ˢ T).filter fun p =>
            (p.1.1.1 < p.1.2.1 ∨ (p.1.1.1 = p.1.2.1 ∧ p.1.1.2 < p.1.2.2)) ∧
            (p.1.2.1 < p.2.1 ∨ (p.1.2.1 = p.2.1 ∧ p.1.2.2 < p.2.2)) ∧
            ((p.1.2.1 : ℤ) - (p.1.1.1 : ℤ)) * ((p.2.2 : ℤ) - (p.1.1.2 : ℤ)) =
              ((p.1.2.2 : ℤ) - (p.1.1.2 : ℤ)) * ((p.2.1 : ℤ) - (p.1.1.1 : ℤ))).card) :
    (let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ S : Finset (ℕ × ℕ), valid n S ∧ (3/2+d)*(n:ℝ) ≤ (S.card:ℝ)) := by
  -- 严格字典序比较（用于将任意三个互异格点规范排序）
  let ltPt : ℕ × ℕ → ℕ × ℕ → Prop := fun p q =>
    p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)
  -- 任意两个互异格点必满足字典序严格可比
  have htrich : ∀ p q : ℕ × ℕ, p ≠ q → ltPt p q ∨ ltPt q p := by
    intro p q hpq
    rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases lt_trichotomy p.2 q.2 with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exfalso
        exact hpq (Prod.ext h1 h2)
      · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inr (Or.inl h1)
  -- 任意三个互异点必能按字典序排列成递增三元组
  have horder3 : ∀ a b c : ℕ × ℕ, a ≠ b → a ≠ c → b ≠ c →
      (ltPt a b ∧ ltPt b c) ∨ (ltPt a c ∧ ltPt c b) ∨
      (ltPt b a ∧ ltPt a c) ∨ (ltPt b c ∧ ltPt c a) ∨
      (ltPt c a ∧ ltPt a b) ∨ (ltPt c b ∧ ltPt b a) := by
    intro a b c hab hac hbc
    have h1 := htrich a b hab
    have h2 := htrich a c hac
    have h3 := htrich b c hbc
    rcases h1 with hab' | hba' <;> rcases h2 with hac' | hca' <;> rcases h3 with hbc' | hcb'
    · exact Or.inl ⟨hab', hbc'⟩
    · exact Or.inr (Or.inl ⟨hac', hcb'⟩)
    · exfalso
      dsimp only [ltPt] at hab' hca' hbc'
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hca', hab'⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨hba', hac'⟩))
    · exfalso
      dsimp only [ltPt] at hba' hac' hcb'
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc', hca'⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcb', hba'⟩))))
  obtain ⟨d, hd, hfam⟩ := h_family
  refine ⟨d, hd, ?_⟩
  intro B
  obtain ⟨n, hBn, T, hTbox, hTcard⟩ := hfam B
  obtain ⟨S, hST, hSempty, hScard⟩ := h_delete T
  refine ⟨n, hBn, S, ?_, ?_⟩
  · -- 证明 S 满足网格边界条件与无三点共线条件
    refine ⟨fun z hz => hTbox z (hST hz), ?_⟩
    intro a ha b hb c hc hab hac hbc hcol
    -- 辅助：若存在规范递增的共线三元组，则与 hSempty 矛盾
    have hcontra : ∀ x y z : ℕ × ℕ, x ∈ S → y ∈ S → z ∈ S →
        ltPt x y → ltPt y z →
        ((y.1 : ℤ) - (x.1 : ℤ)) * ((z.2 : ℤ) - (x.2 : ℤ)) =
          ((y.2 : ℤ) - (x.2 : ℤ)) * ((z.1 : ℤ) - (x.1 : ℤ)) → False := by
      intro x y z hx hy hz hxy hyz hxyz
      have hmem : ((x, y), z) ∈
          (((S ×ˢ S) ×ˢ S).filter fun p =>
            (p.1.1.1 < p.1.2.1 ∨ (p.1.1.1 = p.1.2.1 ∧ p.1.1.2 < p.1.2.2)) ∧
            (p.1.2.1 < p.2.1 ∨ (p.1.2.1 = p.2.1 ∧ p.1.2.2 < p.2.2)) ∧
            ((p.1.2.1 : ℤ) - (p.1.1.1 : ℤ)) * ((p.2.2 : ℤ) - (p.1.1.2 : ℤ)) =
              ((p.1.2.2 : ℤ) - (p.1.1.2 : ℤ)) * ((p.2.1 : ℤ) - (p.1.1.1 : ℤ))) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩, hxy, hyz, hxyz⟩
      rw [hSempty] at hmem
      exact Finset.notMem_empty _ hmem
    -- 利用二维叉积在 6 种排列下的不变性逐一推出矛盾
    rcases horder3 a b c hab hac hbc with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hcontra a b c ha hb hc h1 h2 hcol
    · exact hcontra a c b ha hc hb h1 h2 (by linarith)
    · exact hcontra b a c hb ha hc h1 h2 (by linarith)
    · exact hcontra b c a hb hc ha h1 h2 (by linarith)
    · exact hcontra c a b hc ha hb h1 h2 (by linarith)
    · exact hcontra c b a hc hb ha h1 h2 (by linarith)
  · -- 由点数与共线三元组数的线性不等式推出最终密度下界
    have hScardR : (T.card : ℝ) ≤ (S.card : ℝ) +
        ((((T ×ˢ T) ×ˢ T).filter fun p =>
          (p.1.1.1 < p.1.2.1 ∨ (p.1.1.1 = p.1.2.1 ∧ p.1.1.2 < p.1.2.2)) ∧
          (p.1.2.1 < p.2.1 ∨ (p.1.2.1 = p.2.1 ∧ p.1.2.2 < p.2.2)) ∧
          ((p.1.2.1 : ℤ) - (p.1.1.1 : ℤ)) * ((p.2.2 : ℤ) - (p.1.1.2 : ℤ)) =
            ((p.1.2.2 : ℤ) - (p.1.1.2 : ℤ)) * ((p.2.1 : ℤ) - (p.1.1.1 : ℤ))).card : ℝ) := by
      exact_mod_cast hScard
    linarith
