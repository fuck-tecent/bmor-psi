import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_exchange :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (S : Finset (ℤ × ℤ)) (r x y : ℤ × ℤ), let T := S.erase r; ok S → x≠y → (∀ a∈T,∀ b∈T,a≠b → d a b x≠0 ∧ d a b y≠0) → (∀ a∈T,d x y a≠0) → ok (insert x (insert y T)) := by
  dsimp only
  intro S r x y hok hxy h1 h2 a ha b hb c hc hab hbc hac
  rcases Finset.mem_insert.mp ha with rfl | ha1
  · rcases Finset.mem_insert.mp hb with rfl | hb1
    · exact absurd rfl hab
    · rcases Finset.mem_insert.mp hb1 with rfl | hbT
      · rcases Finset.mem_insert.mp hc with rfl | hc1
        · exact absurd rfl hac
        · rcases Finset.mem_insert.mp hc1 with rfl | hcT
          · exact absurd rfl hbc
          · exact h2 c hcT
      · rcases Finset.mem_insert.mp hc with rfl | hc1
        · exact absurd rfl hac
        · rcases Finset.mem_insert.mp hc1 with rfl | hcT
          · intro h0; exact h2 b hbT (by linear_combination -h0)
          · intro h0; exact (h1 b hbT c hcT hbc).1 (by linear_combination h0)
  · rcases Finset.mem_insert.mp ha1 with rfl | haT
    · rcases Finset.mem_insert.mp hb with rfl | hb1
      · rcases Finset.mem_insert.mp hc with rfl | hc1
        · exact absurd rfl hbc
        · rcases Finset.mem_insert.mp hc1 with rfl | hcT
          · exact absurd rfl hac
          · intro h0; exact h2 c hcT (by linear_combination -h0)
      · rcases Finset.mem_insert.mp hb1 with rfl | hbT
        · exact absurd rfl hab
        · rcases Finset.mem_insert.mp hc with rfl | hc1
          · intro h0; exact h2 b hbT (by linear_combination h0)
          · rcases Finset.mem_insert.mp hc1 with rfl | hcT
            · exact absurd rfl hac
            · intro h0; exact (h1 b hbT c hcT hbc).2 (by linear_combination h0)
    · rcases Finset.mem_insert.mp hb with rfl | hb1
      · rcases Finset.mem_insert.mp hc with rfl | hc1
        · exact absurd rfl hbc
        · rcases Finset.mem_insert.mp hc1 with rfl | hcT
          · intro h0; exact h2 a haT (by linear_combination h0)
          · intro h0; exact (h1 a haT c hcT hac).1 (by linear_combination -h0)
      · rcases Finset.mem_insert.mp hb1 with rfl | hbT
        · rcases Finset.mem_insert.mp hc with rfl | hc1
          · intro h0; exact h2 a haT (by linear_combination -h0)
          · rcases Finset.mem_insert.mp hc1 with rfl | hcT
            · exact absurd rfl hbc
            · intro h0; exact (h1 a haT c hcT hac).2 (by linear_combination -h0)
        · rcases Finset.mem_insert.mp hc with rfl | hc1
          · exact (h1 a haT b hbT hab).1
          · rcases Finset.mem_insert.mp hc1 with rfl | hcT
            · exact (h1 a haT b hbT hab).2
            · exact hok a (Finset.mem_erase.mp haT).2 b (Finset.mem_erase.mp hbT).2 c (Finset.mem_erase.mp hcT).2 hab hbc hac
