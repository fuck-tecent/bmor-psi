import Mathlib

namespace Conjectures.Cuts.Taskbd367fa3aeb676e8acffa6f7_aux

/-- A sum over `m` complete blocks of length `q` of a function that only depends
on the offset inside the block is `m` times the sum over one block. -/
lemma sum_periodic (q : ℕ) (f : ℕ → ℕ) (m : ℕ)
    (hf : ∀ j i : ℕ, f (q * j + i) = f i) :
    ∑ i ∈ Finset.range (q * m), f i = m * ∑ i ∈ Finset.range q, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : q * (m + 1) = q * m + q := by ring
    have hrec : ∑ i ∈ Finset.range q, f (q * m + i) = ∑ i ∈ Finset.range q, f i :=
      Finset.sum_congr rfl (fun i _ => hf m i)
    rw [hsplit, Finset.sum_range_add, ih, hrec, Nat.succ_mul]

end Conjectures.Cuts.Taskbd367fa3aeb676e8acffa6f7_aux

theorem Conjectures.Cuts.Taskbd367fa3aeb676e8acffa6f7 :
    have x1 : Finset ℕ := {(1 : ℕ), (5 : ℕ), (11 : ℕ), (13 : ℕ), (17 : ℕ)}; have x2 : ℕ → ℕ → ℕ := fun (x2 x3 : ℕ) => {x4 ∈ Finset.range ((18 : ℕ) * x3) | x4 % (18 : ℕ) ∈ x1 ∧ (x2 % (18 : ℕ) + (18 : ℕ) - x4 % (18 : ℕ)) % (18 : ℕ) ∈ x1}.card; ∀ (x3 x4 : ℕ), Even x3 → x4 ≤ x2 x3 x4 ∧ x2 x3 x4 = x4 * x2 x3 (1 : ℕ) := by
  intro x1 x2
  let P : ℕ → ℕ → Prop := fun n i =>
    i % 18 ∈ x1 ∧ (n % 18 + 18 - i % 18) % 18 ∈ x1
  have hx2 : ∀ n m : ℕ, x2 n m = ((Finset.range (18 * m)).filter (P n)).card := by
    intro n m; rfl
  have hper : ∀ n j i : ℕ, P n (18 * j + i) ↔ P n i := by
    intro n j i
    have h : (18 * j + i) % 18 = i % 18 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    dsimp only [P]
    rw [h]
  have hmul : ∀ n m : ℕ, x2 n m = m * x2 n 1 := by
    intro n m
    rw [hx2, hx2, Finset.card_filter, Finset.card_filter]
    exact Conjectures.Cuts.Taskbd367fa3aeb676e8acffa6f7_aux.sum_periodic 18
      (fun i => if P n i then 1 else 0) m (fun j i => by simp only [hper n j i])
  intro n m hn
  refine ⟨?_, hmul n m⟩
  rw [hmul n m]
  have h1 : 1 ≤ x2 n 1 := by
    rw [hx2, Finset.one_le_card]
    have he : Even (n % 18) := by
      obtain ⟨k, hk⟩ := hn
      refine ⟨k % 9, ?_⟩
      have h3 : n % 18 = (2 * k) % 18 := by omega
      rw [h3, show (18 : ℕ) = 2 * 9 from rfl, Nat.mul_mod_mul_left]
      omega
    obtain ⟨k, hk⟩ := he
    have hk2 : n % 18 = 2 * k := by omega
    have hk9 : k < 9 := by omega
    interval_cases k
    · exact ⟨1, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨1, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨5, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨1, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨13, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨5, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨1, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨1, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
    · exact ⟨5, by rw [Finset.mem_filter]; refine ⟨by norm_num, ?_⟩; dsimp only [P]; rw [hk2]; norm_num [x1]⟩
  calc m = m * 1 := (Nat.mul_one m).symm
    _ ≤ m * x2 n 1 := Nat.mul_le_mul_left m h1
