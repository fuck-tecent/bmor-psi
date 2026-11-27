import Mathlib

private def cS (n : ℕ) : Finset ℕ := (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n)

private lemma mem_cS {n k : ℕ} : k ∈ cS n ↔ k < n+1 ∧ n < 3*k ∧ 3*k < 2*n := by
  simp only [cS, Finset.mem_filter, Finset.mem_range]

private lemma le_of_mem_cS {n k : ℕ} (h : k ∈ cS n) : k ≤ n := by
  have h1 := (mem_cS.mp h).1
  omega

private lemma cS_mirror {n k : ℕ} (h : k ∈ cS n) : n - k ∈ cS n := by
  rw [mem_cS] at h ⊢
  omega

private lemma sub_inj_on {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : n - a = n - b) : a = b := by
  omega

private lemma image_card {n : ℕ} {A : Finset ℕ} (hA : A ⊆ cS n) :
    (A.image (fun k => n - k)).card = A.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact sub_inj_on (le_of_mem_cS (hA ha)) (le_of_mem_cS (hA hb)) hab

theorem PEqualNP.Outside.L_goldbach_central_support_max_weight :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n (A:Finset ℕ) (w:ℕ→ℝ) (M:ℝ), A⊆S n → (∀ k∈A,w k≤M) → (∑ k ∈ A,w k)≤(A.card:ℝ)*M := by
  change ∀ n (A : Finset ℕ) (w : ℕ → ℝ) (M : ℝ), A ⊆ cS n → (∀ k ∈ A, w k ≤ M) → (∑ k ∈ A, w k) ≤ (A.card : ℝ) * M
  intro n A w M _ hw
  calc ∑ k ∈ A, w k ≤ ∑ k ∈ A, M := Finset.sum_le_sum (fun k hk => hw k hk)
    _ = (A.card : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]
