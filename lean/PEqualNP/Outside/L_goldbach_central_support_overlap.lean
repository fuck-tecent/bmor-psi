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

theorem PEqualNP.Outside.L_goldbach_central_support_overlap :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n (A B : Finset ℕ), A⊆S n → B⊆S n → A.card+B.card≤(S n).card+(A∩B.image (fun k => n-k)).card := by
  change ∀ n (A B : Finset ℕ), A ⊆ cS n → B ⊆ cS n → A.card + B.card ≤ (cS n).card + (A ∩ B.image (fun k => n - k)).card
  intro n A B hA hB
  have hA' : (A.image (fun k => n - k)).card = A.card := image_card hA
  have hB' : (B.image (fun k => n - k)).card = B.card := image_card hB
  have hsub : A ∪ B.image (fun k => n - k) ⊆ cS n := by
    intro k hk
    rcases Finset.mem_union.mp hk with h | h
    · exact hA h
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact cS_mirror (hB hb)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_add_card_inter A (B.image (fun k => n - k))
  omega
