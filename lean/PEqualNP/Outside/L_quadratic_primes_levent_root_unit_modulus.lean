import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_root_unit_modulus :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let psi := fun (q a x : ℕ) => ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n; ∀ q x : ℕ, 0<q → (∑ n ∈ (block x).filter (fun n => q ∣ n^2+1), ArithmeticFunction.vonMangoldt n) = ∑ r ∈ (roots 1 q).filter (fun r => Nat.Coprime r q), (psi q r (2*x) - psi q r x) := by
  intro block roots psi q x hq
  let B := block x
  let S := B.filter (fun n => q ∣ n^2+1)
  let T := (roots 1 q).filter (fun r => Nat.Coprime r q)
  have hroot (n : ℕ) : q ∣ (n % q)^2+1 ↔ q ∣ n^2+1 := by
    simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
  have hcop (r : ℕ) (hr : q ∣ r^2+1) : Nat.Coprime r q := by
    apply Nat.Coprime.of_dvd_right hr
    simpa [pow_two, add_comm] using (Nat.coprime_add_mul_left_right r 1 r).2 (Nat.coprime_one_right r)
  have hmaps : ∀ n ∈ S, n % q ∈ T := by
    intro n hn
    have hnroot : q ∣ n^2+1 := (Finset.mem_filter.mp hn).2
    have hr : q ∣ (n % q)^2+1 := (hroot n).2 hnroot
    change n % q ∈ ((Finset.range q).filter (fun r => q ∣ r^2+1)).filter (fun r => Nat.Coprime r q)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), hr⟩, hcop _ hr⟩
  have hpsi (r : ℕ) (hr : r ∈ T) : psi q r (2*x) - psi q r x =
      ∑ n ∈ S.filter (fun n => n % q = r), ArithmeticFunction.vonMangoldt n := by
    have hR : r ∈ roots 1 q := (Finset.mem_filter.mp hr).1
    have hrlt : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hR).1
    have hrroot : q ∣ r^2+1 := (Finset.mem_filter.mp hR).2
    have hsub : (Finset.Icc 1 x).filter (fun n => n % q = r % q) ⊆
        (Finset.Icc 1 (2*x)).filter (fun n => n % q = r % q) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    have hsets : ((Finset.Icc 1 (2*x)).filter (fun n => n % q = r % q)) \
        ((Finset.Icc 1 x).filter (fun n => n % q = r % q)) = S.filter (fun n => n % q = r) := by
      ext n
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      dsimp [S, B, block]
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      rw [Nat.mod_eq_of_lt hrlt]
      have hmod : n % q = r → q ∣ n^2+1 := by
        intro he
        apply (hroot n).1
        simpa [he] using hrroot
      constructor <;> intro hh <;> simp_all <;> omega
    have hh := Finset.sum_sdiff (f := fun n => ArithmeticFunction.vonMangoldt n) hsub
    rw [hsets] at hh
    change (∑ n ∈ (Finset.Icc 1 (2*x)).filter (fun n => n % q = r % q), ArithmeticFunction.vonMangoldt n) -
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = r % q), ArithmeticFunction.vonMangoldt n) = _
    linarith
  change (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) = ∑ r ∈ T, (psi q r (2*x) - psi q r x)
  calc
    _ = ∑ r ∈ T, ∑ n ∈ S.filter (fun n => n % q = r), ArithmeticFunction.vonMangoldt n :=
      (Finset.sum_fiberwise_of_maps_to hmaps (fun n => ArithmeticFunction.vonMangoldt n)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hpsi r hr).symm
