import Mathlib

theorem Conjectures.QuadraticPrimes.SieveEvenParameter :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; ∀ x : ℕ, 2≤x →
  ((Finset.Ioc x (2*x)).filter (fun n => (n^2+1).Prime)) =
    ((block x).filter (fun k => (f k).Prime)).image (fun k => 2*k) := by
  intro f block x hx
  ext n
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hn, hp⟩
    rw [Finset.mem_Ioc] at hn
    obtain ⟨h1, h2⟩ := hn
    have h4 : 4 ≤ n ^ 2 := by
      have h22 : 2 ≤ n := by omega
      calc 4 = 2*2 := by norm_num
        _ ≤ n*n := Nat.mul_le_mul h22 h22
        _ = n^2 := by ring
    have hpne : n ^ 2 + 1 ≠ 2 := by omega
    have hodd : Odd (n^2+1) := hp.odd_of_ne_two hpne
    have hn2e : Even (n^2) := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m, by omega⟩
    have h2dvd : (2:ℕ) ∣ n^2 := by
      obtain ⟨m, hm⟩ := hn2e
      exact ⟨m, by omega⟩
    have h2n : (2:ℕ) ∣ n := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    obtain ⟨k, hk⟩ := h2n
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hk] at h1
        exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).2 (by omega)
      · omega
      · rw [hk] at hp
        have he : (2*k)^2 + 1 = 4*k^2 + 1 := by ring
        rwa [he] at hp
    · omega
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    obtain ⟨⟨hk1, hk2⟩, hpk⟩ := hk
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hx1 : x < k * 2 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hk1
      omega
    · omega
    · have he : (2*k)^2 + 1 = 4*k^2 + 1 := by ring
      rwa [he]
