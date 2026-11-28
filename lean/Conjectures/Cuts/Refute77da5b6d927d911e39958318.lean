import Mathlib
import Conjectures.Goldbach.PacketLagEnergyIdentity
import Conjectures.Goldbach.PacketWheelMaskedBudget
import Conjectures.Goldbach.PacketShortWheelError

open Finset Conjectures.Goldbach.PacketShortWheelError_aux
open GoldbachPacket

namespace WheelRefute

open Conjectures.Goldbach.PacketShortWheelError_aux

noncomputable def lagLong (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  2 * ∑ h ∈ Finset.Icc ((GoldbachPacket.length n)^2 + 1) n,
    GoldbachPacket.correlation n h a * GoldbachPacket.cosineMoment n h

noncomputable def lagEnergy (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  intervalIntegral ((GoldbachPacket.resonant n).indicator
    (fun t => ‖GoldbachBudget.spec n a t‖^2)) 0 1 MeasureTheory.volume

theorem lag_energy_split (n : ℕ) (a : ℕ → ℝ) :
    lagEnergy n a = GoldbachPacket.shortPart n a + lagLong n a :=
  Conjectures.Goldbach.PacketLagEnergyIdentity n a

theorem uniform_short : ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ → ℝ,
    (∀ k ≤ n, |a k| ≤ 4) → |GoldbachPacket.shortPart n a| ≤ (n:ℝ)/10000 := by
  obtain ⟨N,hN⟩ := GoldbachPacket.maskLogDecay 4 (1/2880000) (by norm_num)
  refine ⟨max 1 N, ?_⟩
  intro n hn a cap
  have pos : 1 ≤ n := (le_max_left ..).trans hn
  have logz := Real.log_nonneg (by exact_mod_cast pos : (1:ℝ) ≤ n)
  have q := GoldbachPacket.shortAtLogScale n pos a (fun k hk => (cap k hk).trans (by linarith))
  have t := hN n ((le_max_right ..).trans hn)
  rw [← GoldbachPacket.zeroMoment] at t
  have u := mul_le_mul_of_nonneg_left t (Nat.cast_nonneg (α:=ℝ) n)
  linarith only [q,u]

theorem long_lower : ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ → ℝ,
    (∀ k ≤ n, |a k| ≤ 4) → -(n:ℝ)/10000 ≤ lagLong n a := by
  obtain ⟨N,hs⟩ := uniform_short
  refine ⟨N,?_⟩
  intro n hn a ha
  have energy : 0 ≤ lagEnergy n a :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t _ => Set.indicator_nonneg (fun x _=>sq_nonneg _) t)
  rw [lag_energy_split] at energy
  have bound := (abs_le.mp (hs n hn a ha)).2
  linarith only [energy,bound]

theorem wheel_long_upper : ∃ N : ℕ, ∀ n ≥ N, Even n →
    lagLong n GoldbachPacket.wheel ≤ (n:ℝ)/2304 + (n:ℝ)/10000 := by
  have wheel : ∃ N : ℕ, ∀ n ≥ N, Even n → lagEnergy n GoldbachPacket.wheel ≤ (n:ℝ)/2304 :=
    Conjectures.Goldbach.PacketWheelMaskedBudget
  obtain ⟨K,hw⟩ := wheel
  obtain ⟨N,hs⟩ := uniform_short
  refine ⟨max N K,?_⟩
  intro n hn ev
  have b := hw n ((le_max_right ..).trans hn) ev
  rw [lag_energy_split] at b
  have cap (k : ℕ) (_ : k ≤ n) : |GoldbachPacket.wheel k| ≤ 4 := by
    unfold GoldbachPacket.wheel
    split <;> norm_num
  have z := (abs_le.mp (hs n ((le_max_left ..).trans hn) _ cap)).1
  linarith only [b,z]

end WheelRefute

namespace WheelRefute

open Conjectures.Goldbach.PacketShortWheelError_aux
open Finset

def resWeight (n d r k : ℕ) : ℝ :=
  if k < n ∧ k % d = r then 1 else 0

theorem resWeight_bound (n d r k : ℕ) : |resWeight n d r k| ≤ (4 : ℝ) := by
  unfold resWeight
  split_ifs <;> norm_num

private theorem residue_pair_sum (n d h k : ℕ) (hd : 0 < d) :
    (∑ r ∈ Finset.range d, resWeight n d r k * resWeight n d r (k+h)) =
      if k+h < n ∧ d ∣ h then (1:ℝ) else 0 := by
  by_cases hk : k+h < n
  · have hk' : k < n := by omega
    have hkd : k % d ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
    have hkd' : (k+h) % d ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
    have hmod : k % d = (k+h) % d ↔ d ∣ h := by
      simpa only [Nat.ModEq] using (Nat.left_modEq_add_iff : k ≡ k+h [MOD d] ↔ d ∣ h)
    simp [resWeight, hk, hk', hkd, hkd', hmod]
  · simp [resWeight, hk]

theorem sum_autocorr (n d h : ℕ) (hd : 0 < d) (hh : h ≤ n) :
    (∑ r ∈ Finset.range d, GoldbachPacket.correlation n h (resWeight n d r)) =
      if d ∣ h then (n:ℝ)-h else 0 := by
  simp only [GoldbachPacket.correlation]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (by
    intro k hk
    exact residue_pair_sum n d h k hd)]
  by_cases dh : d ∣ h
  · simp only [dh, and_true, ite_true]
    have hiff (k : ℕ) : k+h < n ↔ k < n-h := by omega
    simp_rw [hiff]
    calc
      (∑ k ∈ Finset.range (n+1-h), if k < n-h then (1:ℝ) else 0) =
          ∑ k ∈ (Finset.range (n+1-h)).filter (· < n-h), (1:ℝ) := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range (n-h), (1:ℝ) := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      _ = (n:ℝ)-h := by simp [Nat.cast_sub hh]
  · simp [dh]

end WheelRefute

namespace WheelRefute

noncomputable def residueLong (n d : ℕ) : ℝ :=
  2*∑h ∈ Finset.Icc ((GoldbachPacket.length n)^2+1) n,
    (if d∣h then (n:ℝ)-h else 0)*GoldbachPacket.cosineMoment n h

theorem residueLong_eq_sum (n d : ℕ) (hd : 0<d) :
    residueLong n d = ∑r∈Finset.range d,lagLong n (resWeight n d r) := by
  unfold residueLong lagLong
  rw [←Finset.mul_sum,Finset.sum_comm (s:=Finset.range d)]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [←Finset.sum_mul,sum_autocorr n d h hd (Finset.mem_Icc.mp hh).2]

theorem residueLong_lower : ∃N:ℕ,∀ n≥N,∀d:ℕ,0<d →
    -(d:ℝ)*(n:ℝ)/10000 ≤ residueLong n d := by
  obtain ⟨N,bound⟩:=long_lower
  refine ⟨N,?_⟩
  intro n hn d hd
  rw [residueLong_eq_sum n d hd]
  calc
    _ = ∑_r∈Finset.range d,-(n:ℝ)/10000 := by simp;ring
    _ ≤ _ := Finset.sum_le_sum (fun r _=>bound n hn (resWeight n d r) (fun k _=>resWeight_bound n d r k))

end WheelRefute

namespace WheelRefute

private def profile (h : ℕ) : ℝ :=
  (2:ℝ)^(if 3∣h then 1 else 0 : ℕ) *
    (3*(if 5∣h then 0 else 1)+4*(if 5∣h then 1 else 0))

private noncomputable def discrepancy (n : ℕ) : ℝ :=
  2 * ∑ h ∈ Icc ((length n)^2+1) n,
    (((n:ℝ)-h)*(15/32)*profile h-correlation n h wheel)*cosineMoment n h

private theorem profile_decomposition (h : ℕ) :
    profile h = 3 + (if 3∣h then 3 else 0) + (if 5∣h then 1 else 0)
      + (if 15∣h then 1 else 0) := by
  have hd : 15∣h ↔ 3∣h ∧ 5∣h := by omega
  unfold profile
  by_cases ha : 3∣h <;> by_cases hb : 5∣h <;> norm_num [ha,hb,hd]

private theorem discrepancy_eq (n : ℕ) :
    discrepancy n = (15/32:ℝ)*(3*residueLong n 1 + 3*residueLong n 3 +
      residueLong n 5 + residueLong n 15) - lagLong n wheel := by
  unfold discrepancy residueLong lagLong
  simp only [one_dvd,ite_true]
  simp only [mul_add,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro h _
  rw [profile_decomposition]
  split_ifs <;> ring

end WheelRefute

theorem Conjectures.Cuts.Refute77da5b6d927d911e39958318 : ¬ (have x1 : ℕ → ℕ := fun (x1 : ℕ) => Nat.log (2 : ℕ) (x1 + (2 : ℕ)) ^ (2 : ℕ); have x2 : ℕ → Set ℝ := fun (x2 : ℕ) => {x3 : ℝ | ∃ (x4 : ℕ) (x5 : ℕ), (1 : ℕ) ≤ x4 ∧ x4 ≤ x1 x2 ∧ x5 ≤ x4 ∧ x5.Coprime x4 ∧ |x3 - ↑x5 / ↑x4| ≤ ↑(x1 x2) / (↑x4 * ↑x2)}; have x3 : ℕ → ℕ := fun (x3 : ℕ) => Max.max (1 : ℕ) (Nat.log (2 : ℕ) x3 / (2 : ℕ)); have x4 : ℕ → ℝ → ℝ := fun (x4 : ℕ) (x5 : ℝ) => (∑ x6 ∈ Finset.range (x3 x4), Real.cos ((2 : ℝ) * Real.pi * (2 : ℝ) ^ (x6 + (1 : ℕ)) * x5)) / ↑(x3 x4); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | x6 ∉ x2 x5 ∧ (1 / 2 : ℝ) < x4 x5 x6}; have x6 : ℕ → ℕ → ℝ := fun (x6 x7 : ℕ) => intervalIntegral ((x5 x6).indicator fun (x8 : ℝ) => Real.cos ((2 : ℝ) * Real.pi * ↑x7 * x8)) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume; have x7 : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun (x7 x8 : ℕ) (x9 : ℕ → ℝ) => ∑ x10 ∈ Finset.range (x7 + (1 : ℕ) - x8), x9 x10 * x9 (x10 + x8); have x8 : ℕ → ℝ := fun (x8 : ℕ) => if x8.Coprime (30 : ℕ) then (30 / 8 : ℝ) else (0 : ℝ); have x9 : ℕ → ℝ := fun (x9 : ℕ) => ((2 : ℝ) ^ if (3 : ℕ) ∣ x9 then (1 : ℕ) else (0 : ℕ)) * (((3 : ℝ) * if (5 : ℕ) ∣ x9 then (0 : ℝ) else (1 : ℝ)) + (4 : ℝ) * if (5 : ℕ) ∣ x9 then (1 : ℝ) else (0 : ℝ)); have x10 : ℕ → ℝ := fun (x10 : ℕ) => (2 : ℝ) * ∑ x11 ∈ Finset.Icc (x3 x10 ^ (2 : ℕ) + (1 : ℕ)) x10, ((↑x10 - ↑x11) * (15 / 32 : ℝ) * x9 x11 - x7 x10 x11 x8) * x6 x10 x11; ∃ (x11 : ℕ), ∀ (x12 : ℕ), x11 ≤ x12 → Even x12 → x10 x12 ≤ -(1 / 312 : ℝ) * ↑x12) := by
  classical
  change ¬∃ N : ℕ, ∀ n ≥ N, Even n → WheelRefute.discrepancy n ≤ -(1/312:ℝ)*n
  rintro ⟨N,claim⟩
  obtain ⟨A,low⟩ := WheelRefute.residueLong_lower
  obtain ⟨B,upper⟩ := WheelRefute.wheel_long_upper
  let n := 2*(N+A+B+1)
  have en : Even n := ⟨N+A+B+1, by dsimp [n]; omega⟩
  have hn : 0 < n := by dsimp [n]; omega
  have hnN : N ≤ n := by dsimp [n]; omega
  have hnA : A ≤ n := by dsimp [n]; omega
  have hnB : B ≤ n := by dsimp [n]; omega
  have contrad := claim n hnN en
  rw [WheelRefute.discrepancy_eq] at contrad
  have h1 := low n hnA 1 (by decide)
  have h3 := low n hnA 3 (by decide)
  have h5 := low n hnA 5 (by decide)
  have h15 := low n hnA 15 (by decide)
  have hw := upper n hnB en
  norm_num at h1 h3 h5 h15
  linarith only [contrad,h1,h3,h5,h15,hw,(by exact_mod_cast hn : (0:ℝ)<n)]
