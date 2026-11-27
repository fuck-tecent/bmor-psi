import Mathlib

noncomputable section

private def goldbachCert112Term (a b : Nat) : Complex :=
  Complex.exp (((2 * Real.pi * (a : Real) * b / 112 : Real) : Complex) * Complex.I)

private lemma goldbachCert112Shift (a : Nat) (ha : Odd a) (b : Nat) :
    goldbachCert112Term a (b + 56) = -goldbachCert112Term a b := by
  unfold goldbachCert112Term
  have harg :
      (((2 * Real.pi * (a : Real) * ((b + 56 : Nat) : Real) / 112 : Real) : Complex) * Complex.I) =
        (((2 * Real.pi * (a : Real) * (b : Real) / 112 : Real) : Complex) * Complex.I) +
          (((Real.pi * (a : Real) : Real) : Complex) * Complex.I) := by
    push_cast
    ring
  have hphaseArg :
      (((Real.pi * (a : Real) : Real) : Complex) * Complex.I) =
        (a : Complex) * (Real.pi * Complex.I) := by
    push_cast
    ring
  have hphase :
      Complex.exp (((Real.pi * (a : Real) : Real) : Complex) * Complex.I) = -1 := by
    rw [hphaseArg]
    calc
      Complex.exp ((a : Complex) * (Real.pi * Complex.I)) =
          Complex.exp (Real.pi * Complex.I) ^ a := Complex.exp_nat_mul _ _
      _ = (-1 : Complex) ^ a := by rw [Complex.exp_pi_mul_I]
      _ = -1 := ha.neg_one_pow
  rw [harg, Complex.exp_add, hphase]
  ring

end

theorem PEqualNP.Outside.L_goldbach_cert_112 :
    forall a : Nat, Nat.Coprime a 112 ->
      Finset.sum ((Finset.range 112).filter (fun b => Nat.Coprime b 112))
        (fun b => Complex.exp (((2 * Real.pi * (a : Real) * b / 112 : Real) : Complex) * Complex.I)) /
          (48 : Complex) = (0 : Complex) / 48 := by
  intro a ha
  have haOdd : Odd a := by
    by_contra hNotOdd
    have hEven : Even a := (Nat.even_or_odd a).resolve_right hNotOdd
    cases hEven with
    | intro k hk =>
      have hdiv : Dvd.dvd 2 a := Exists.intro k (by omega)
      have hgcd : Dvd.dvd 2 (Nat.gcd a 112) := Nat.dvd_gcd hdiv (by norm_num)
      have hcop : Nat.gcd a 112 = 1 := ha.gcd_eq_one
      rw [hcop] at hgcd
      omega
  have hunitSet :
      (Finset.range 112).filter (fun b => Nat.Coprime b 112) =
        ({1, 57, 3, 59, 5, 61, 9, 65, 11, 67, 13, 69, 15, 71, 17, 73, 19, 75, 23, 79, 25, 81, 27, 83, 29, 85, 31, 87, 33, 89, 37, 93, 39, 95, 41, 97, 43, 99, 45, 101, 47, 103, 51, 107, 53, 109, 55, 111} : Finset Nat) := by
    decide
  have hsum :
      Finset.sum ((Finset.range 112).filter (fun b => Nat.Coprime b 112))
        (fun b => goldbachCert112Term a b) = 0 := by
    rw [hunitSet]
    simp [Finset.sum_insert]
    have h57 : goldbachCert112Term a 57 = -goldbachCert112Term a 1 := by
      simpa using goldbachCert112Shift a haOdd 1
    have h59 : goldbachCert112Term a 59 = -goldbachCert112Term a 3 := by
      simpa using goldbachCert112Shift a haOdd 3
    have h61 : goldbachCert112Term a 61 = -goldbachCert112Term a 5 := by
      simpa using goldbachCert112Shift a haOdd 5
    have h65 : goldbachCert112Term a 65 = -goldbachCert112Term a 9 := by
      simpa using goldbachCert112Shift a haOdd 9
    have h67 : goldbachCert112Term a 67 = -goldbachCert112Term a 11 := by
      simpa using goldbachCert112Shift a haOdd 11
    have h69 : goldbachCert112Term a 69 = -goldbachCert112Term a 13 := by
      simpa using goldbachCert112Shift a haOdd 13
    have h71 : goldbachCert112Term a 71 = -goldbachCert112Term a 15 := by
      simpa using goldbachCert112Shift a haOdd 15
    have h73 : goldbachCert112Term a 73 = -goldbachCert112Term a 17 := by
      simpa using goldbachCert112Shift a haOdd 17
    have h75 : goldbachCert112Term a 75 = -goldbachCert112Term a 19 := by
      simpa using goldbachCert112Shift a haOdd 19
    have h79 : goldbachCert112Term a 79 = -goldbachCert112Term a 23 := by
      simpa using goldbachCert112Shift a haOdd 23
    have h81 : goldbachCert112Term a 81 = -goldbachCert112Term a 25 := by
      simpa using goldbachCert112Shift a haOdd 25
    have h83 : goldbachCert112Term a 83 = -goldbachCert112Term a 27 := by
      simpa using goldbachCert112Shift a haOdd 27
    have h85 : goldbachCert112Term a 85 = -goldbachCert112Term a 29 := by
      simpa using goldbachCert112Shift a haOdd 29
    have h87 : goldbachCert112Term a 87 = -goldbachCert112Term a 31 := by
      simpa using goldbachCert112Shift a haOdd 31
    have h89 : goldbachCert112Term a 89 = -goldbachCert112Term a 33 := by
      simpa using goldbachCert112Shift a haOdd 33
    have h93 : goldbachCert112Term a 93 = -goldbachCert112Term a 37 := by
      simpa using goldbachCert112Shift a haOdd 37
    have h95 : goldbachCert112Term a 95 = -goldbachCert112Term a 39 := by
      simpa using goldbachCert112Shift a haOdd 39
    have h97 : goldbachCert112Term a 97 = -goldbachCert112Term a 41 := by
      simpa using goldbachCert112Shift a haOdd 41
    have h99 : goldbachCert112Term a 99 = -goldbachCert112Term a 43 := by
      simpa using goldbachCert112Shift a haOdd 43
    have h101 : goldbachCert112Term a 101 = -goldbachCert112Term a 45 := by
      simpa using goldbachCert112Shift a haOdd 45
    have h103 : goldbachCert112Term a 103 = -goldbachCert112Term a 47 := by
      simpa using goldbachCert112Shift a haOdd 47
    have h107 : goldbachCert112Term a 107 = -goldbachCert112Term a 51 := by
      simpa using goldbachCert112Shift a haOdd 51
    have h109 : goldbachCert112Term a 109 = -goldbachCert112Term a 53 := by
      simpa using goldbachCert112Shift a haOdd 53
    have h111 : goldbachCert112Term a 111 = -goldbachCert112Term a 55 := by
      simpa using goldbachCert112Shift a haOdd 55
    rw [h57, h59, h61, h65, h67, h69, h71, h73, h75, h79, h81, h83, h85, h87, h89, h93, h95, h97, h99, h101, h103, h107, h109, h111]
    ring
  change Finset.sum ((Finset.range 112).filter (fun b => Nat.Coprime b 112))
      (fun b => goldbachCert112Term a b) / (48 : Complex) = (0 : Complex) / 48
  rw [hsum]
