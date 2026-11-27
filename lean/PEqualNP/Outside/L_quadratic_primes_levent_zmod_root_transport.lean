import Mathlib
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_quadratic_primes_levent_zmod_root_transport :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ (q : ℕ) [NeZero q], ∃ e : {r : ℕ // r ∈ roots 1 q} ≃ {u : ZMod q // u^2+1=0}, ∀ r, (e r).1.val = r.1 := by
  intro roots q _
  refine ⟨{ toFun := fun r => ⟨(r.1 : ZMod q), ?_⟩
            invFun := fun u => ⟨u.1.val, ?_⟩
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · show ((r.1 : ZMod q))^2 + 1 = 0
    have hdvd : q ∣ r.1^2+1 := (Finset.mem_filter.1 r.2).2
    have h0 : ((r.1^2+1 : ℕ) : ZMod q) = 0 := (CharP.cast_eq_zero_iff (ZMod q) q _).2 hdvd
    push_cast at h0
    simpa using h0
  · show u.1.val ∈ (Finset.range q).filter (fun r => q ∣ r^2+1)
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt u.1), ?_⟩
    have h0 : ((u.1.val^2+1 : ℕ) : ZMod q) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact u.2
    exact (CharP.cast_eq_zero_iff (ZMod q) q _).1 h0
  · intro r
    exact Subtype.ext (ZMod.val_natCast_of_lt ((Finset.mem_filter.1 r.2).1 |> Finset.mem_range.1))
  · intro u
    exact Subtype.ext (ZMod.natCast_zmod_val u.1)
  · intro r
    exact ZMod.val_natCast_of_lt ((Finset.mem_filter.1 r.2).1 |> Finset.mem_range.1)
