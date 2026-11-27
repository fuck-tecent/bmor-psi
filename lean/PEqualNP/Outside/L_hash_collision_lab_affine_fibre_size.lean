import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_affine_fibre_size :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b c : ZMod p), (a ≠ 0 ∨ b ≠ 0) → ∀ v : ZMod p, (Finset.univ.filter (fun z : ZMod p × ZMod p => a*z.1+b*z.2+c = v)).card = p := by
  intro p hp a b c hab v
  rcases hab with ha | hb
  · have hset : Finset.univ.filter (fun z : ZMod p × ZMod p => a * z.1 + b * z.2 + c = v)
        = Finset.univ.image (fun t : ZMod p => (a⁻¹ * (v - c - b * t), t)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hz
        refine ⟨z.2, Prod.ext ?_ rfl⟩
        have h1 : a * z.1 = v - c - b * z.2 := by
          have h2 : a * z.1 + (b * z.2 + c) = v := by
            rw [← add_assoc]
            exact hz
          have h3 : a * z.1 = v - (b * z.2 + c) := eq_sub_iff_add_eq.mpr h2
          rw [h3]
          ring
        rw [← h1]
        exact inv_mul_cancel_left₀ ha z.1
      · rintro ⟨t, rfl⟩
        rw [mul_inv_cancel_left₀ ha]
        ring
    rw [hset]
    have hinj : Function.Injective (fun t : ZMod p => (a⁻¹ * (v - c - b * t), t)) := by
      intro s t hst
      exact congrArg Prod.snd hst
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  · have hset : Finset.univ.filter (fun z : ZMod p × ZMod p => a * z.1 + b * z.2 + c = v)
        = Finset.univ.image (fun t : ZMod p => (t, b⁻¹ * (v - c - a * t))) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hz
        refine ⟨z.1, Prod.ext rfl ?_⟩
        have h1 : b * z.2 = v - c - a * z.1 := by
          have hz' : b * z.2 + a * z.1 + c = v := by
            rw [add_comm (b * z.2) (a * z.1)]
            exact hz
          have h2 : b * z.2 + (a * z.1 + c) = v := by
            rw [← add_assoc]
            exact hz'
          have h3 : b * z.2 = v - (a * z.1 + c) := eq_sub_iff_add_eq.mpr h2
          rw [h3]
          ring
        rw [← h1]
        exact inv_mul_cancel_left₀ hb z.2
      · rintro ⟨t, rfl⟩
        rw [mul_inv_cancel_left₀ hb]
        ring
    rw [hset]
    have hinj : Function.Injective (fun t : ZMod p => (t, b⁻¹ * (v - c - a * t))) := by
      intro s t hst
      exact congrArg Prod.fst hst
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
