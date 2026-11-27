import Mathlib.Topology.Closure

theorem Conjectures.Goldbach.BeaumontDenseOpenHit :
∀ {X : Type} [TopologicalSpace X] (O U : Set X), Dense O → IsOpen U → U.Nonempty → (O ∩ U).Nonempty := by
  intro X inst O U hO hU hne
  rcases hO.inter_open_nonempty U hU hne with ⟨x, hxU, hxO⟩
  exact ⟨x, hxO, hxU⟩
