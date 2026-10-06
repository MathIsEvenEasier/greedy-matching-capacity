import NeighborhoodOrder

/-! Deliberately false: RANKING cannot choose the later of two available
neighbors. This checks that its common order was not replaced by RV symmetry. -/
set_option autoImplicit false
open MatchingCapacity
open Classical
example : rankingPick (Finset.univ : Finset (Fin 2)) Finset.univ = some (1 : Fin 2) := by
  have h : rankingPick (Finset.univ : Finset (Fin 2)) Finset.univ = some (0 : Fin 2) := by
    apply (rankingPick_eq_some_iff _ _ _).mpr
    exact ⟨by simp, fun l _ => Fin.zero_le l⟩
  rw [h]
  norm_num
