import SourceModel

/-! Deliberately false: after swapping the ranks of two available bins,
the original label zero is no longer the preferred bin. -/
open MatchingCapacity

example : priorityResponse (Equiv.swap (0 : Fin 2) 1) Finset.univ Finset.univ (some 0) = 1 := by
  rw [priority_response_choice]
  norm_num [Fin.forall_fin_succ]
