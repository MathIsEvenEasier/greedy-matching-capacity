import HistoryFiber

/-! False control: without the final residual cap, a formerly available
bin can fill, so the fixed availability path is not preserved. -/
set_option autoImplicit false
namespace MatchingCapacity
open Classical

theorem invalid_drop_residual_cap :
    historyAvailable 0
      (completeHistory (Finset.univ : Finset (Fin 1)) (fun _ => none)
        (D := (∅ : Finset (Fin 1))) (fun _ => ⟨0, by simp⟩)) 1 =
    historyAvailable 0 (fixedHistory (Finset.univ : Finset (Fin 1)) (fun _ => none)) 1 := by
  norm_num [Finset.ext_iff, historyAvailable, historyLoad, completeHistory, fixedHistory,
    Fin.sum_univ_one, Fin.forall_fin_one]

end MatchingCapacity
