import RejectionKernel

/-! False control: a unit-degree arrival into the sole available bin is
certainly accepted, so waiting past it cannot have positive mass. -/
set_option autoImplicit false
namespace MatchingCapacity
open Classical
example : waitingWeight (fun _ => rvKernel 1) (Finset.univ : Finset (Fin 1)) 0 1 = 1 := by
  norm_num [waitingWeight, rv_rejection_formula, Finset.card_compl]
end MatchingCapacity
