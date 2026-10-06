import CoarseHistorySupport

/-! Deliberately false: a normalized mark probability on the empty
next-success event must not be assigned the positive value one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical

theorem null_next_event_has_probability_one :
    coarseNextSaturation (m := 0) (fun j => rvKernel j) 0 0 0 0 0 = 1 := by
  norm_num [coarseNextSaturation, coarseNextMoment, availableNextMoment, historyAvailable]

end MatchingCapacity
