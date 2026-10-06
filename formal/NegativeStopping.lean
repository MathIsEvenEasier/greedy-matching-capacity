import StoppingTransitionLaws

/-! False control: a history consisting of one rejection cannot have
reached its first acceptance. The never-reached constructor is essential. -/
set_option autoImplicit false
namespace MatchingCapacity
open Classical
example : stoppingState 0 (Fin.snoc (fun j : Fin 0 => j.elim0) (none : Option (Fin 1))) 1 = some (1,0) := by
  rw [stoppingState_snoc]
  norm_num [stoppingState]
end MatchingCapacity
