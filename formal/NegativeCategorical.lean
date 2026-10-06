import CategoricalNextChoice

/-! Deliberately false: nonnegative row weights need not be probabilities.
One row with two weights equal to one has total assignment mass two. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem invalid_unnormalized_assignment_probability :
    (∑ d : Fin 1 → Fin 2, assignmentWeight (fun _ _ => (1 : ℚ)) d) = 1 := by
  rw [assignmentWeight_total]
  norm_num [Fin.sum_univ_succ]

end MatchingCapacity
