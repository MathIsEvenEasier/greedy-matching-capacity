import CappedAssociation

/-! Expected mathematical rejection. On the two loads (0,1),(1,0), the
coordinate functions have negative covariance. They are coordinatewise
increasing, but are not increasing in majorization. The order hypothesis
in cappedAssociation_all cannot be dropped or silently replaced. -/
set_option autoImplicit false
open scoped BigOperators
open MatchingCapacity

example : CovNonneg (fun _ : Fin 2 => (1 : ℚ))
    (fun i => if i.val = 0 then (0 : ℚ) else 1)
    (fun i => if i.val = 0 then (1 : ℚ) else 0) := by
  norm_num [CovNonneg, moment, total, Fin.sum_univ_succ]
