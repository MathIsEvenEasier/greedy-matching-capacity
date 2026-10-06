import FiniteCovariance

-- Deliberately false: opposite directions are not positively correlated.
example : MatchingCapacity.CovNonneg
    (fun _ : Fin 2 => (1 : ℚ)) (fun i => (i.val : ℚ))
    (fun i => -(i.val : ℚ)) := by
  norm_num [MatchingCapacity.CovNonneg, MatchingCapacity.moment,
    MatchingCapacity.total, Fin.sum_univ_two]
