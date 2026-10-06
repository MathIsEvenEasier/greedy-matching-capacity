import EfronTwo

-- Without log-concavity: at total 1 only (0,1) is possible; at total 2
-- only (2,0) is possible. The increasing observable phi(x,y)=y decreases.
-- This intentionally false assertion must be rejected with a False goal.
example :
    MatchingCapacity.twoExpectation
      (fun k : ℤ => if k = 0 ∨ k = 2 then 1 else 0)
      (fun k : ℤ => if k = 0 ∨ k = 1 then 1 else 0) 1 (fun _ y => (y : ℚ)) ≤
    MatchingCapacity.twoExpectation
      (fun k : ℤ => if k = 0 ∨ k = 2 then 1 else 0)
      (fun k : ℤ => if k = 0 ∨ k = 1 then 1 else 0) 2 (fun _ y => (y : ℚ)) := by
  norm_num [MatchingCapacity.twoExpectation, MatchingCapacity.normalized,
    MatchingCapacity.cumMass, MatchingCapacity.sumLayer, Finset.sum_range_succ]
