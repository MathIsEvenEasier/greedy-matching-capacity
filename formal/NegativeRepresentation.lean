import CappedPrefix

-- Two cap-2 coordinates with total 2 have weights 1/2, 1, 1/2.
-- Replacing the factorial law by uniform weights would give 10/3 for
-- the observable x_1^2+x_2^2, whereas its correct mean is 3.
-- The intentionally false equality must fail with an unsolved False goal.
open MatchingCapacity
example :
    expectation (fun i : Fin 3 => if i = 1 then 1 else 1/2)
      (fun i => if i = 1 then 2 else 4) =
    expectation (fun _ : Fin 3 => (1 : ℚ))
      (fun i => if i = 1 then 2 else 4) := by
  norm_num [expectation, moment, total, Fin.sum_univ_succ]
