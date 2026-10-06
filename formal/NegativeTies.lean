import CappedTieComparison

-- A maximum law with two tie-count strata has masses in ratio 2:1.
-- Forgetting the necessary size bias would equate mean counts 4/3 and
-- 3/2. The false equality must be rejected mathematically.
open MatchingCapacity
example :
    expectation (fun i : Fin 2 => if i = 0 then 2 else 1)
      (fun i => if i = 0 then 1 else 2) =
    expectation (sizeBias (fun i : Fin 2 => if i = 0 then 2 else 1)
      (fun i => if i = 0 then 1 else 2)) (fun i => if i = 0 then 1 else 2) := by
  norm_num [expectation, moment, total, sizeBias, Fin.sum_univ_succ]
