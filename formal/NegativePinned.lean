import PinnedMajorization

-- The pinned-coordinate comparison needs the distinguished coordinate
-- to be at least the residual cap. Without that hypothesis, total 2,
-- one residual coordinate capped at 2, and pin values 0 and 1 give
-- vectors (0,2) and (1,1). Their maximum decreases from 2 to 1.
open MatchingCapacity
example :
    productMean [factorialCarrier 2] 2
      (fun xs => (max 0 (xs.getD 0 0) : ℚ)) ≤
    productMean [factorialCarrier 2] 1
      (fun xs => (max 1 (xs.getD 0 0) : ℚ)) := by
  norm_num [productMean, productMoment, carrierProduct, carrierConv,
    factorialCarrier, finiteConv, integerCarrier, cappedCarrier, factorialWeight,
    Finset.sum_range_succ]
