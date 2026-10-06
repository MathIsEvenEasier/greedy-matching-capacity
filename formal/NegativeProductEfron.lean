import ProductEfron

-- All three carriers satisfy the theorem's assumptions. The observable
-- minus the total is decreasing, so the claimed increasing comparison
-- must be rejected. At totals 0 and 1 its means are exactly 0 and -1.
open MatchingCapacity
example :
    productMean [factorialCarrier 1, factorialCarrier 1, factorialCarrier 1]
      0 (fun xs => -(xs.sum : ℚ)) ≤
    productMean [factorialCarrier 1, factorialCarrier 1, factorialCarrier 1]
      1 (fun xs => -(xs.sum : ℚ)) := by
  norm_num [productMean, productMoment, carrierProduct, carrierConv,
    factorialCarrier, finiteConv, integerCarrier, cappedCarrier, factorialWeight,
    Finset.sum_range_succ]
