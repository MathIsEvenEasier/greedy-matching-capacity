import CappedStrata

-- A fixed tie count cannot be replaced by "at least this many maxima".
-- In three bins with cap 2 and total 4, exactly two maxima have weight
-- choose(3,2) * (1/2!)^2 = 3/4. The unconditioned residual cap 2 with
-- one maximum deleted also permits the one-tie configurations (2,1,1).
-- Omitting the exact residual tie stratum incorrectly equates 3/4 and 3/2.
open MatchingCapacity
example : (3 : ℚ) * (1/2)^2 = (3 : ℚ) / 2 * ((1/2) + 1 + (1/2)) / 2 := by
  norm_num
