import FixedPriorityComparison

open MatchingCapacity

-- Equal next-hit times do not suffice: the first process must not gain
-- a full bin when the second gains none at tied old counts.
example : RawStopLE (markedNextState 0 ((0 : Fin 2),true))
    (markedNextState 0 ((0 : Fin 2),false)) := by
  norm_num [RawStopLE,markedNextState]
