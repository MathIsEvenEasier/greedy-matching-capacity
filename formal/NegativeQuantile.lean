import StoppingWaitingCoupling
import BernoulliCoupling

open MatchingCapacity

-- Reversing the CDF comparison is false: an immediate certain success
-- has CDF one, whereas an always-failing process has CDF zero.
example : cumMass (finiteWaitMass (fun _ => 0) 1) 1 ≤
    cumMass (finiteWaitMass (fun _ => 1) 1) 1 := by
  norm_num [cumMass, finiteWaitMass, survivalProduct]
