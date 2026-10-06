import LoadMajorization

/-! Deliberately false: a transfer between equal coordinates concentrates
the load, so the donor-recipient gap condition cannot be discarded. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem invalid_unrestricted_balancing :
    (∑ k : Fin 2, (balanceLoad (fun _ => 1) 0 1 k)^2) ≤
      ∑ _k : Fin 2, (1 : ℕ)^2 := by
  norm_num [Fin.sum_univ_succ, balanceLoad]

end MatchingCapacity
