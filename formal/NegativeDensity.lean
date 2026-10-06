import CategoricalDensity

/-! Deliberately false: common row ordering cannot be dropped.
The crossed rows (1,0),(0,1) give P=X; balancing increases the
symmetrized factorial-weighted pair contribution from zero to two. -/
set_option autoImplicit false
open Polynomial
namespace MatchingCapacity

theorem invalid_balancing_without_common_order :
    let P := pairPolynomial Finset.univ
      (fun r : Fin 2 => if r = 0 then (1 : ℚ) else 0)
      (fun r : Fin 2 => if r = 0 then (0 : ℚ) else 1)
    P.coeff 1 + P.coeff 1 ≤ 2 * (P.coeff 2 + P.coeff 0) := by
  norm_num [pairPolynomial, Fin.prod_univ_succ, Polynomial.coeff_X]

end MatchingCapacity
