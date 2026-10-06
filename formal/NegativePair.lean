import PairApplications

/-! Deliberately false: removing binomial normalization destroys
coefficient monotonicity, even when every factor is 1+X. -/
set_option autoImplicit false
open Polynomial
namespace MatchingCapacity

theorem invalid_raw_coefficient_monotonicity :
    (pairPolynomial (Finset.range 2) (fun _ => 1) (fun _ => 1)).coeff 1 ≤
      (pairPolynomial (Finset.range 2) (fun _ => 1) (fun _ => 1)).coeff 2 := by
  have hp : pairPolynomial (Finset.range 2) (fun _ => 1) (fun _ => 1) =
      (1+X : ℚ[X])^2 := by
    simp [pairPolynomial, pow_two, add_comm]
  rw [hp]
  norm_num [Polynomial.coeff_one_add_X_pow]

end MatchingCapacity
