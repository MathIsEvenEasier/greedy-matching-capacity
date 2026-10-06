import FiniteCovariance
import Mathlib.Data.Nat.Factorial.Basic

/-! The actual finite carrier used in the written association application.
These theorems establish its support and log-concavity for all caps and
indices, rather than checking any finite collection of parameter values. -/

set_option autoImplicit false

namespace MatchingCapacity

def factorialWeight (k : ℕ) : ℚ := (k.factorial : ℚ)⁻¹
def cappedCarrier (q k : ℕ) : ℚ := if k ≤ q then factorialWeight k else 0

theorem factorialWeight_pos (k : ℕ) : 0 < factorialWeight k := by
  apply inv_pos.mpr
  exact_mod_cast Nat.factorial_pos k

theorem factorialWeight_step (k : ℕ) :
    ((k : ℚ) + 1) * factorialWeight (k+1) = factorialWeight k := by
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [factorialWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem factorialWeight_logconcave (k : ℕ) :
    factorialWeight k * factorialWeight (k+2) ≤ factorialWeight (k+1)^2 := by
  have h1 := congrArg (fun z : ℚ => z * factorialWeight (k+2)) (factorialWeight_step k)
  have h2 := congrArg (fun z : ℚ => factorialWeight (k+1) * z) (factorialWeight_step (k+1))
  have hn := mul_nonneg (le_of_lt (factorialWeight_pos (k+1)))
    (le_of_lt (factorialWeight_pos (k+2)))
  norm_num only [Nat.cast_add, Nat.cast_one] at h1 h2
  nlinarith

theorem cappedCarrier_pos_iff (q k : ℕ) : 0 < cappedCarrier q k ↔ k ≤ q := by
  by_cases h : k ≤ q
  · simp [cappedCarrier, h, factorialWeight_pos]
  · simp [cappedCarrier, h]

theorem cappedCarrier_nonneg (q k : ℕ) : 0 ≤ cappedCarrier q k := by
  by_cases h : k ≤ q
  · exact le_of_lt ((cappedCarrier_pos_iff q k).mpr h)
  · simp [cappedCarrier, h]

theorem cappedCarrier_logconcave (q k : ℕ) :
    cappedCarrier q k * cappedCarrier q (k+2) ≤ cappedCarrier q (k+1)^2 := by
  by_cases h : k+2 ≤ q
  · have h0 : k ≤ q := by omega
    have h1 : k+1 ≤ q := by omega
    simpa only [cappedCarrier, ite_eq_left h, ite_eq_left h0, ite_eq_left h1] using
      factorialWeight_logconcave k
  · simp only [cappedCarrier, ite_eq_right h, mul_zero]
    exact sq_nonneg _

end MatchingCapacity
