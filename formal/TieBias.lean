import FiniteCovariance

/-! The order effect of weighting by an increasing nonnegative tie count.
This is the algebraic comparison used for size bias; identification of the
specific discrete order-statistic laws is a separate remaining obligation. -/

set_option autoImplicit false
namespace MatchingCapacity

variable {ι : Type*} [Fintype ι]

def expectation (w f : ι → ℚ) : ℚ := moment w f / total w
def sizeBias (w l : ι → ℚ) (i : ι) : ℚ := w i * l i

omit [Fintype ι] in
theorem sizeBias_nonneg (w l : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hl : ∀ i, 0 ≤ l i) : ∀ i, 0 ≤ sizeBias w l i := by
  intro i
  exact mul_nonneg (hw i) (hl i)

theorem expectation_le_sizeBias [LinearOrder ι] (w l f : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hZ : 0 < total w) (hL : 0 < moment w l)
    (hl : Monotone l) (hf : Monotone f) :
    expectation w f ≤ expectation (sizeBias w l) f := by
  have hcov := weighted_chebyshev w l f hw hl hf
  have hz : total (sizeBias w l) = moment w l := rfl
  have hm : moment (sizeBias w l) f = moment w (fun i => l i * f i) := by
    simp only [moment, sizeBias, mul_assoc]
  unfold expectation
  rw [hz, hm]
  apply (div_le_div_iff₀ hZ hL).2
  unfold CovNonneg at hcov
  nlinarith

end MatchingCapacity
