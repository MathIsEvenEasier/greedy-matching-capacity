import AssociationStep
import TieBias

/-! Forgetting a chosen mark multiplies an outcome's weight by its number
of marks. Applying this with marks at maximal coordinates is the size-bias
mechanism in the discrete tie argument. The iid/exchangeability bridge to
the order-statistic law has not been asserted here. -/

set_option autoImplicit false
open scoped BigOperators

namespace MatchingCapacity

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem marking_total (w : Ω → ℚ) (mark : Ω → ι → ℚ) :
    total (jointWeight w mark) = total (sizeBias w (fun x => total (mark x))) := by
  classical
  simp only [total, jointWeight, sizeBias, Fintype.sum_prod_type, ← Finset.mul_sum]

theorem marking_moment (w f : Ω → ℚ) (mark : Ω → ι → ℚ) :
    moment (jointWeight w mark) (fun x => f x.1) =
      moment (sizeBias w (fun x => total (mark x))) f := by
  rw [show moment (jointWeight w mark) (fun x => f x.1) =
    moment w (fun x => moment (mark x) (fun _ => f x)) from
    joint_moment w mark (fun x _ => f x)]
  simp only [moment, total, sizeBias, ← Finset.sum_mul, mul_assoc]

theorem expectation_marked_eq_sizeBias (w f : Ω → ℚ) (mark : Ω → ι → ℚ) :
    expectation (jointWeight w mark) (fun x => f x.1) =
      expectation (sizeBias w (fun x => total (mark x))) f := by
  unfold expectation
  rw [marking_moment, marking_total]

-- A random distinguished mark biases its count upwards. No order on Ω,
-- and no assumption that the outcome function itself is associated, is needed.
theorem expectation_count_le_marked (w : Ω → ℚ) (mark : Ω → ι → ℚ)
    (φ : ℚ → ℚ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < total w)
    (hM : 0 < moment w (fun x => total (mark x))) (hφ : Monotone φ) :
    expectation w (fun x => φ (total (mark x))) ≤
      expectation (jointWeight w mark) (fun x => φ (total (mark x.1))) := by
  let c : Ω → ℚ := fun x => total (mark x)
  have hcov : CovNonneg w c (fun x => φ (c x)) := by
    apply covariance_of_pairwise _ _ _ hw
    intro x y
    rcases le_total (c x) (c y) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (hφ h))
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hφ h))
  rw [expectation_marked_eq_sizeBias w (fun x => φ (total (mark x))) mark]
  change moment w (fun x => φ (c x)) / total w ≤
    moment (sizeBias w c) (fun x => φ (c x)) / total (sizeBias w c)
  have hm : moment (sizeBias w c) (fun x => φ (c x)) =
      moment w (fun x => c x * φ (c x)) := by
    simp only [moment, sizeBias, mul_assoc]
  rw [show total (sizeBias w c) = moment w c from rfl, hm]
  apply (div_le_div_iff₀ hZ hM).2
  unfold CovNonneg at hcov
  nlinarith

end MatchingCapacity
