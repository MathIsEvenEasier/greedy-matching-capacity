import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Rat.BigOperators

/-! Finite rational covariance identities. No probability normalization is
required until it is explicitly stated. These are general algebraic tools,
not the capped-multinomial association theorem. -/

set_option autoImplicit false
open scoped BigOperators

namespace MatchingCapacity

variable {ι : Type*} [Fintype ι]

def total (w : ι → ℚ) : ℚ := ∑ i, w i
def moment (w f : ι → ℚ) : ℚ := ∑ i, w i * f i

def CovNonneg (w f g : ι → ℚ) : Prop :=
  moment w f * moment w g ≤ total w * moment w (fun i => f i * g i)

theorem total_nonneg (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ total w := by
  exact Finset.sum_nonneg fun i _ => hw i

theorem moment_mono (w f g : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hfg : ∀ i, f i ≤ g i) : moment w f ≤ moment w g := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfg i) (hw i)

theorem covariance_identity (w f g : ι → ℚ) :
    (∑ i, ∑ j, w i * w j * ((f i - f j) * (g i - g j))) =
      2 * (total w * moment w (fun i => f i * g i) - moment w f * moment w g) := by
  classical
  have he : ∀ i j,
      w i * w j * ((f i - f j) * (g i - g j)) =
      (w i * (f i * g i)) * w j + w i * (w j * (f j * g j)) -
      (w i * f i) * (w j * g j) - (w i * g i) * (w j * f j) := by
    intro i j
    ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  unfold total moment
  ring

theorem covariance_of_pairwise (w f g : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hfg : ∀ i j, 0 ≤ (f i - f j) * (g i - g j)) : CovNonneg w f g := by
  have h : 0 ≤ ∑ i, ∑ j, w i * w j * ((f i - f j) * (g i - g j)) := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hw i) (hw j)) (hfg i j)
  rw [covariance_identity] at h
  unfold CovNonneg
  linarith

theorem moment_mono_on_support (w f g : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hfg : ∀ i, 0 < w i → f i ≤ g i) : moment w f ≤ moment w g := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : w i = 0
  · simp [hi]
  · exact mul_le_mul_of_nonneg_left
      (hfg i (lt_of_le_of_ne (hw i) (Ne.symm hi))) (hw i)

theorem covariance_on_support (w f g : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hfg : ∀ i j, 0 < w i → 0 < w j →
      0 ≤ (f i - f j) * (g i - g j)) : CovNonneg w f g := by
  have h : 0 ≤ ∑ i, ∑ j, w i * w j * ((f i - f j) * (g i - g j)) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hi : w i = 0
    · simp [hi]
    by_cases hj : w j = 0
    · simp [hj]
    exact mul_nonneg (mul_nonneg (hw i) (hw j))
      (hfg i j (lt_of_le_of_ne (hw i) (Ne.symm hi)) (lt_of_le_of_ne (hw j) (Ne.symm hj)))
  rw [covariance_identity] at h
  unfold CovNonneg
  linarith

theorem weighted_chebyshev [LinearOrder ι] (w f g : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hf : Monotone f) (hg : Monotone g) :
    CovNonneg w f g := by
  apply covariance_of_pairwise w f g hw
  intro i j
  rcases le_total i j with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr (hg h))
  · exact mul_nonneg (sub_nonneg.mpr (hf h)) (sub_nonneg.mpr (hg h))

end MatchingCapacity
