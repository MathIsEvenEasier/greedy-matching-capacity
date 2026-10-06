import FiniteCovariance

/-! The finite mixture step in the proof of Cohen--Sackrowitz Lemma 4.1.
Its covariance and regression hypotheses are explicit. In particular this
file does not claim that the capped-multinomial fibers satisfy them. -/

set_option autoImplicit false
open scoped BigOperators

namespace MatchingCapacity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def jointWeight (w : ι → ℚ) (q : ι → κ → ℚ) (x : ι × κ) : ℚ :=
  w x.1 * q x.1 x.2

theorem joint_moment (w : ι → ℚ) (q f : ι → κ → ℚ) :
    moment (jointWeight w q) (fun x => f x.1 x.2) =
      moment w (fun i => moment (q i) (f i)) := by
  classical
  simp [moment, jointWeight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem joint_total (w : ι → ℚ) (q : ι → κ → ℚ)
    (hq : ∀ i, total (q i) = 1) : total (jointWeight w q) = total w := by
  classical
  change ∀ i, (∑ j, q i j) = 1 at hq
  simp [total, jointWeight, Fintype.sum_prod_type, ← Finset.mul_sum, hq]

theorem association_step (w : ι → ℚ) (q f g : ι → κ → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, total (q i) = 1)
    (hfib : ∀ i, CovNonneg (q i) (f i) (g i))
    (hreg : ∀ i j, 0 ≤
      (moment (q i) (f i) - moment (q j) (f j)) *
      (moment (q i) (g i) - moment (q j) (g j))) :
    moment w (fun i => moment (q i) (f i)) *
      moment w (fun i => moment (q i) (g i)) ≤
    total w * moment w (fun i => moment (q i) (fun j => f i j * g i j)) := by
  have hinner : ∀ i,
      moment (q i) (f i) * moment (q i) (g i) ≤
      moment (q i) (fun j => f i j * g i j) := by
    intro i
    simpa only [CovNonneg, hq i, one_mul] using hfib i
  calc
    _ ≤ total w * moment w
        (fun i => moment (q i) (f i) * moment (q i) (g i)) :=
      covariance_of_pairwise w _ _ hw hreg
    _ ≤ _ := mul_le_mul_of_nonneg_left (moment_mono w _ _ hw hinner) (total_nonneg w hw)

theorem joint_covariance_of_fibers (w : ι → ℚ) (q f g : ι → κ → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, total (q i) = 1)
    (hfib : ∀ i, CovNonneg (q i) (f i) (g i))
    (hreg : ∀ i j, 0 ≤
      (moment (q i) (f i) - moment (q j) (f j)) *
      (moment (q i) (g i) - moment (q j) (g j))) :
    CovNonneg (jointWeight w q) (fun x => f x.1 x.2) (fun x => g x.1 x.2) := by
  unfold CovNonneg
  rw [joint_moment, joint_moment, joint_total w q hq]
  rw [show moment (jointWeight w q) (fun x => f x.1 x.2 * g x.1 x.2) =
    moment w (fun i => moment (q i) (fun j => f i j * g i j)) from
    joint_moment w q (fun i j => f i j * g i j)]
  exact association_step w q f g hw hq hfib hreg

-- No properties are required of conditional rows on zero-probability events.
theorem association_step_on_support (w : ι → ℚ) (q f g : ι → κ → ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i, 0 < w i → total (q i) = 1)
    (hfib : ∀ i, 0 < w i → CovNonneg (q i) (f i) (g i))
    (hreg : ∀ i j, 0 < w i → 0 < w j → 0 ≤
      (moment (q i) (f i) - moment (q j) (f j)) *
      (moment (q i) (g i) - moment (q j) (g j))) :
    moment w (fun i => moment (q i) (f i)) *
      moment w (fun i => moment (q i) (g i)) ≤
    total w * moment w (fun i => moment (q i) (fun j => f i j * g i j)) := by
  have hinner : ∀ i, 0 < w i →
      moment (q i) (f i) * moment (q i) (g i) ≤
      moment (q i) (fun j => f i j * g i j) := by
    intro i hi
    simpa only [CovNonneg, hq i hi, one_mul] using hfib i hi
  calc
    _ ≤ total w * moment w
        (fun i => moment (q i) (f i) * moment (q i) (g i)) :=
      covariance_on_support w _ _ hw hreg
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (moment_mono_on_support w _ _ hw hinner) (total_nonneg w hw)

end MatchingCapacity
