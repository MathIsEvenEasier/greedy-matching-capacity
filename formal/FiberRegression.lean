import TieBias

/-! Finite regression by a statistic. Conditional means on zero-mass
fibers are never assumed monotone. This is a reduction with an explicit
regression premise, not a proof of the capped tie-count regression. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity
variable {Ω κ : Type*}

def fiberWeight [DecidableEq κ] (w : Ω → ℚ) (c : Ω → κ) (k : κ) (x : Ω) : ℚ :=
  if c x = k then w x else 0

theorem fiberWeight_nonneg [DecidableEq κ] (w : Ω → ℚ) (c : Ω → κ)
    (hw : ∀ x, 0 ≤ w x) (k : κ) (x : Ω) : 0 ≤ fiberWeight w c k x := by
  unfold fiberWeight
  split <;> simp_all

theorem moment_eq_total_mul_expectation [Fintype Ω] (w f : Ω → ℚ)
    (hw : ∀ x, 0 ≤ w x) : moment w f = total w * expectation w f := by
  by_cases hZ : total w = 0
  · have hz : ∀ x, w x = 0 := by
      intro x
      have h : w x ≤ total w := Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)
      exact le_antisymm (by simpa only [hZ] using h) (hw x)
    simp [moment, total, expectation, hz]
  · unfold expectation
    field_simp

theorem sum_fiber_moment [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w f : Ω → ℚ) (c : Ω → κ) (l : κ → ℚ) :
    (∑ k, l k * moment (fiberWeight w c k) f) =
      moment w (fun x => l (c x) * f x) := by
  unfold moment fiberWeight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  simp [mul_comm, mul_left_comm]

theorem fiber_mass_total [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w : Ω → ℚ) (c : Ω → κ) : total (fun k => total (fiberWeight w c k)) = total w := by
  simpa only [moment, total, mul_one, one_mul] using sum_fiber_moment w (fun _ => 1) c (fun _ => 1)

theorem fiber_class_moment [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w : Ω → ℚ) (c : Ω → κ) (l : κ → ℚ) :
    moment (fun k => total (fiberWeight w c k)) l = moment w (fun x => l (c x)) := by
  simpa only [moment, total, mul_one, mul_comm] using sum_fiber_moment w (fun _ => 1) c l

theorem fiber_mixed_moment [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w f : Ω → ℚ) (c : Ω → κ) (l : κ → ℚ) (hw : ∀ x, 0 ≤ w x) :
    moment (fun k => total (fiberWeight w c k)) (fun k => l k * expectation (fiberWeight w c k) f) =
      moment w (fun x => l (c x) * f x) := by
  have he : ∀ k, total (fiberWeight w c k) * (l k * expectation (fiberWeight w c k) f) =
      l k * moment (fiberWeight w c k) f := by
    intro k
    rw [moment_eq_total_mul_expectation _ f (fiberWeight_nonneg w c hw k)]
    ring
  unfold moment
  simp_rw [he]
  exact sum_fiber_moment w f c l

theorem fiber_mean_moment [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w f : Ω → ℚ) (c : Ω → κ) (hw : ∀ x, 0 ≤ w x) :
    moment (fun k => total (fiberWeight w c k)) (fun k => expectation (fiberWeight w c k) f) =
      moment w f := by
  simpa only [one_mul] using fiber_mixed_moment w f c (fun _ => 1) hw

theorem covariance_of_regression [Fintype Ω] [Fintype κ] [LinearOrder κ]
    (w f : Ω → ℚ) (c : Ω → κ) (l : κ → ℚ) (hw : ∀ x, 0 ≤ w x)
    (hl : Monotone l)
    (hreg : ∀ i j, 0 < total (fiberWeight w c i) → 0 < total (fiberWeight w c j) →
      i ≤ j → expectation (fiberWeight w c i) f ≤ expectation (fiberWeight w c j) f) :
    CovNonneg w (fun x => l (c x)) f := by
  have h := covariance_on_support (fun k => total (fiberWeight w c k)) l
    (fun k => expectation (fiberWeight w c k) f)
    (fun k => total_nonneg _ (fiberWeight_nonneg w c hw k)) (by
      intro i j hi hj
      rcases le_total i j with hij | hji
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hl hij))
          (sub_nonpos.mpr (hreg i j hi hj hij))
      · exact mul_nonneg (sub_nonneg.mpr (hl hji))
          (sub_nonneg.mpr (hreg j i hj hi hji)))
  unfold CovNonneg at h ⊢
  rwa [fiber_class_moment, fiber_mean_moment w f c hw, fiber_mass_total,
    fiber_mixed_moment w f c l hw] at h

theorem expectation_sizeBias_eq_ratio [Fintype Ω] (w l f : Ω → ℚ) (hZ : total w ≠ 0) :
    expectation (sizeBias w l) f = expectation w (fun x => l x * f x) / expectation w l := by
  have hm : moment (sizeBias w l) f = moment w (fun x => l x * f x) := by
    simp only [moment, sizeBias, mul_assoc]
  unfold expectation
  rw [hm, show total (sizeBias w l) = moment w l from rfl]
  exact (div_div_div_cancel_right₀ hZ _ _).symm

theorem expectation_le_bias_of_regression [Fintype Ω] [Fintype κ] [LinearOrder κ]
    (w f : Ω → ℚ) (c : Ω → κ) (l : κ → ℚ) (hw : ∀ x, 0 ≤ w x)
    (hZ : 0 < total w) (hL : 0 < moment w (fun x => l (c x))) (hl : Monotone l)
    (hreg : ∀ i j, 0 < total (fiberWeight w c i) → 0 < total (fiberWeight w c j) →
      i ≤ j → expectation (fiberWeight w c i) f ≤ expectation (fiberWeight w c j) f) :
    expectation w f ≤ expectation (sizeBias w (fun x => l (c x))) f := by
  have h := covariance_of_regression w f c l hw hl hreg
  have hm : moment (sizeBias w (fun x => l (c x))) f = moment w (fun x => l (c x) * f x) := by
    simp only [moment, sizeBias, mul_assoc]
  unfold expectation
  rw [show total (sizeBias w (fun x => l (c x))) = moment w (fun x => l (c x)) from rfl, hm]
  apply (div_le_div_iff₀ hZ hL).mpr
  unfold CovNonneg at h
  nlinarith

end MatchingCapacity
