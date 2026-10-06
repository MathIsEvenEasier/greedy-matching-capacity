import CategoricalConditioning
import CategoricalNextChoice

/-! The complete categorical saturation bound: concentration of the old
loads and the ordered next-choice comparison combine without a hazard premise. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b q : ℕ}

theorem capped_assignment_maxCount (p : ι → Fin b → ℚ) (q : ℕ) :
    cappedAssignmentMoment p q (fun x => (maxCount x : ℚ)) = ∑ k, cappedBoundaryMass p q k := by
  unfold cappedAssignmentMoment cappedBoundaryMass assignmentEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : assignmentCapped q d
  · rw [dite_eq_left hd]
    change assignmentWeight p d * (maxCount (cappedAssignment d hd) : ℚ) = _
    rw [← total_maxMark]
    change assignmentWeight p d * (∑ k, if assignmentLoad d k = q then (1 : ℚ) else 0) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : assignmentLoad d k = q <;> simp [hd, hk]
  · simp [hd]

theorem uniform_next_saturation_eq (p : ι → Fin b → ℚ) (q : ℕ) :
    nextSaturationProbability p (fun _ => 1/(b : ℚ)) q =
      (cappedAssignmentMoment p q (fun x => (maxCount x : ℚ)) /
        assignmentEventMass p (assignmentCapped q)) / (b : ℚ) := by
  rw [nextSaturationProbability_eq, ← Finset.mul_sum]
  unfold cappedBoundaryProbability
  rw [← Finset.sum_div, ← capped_assignment_maxCount]
  ring

theorem categorical_saturation_lower_bound (hb : 0 < b) (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (v : Fin b → ℚ) (hv : Antitone v) (hprob : ∑ k, v k = 1)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) :
    expectation (cappedWeight (b := b) (q := q) (r := Fintype.card ι))
      (fun x => (maxCount x : ℚ)) / (b : ℚ) ≤ nextSaturationProbability p v q := by
  have h := categorical_conditional_concentration p hp horder hcap
    (fun x => (maxCount x : ℚ)) (fun x y hxy => Nat.cast_le.mpr (maxCount_mono x y hxy))
  have hh := div_le_div_of_nonneg_right h (show (0 : ℚ) ≤ b from Nat.cast_nonneg b)
  rw [← uniform_next_saturation_eq] at hh
  exact hh.trans (uniform_next_minimizes_saturation hb p hp horder v hv hprob q hcap)

end MatchingCapacity
