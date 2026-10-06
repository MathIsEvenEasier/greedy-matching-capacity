import CategoricalConcentration

/-! Exact identification of capped-load expectations with conditional
expectations of the original independent categorical assignments. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b q : ℕ}

def cappedAssignment (d : ι → Fin b) (h : assignmentCapped q d) :
    CappedLoad b q (Fintype.card ι) :=
  ⟨fun k => ⟨assignmentLoad d k, Nat.lt_succ_of_le (h k)⟩, assignmentLoad_total d⟩

def cappedAssignmentMoment (p : ι → Fin b → ℚ) (q : ℕ)
    (F : CappedLoad b q (Fintype.card ι) → ℚ) : ℚ :=
  ∑ d, if h : assignmentCapped q d then assignmentWeight p d * F (cappedAssignment d h) else 0

omit [DecidableEq ι] in
theorem cappedAssignment_eq_iff (d : ι → Fin b) (h : assignmentCapped q d)
    (x : CappedLoad b q (Fintype.card ι)) :
    assignmentLoad d = (fun k => (x.val k).val) ↔ cappedAssignment d h = x := by
  constructor
  · intro he
    apply Subtype.ext
    funext k
    apply Fin.ext
    exact congrFun he k
  · intro he
    subst x
    rfl

theorem capped_categorical_assignment_moment (p : ι → Fin b → ℚ)
    (F : CappedLoad b q (Fintype.card ι) → ℚ) :
    moment (cappedCategoricalWeight p) F = cappedAssignmentMoment p q F := by
  unfold moment cappedCategoricalWeight categoricalLoadMass assignmentEventMass cappedAssignmentMoment
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : assignmentCapped q d
  · rw [dite_eq_left hd]
    simp_rw [cappedAssignment_eq_iff d hd]
    simp
  · rw [dite_eq_right hd]
    apply Finset.sum_eq_zero
    intro x _
    have he : assignmentLoad d ≠ (fun k => (x.val k).val) := by
      intro hh
      apply hd
      intro k
      rw [hh]
      exact Nat.le_of_lt_succ (x.val k).isLt
    simp [he]

theorem capped_categorical_assignment_total (p : ι → Fin b → ℚ) (q : ℕ) :
    total (cappedCategoricalWeight (q := q) (T := Fintype.card ι) p) =
      assignmentEventMass p (assignmentCapped q) := by
  have h := capped_categorical_assignment_moment p (fun _ : CappedLoad b q (Fintype.card ι) => 1)
  simpa only [moment, total, mul_one, cappedAssignmentMoment, assignmentEventMass,
    dite_eq_ite] using h

theorem categorical_conditional_concentration (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (hcap : 0 < assignmentEventMass p (assignmentCapped q))
    (F : CappedLoad b q (Fintype.card ι) → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y) :
    expectation cappedWeight F ≤
      cappedAssignmentMoment p q F / assignmentEventMass p (assignmentCapped q) := by
  have hmass : 0 < total (cappedCategoricalWeight (q := q) (T := Fintype.card ι) p) := by
    rwa [capped_categorical_assignment_total]
  have h := capped_categorical_concentration p hp horder hmass F hF
  simpa only [expectation, capped_categorical_assignment_moment, capped_categorical_assignment_total] using h

end MatchingCapacity
