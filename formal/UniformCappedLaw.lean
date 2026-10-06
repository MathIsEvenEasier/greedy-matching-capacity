import UniformLoadMass
import CategoricalHazard

/-! Exact uniform-row reference law and direct comparisons between
actual categorical assignment laws, including cap feasibility. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b q : ℕ}

def uniformRows (b : ℕ) : ι → Fin b → ℚ := fun _ _ => 1/(b : ℚ)

def uniformLoadScale (r b : ℕ) : ℚ := (1/(b : ℚ))^r * (r.factorial : ℚ)

theorem uniformLoadScale_pos (r b : ℕ) (hb : 0 < b) : 0 < uniformLoadScale r b := by
  unfold uniformLoadScale
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  exact mul_pos (pow_pos (one_div_pos.mpr hbq) r) (by exact_mod_cast Nat.factorial_pos r)

omit [Fintype ι] [DecidableEq ι] in
theorem uniformRows_probability (hb : 0 < b) (r : ι) : ∑ k, uniformRows b r k = 1 := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp [uniformRows, hbq]

theorem uniform_assignment_probability (hb : 0 < b) :
    (∑ d : ι → Fin b, assignmentWeight (uniformRows b) d) = 1 := by
  exact assignmentWeight_probability _ (uniformRows_probability hb)

theorem uniform_capped_weight (x : CappedLoad b q (Fintype.card ι)) :
    cappedCategoricalWeight (uniformRows (ι := ι) b) x =
      uniformLoadScale (Fintype.card ι) b * cappedWeight x := by
  unfold cappedCategoricalWeight uniformRows
  rw [constantRowLoadMass_factorial _ _ x.property]
  simp only [Finset.prod_const, Finset.card_univ, uniformLoadScale, cappedWeight]

theorem uniform_capped_moment (F : CappedLoad b q (Fintype.card ι) → ℚ) :
    moment (cappedCategoricalWeight (uniformRows (ι := ι) b)) F =
      uniformLoadScale (Fintype.card ι) b * moment cappedWeight F := by
  simp only [moment, uniform_capped_weight, mul_assoc, Finset.mul_sum]

theorem uniform_capped_total (q : ℕ) :
    total (cappedCategoricalWeight (q := q) (T := Fintype.card ι) (uniformRows (ι := ι) b)) =
      uniformLoadScale (Fintype.card ι) b * total (cappedWeight (b := b) (q := q) (r := Fintype.card ι)) := by
  simpa only [moment, total, mul_one] using
    uniform_capped_moment (fun _ : CappedLoad b q (Fintype.card ι) => 1)

theorem uniform_capped_expectation (hb : 0 < b) (F : CappedLoad b q (Fintype.card ι) → ℚ) :
    expectation (cappedCategoricalWeight (uniformRows (ι := ι) b)) F = expectation cappedWeight F := by
  unfold expectation
  rw [uniform_capped_moment, uniform_capped_total,
    mul_div_mul_left _ _ (uniformLoadScale_pos (Fintype.card ι) b hb).ne']

theorem uniform_assignment_cap_mass (q : ℕ) :
    assignmentEventMass (uniformRows (ι := ι) b) (assignmentCapped q) =
      uniformLoadScale (Fintype.card ι) b * total (cappedWeight (b := b) (q := q) (r := Fintype.card ι)) := by
  rw [← capped_categorical_assignment_total, uniform_capped_total]

theorem uniform_cap_feasible (hb : 0 < b) (q : ℕ) :
    0 < assignmentEventMass (uniformRows (ι := ι) b) (assignmentCapped q) ↔ Fintype.card ι ≤ b*q := by
  rw [uniform_assignment_cap_mass, mul_pos_iff_of_pos_left (uniformLoadScale_pos (Fintype.card ι) b hb),
    capped_total_pos_iff]

theorem positive_assignment_cap_feasible (p : ι → Fin b → ℚ)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) : Fintype.card ι ≤ b*q := by
  have hm : 0 < total (cappedCategoricalWeight (q := q) (T := Fintype.card ι) p) := by
    rwa [capped_categorical_assignment_total]
  have hnonempty : Nonempty (CappedLoad b q (Fintype.card ι)) := by
    by_contra h
    have : IsEmpty (CappedLoad b q (Fintype.card ι)) := not_nonempty_iff.mp h
    simp [total] at hm
  obtain ⟨x⟩ := hnonempty
  calc
    Fintype.card ι = ∑ i, (x.val i).val := x.property.symm
    _ ≤ ∑ _i : Fin b, q := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x.val i).isLt)
    _ = b*q := by simp

theorem uniform_cap_positive_of_positive (hb : 0 < b) (p : ι → Fin b → ℚ)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) :
    0 < assignmentEventMass (uniformRows (ι := ι) b) (assignmentCapped q) :=
  (uniform_cap_feasible hb q).mpr (positive_assignment_cap_feasible p hcap)

theorem uniform_conditional_expectation (hb : 0 < b)
    (F : CappedLoad b q (Fintype.card ι) → ℚ) :
    cappedAssignmentMoment (uniformRows b) q F /
      assignmentEventMass (uniformRows (ι := ι) b) (assignmentCapped q) = expectation cappedWeight F := by
  rw [← capped_categorical_assignment_moment, ← capped_categorical_assignment_total]
  exact uniform_capped_expectation hb F

theorem uniform_saturation_reference (hb : 0 < b) (q : ℕ) :
    nextSaturationProbability (uniformRows (ι := ι) b) (fun _ => 1/(b : ℚ)) q =
      expectation (cappedWeight (b := b) (q := q) (r := Fintype.card ι))
        (fun x => (maxCount x : ℚ)) / (b : ℚ) := by
  rw [uniform_next_saturation_eq, uniform_conditional_expectation hb]

theorem ordered_vs_uniform_concentration (hb : 0 < b) (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (hcap : 0 < assignmentEventMass p (assignmentCapped q))
    (F : CappedLoad b q (Fintype.card ι) → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y) :
    cappedAssignmentMoment (uniformRows b) q F /
      assignmentEventMass (uniformRows (ι := ι) b) (assignmentCapped q) ≤
    cappedAssignmentMoment p q F / assignmentEventMass p (assignmentCapped q) := by
  rw [uniform_conditional_expectation hb]
  exact categorical_conditional_concentration p hp horder hcap F hF

theorem ordered_vs_uniform_saturation (hb : 0 < b) (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (v : Fin b → ℚ) (hv : Antitone v) (hprob : ∑ k, v k = 1)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) :
    nextSaturationProbability (uniformRows (ι := ι) b) (fun _ => 1/(b : ℚ)) q ≤
      nextSaturationProbability p v q := by
  rw [uniform_saturation_reference hb]
  exact categorical_saturation_lower_bound hb p hp horder v hv hprob hcap

end MatchingCapacity
