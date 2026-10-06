import CategoricalRelabel

/-! Row constants cancel after conditioning, without assuming normalized
old rows. This is essential for the raw RV rows of a history refinement. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem constant_rows_cap_mass (w : ι → ℚ) (q : ℕ) :
    assignmentEventMass (fun r (_ : κ) => w r) (assignmentCapped q) =
      (∏ r, w r) * assignmentEventMass (fun (_ : ι) (_ : κ) => 1) (assignmentCapped q) := by
  unfold assignmentEventMass assignmentWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

theorem constant_rows_next_mass (w : ι → ℚ) (v : κ → ℚ) (q : ℕ) :
    nextSaturationMass (fun r _ => w r) v q =
      (∏ r, w r) * nextSaturationMass (fun (_ : ι) _ => 1) v q := by
  unfold nextSaturationMass assignmentWeight
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem constant_rows_saturation (w : ι → ℚ) (v : κ → ℚ) (q : ℕ)
    (hm : 0 < assignmentEventMass (fun r (_ : κ) => w r) (assignmentCapped q)) :
    nextSaturationProbability (fun r _ => w r) v q =
      nextSaturationProbability (fun (_ : ι) _ => 1) v q := by
  have hw : (∏ r, w r) ≠ 0 := by
    intro hw
    rw [constant_rows_cap_mass, hw, zero_mul] at hm
    exact (lt_irrefl 0) hm
  unfold nextSaturationProbability
  rw [constant_rows_next_mass, constant_rows_cap_mass, mul_div_mul_left _ _ hw]

omit [Fintype κ] [DecidableEq κ] in
theorem constant_rows_eq_uniform {b : ℕ} (hb : 0 < b) (p : ι → Fin b → ℚ)
    (hc : ∀ r i j, p r i = p r j) (v : Fin b → ℚ) (q : ℕ)
    (hm : 0 < assignmentEventMass p (assignmentCapped q)) :
    nextSaturationProbability p v q = nextSaturationProbability (uniformRows (ι := ι) b) v q := by
  let k : Fin b := ⟨0,hb⟩
  have he : p = fun r _ => p r k := by funext r l; exact hc r l k
  have hu := uniform_cap_positive_of_positive hb p hm
  rw [he] at hm ⊢
  rw [constant_rows_saturation _ v q hm]
  exact (constant_rows_saturation (fun _ : ι => 1/(b : ℚ)) v q hu).symm

end MatchingCapacity
