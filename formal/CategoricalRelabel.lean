import UniformCappedLaw

/-! Reindexing the bins changes no conditional saturation probability. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

def assignmentRelabel (e : κ ≃ τ) : (ι → κ) ≃ (ι → τ) where
  toFun d := e ∘ d
  invFun d := e.symm ∘ d
  left_inv d := by funext r; exact e.symm_apply_apply (d r)
  right_inv d := by funext r; exact e.apply_symm_apply (d r)

omit [Fintype κ] [Fintype τ] [DecidableEq ι] in
theorem assignmentLoad_relabel (e : κ ≃ τ) (d : ι → κ) (k : κ) :
    assignmentLoad (assignmentRelabel e d) (e k) = assignmentLoad d k := by
  simp [assignmentLoad, assignmentRelabel]

omit [Fintype κ] [Fintype τ] [DecidableEq ι] in
theorem assignmentCapped_relabel (e : κ ≃ τ) (q : ℕ) (d : ι → κ) :
    assignmentCapped q (assignmentRelabel e d) ↔ assignmentCapped q d := by
  unfold assignmentCapped
  constructor
  · intro h k
    simpa only [assignmentLoad_relabel] using h (e k)
  · intro h k
    obtain ⟨l,rfl⟩ := e.surjective k
    simpa only [assignmentLoad_relabel] using h l

theorem assignment_cap_mass_relabel (e : κ ≃ τ) (p : ι → τ → ℚ) (q : ℕ) :
    assignmentEventMass (fun r k => p r (e k)) (assignmentCapped q) =
      assignmentEventMass p (assignmentCapped q) := by
  unfold assignmentEventMass
  rw [← (assignmentRelabel (ι := ι) e).sum_comp
    (fun d => if assignmentCapped q d then assignmentWeight p d else 0)]
  simp only [assignmentCapped_relabel]
  rfl

theorem next_saturation_relabel (e : κ ≃ τ) (p : ι → τ → ℚ) (v : τ → ℚ) (q : ℕ) :
    nextSaturationProbability (fun r k => p r (e k)) (fun k => v (e k)) q =
      nextSaturationProbability p v q := by
  unfold nextSaturationProbability
  rw [assignment_cap_mass_relabel]
  congr 1
  unfold nextSaturationMass
  rw [← (assignmentRelabel (ι := ι) e).sum_comp
    (fun d => ∑ k, if assignmentCapped q d ∧ assignmentLoad d k = q then assignmentWeight p d * v k else 0)]
  apply Finset.sum_congr rfl
  intro d _
  rw [← e.sum_comp (fun k => if assignmentCapped q (assignmentRelabel e d) ∧
    assignmentLoad (assignmentRelabel e d) k = q then assignmentWeight p (assignmentRelabel e d) * v k else 0)]
  simp only [assignmentCapped_relabel, assignmentLoad_relabel]
  rfl

end MatchingCapacity
