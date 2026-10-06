import CategoricalBoundary

/-! Actual joint mass of independent old assignments and a next choice.
Commonly ordered rows imply that a uniform next choice minimizes the
conditional saturation probability. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def nextSaturationMass (p : ι → κ → ℚ) (v : κ → ℚ) (q : ℕ) : ℚ := by
  classical
  exact ∑ d, ∑ k, if assignmentCapped q d ∧ assignmentLoad d k = q then assignmentWeight p d * v k else 0

def nextSaturationProbability (p : ι → κ → ℚ) (v : κ → ℚ) (q : ℕ) : ℚ :=
  nextSaturationMass p v q / assignmentEventMass p (assignmentCapped q)

theorem nextSaturationMass_eq (p : ι → κ → ℚ) (v : κ → ℚ) (q : ℕ) :
    nextSaturationMass p v q = ∑ k, v k * cappedBoundaryMass p q k := by
  classical
  unfold nextSaturationMass cappedBoundaryMass assignmentEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> ring

theorem nextSaturationProbability_eq (p : ι → κ → ℚ) (v : κ → ℚ) (q : ℕ) :
    nextSaturationProbability p v q = ∑ k, v k * cappedBoundaryProbability p q k := by
  unfold nextSaturationProbability cappedBoundaryProbability
  rw [nextSaturationMass_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_div_assoc _ _ _

theorem cappedBoundaryProbability_antitone {b : ℕ} (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r)) (q : ℕ)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) :
    Antitone (cappedBoundaryProbability p q) := by
  intro i j hij
  by_cases he : i = j
  · subst j
    exact le_rfl
  · exact cappedBoundaryProbability_ordered p hp i j he (fun r => horder r hij) q hcap

theorem uniform_next_minimizes_saturation {b : ℕ} (hb : 0 < b)
    (p : ι → Fin b → ℚ) (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (v : Fin b → ℚ) (hv : Antitone v) (hprob : ∑ k, v k = 1) (q : ℕ)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) :
    nextSaturationProbability p (fun _ => 1/(b : ℚ)) q ≤ nextSaturationProbability p v q := by
  have hg := cappedBoundaryProbability_antitone p hp horder q hcap
  have hc : CovNonneg (fun _ : Fin b => 1) v (cappedBoundaryProbability p q) := by
    apply covariance_of_pairwise _ _ _ (fun _ => zero_le_one)
    intro i j
    rcases le_total i j with h | h
    · exact mul_nonneg (sub_nonneg.mpr (hv h)) (sub_nonneg.mpr (hg h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hv h)) (sub_nonpos.mpr (hg h))
  have he : (∑ k, cappedBoundaryProbability p q k) ≤
      (b : ℚ) * ∑ k, v k * cappedBoundaryProbability p q k := by
    simpa [CovNonneg, total, moment, hprob] using hc
  rw [nextSaturationProbability_eq, nextSaturationProbability_eq, ← Finset.mul_sum]
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hh : (∑ k, cappedBoundaryProbability p q k) / (b : ℚ) ≤
      ∑ k, v k * cappedBoundaryProbability p q k := by
    apply (div_le_iff₀ hbq).mpr
    nlinarith
  simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hh

end MatchingCapacity
