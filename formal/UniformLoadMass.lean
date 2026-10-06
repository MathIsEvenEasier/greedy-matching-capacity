import CategoricalLaw
import CappedCarrier
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! The multinomial coefficient counts actual assignment fibers.
Constant destination weights in each row therefore give exactly the
factorial reference law, before any cap or normalization is imposed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def loadExponent (x : κ → ℕ) : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm x

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem loadExponent_apply (x : κ → ℕ) (k : κ) : loadExponent x k = x k := rfl

omit [DecidableEq ι] in
theorem assignment_loadExponent (d : ι → κ) :
    loadExponent (assignmentLoad d) = ∑ r, Finsupp.single (d r) 1 := by
  ext k
  simp [loadExponent, assignmentLoad, Finsupp.single_apply]

omit [DecidableEq ι] in
theorem assignment_monomial (d : ι → κ) :
    (MvPolynomial.monomial (loadExponent (assignmentLoad d)) 1 : MvPolynomial κ ℚ) =
      ∏ r, MvPolynomial.X (d r) := by
  rw [assignment_loadExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem assignment_polynomial_expansion :
    (∑ k, MvPolynomial.X k : MvPolynomial κ ℚ)^(Fintype.card ι) =
      ∑ d : ι → κ, MvPolynomial.monomial (loadExponent (assignmentLoad d)) 1 := by
  have h : (∑ k, MvPolynomial.X k : MvPolynomial κ ℚ)^(Fintype.card ι) =
      ∏ _r : ι, ∑ k, MvPolynomial.X k := by simp
  rw [h, Fintype.prod_sum]
  simp_rw [assignment_monomial]

theorem unitLoadMass_coeff (x : κ → ℕ) :
    ((∑ k, MvPolynomial.X k : MvPolynomial κ ℚ)^(Fintype.card ι)).coeff (loadExponent x) =
      categoricalLoadMass (fun _ : ι => fun _ : κ => (1 : ℚ)) x := by
  rw [assignment_polynomial_expansion, MvPolynomial.coeff_sum]
  unfold categoricalLoadMass assignmentEventMass
  apply Finset.sum_congr rfl
  intro d _
  have he : loadExponent (assignmentLoad d) = loadExponent x ↔ assignmentLoad d = x :=
    Finsupp.equivFunOnFinite.symm.injective.eq_iff
  simp only [MvPolynomial.coeff_monomial, he, assignmentWeight, Finset.prod_const_one]
  by_cases h : assignmentLoad d = x <;> simp [h]

theorem unitLoadMass_multinomial (x : κ → ℕ) (hx : (∑ k, x k) = Fintype.card ι) :
    categoricalLoadMass (fun _ : ι => fun _ : κ => (1 : ℚ)) x =
      (Nat.multinomial Finset.univ x : ℚ) := by
  rw [← unitLoadMass_coeff, MvPolynomial.coeff_sum_X_pow_of_fintype]
  have he : (loadExponent x).sum (fun _ m => m) = ∑ k, x k :=
    Finsupp.equivFunOnFinite_symm_sum x
  rw [he, hx, ite_eq_left rfl, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  rfl

theorem categoricalLoadMass_row_constant (w : ι → ℚ) (x : κ → ℕ) :
    categoricalLoadMass (fun r _ => w r) x =
      (∏ r, w r) * categoricalLoadMass (fun _ : ι => fun _ : κ => (1 : ℚ)) x := by
  unfold categoricalLoadMass assignmentEventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : assignmentLoad d = x <;> simp [h, assignmentWeight]

theorem constantRowLoadMass_factorial (w : ι → ℚ) (x : κ → ℕ)
    (hx : (∑ k, x k) = Fintype.card ι) :
    categoricalLoadMass (fun r _ => w r) x =
      (∏ r, w r) * ((Fintype.card ι).factorial : ℚ) * ∏ k, factorialWeight (x k) := by
  have hm : (Nat.multinomial Finset.univ x : ℚ) * (∏ k, ((x k).factorial : ℚ)) =
      ((Fintype.card ι).factorial : ℚ) := by
    have h := Nat.multinomial_spec Finset.univ x
    rw [hx] at h
    exact_mod_cast ((mul_comm (Nat.multinomial Finset.univ x) (∏ k, (x k).factorial)).trans h)
  have hD : (∏ k, ((x k).factorial : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact_mod_cast Nat.factorial_ne_zero (x k)
  have hprod : (∏ k, factorialWeight (x k)) = (∏ k, ((x k).factorial : ℚ))⁻¹ := by
    simp [factorialWeight]
  rw [categoricalLoadMass_row_constant, unitLoadMass_multinomial x hx, hprod, ← hm]
  field_simp [hD]

end MatchingCapacity
