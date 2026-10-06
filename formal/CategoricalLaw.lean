import PairApplications

/-! Exact weights of independent categorical assignments and their
one-coordinate generating polynomial, with arbitrary rowwise restrictions. -/
set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def assignmentWeight (p : ι → κ → ℚ) (d : ι → κ) : ℚ := ∏ r, p r (d r)

def assignmentLoad (d : ι → κ) (k : κ) : ℕ := ∑ r, if d r = k then 1 else 0

def assignmentEventMass (p : ι → κ → ℚ) (E : (ι → κ) → Prop) : ℚ := by
  classical
  exact ∑ d, if E d then assignmentWeight p d else 0

def categoricalLoadMass (p : ι → κ → ℚ) (x : κ → ℕ) : ℚ :=
  assignmentEventMass p (fun d => assignmentLoad d = x)

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem assignmentWeight_nonneg (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k) (d : ι → κ) :
    0 ≤ assignmentWeight p d := by
  exact Finset.prod_nonneg (fun r _ => hp r (d r))

omit [DecidableEq κ] in
theorem assignmentEventMass_nonneg (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (E : (ι → κ) → Prop) : 0 ≤ assignmentEventMass p E := by
  classical
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact assignmentWeight_nonneg p hp d
  · exact le_rfl

omit [DecidableEq κ] in
theorem assignmentWeight_total (p : ι → κ → ℚ) :
    (∑ d, assignmentWeight p d) = ∏ r, ∑ k, p r k := by
  exact (Fintype.prod_sum p).symm

omit [DecidableEq κ] in
theorem assignmentWeight_probability (p : ι → κ → ℚ) (hp : ∀ r, ∑ k, p r k = 1) :
    (∑ d, assignmentWeight p d) = 1 := by
  rw [assignmentWeight_total]
  simp [hp]

omit [DecidableEq ι] in
theorem assignmentLoad_total (d : ι → κ) : ∑ k, assignmentLoad d k = Fintype.card ι := by
  unfold assignmentLoad
  rw [Finset.sum_comm]
  simp

theorem categoricalLoadMass_zero (p : ι → κ → ℚ) (x : κ → ℕ)
    (hx : (∑ k, x k) ≠ Fintype.card ι) : categoricalLoadMass p x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d _
  have h : assignmentLoad d ≠ x := by
    intro he
    exact hx (he ▸ assignmentLoad_total d)
  exact ite_eq_right h

def restrictedAssignmentWeight (p : ι → κ → ℚ) (A : ι → κ → Prop) (d : ι → κ) : ℚ := by
  classical
  exact ∏ r, if A r (d r) then p r (d r) else 0

def rowMarkedPolynomial (p : ι → κ → ℚ) (A : ι → κ → Prop) (k : κ) (r : ι) : ℚ[X] := by
  classical
  exact ∑ b, if A r b then C (p r b)*X^(if b = k then 1 else 0) else 0

def markedProduct (p : ι → κ → ℚ) (A : ι → κ → Prop) (k : κ) : ℚ[X] :=
  ∏ r, rowMarkedPolynomial p A k r

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem restrictedAssignmentWeight_eq (p : ι → κ → ℚ) (A : ι → κ → Prop) (d : ι → κ) :
    restrictedAssignmentWeight p A d = if ∀ r, A r (d r) then assignmentWeight p d else 0 := by
  classical
  by_cases h : ∀ r, A r (d r)
  · simp [restrictedAssignmentWeight, assignmentWeight, h]
  · rw [ite_eq_right h]
    obtain ⟨r, hr⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    exact ite_eq_right hr

theorem markedProduct_expansion (p : ι → κ → ℚ) (A : ι → κ → Prop) (k : κ) :
    markedProduct p A k = ∑ d, C (restrictedAssignmentWeight p A d)*X^(assignmentLoad d k) := by
  classical
  unfold markedProduct rowMarkedPolynomial
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he : (∏ r, if A r (d r) then C (p r (d r))*X^(if d r = k then 1 else 0) else 0) =
      ∏ r, C (if A r (d r) then p r (d r) else 0)*X^(if d r = k then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro r _
    split_ifs <;> simp
  rw [he, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rfl

theorem markedProduct_coeff (p : ι → κ → ℚ) (A : ι → κ → Prop) (k : κ) (a : ℕ) :
    (markedProduct p A k).coeff a =
      assignmentEventMass p (fun d => (∀ r, A r (d r)) ∧ assignmentLoad d k = a) := by
  classical
  rw [markedProduct_expansion, Polynomial.finsetSum_coeff]
  unfold assignmentEventMass
  apply Finset.sum_congr rfl
  intro d _
  rw [Polynomial.coeff_C_mul_X_pow, restrictedAssignmentWeight_eq]
  by_cases h : ∀ r, A r (d r)
  · simp [h, eq_comm]
  · simp [h]

omit [DecidableEq κ] in
theorem assignmentEventMass_partition {τ : Type*} [Fintype τ] [DecidableEq τ]
    (p : ι → κ → ℚ) (f : (ι → κ) → τ) (E : (ι → κ) → Prop) :
    assignmentEventMass p E = ∑ t, assignmentEventMass p (fun d => f d = t ∧ E d) := by
  classical
  unfold assignmentEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : E d <;> simp [h]

omit [DecidableEq κ] in
theorem assignmentEventMass_congr (p : ι → κ → ℚ) (E D : (ι → κ) → Prop)
    (h : ∀ d, E d ↔ D d) : assignmentEventMass p E = assignmentEventMass p D := by
  classical
  unfold assignmentEventMass
  simp_rw [h]

end MatchingCapacity
