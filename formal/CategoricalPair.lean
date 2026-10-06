import CategoricalLaw

/-! Fix all destinations outside a distinguished pair. The remaining
fiber of actual assignments has exactly the earlier pair polynomial. -/
set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

abbrev PairOutside (i j : κ) := Option {k : κ // k ≠ i ∧ k ≠ j}

def pairLabel (i j k : κ) : PairOutside i j :=
  if h : k = i ∨ k = j then none else some ⟨k, by tauto⟩

def pairPattern (i j : κ) (d : ι → κ) : ι → PairOutside i j := fun r => pairLabel i j (d r)

def pairActive (i j : κ) (o : ι → PairOutside i j) : Finset ι :=
  Finset.univ.filter (fun r => o r = none)

def pairOutsideWeight (p : ι → κ → ℚ) (i j : κ) (o : ι → PairOutside i j) : ℚ :=
  ∏ r, match o r with | none => 1 | some k => p r k.val

def pairSliceMass (p : ι → κ → ℚ) (i j : κ) (o : ι → PairOutside i j) (a : ℕ) : ℚ :=
  assignmentEventMass p (fun d => pairPattern i j d = o ∧ assignmentLoad d i = a)

omit [Fintype κ] in
theorem pairLabel_none_iff (i j k : κ) : pairLabel i j k = none ↔ k = i ∨ k = j := by
  unfold pairLabel
  split <;> simp_all

omit [Fintype κ] in
theorem pairLabel_some_iff (i j b : κ) (k : {k : κ // k ≠ i ∧ k ≠ j}) :
    pairLabel i j b = some k ↔ b = k.val := by
  by_cases h : b = i ∨ b = j
  · simp only [pairLabel, dite_eq_left h, reduceCtorEq, false_iff]
    intro he
    subst b
    exact h.elim k.property.1 k.property.2
  · simp [pairLabel, h, Subtype.ext_iff]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem pairOutsideWeight_nonneg (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (i j : κ) (o : ι → PairOutside i j) : 0 ≤ pairOutsideWeight p i j o := by
  apply Finset.prod_nonneg
  intro r _
  cases o r with
  | none => exact zero_le_one
  | some k => exact hp r k.val

omit [Fintype ι] [DecidableEq ι] in
theorem pair_row_polynomial (p : ι → κ → ℚ) (i j : κ) (hij : i ≠ j)
    (o : ι → PairOutside i j) (r : ι) :
    rowMarkedPolynomial p (fun r b => pairLabel i j b = o r) i r =
      C (match o r with | none => 1 | some k => p r k.val) *
        (if o r = none then C (p r i)*X + C (p r j) else 1) := by
  classical
  unfold rowMarkedPolynomial
  cases ho : o r with
  | none =>
    simp only [ho, pairLabel_none_iff]
    have h := Finset.sum_eq_add_of_mem (f := fun b : κ =>
      if b = i ∨ b = j then C (p r b)*X^(if b = i then 1 else 0) else 0)
      i j (Finset.mem_univ i) (Finset.mem_univ j) hij (by
        intro b _ hb
        simp [hb.1, hb.2])
    simpa [hij, hij.symm] using h
  | some k =>
    simp only [ho, pairLabel_some_iff]
    simp [k.property.1]

omit [DecidableEq ι] in
theorem pair_fiber_polynomial (p : ι → κ → ℚ) (i j : κ) (hij : i ≠ j)
    (o : ι → PairOutside i j) :
    markedProduct p (fun r b => pairLabel i j b = o r) i =
      C (pairOutsideWeight p i j o) * pairPolynomial (pairActive i j o) (fun r => p r i) (fun r => p r j) := by
  classical
  unfold markedProduct
  simp_rw [pair_row_polynomial p i j hij o]
  rw [Finset.prod_mul_distrib, ← map_prod]
  congr 1
  simp [pairPolynomial, pairActive, Finset.prod_filter]

theorem pairSliceMass_coeff (p : ι → κ → ℚ) (i j : κ) (hij : i ≠ j)
    (o : ι → PairOutside i j) (a : ℕ) :
    pairSliceMass p i j o a = pairOutsideWeight p i j o *
      (pairPolynomial (pairActive i j o) (fun r => p r i) (fun r => p r j)).coeff a := by
  have h := markedProduct_coeff p (fun r b => pairLabel i j b = o r) i a
  rw [pair_fiber_polynomial p i j hij o, Polynomial.coeff_C_mul] at h
  rw [h]
  apply assignmentEventMass_congr
  intro d
  simp only [pairPattern, funext_iff]

theorem pairSliceMass_partition (p : ι → κ → ℚ) (i j : κ) (a : ℕ) :
    assignmentEventMass p (fun d => assignmentLoad d i = a) = ∑ o, pairSliceMass p i j o a := by
  exact assignmentEventMass_partition p (pairPattern i j) (fun d => assignmentLoad d i = a)

theorem pairSliceMass_boundary (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (i j : κ) (hij : i ≠ j) (horder : ∀ r, p r j ≤ p r i)
    (o : ι → PairOutside i j) (q : ℕ)
    (hq : q ≤ (pairActive i j o).card) (ht : (pairActive i j o).card ≤ 2*q) :
    pairSliceMass p i j o ((pairActive i j o).card-q) ≤ pairSliceMass p i j o q := by
  rw [pairSliceMass_coeff p i j hij, pairSliceMass_coeff p i j hij]
  exact mul_le_mul_of_nonneg_left
    (pair_boundary_coeff _ _ _ (fun r _ => horder r) (fun r _ => hp r j) q hq ht)
    (pairOutsideWeight_nonneg p hp i j o)

theorem pairSliceMass_balancing (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (i j : κ) (hij : i ≠ j) (horder : ∀ r, p r j ≤ p r i)
    (o : ι → PairOutside i j) (a c : ℕ)
    (hac : a+c = (pairActive i j o).card) (hgap : c+2 ≤ a) :
    ((a-1).factorial : ℚ)*((c+1).factorial : ℚ)*
      (pairSliceMass p i j o (a-1) + pairSliceMass p i j o (c+1)) ≤
      (a.factorial : ℚ)*(c.factorial : ℚ)*(pairSliceMass p i j o a + pairSliceMass p i j o c) := by
  simp only [pairSliceMass_coeff p i j hij]
  have h := mul_le_mul_of_nonneg_left
    (pair_factorial_balancing (pairActive i j o) (fun r => p r i) (fun r => p r j)
      (fun r _ => horder r) (fun r _ => hp r j) a c hac hgap)
    (pairOutsideWeight_nonneg p hp i j o)
  nlinarith

omit [Fintype κ] [DecidableEq ι] in
theorem pairPattern_count (i j : κ) (hij : i ≠ j) (d : ι → κ)
    (o : ι → PairOutside i j) (ho : pairPattern i j d = o) :
    assignmentLoad d i + assignmentLoad d j = (pairActive i j o).card := by
  classical
  subst o
  simp only [assignmentLoad, ← Finset.sum_add_distrib, pairActive, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro r _
  simp only [pairPattern, pairLabel_none_iff]
  by_cases hi : d r = i
  · simp [hi, hij]
  · by_cases hj : d r = j
    · simp [hj, hij.symm]
    · simp [hi, hj]

def pairOutsideLoad (i j : κ) (o : ι → PairOutside i j)
    (k : {k : κ // k ≠ i ∧ k ≠ j}) : ℕ := ∑ r, if o r = some k then 1 else 0

omit [Fintype κ] [DecidableEq ι] in
theorem pairPattern_outside_load (i j : κ) (d : ι → κ)
    (o : ι → PairOutside i j) (ho : pairPattern i j d = o)
    (k : {k : κ // k ≠ i ∧ k ≠ j}) : assignmentLoad d k.val = pairOutsideLoad i j o k := by
  subst o
  simp only [assignmentLoad, pairOutsideLoad, pairPattern, pairLabel_some_iff]

end MatchingCapacity
