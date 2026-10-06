import CategoricalPair

/-! The boundary comparison for the actual capped categorical law.
Zero-mass patterns remain in the finite sums with weight zero. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def assignmentCapped (q : ℕ) (d : ι → κ) : Prop := ∀ k, assignmentLoad d k ≤ q

def cappedBoundaryMass (p : ι → κ → ℚ) (q : ℕ) (k : κ) : ℚ :=
  assignmentEventMass p (fun d => assignmentCapped q d ∧ assignmentLoad d k = q)

def pairOutsideCapped (i j : κ) (o : ι → PairOutside i j) (q : ℕ) : Prop :=
  ∀ k, pairOutsideLoad i j o k ≤ q

def pairBoundaryAllowed (i j : κ) (o : ι → PairOutside i j) (q : ℕ) : Prop :=
  pairOutsideCapped i j o q ∧ q ≤ (pairActive i j o).card ∧ (pairActive i j o).card ≤ 2*q

omit [Fintype κ] [DecidableEq ι] in
theorem assignmentCapped_pattern (i j : κ) (d : ι → κ) (o : ι → PairOutside i j)
    (ho : pairPattern i j d = o) (q : ℕ) :
    assignmentCapped q d ↔ pairOutsideCapped i j o q ∧ assignmentLoad d i ≤ q ∧ assignmentLoad d j ≤ q := by
  constructor
  · intro h
    refine ⟨?_, h i, h j⟩
    intro k
    rw [← pairPattern_outside_load i j d o ho k]
    exact h k.val
  · rintro ⟨h, hi, hj⟩ k
    by_cases hki : k = i
    · simpa [hki] using hi
    · by_cases hkj : k = j
      · simpa [hkj] using hj
      · rw [pairPattern_outside_load i j d o ho ⟨k, hki, hkj⟩]
        exact h ⟨k, hki, hkj⟩

omit [Fintype κ] [DecidableEq ι] in
theorem cappedBoundary_pattern_left (i j : κ) (hij : i ≠ j) (d : ι → κ)
    (o : ι → PairOutside i j) (ho : pairPattern i j d = o) (q : ℕ) :
    (assignmentCapped q d ∧ assignmentLoad d i = q) ↔
      pairBoundaryAllowed i j o q ∧ assignmentLoad d i = q := by
  rw [assignmentCapped_pattern i j d o ho q]
  have hc := pairPattern_count i j hij d o ho
  unfold pairBoundaryAllowed
  constructor
  · rintro ⟨⟨hout, hi, hj⟩, he⟩
    exact ⟨⟨hout, by omega, by omega⟩, he⟩
  · rintro ⟨⟨hout, hq, ht⟩, he⟩
    exact ⟨⟨hout, by omega, by omega⟩, he⟩

omit [Fintype κ] [DecidableEq ι] in
theorem cappedBoundary_pattern_right (i j : κ) (hij : i ≠ j) (d : ι → κ)
    (o : ι → PairOutside i j) (ho : pairPattern i j d = o) (q : ℕ) :
    (assignmentCapped q d ∧ assignmentLoad d j = q) ↔
      pairBoundaryAllowed i j o q ∧ assignmentLoad d i = (pairActive i j o).card-q := by
  rw [assignmentCapped_pattern i j d o ho q]
  have hc := pairPattern_count i j hij d o ho
  unfold pairBoundaryAllowed
  constructor
  · rintro ⟨⟨hout, hi, hj⟩, he⟩
    exact ⟨⟨hout, by omega, by omega⟩, by omega⟩
  · rintro ⟨⟨hout, hq, ht⟩, he⟩
    exact ⟨⟨hout, by omega, by omega⟩, by omega⟩

theorem pairSliceMass_partition_event (p : ι → κ → ℚ) (i j : κ)
    (E : (ι → κ) → Prop) (A : (ι → PairOutside i j) → Prop)
    (a : (ι → PairOutside i j) → ℕ)
    (hE : ∀ d o, pairPattern i j d = o → (E d ↔ A o ∧ assignmentLoad d i = a o)) :
    assignmentEventMass p E = ∑ o, if A o then pairSliceMass p i j o (a o) else 0 := by
  classical
  rw [assignmentEventMass_partition p (pairPattern i j) E]
  apply Finset.sum_congr rfl
  intro o _
  have he : assignmentEventMass p (fun d => pairPattern i j d = o ∧ E d) =
      assignmentEventMass p (fun d => A o ∧ pairPattern i j d = o ∧ assignmentLoad d i = a o) := by
    apply assignmentEventMass_congr
    intro d
    constructor
    · rintro ⟨ho, h⟩
      obtain ⟨ha, hl⟩ := (hE d o ho).mp h
      exact ⟨ha, ho, hl⟩
    · rintro ⟨ha, ho, hl⟩
      exact ⟨ho, (hE d o ho).mpr ⟨ha, hl⟩⟩
  rw [he]
  by_cases ha : A o
  · simp only [ha, true_and, ite_eq_left]
    rfl
  · simp [assignmentEventMass, ha]

theorem cappedBoundaryMass_left (p : ι → κ → ℚ) (i j : κ) (hij : i ≠ j) (q : ℕ) :
    cappedBoundaryMass p q i =
      ∑ o, if pairBoundaryAllowed i j o q then pairSliceMass p i j o q else 0 := by
  exact pairSliceMass_partition_event p i j _ _ _
    (fun d o ho => cappedBoundary_pattern_left i j hij d o ho q)

theorem cappedBoundaryMass_right (p : ι → κ → ℚ) (i j : κ) (hij : i ≠ j) (q : ℕ) :
    cappedBoundaryMass p q j = ∑ o, if pairBoundaryAllowed i j o q then
      pairSliceMass p i j o ((pairActive i j o).card-q) else 0 := by
  exact pairSliceMass_partition_event p i j _ _ _
    (fun d o ho => cappedBoundary_pattern_right i j hij d o ho q)

theorem cappedBoundaryMass_ordered (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (i j : κ) (hij : i ≠ j) (horder : ∀ r, p r j ≤ p r i) (q : ℕ) :
    cappedBoundaryMass p q j ≤ cappedBoundaryMass p q i := by
  classical
  rw [cappedBoundaryMass_left p i j hij q, cappedBoundaryMass_right p i j hij q]
  apply Finset.sum_le_sum
  intro o _
  by_cases ha : pairBoundaryAllowed i j o q
  · simp only [ite_eq_left ha]
    exact pairSliceMass_boundary p hp i j hij horder o q ha.2.1 ha.2.2
  · simp only [ite_eq_right ha, le_refl]

def cappedBoundaryProbability (p : ι → κ → ℚ) (q : ℕ) (k : κ) : ℚ :=
  cappedBoundaryMass p q k / assignmentEventMass p (assignmentCapped q)

theorem cappedBoundaryProbability_ordered (p : ι → κ → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (i j : κ) (hij : i ≠ j) (horder : ∀ r, p r j ≤ p r i) (q : ℕ)
    (hcap : 0 < assignmentEventMass p (assignmentCapped q)) :
    cappedBoundaryProbability p q j ≤ cappedBoundaryProbability p q i := by
  exact div_le_div_of_nonneg_right (cappedBoundaryMass_ordered p hp i j hij horder q) hcap.le

end MatchingCapacity
