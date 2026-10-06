import BernoulliCoupling

/-! Coupling an ordered finite time law with zero/one increments.
The last time is a cemetery outcome, where no count comparison is needed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N : ℕ}

def markedTimeMass (w p : Fin (N+1) → ℚ) (z : Fin (N+1) × Bool) : ℚ :=
  w z.1 * bernoulliMass (p z.1) z.2

def timePairMarks (p r : Fin (N+1) → ℚ) (a b : ℕ)
    (i j : Fin (N+1)) (x y : Bool) : ℚ :=
  if a = b ∧ i.val < N ∧ j.val < N then bernoulliJoint (p i) (r j) x y
  else bernoulliMass (p i) x * bernoulliMass (r j) y

def markedTimeJoint (c : Fin (N+1) → Fin (N+1) → ℚ) (p r : Fin (N+1) → ℚ)
    (a b : ℕ) (x y : Fin (N+1) × Bool) : ℚ :=
  c x.1 y.1 * timePairMarks p r a b x.1 y.1 x.2 y.2

theorem timePairMarks_row (p r : Fin (N+1) → ℚ) (a b : ℕ)
    (i j : Fin (N+1)) (x : Bool) :
    (∑ y, timePairMarks p r a b i j x y) = bernoulliMass (p i) x := by
  unfold timePairMarks
  split_ifs
  · exact bernoulliJoint_row _ _ x
  · rw [← Finset.mul_sum, bernoulliMass_probability, mul_one]

theorem timePairMarks_column (p r : Fin (N+1) → ℚ) (a b : ℕ)
    (i j : Fin (N+1)) (y : Bool) :
    (∑ x, timePairMarks p r a b i j x y) = bernoulliMass (r j) y := by
  unfold timePairMarks
  split_ifs
  · exact bernoulliJoint_column _ _ y
  · rw [← Finset.sum_mul, bernoulliMass_probability, one_mul]

theorem markedTimeJoint_row (c : Fin (N+1) → Fin (N+1) → ℚ)
    (w p r : Fin (N+1) → ℚ) (a b : ℕ) (hc : ∀ i, ∑ j, c i j = w i)
    (x : Fin (N+1) × Bool) :
    (∑ y, markedTimeJoint c p r a b x y) = markedTimeMass w p x := by
  simp only [markedTimeJoint, Fintype.sum_prod_type, ← Finset.mul_sum,
    timePairMarks_row, ← Finset.sum_mul, hc, markedTimeMass]

theorem markedTimeJoint_column (c : Fin (N+1) → Fin (N+1) → ℚ)
    (w p r : Fin (N+1) → ℚ) (a b : ℕ) (hc : ∀ j, ∑ i, c i j = w j)
    (y : Fin (N+1) × Bool) :
    (∑ x, markedTimeJoint c p r a b x y) = markedTimeMass w r y := by
  simp only [markedTimeJoint, Fintype.sum_prod_type, ← Finset.mul_sum,
    timePairMarks_column, ← Finset.sum_mul, hc, markedTimeMass]

theorem markedTimeJoint_nonneg (c : Fin (N+1) → Fin (N+1) → ℚ)
    (p r : Fin (N+1) → ℚ) (a b : ℕ) (hc : ∀ i j, 0 ≤ c i j)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hr : ∀ j, 0 ≤ r j ∧ r j ≤ 1)
    (ho : ∀ i j, 0 < c i j → a = b → i.val < N → j.val < N → p i ≤ r j)
    (x y : Fin (N+1) × Bool) : 0 ≤ markedTimeJoint c p r a b x y := by
  unfold markedTimeJoint
  by_cases hz : c x.1 y.1 = 0
  · simp [hz]
  · apply mul_nonneg (hc _ _)
    unfold timePairMarks
    split_ifs with h
    · exact bernoulliJoint_nonneg _ _ (hp x.1).1
        (ho _ _ (lt_of_le_of_ne (hc _ _) (Ne.symm hz)) h.1 h.2.1 h.2.2) (hr y.1).2 _ _
    · exact mul_nonneg (bernoulliMass_nonneg _ (hp x.1).1 (hp x.1).2 _)
        (bernoulliMass_nonneg _ (hr y.1).1 (hr y.1).2 _)

theorem markedTimeJoint_ordered (c : Fin (N+1) → Fin (N+1) → ℚ)
    (p r : Fin (N+1) → ℚ) (a b : ℕ) (hab : a ≤ b)
    (hc : ∀ i j, j < i → c i j = 0) (x y : Fin (N+1) × Bool)
    (hy : y.1.val < N) (hbad : ¬ (x.1 ≤ y.1 ∧ a+x.2.toNat ≤ b+y.2.toNat)) :
    markedTimeJoint c p r a b x y = 0 := by
  by_cases ht : x.1 ≤ y.1
  · have hb : b+y.2.toNat < a+x.2.toNat := by omega
    by_cases he : a = b
    · have hx : x.1.val < N := lt_of_le_of_lt ht hy
      unfold markedTimeJoint timePairMarks
      rw [ite_eq_left ⟨he,hx,hy⟩, bernoulliJoint_ordered _ _ _ _ (by omega), mul_zero]
    · have hh := unequal_counts_stay_ordered a b (by omega) x.2 y.2
      omega
  · simp [markedTimeJoint, hc _ _ (lt_of_not_ge ht)]

theorem coupling_row_positive (c : Fin (N+1) → Fin (N+1) → ℚ)
    (hc : ∀ i j, 0 ≤ c i j) (i j : Fin (N+1)) (hij : 0 < c i j) : 0 < ∑ k, c i k :=
  hij.trans_le (Finset.single_le_sum (fun k _ => hc i k) (Finset.mem_univ j))

theorem coupling_column_positive (c : Fin (N+1) → Fin (N+1) → ℚ)
    (hc : ∀ i j, 0 ≤ c i j) (i j : Fin (N+1)) (hij : 0 < c i j) : 0 < ∑ k, c k j :=
  hij.trans_le (Finset.single_le_sum (fun k _ => hc k j) (Finset.mem_univ i))

end MatchingCapacity
