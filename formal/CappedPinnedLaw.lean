import CappedSymmetry

/-! Deleting a labelled maximal coordinate in CappedLoad gives the exact
lower-dimensional capped factorial law, including its normalizing mass. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def prependCapped {n q r : ℕ} (x : CappedLoad n q r) : CappedLoad (n+1) q (q+r) :=
  ⟨Fin.cons ⟨q, by omega⟩ x.val, by
    rw [Fin.sum_univ_succ]
    simpa only [Fin.cons_zero, Fin.cons_succ] using congrArg (q + ·) x.property⟩

abbrev HeadMaxLoad (n q r : ℕ) :=
  {x : CappedLoad (n+1) q (q+r) // (x.val 0).val = q}

def deleteHeadMax {n q r : ℕ} (x : HeadMaxLoad n q r) : CappedLoad n q r :=
  ⟨fun i => x.val.val i.succ, by
    have h := x.val.property
    rw [Fin.sum_univ_succ, x.property] at h
    exact Nat.add_left_cancel h⟩

def headMaxEquiv (n q r : ℕ) : CappedLoad n q r ≃ HeadMaxLoad n q r where
  toFun := fun x => ⟨prependCapped x, rfl⟩
  invFun := deleteHeadMax
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    apply Fin.ext
    exact x.property.symm

theorem cappedWeight_prepend {n q r : ℕ} (x : CappedLoad n q r) :
    cappedWeight (prependCapped x) = factorialWeight q * cappedWeight x := by
  unfold cappedWeight
  rw [Fin.prod_univ_succ]
  rfl

theorem maxCount_prepend {n q r : ℕ} (x : CappedLoad n q r) :
    maxCount (prependCapped x) = 1 + maxCount x := by
  have h : (maxCount (prependCapped x) : ℚ) = 1 + (maxCount x : ℚ) := by
    rw [← total_maxMark (prependCapped x), ← total_maxMark x]
    unfold total
    rw [Fin.sum_univ_succ]
    simp [maxMark, prependCapped]
  exact_mod_cast h

theorem fixedMaximum_moment_delete (n q r : ℕ) (F : CappedLoad (n+1) q (q+r) → ℚ) :
    moment (fixedMaximumWeight (0 : Fin (n+1))) F =
      factorialWeight q * moment cappedWeight (fun x : CappedLoad n q r => F (prependCapped x)) := by
  classical
  have hs : moment (fixedMaximumWeight (0 : Fin (n+1))) F =
      ∑ x : HeadMaxLoad n q r, cappedWeight x.val * F x.val := by
    apply Finset.sum_congr_set {x : CappedLoad (n+1) q (q+r) | (x.val 0).val = q} _ _
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      simp [fixedMaximumWeight, maxMark, hx]
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      simp [fixedMaximumWeight, maxMark, hx]
  rw [hs, ← (headMaxEquiv n q r).sum_comp (fun x => cappedWeight x.val * F x.val)]
  change (∑ x : CappedLoad n q r, cappedWeight (prependCapped x) * F (prependCapped x)) = _
  simp_rw [cappedWeight_prepend, mul_assoc]
  rw [← Finset.mul_sum]
  rfl

theorem fixedMaximum_total_delete (n q r : ℕ) :
    total (fixedMaximumWeight (b := n+1) (q := q) (r := q+r) 0) =
      factorialWeight q * total (cappedWeight (b := n) (q := q) (r := r)) := by
  simpa only [moment, total, mul_one] using fixedMaximum_moment_delete n q r (fun _ => 1)

theorem fixedMaximum_expectation_delete (n q r : ℕ) (F : CappedLoad (n+1) q (q+r) → ℚ) :
    expectation (fixedMaximumWeight (0 : Fin (n+1))) F =
      expectation cappedWeight (fun x : CappedLoad n q r => F (prependCapped x)) := by
  unfold expectation
  rw [fixedMaximum_moment_delete, fixedMaximum_total_delete,
    mul_div_mul_left _ _ (ne_of_gt (factorialWeight_pos q))]

theorem tieBias_expectation_delete (n q r : ℕ) (F : CappedLoad (n+1) q (q+r) → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    expectation (sizeBias maximumWeight (fun x : CappedLoad (n+1) q (q+r) => (maxCount x : ℚ))) F =
      expectation cappedWeight (fun x : CappedLoad n q r => F (prependCapped x)) := by
  rw [← fixedMaximum_expectation_eq_tieBias 0 F hF]
  exact fixedMaximum_expectation_delete n q r F

end MatchingCapacity
