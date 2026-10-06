import CappedPinnedLaw
import FiberRegression

/-! The concrete maximum-to-residual comparison corresponding to the
finite capped form of Cohen--Sackrowitz Lemma 5.2. The tie-regression
premise is explicit and remains to be proved by the simultaneous induction. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def maxClass {b q r : ℕ} (x : CappedLoad b q r) : Fin (b+1) :=
  ⟨maxCount x, by
    have h := Finset.card_le_card (Finset.filter_subset (fun i => (x.val i).val = q) Finset.univ)
    have hb : maxCount x ≤ b := by simpa only [maxCount, Finset.card_univ, Fintype.card_fin] using h
    omega⟩

def maximumFiberWeight (b q r : ℕ) (k : Fin (b+1)) : CappedLoad b q r → ℚ :=
  fiberWeight maximumWeight maxClass k

theorem maximum_tie_mass_pos {b q r : ℕ}
    (hZ : 0 < total (maximumWeight (b := b) (q := q) (r := r))) :
    0 < moment maximumWeight (fun x : CappedLoad b q r => (maxCount x : ℚ)) := by
  have h := moment_mono_on_support (maximumWeight (b := b) (q := q) (r := r))
    (fun _ => 1) (fun x => (maxCount x : ℚ)) maximumWeight_nonneg (by
      intro x hx
      have hc : 0 < maxCount x := by
        by_contra hc
        simp [maximumWeight, hc] at hx
      exact_mod_cast (Nat.succ_le_iff.mpr hc))
  have he : moment (maximumWeight (b := b) (q := q) (r := r)) (fun _ => 1) = total (maximumWeight (b := b) (q := q) (r := r)) := by
    simp only [moment, total, mul_one]
  rw [he] at h
  exact hZ.trans_le h

theorem maximum_expectation_le_tieBias {b q r : ℕ} (F : CappedLoad b q r → ℚ)
    (hZ : 0 < total (maximumWeight (b := b) (q := q) (r := r)))
    (hreg : ∀ i j : Fin (b+1),
      0 < total (maximumFiberWeight b q r i) →
      0 < total (maximumFiberWeight b q r j) → i ≤ j →
      expectation (maximumFiberWeight b q r i) F ≤
      expectation (maximumFiberWeight b q r j) F) :
    expectation maximumWeight F ≤
      expectation (sizeBias maximumWeight (fun x : CappedLoad b q r => (maxCount x : ℚ))) F := by
  exact expectation_le_bias_of_regression maximumWeight F maxClass (fun k => (k.val : ℚ))
    maximumWeight_nonneg hZ (maximum_tie_mass_pos hZ)
    (by intro i j hij
        change (i.val : ℚ) ≤ (j.val : ℚ)
        exact Nat.cast_le.mpr hij) hreg

-- This stochastic tie-count comparison has no tie-regression premise.
theorem maximum_count_le_residual (n q r : ℕ) (φ : ℚ → ℚ) (hφ : Monotone φ)
    (hZ : 0 < total (maximumWeight (b := n+1) (q := q) (r := q+r))) :
    expectation maximumWeight (fun x : CappedLoad (n+1) q (q+r) => φ (maxCount x : ℚ)) ≤
      expectation cappedWeight (fun x : CappedLoad n q r => φ (1 + (maxCount x : ℚ))) := by
  let F := fun x : CappedLoad (n+1) q (q+r) => φ (maxCount x : ℚ)
  have h := maximum_count_le_marked φ hZ hφ
  change expectation maximumWeight F ≤
    expectation (jointWeight maximumWeight maxMark) (fun x => F x.1) at h
  have hF : ∀ e x, F (permuteCapped e x) = F x := by
    intro e x
    dsimp [F]
    rw [maxCount_permute]
  rw [marked_maximum_eq_sizeBias F, tieBias_expectation_delete n q r F hF] at h
  simpa only [F, maxCount_prepend, Nat.cast_add, Nat.cast_one] using h

theorem maximum_expectation_le_residual (n q r : ℕ) (F : CappedLoad (n+1) q (q+r) → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y)
    (hZ : 0 < total (maximumWeight (b := n+1) (q := q) (r := q+r)))
    (hreg : ∀ i j : Fin (n+2),
      0 < total (maximumFiberWeight (n+1) q (q+r) i) →
      0 < total (maximumFiberWeight (n+1) q (q+r) j) → i ≤ j →
      expectation (maximumFiberWeight (n+1) q (q+r) i) F ≤
      expectation (maximumFiberWeight (n+1) q (q+r) j) F) :
    expectation maximumWeight F ≤
      expectation cappedWeight (fun x : CappedLoad n q r => F (prependCapped x)) := by
  have h := maximum_expectation_le_tieBias F hZ hreg
  rwa [tieBias_expectation_delete n q r F (capped_increasing_symmetric F hF)] at h

-- The same premise implies that the residual distribution has positive
-- total mass; deletion is not conditioning on an impossible event.
theorem residual_mass_pos (n q r : ℕ)
    (hZ : 0 < total (maximumWeight (b := n+1) (q := q) (r := q+r))) :
    0 < total (cappedWeight (b := n) (q := q) (r := r)) := by
  have hL := maximum_tie_mass_pos hZ
  have ht : moment maximumWeight (fun x : CappedLoad (n+1) q (q+r) => (maxCount x : ℚ)) =
      ((n+1 : ℕ) : ℚ) * total (fixedMaximumWeight (b := n+1) (q := q) (r := q+r) 0) := by
    simpa only [moment, total, sizeBias, mul_one] using
      tieBias_moment_eq_fixed (0 : Fin (n+1)) (fun _ : CappedLoad (n+1) q (q+r) => 1) (by intros; rfl)
  rw [ht, fixedMaximum_total_delete] at hL
  have hnonneg := total_nonneg (cappedWeight (b := n) (q := q) (r := r)) (fun x => le_of_lt (cappedWeight_pos x))
  by_contra hn
  have hz : total (cappedWeight (b := n) (q := q) (r := r)) = 0 := le_antisymm (le_of_not_gt hn) hnonneg
  rw [hz, mul_zero, mul_zero] at hL
  exact (lt_irrefl 0) hL

end MatchingCapacity
