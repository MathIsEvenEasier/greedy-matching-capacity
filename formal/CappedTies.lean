import AssociationTarget
import MarkedLaw

/-! Distinguished maximal coordinates in the concrete capped factorial law.
This proves the size-bias part of the integer tie argument. It does not yet
identify the law after deleting a pinned coordinate or prove regression of
general Schur-increasing functions in the number of ties. -/

set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def maxMark {b q r : ℕ} (x : CappedLoad b q r) (i : Fin b) : ℚ :=
  if (x.val i).val = q then 1 else 0

def maxCount {b q r : ℕ} (x : CappedLoad b q r) : ℕ :=
  (Finset.univ.filter (fun i => (x.val i).val = q)).card

theorem total_maxMark {b q r : ℕ} (x : CappedLoad b q r) :
    total (maxMark x) = (maxCount x : ℚ) := by
  simp [total, maxMark, maxCount, Finset.sum_boole]

def maximumWeight {b q r : ℕ} (x : CappedLoad b q r) : ℚ :=
  if 0 < maxCount x then cappedWeight x else 0

theorem maximumWeight_nonneg {b q r : ℕ} (x : CappedLoad b q r) :
    0 ≤ maximumWeight x := by
  unfold maximumWeight
  split
  · exact le_of_lt (cappedWeight_pos x)
  · exact le_rfl

theorem marked_maximum_eq_sizeBias {b q r : ℕ} (f : CappedLoad b q r → ℚ) :
    expectation (jointWeight maximumWeight maxMark) (fun x => f x.1) =
      expectation (sizeBias maximumWeight (fun x => (maxCount x : ℚ))) f := by
  simpa only [total_maxMark] using
    expectation_marked_eq_sizeBias (maximumWeight (b := b) (q := q) (r := r)) f maxMark

theorem maximum_count_le_marked {b q r : ℕ} (φ : ℚ → ℚ)
    (hZ : 0 < total (maximumWeight (b := b) (q := q) (r := r)))
    (hφ : Monotone φ) :
    expectation maximumWeight (fun x : CappedLoad b q r => φ (maxCount x : ℚ)) ≤
      expectation (jointWeight maximumWeight maxMark)
        (fun x : CappedLoad b q r × Fin b => φ (maxCount x.1 : ℚ)) := by
  have hl := moment_mono_on_support (maximumWeight (b := b) (q := q) (r := r))
    (fun _ => 1) (fun x => (maxCount x : ℚ)) maximumWeight_nonneg (by
      intro x hx
      have hc : 0 < maxCount x := by
        by_contra hc
        simp [maximumWeight, hc] at hx
      exact_mod_cast (Nat.succ_le_iff.mpr hc))
  have hunit : moment (maximumWeight (b := b) (q := q) (r := r)) (fun _ => 1) =
      total (maximumWeight (b := b) (q := q) (r := r)) := by
    simp only [moment, total, mul_one]
  rw [hunit] at hl
  have hM : 0 < moment (maximumWeight (b := b) (q := q) (r := r))
      (fun x => (maxCount x : ℚ)) := by
    exact lt_of_lt_of_le hZ hl
  have hm : 0 < moment (maximumWeight (b := b) (q := q) (r := r))
      (fun x => total (maxMark x)) := by
    simpa only [total_maxMark] using hM
  simpa only [total_maxMark] using
    expectation_count_le_marked maximumWeight maxMark φ maximumWeight_nonneg hZ hm hφ

end MatchingCapacity
