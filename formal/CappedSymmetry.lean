import CappedTies

/-! Coordinate exchangeability of the concrete capped factorial law.
A fixed labelled maximum is exactly the maximum law biased by its tie
count, for every permutation-invariant observable. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def permuteCapped {b q r : ℕ} (e : Equiv.Perm (Fin b)) (x : CappedLoad b q r) :
    CappedLoad b q r :=
  ⟨fun i => x.val (e i), (Equiv.sum_comp e (fun i => (x.val i).val)).trans x.property⟩

def cappedPermEquiv {b q r : ℕ} (e : Equiv.Perm (Fin b)) :
    CappedLoad b q r ≃ CappedLoad b q r where
  toFun := permuteCapped e
  invFun := permuteCapped e.symm
  left_inv := by intro x; apply Subtype.ext; funext i; simp [permuteCapped]
  right_inv := by intro x; apply Subtype.ext; funext i; simp [permuteCapped]

theorem cappedWeight_permute {b q r : ℕ} (e : Equiv.Perm (Fin b)) (x : CappedLoad b q r) :
    cappedWeight (permuteCapped e x) = cappedWeight x := by
  exact Equiv.prod_comp e (fun i => factorialWeight (x.val i).val)

theorem maxCount_permute {b q r : ℕ} (e : Equiv.Perm (Fin b)) (x : CappedLoad b q r) :
    maxCount (permuteCapped e x) = maxCount x := by
  have h : (maxCount (permuteCapped e x) : ℚ) = (maxCount x : ℚ) := by
    rw [← total_maxMark (permuteCapped e x), ← total_maxMark x]
    exact Equiv.sum_comp e (fun i => maxMark x i)
  exact_mod_cast h

theorem loadLE_reindex {b : ℕ} (x : Fin b → ℕ) (e : Equiv.Perm (Fin b)) :
    LoadLE (fun i => x (e i)) x := by
  intro s
  refine ⟨s.map e.toEmbedding, by simp, ?_⟩
  simp [Finset.sum_map]

theorem capped_increasing_symmetric {b q r : ℕ} (F : CappedLoad b q r → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y)
    (e : Equiv.Perm (Fin b)) (x : CappedLoad b q r) : F (permuteCapped e x) = F x := by
  apply le_antisymm
  · apply hF
    simpa only [permuteCapped] using loadLE_reindex (fun i => (x.val i).val) e
  · apply hF
    have h := loadLE_reindex (fun i => (x.val (e i)).val) e.symm
    simpa only [permuteCapped, Equiv.apply_symm_apply] using h

def fixedMaximumWeight {b q r : ℕ} (j : Fin b) (x : CappedLoad b q r) : ℚ :=
  cappedWeight x * maxMark x j

theorem maxCount_pos_of_mark {b q r : ℕ} (x : CappedLoad b q r) (j : Fin b)
    (hj : (x.val j).val = q) : 0 < maxCount x := by
  apply Finset.card_pos.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩

theorem maximum_mark_eq_fixed {b q r : ℕ} (x : CappedLoad b q r) (j : Fin b) :
    maximumWeight x * maxMark x j = fixedMaximumWeight j x := by
  by_cases hj : (x.val j).val = q
  · simp [fixedMaximumWeight, maximumWeight, maxMark, hj, maxCount_pos_of_mark x j hj]
  · simp [fixedMaximumWeight, maxMark, hj]

theorem fixedMaximum_moment_eq {b q r : ℕ} (i j : Fin b) (F : CappedLoad b q r → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    moment (fixedMaximumWeight i) F = moment (fixedMaximumWeight j) F := by
  classical
  let e := Equiv.swap i j
  have h := (cappedPermEquiv (q := q) (r := r) e).sum_comp
    (fun x => fixedMaximumWeight i x * F x)
  unfold moment
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  change cappedWeight (permuteCapped e x) * maxMark (permuteCapped e x) i *
    F (permuteCapped e x) = _
  rw [cappedWeight_permute, hF]
  simp [fixedMaximumWeight, maxMark, permuteCapped, e]

theorem tieBias_moment_eq_fixed {b q r : ℕ} (j : Fin b) (F : CappedLoad b q r → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    moment (sizeBias maximumWeight (fun x : CappedLoad b q r => (maxCount x : ℚ))) F =
      (b : ℚ) * moment (fixedMaximumWeight j) F := by
  have hm := marking_moment (maximumWeight (b := b) (q := q) (r := r)) F maxMark
  simp only [total_maxMark] at hm
  rw [← hm]
  unfold moment jointWeight
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [maximum_mark_eq_fixed]
  change (∑ i : Fin b, moment (fixedMaximumWeight i) F) = _
  simp_rw [fixedMaximum_moment_eq _ j F hF]
  simp [moment]

theorem fixedMaximum_expectation_eq_tieBias {b q r : ℕ} (j : Fin b) (F : CappedLoad b q r → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    expectation (fixedMaximumWeight j) F =
      expectation (sizeBias maximumWeight (fun x : CappedLoad b q r => (maxCount x : ℚ))) F := by
  have hb : (b : ℚ) ≠ 0 := by have hj := j.isLt; exact_mod_cast (show b ≠ 0 by omega)
  have hZ : total (sizeBias maximumWeight (fun x : CappedLoad b q r => (maxCount x : ℚ))) =
      (b : ℚ) * total (fixedMaximumWeight (q := q) (r := r) j) := by
    simpa only [moment, total, mul_one] using tieBias_moment_eq_fixed j (fun _ : CappedLoad b q r => 1) (by intros; rfl)
  unfold expectation
  rw [tieBias_moment_eq_fixed j F hF, hZ, mul_div_mul_left _ _ hb]

end MatchingCapacity
