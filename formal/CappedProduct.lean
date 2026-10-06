import CappedStrata
import PinnedLaw
import Mathlib.Data.List.GetD

/-! Exact representation bridge from recursive product-list moments to the
finite capped-vector law. All weights, fixed totals and normalizing masses
are identified, including zero-mass fibers. Efron then applies to this law. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def boxList {n q : ℕ} (x : Fin n → Fin (q+1)) : List ℕ :=
  List.ofFn (fun i => (x i).val)

def boxWeight {n q : ℕ} (x : Fin n → Fin (q+1)) : ℚ :=
  ∏ i, factorialWeight (x i).val

def boxMoment (n q r : ℕ) (φ : List ℕ → ℚ) : ℚ :=
  ∑ x : Fin n → Fin (q+1), if (∑ i, (x i).val) = r then boxWeight x * φ (boxList x) else 0

def headTailBoxEquiv (n q : ℕ) :
    (Fin (n+1) → Fin (q+1)) ≃ Fin (q+1) × (Fin n → Fin (q+1)) where
  toFun := fun x => (x 0, fun i => x i.succ)
  invFun := fun x => Fin.cons x.1 x.2
  left_inv := by intro x; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by intro x; rfl

theorem boxList_cons {n q : ℕ} (a : Fin (q+1)) (x : Fin n → Fin (q+1)) :
    boxList (Fin.cons a x) = a.val :: boxList x := by
  rw [boxList, List.ofFn_succ]
  rfl

theorem boxWeight_cons {n q : ℕ} (a : Fin (q+1)) (x : Fin n → Fin (q+1)) :
    boxWeight (Fin.cons a x) = factorialWeight a.val * boxWeight x := by
  unfold boxWeight
  rw [Fin.prod_univ_succ]
  rfl

theorem boxMoment_zero (q r : ℕ) (φ : List ℕ → ℚ) :
    boxMoment 0 q r φ = if r = 0 then φ [] else 0 := by
  simp [boxMoment, boxWeight, boxList, eq_comm]

theorem boxMoment_succ (n q r : ℕ) (φ : List ℕ → ℚ) :
    boxMoment (n+1) q r φ = ∑ a : Fin (q+1),
      if a.val ≤ r then factorialWeight a.val * boxMoment n q (r-a.val) (fun xs => φ (a.val::xs)) else 0 := by
  unfold boxMoment
  rw [← (headTailBoxEquiv n q).symm.sum_comp
    (fun x => if (∑ i, (x i).val) = r then boxWeight x * φ (boxList x) else 0)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ x : Fin n → Fin (q+1),
    if (∑ i : Fin (n+1), ((Fin.cons a x : Fin (n+1) → Fin (q+1)) i).val) = r then boxWeight (Fin.cons a x) * φ (boxList (Fin.cons a x)) else 0) = _
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, boxWeight_cons, boxList_cons]
  by_cases ha : a.val ≤ r
  · rw [ite_eq_left ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have he : a.val + (∑ i, (x i).val) = r ↔ (∑ i, (x i).val) = r-a.val := by omega
    simp only [he, mul_ite, mul_zero, mul_assoc]
  · rw [ite_eq_right ha]
    apply Finset.sum_eq_zero
    intro x _
    have he : a.val + (∑ i, (x i).val) ≠ r := by omega
    simp only [ite_eq_right he]

theorem sum_truncated_rectangle (q r : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range (r+1), if i ≤ q then f i else 0) =
      ∑ i ∈ Finset.range (q+1), if i ≤ r then f i else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem productMoment_eq_boxMoment (n q r : ℕ) (φ : List ℕ → ℚ) :
    productMoment ((List.replicate n q).map factorialCarrier) r φ = boxMoment n q r φ := by
  induction n generalizing r φ with
  | zero => simp [productMoment, boxMoment_zero]
  | succ n ih =>
    rw [List.replicate_succ, List.map_cons, productMoment, boxMoment_succ]
    simp_rw [ih]
    change (∑ i ∈ Finset.range (r+1), integerCarrier q i *
      boxMoment n q (r-i) (fun xs => φ (i::xs))) = _
    simp_rw [integerCarrier_nat, cappedCarrier, ite_mul, zero_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      if i ≤ r then factorialWeight i * boxMoment n q (r-i) (fun xs => φ (i::xs)) else 0)]
    exact sum_truncated_rectangle q r (fun i => factorialWeight i * boxMoment n q (r-i) (fun xs => φ (i::xs)))

theorem cappedMoment_eq_boxMoment (n q r : ℕ) (φ : List ℕ → ℚ) :
    moment cappedWeight (fun x : CappedLoad n q r => φ (boxList x.val)) = boxMoment n q r φ := by
  classical
  symm
  unfold boxMoment moment
  apply Finset.sum_congr_set {x : Fin n → Fin (q+1) | (∑ i, (x i).val) = r} _ _
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [ite_eq_left hx]
    rfl
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    exact ite_eq_right hx

theorem productMoment_eq_cappedMoment (n q r : ℕ) (φ : List ℕ → ℚ) :
    productMoment ((List.replicate n q).map factorialCarrier) r φ =
      moment cappedWeight (fun x : CappedLoad n q r => φ (boxList x.val)) := by
  rw [productMoment_eq_boxMoment, cappedMoment_eq_boxMoment]

theorem capped_total_eq_product (n q r : ℕ) :
    total (cappedWeight (b := n) (q := q) (r := r)) =
      (carrierProduct ((List.replicate n q).map factorialCarrier)).weight r := by
  have h := productMoment_eq_cappedMoment n q r (fun _ => 1)
  rw [productMoment_one] at h
  simpa only [moment, total, mul_one] using h.symm

theorem capped_total_pos_iff (n q r : ℕ) :
    0 < total (cappedWeight (b := n) (q := q) (r := r)) ↔ r ≤ n*q := by
  rw [capped_total_eq_product, (carrierProduct _).positive_iff, carrierProduct_cap, totalCap_factorial]
  simp only [List.sum_replicate, smul_eq_mul]
  omega

theorem boxList_getD {n q : ℕ} (x : Fin n → Fin (q+1)) (i : Fin n) :
    (boxList x).getD i.val 0 = (x i).val := by
  rw [List.getD_eq_getElem _ _ (by simpa only [boxList, List.length_ofFn] using i.isLt)]
  simp [boxList]

def cappedMean (n q r : ℕ) (F : (Fin n → ℕ) → ℚ) : ℚ :=
  expectation cappedWeight (fun x : CappedLoad n q r => F (fun i => (x.val i).val))

theorem cappedMean_eq_productMean (n q r : ℕ) (F : (Fin n → ℕ) → ℚ) :
    cappedMean n q r F = productMean ((List.replicate n q).map factorialCarrier) r
      (fun xs => F (fun i => xs.getD i.val 0)) := by
  unfold cappedMean expectation productMean
  rw [productMoment_eq_cappedMoment, capped_total_eq_product]
  congr 1
  unfold moment
  apply Finset.sum_congr rfl
  intro x _
  simp only [boxList_getD]

-- The Efron hypotheses are now stated on the actual capped vector box.
theorem capped_vector_efron (n q s t : ℕ) (hst : s ≤ t) (ht : t ≤ n*q)
    (F : (Fin n → ℕ) → ℚ)
    (hF : ∀ x y, (∀ i, x i ≤ q) → (∀ i, y i ≤ q) →
      s ≤ (∑ i, x i) → (∑ i, y i) ≤ t → (∀ i, x i ≤ y i) → F x ≤ F y) :
    cappedMean n q s F ≤ cappedMean n q t F := by
  rw [cappedMean_eq_productMean, cappedMean_eq_productMean]
  apply capped_efron_band (List.replicate n q) s t hst
    (by simpa only [List.sum_replicate, smul_eq_mul] using ht)
  intro xs ys hx hy hs ht' hxy
  apply hF
  · intro i; exact fitsCaps_getD n q xs hx i.val
  · intro i; exact fitsCaps_getD n q ys hy i.val
  · rwa [sum_getD n xs (by simpa using fitsCaps_length _ _ hx)]
  · rwa [sum_getD n ys (by simpa using fitsCaps_length _ _ hy)]
  · intro i; exact coordLE_getD xs ys hxy i.val

theorem capped_vector_pinned_majorization (n q T a b : ℕ) (hqa : q ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) (hfeasible : T-a ≤ n*q)
    (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : ∀ x y, (∑ i, x i) = T → (∑ i, y i) = T → LoadLE x y → F x ≤ F y) :
    cappedMean n q (T-a) (fun x => F (Fin.cons a x)) ≤
      cappedMean n q (T-b) (fun x => F (Fin.cons b x)) := by
  rw [cappedMean_eq_productMean, cappedMean_eq_productMean]
  exact pinned_efron_majorization n q T a b hqa hab hbT hfeasible F hF

theorem tieStratum_feasible (n q r k : ℕ) :
    0 < tieTotal (n+k) (q+1) ((q+1)*k+r) k ↔ r ≤ n*q := by
  rw [tieStratum_all_mass_pos_iff, capped_total_pos_iff]

theorem capped_pinned_residual_masses_pos (n q T a b : ℕ) (hab : a ≤ b)
    (hfeasible : T-a ≤ n*q) :
    0 < total (cappedWeight (b := n) (q := q) (r := T-a)) ∧
    0 < total (cappedWeight (b := n) (q := q) (r := T-b)) := by
  constructor
  · exact (capped_total_pos_iff n q (T-a)).mpr hfeasible
  · exact (capped_total_pos_iff n q (T-b)).mpr (by omega)

theorem maximum_mass_pos_iff (n q r : ℕ) :
    0 < total (maximumWeight (b := n+1) (q := q) (r := q+r)) ↔ r ≤ n*q := by
  constructor
  · intro h
    exact (capped_total_pos_iff n q r).mp (residual_mass_pos n q r h)
  · intro hr
    have hp := (capped_total_pos_iff n q r).mpr hr
    have he : moment maximumWeight (fun x : CappedLoad (n+1) q (q+r) => (maxCount x : ℚ)) =
        ((n+1 : ℕ) : ℚ) * total (fixedMaximumWeight (b := n+1) (q := q) (r := q+r) 0) := by
      simpa only [moment, total, sizeBias, mul_one] using
        tieBias_moment_eq_fixed (0 : Fin (n+1)) (fun _ : CappedLoad (n+1) q (q+r) => 1) (by intros; rfl)
    rw [fixedMaximum_total_delete] at he
    have hL : 0 < moment maximumWeight (fun x : CappedLoad (n+1) q (q+r) => (maxCount x : ℚ)) := by
      rw [he]
      exact mul_pos (by positivity) (mul_pos (factorialWeight_pos q) hp)
    by_contra hn
    have hz : total (maximumWeight (b := n+1) (q := q) (r := q+r)) = 0 :=
      le_antisymm (le_of_not_gt hn) (total_nonneg _ maximumWeight_nonneg)
    have hm := moment_eq_total_mul_expectation maximumWeight
      (fun x : CappedLoad (n+1) q (q+r) => (maxCount x : ℚ)) maximumWeight_nonneg
    rw [hz, zero_mul] at hm
    rw [hm] at hL
    exact (lt_irrefl 0) hL

end MatchingCapacity
