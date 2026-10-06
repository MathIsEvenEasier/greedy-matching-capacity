import ProductEfron

/-! Efron monotonicity for observables increasing only on the relevant
bounded sum band. The extension and support identities are proved. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def FitsCaps : List ℕ → List ℕ → Prop
  | [], [] => True
  | q :: qs, x :: xs => x ≤ q ∧ FitsCaps qs xs
  | _, _ => False

def capBox : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | q :: qs => (Finset.range (q+1)).biUnion (fun x => (capBox qs).image (List.cons x))

theorem mem_capBox (qs xs : List ℕ) : xs ∈ capBox qs ↔ FitsCaps qs xs := by
  induction qs generalizing xs with
  | nil => cases xs <;> simp [capBox, FitsCaps]
  | cons q qs ih =>
    cases xs with
    | nil => simp [capBox, FitsCaps]
    | cons x xs => simp [capBox, FitsCaps, ih]

def clampCaps : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _q :: qs, [] => 0 :: clampCaps qs []
  | q :: qs, x :: xs => min x q :: clampCaps qs xs

theorem clampCaps_fits (qs xs : List ℕ) : FitsCaps qs (clampCaps qs xs) := by
  induction qs generalizing xs with
  | nil => trivial
  | cons q qs ih => cases xs <;> exact ⟨by omega, ih _⟩

theorem clampCaps_eq (qs xs : List ℕ) (h : FitsCaps qs xs) : clampCaps qs xs = xs := by
  induction qs generalizing xs with
  | nil => cases xs <;> simp_all [FitsCaps, clampCaps]
  | cons q qs ih => cases xs <;> simp_all [FitsCaps, clampCaps]

theorem clampCaps_mono (qs xs ys : List ℕ) (h : CoordLE xs ys) :
    CoordLE (clampCaps qs xs) (clampCaps qs ys) := by
  induction qs generalizing xs ys with
  | nil => trivial
  | cons q qs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => exact ⟨le_rfl, ih [] [] trivial⟩
      | cons y ys => exact False.elim h
    | cons x xs =>
      cases ys with
      | nil => exact False.elim h
      | cons y ys => exact ⟨min_le_min h.1 le_rfl, ih _ _ h.2⟩

theorem coordLE_sum (xs ys : List ℕ) (h : CoordLE xs ys) : xs.sum ≤ ys.sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim h
    | cons y ys => exact Nat.add_le_add h.1 (ih ys h.2)

theorem fitsCaps_length (qs xs : List ℕ) (h : FitsCaps qs xs) : xs.length = qs.length := by
  induction qs generalizing xs with
  | nil => cases xs <;> simp_all [FitsCaps]
  | cons q qs ih => cases xs <;> simp_all [FitsCaps]

theorem fitsCaps_sum (qs xs : List ℕ) (h : FitsCaps qs xs) : xs.sum ≤ qs.sum := by
  induction qs generalizing xs with
  | nil => cases xs <;> simp_all [FitsCaps]
  | cons q qs ih =>
    cases xs with
    | nil => exact False.elim h
    | cons x xs => exact Nat.add_le_add h.1 (ih xs h.2)

def boxBound (qs : List ℕ) (φ : List ℕ → ℚ) : ℚ := ∑ xs ∈ capBox qs, |φ xs|

theorem boxBound_nonneg (qs : List ℕ) (φ : List ℕ → ℚ) : 0 ≤ boxBound qs φ :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem boxBound_bounds (qs xs : List ℕ) (φ : List ℕ → ℚ) (h : FitsCaps qs xs) :
    -boxBound qs φ ≤ φ xs ∧ φ xs ≤ boxBound qs φ := by
  have ha : |φ xs| ≤ boxBound qs φ :=
    Finset.single_le_sum (fun y _ => abs_nonneg (φ y)) ((mem_capBox qs xs).mpr h)
  exact abs_le.mp ha

def bandValue (s t : ℕ) (B : ℚ) (φ : List ℕ → ℚ) (xs : List ℕ) : ℚ :=
  if xs.sum < s then -B else if t < xs.sum then B else φ xs

theorem bandValue_eq (s t : ℕ) (B : ℚ) (φ : List ℕ → ℚ) (xs : List ℕ)
    (hs : s ≤ xs.sum) (ht : xs.sum ≤ t) : bandValue s t B φ xs = φ xs := by
  simp [bandValue, not_lt.mpr hs, not_lt.mpr ht]

theorem bandValue_mono (qs : List ℕ) (s t : ℕ) (φ : List ℕ → ℚ)
    (hφ : ∀ xs ys, FitsCaps qs xs → FitsCaps qs ys → s ≤ xs.sum → ys.sum ≤ t →
      CoordLE xs ys → φ xs ≤ φ ys)
    (xs ys : List ℕ) (hx : FitsCaps qs xs) (hy : FitsCaps qs ys) (hxy : CoordLE xs ys) :
    bandValue s t (boxBound qs φ) φ xs ≤ bandValue s t (boxBound qs φ) φ ys := by
  have hs := coordLE_sum xs ys hxy
  have hB := boxBound_nonneg qs φ
  have bx := boxBound_bounds qs xs φ hx
  have by' := boxBound_bounds qs ys φ hy
  unfold bandValue
  by_cases hxl : xs.sum < s
  · rw [ite_eq_left hxl]
    by_cases hyl : ys.sum < s
    · rw [ite_eq_left hyl]
    · rw [ite_eq_right hyl]
      by_cases hyh : t < ys.sum
      · rw [ite_eq_left hyh]; linarith
      · rw [ite_eq_right hyh]; exact by'.1
  · rw [ite_eq_right hxl]
    have hyl : ¬ ys.sum < s := by omega
    rw [ite_eq_right hyl]
    by_cases hxh : t < xs.sum
    · have hyh : t < ys.sum := by omega
      rw [ite_eq_left hxh, ite_eq_left hyh]
    · rw [ite_eq_right hxh]
      by_cases hyh : t < ys.sum
      · rw [ite_eq_left hyh]; exact bx.2
      · rw [ite_eq_right hyh]; exact hφ xs ys hx hy (by omega) (by omega) hxy

theorem cappedMoment_congr (qs : List ℕ) (s : ℕ) (φ ψ : List ℕ → ℚ)
    (h : ∀ xs, FitsCaps qs xs → xs.sum = s → φ xs = ψ xs) :
    productMoment (qs.map factorialCarrier) s φ = productMoment (qs.map factorialCarrier) s ψ := by
  induction qs generalizing s φ ψ with
  | nil =>
    by_cases hs : s = 0
    · subst s; exact h [] trivial rfl
    · simp [productMoment, hs]
  | cons q qs ih =>
    change (∑ i ∈ Finset.range (s+1), (factorialCarrier q).weight i *
      productMoment (qs.map factorialCarrier) (s-i) (fun xs => φ (i::xs))) = _
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases hq : i ≤ q
    · rw [ih (s-i) (fun xs => φ (i::xs)) (fun xs => ψ (i::xs)) (by
        intro xs hx hs
        exact h (i::xs) ⟨hq,hx⟩ (by simp only [List.sum_cons]; omega))]
    · have hz : (factorialCarrier q).weight i = 0 :=
        (factorialCarrier q).zero_outside i (by change ¬ (0 ≤ (i:ℤ) ∧ (i:ℤ) ≤ q); omega)
      rw [hz, zero_mul, zero_mul]

theorem productMoment_neg (cs : List FiniteCarrier) (s : ℕ) (φ : List ℕ → ℚ) :
    productMoment cs s (fun xs => -φ xs) = -productMoment cs s φ := by
  induction cs generalizing s φ with
  | nil => simp only [productMoment]; split <;> simp
  | cons a cs ih => simp only [productMoment, ih, mul_neg, Finset.sum_neg_distrib]

theorem productMean_neg (cs : List FiniteCarrier) (s : ℕ) (φ : List ℕ → ℚ) :
    productMean cs s (fun xs => -φ xs) = -productMean cs s φ := by
  simp only [productMean, productMoment_neg, neg_div]

theorem capped_efron_band (qs : List ℕ) (s t : ℕ) (hst : s ≤ t) (ht : t ≤ qs.sum)
    (φ : List ℕ → ℚ)
    (hφ : ∀ xs ys, FitsCaps qs xs → FitsCaps qs ys → s ≤ xs.sum → ys.sum ≤ t →
      CoordLE xs ys → φ xs ≤ φ ys) :
    productMean (qs.map factorialCarrier) s φ ≤ productMean (qs.map factorialCarrier) t φ := by
  let ψ := fun xs => bandValue s t (boxBound qs φ) φ (clampCaps qs xs)
  have hp : CoordinateIncreasing ψ := by
    intro xs ys hxy
    exact bandValue_mono qs s t φ hφ _ _ (clampCaps_fits qs xs)
      (clampCaps_fits qs ys) (clampCaps_mono qs xs ys hxy)
  have he : ∀ u, s ≤ u → u ≤ t → productMean (qs.map factorialCarrier) u ψ =
      productMean (qs.map factorialCarrier) u φ := by
    intro u hsu hut
    unfold productMean
    congr 1
    apply cappedMoment_congr
    intro xs hx hs
    dsimp [ψ]
    rw [clampCaps_eq qs xs hx, bandValue_eq s t _ φ xs (by omega) (by omega)]
  have h := capped_product_efron qs s t hst ht ψ hp
  rwa [he s le_rfl hst, he t hst le_rfl] at h

theorem capped_efron_band_antitone (qs : List ℕ) (s t : ℕ) (hst : s ≤ t) (ht : t ≤ qs.sum)
    (φ : List ℕ → ℚ)
    (hφ : ∀ xs ys, FitsCaps qs xs → FitsCaps qs ys → s ≤ xs.sum → ys.sum ≤ t →
      CoordLE xs ys → φ ys ≤ φ xs) :
    productMean (qs.map factorialCarrier) t φ ≤ productMean (qs.map factorialCarrier) s φ := by
  have h := capped_efron_band qs s t hst ht (fun xs => -φ xs) (by
    intro xs ys hx hy hs ht hxy
    exact neg_le_neg (hφ xs ys hx hy hs ht hxy))
  simpa only [productMean_neg, neg_le_neg_iff] using h

end MatchingCapacity
