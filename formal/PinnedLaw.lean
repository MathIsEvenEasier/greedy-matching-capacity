import PinnedMajorization

/-! Exact conditioning on a labelled coordinate in the finite product law.
This does not identify conditioning on the unlabelled maximum: ties remain
an additional probability-law comparison. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def headSlice (k : ℕ) (φ : List ℕ → ℚ) : List ℕ → ℚ
  | [] => 0
  | i :: xs => if i = k then φ xs else 0

theorem productMoment_zero (cs : List FiniteCarrier) (s : ℕ) :
    productMoment cs s (fun _ => 0) = 0 := by
  induction cs generalizing s with
  | nil => simp [productMoment]
  | cons a cs ih => simp only [productMoment, ih, mul_zero, Finset.sum_const_zero]

theorem headSlice_moment (a : FiniteCarrier) (cs : List FiniteCarrier) (T k : ℕ)
    (hkT : k ≤ T) (φ : List ℕ → ℚ) :
    productMoment (a :: cs) T (headSlice k φ) =
      a.weight k * productMoment cs (T-k) φ := by
  change (∑ i ∈ Finset.range (T+1), a.weight i *
    productMoment cs (T-i) (fun xs => headSlice k φ (i::xs))) = _
  rw [Finset.sum_eq_single k]
  · simp [headSlice]
  · intro i _ hik
    simp only [headSlice, ite_eq_right hik, productMoment_zero, mul_zero]
  · intro hk
    exact False.elim (hk (Finset.mem_range.mpr (by omega)))

-- Raw weights are used in both numerator and denominator: the common
-- normalization of the original total-T product law cancels.
def pinnedMean (a : FiniteCarrier) (cs : List FiniteCarrier) (T k : ℕ)
    (φ : List ℕ → ℚ) : ℚ :=
  productMoment (a :: cs) T (headSlice k φ) /
    productMoment (a :: cs) T (headSlice k (fun _ => 1))

theorem pinnedMean_eq_normalized (a : FiniteCarrier) (cs : List FiniteCarrier) (T k : ℕ)
    (hT : T ≤ totalCap (a :: cs)) (φ : List ℕ → ℚ) :
    pinnedMean a cs T k φ =
      productMean (a :: cs) T (headSlice k φ) /
        productMean (a :: cs) T (headSlice k (fun _ => 1)) := by
  have hZ : 0 < (carrierProduct (a :: cs)).weight T := by
    apply ((carrierProduct (a :: cs)).positive_iff _).mpr
    rw [carrierProduct_cap]
    omega
  unfold pinnedMean productMean
  exact (div_div_div_cancel_right₀ (ne_of_gt hZ) _ _).symm

theorem headSlice_mass_pos (a : FiniteCarrier) (cs : List FiniteCarrier) (T k : ℕ)
    (hk : k ≤ a.cap) (hkT : k ≤ T) (hrest : T-k ≤ totalCap cs) :
    0 < productMoment (a :: cs) T (headSlice k (fun _ => 1)) := by
  rw [headSlice_moment a cs T k hkT, productMoment_one]
  apply mul_pos
  · exact (a.positive_iff k).mpr (by omega)
  · apply ((carrierProduct cs).positive_iff _).mpr
    rw [carrierProduct_cap]
    omega

theorem pinnedMean_eq (a : FiniteCarrier) (cs : List FiniteCarrier) (T k : ℕ)
    (hk : k ≤ a.cap) (hkT : k ≤ T) (φ : List ℕ → ℚ) :
    pinnedMean a cs T k φ = productMean cs (T-k) φ := by
  have ha : a.weight k ≠ 0 := ne_of_gt ((a.positive_iff k).mpr (by omega))
  unfold pinnedMean
  rw [headSlice_moment a cs T k hkT, headSlice_moment a cs T k hkT, productMoment_one]
  exact mul_div_mul_left _ _ ha

theorem labelled_maximum_conditioning_pos (n q T a b : ℕ) (hab : a ≤ b)
    (hbT : b ≤ T) (hfeasible : T-a ≤ n*q) :
    0 < productMoment (factorialCarrier b :: (List.replicate n q).map factorialCarrier) T
        (headSlice a (fun _ => 1)) ∧
    0 < productMoment (factorialCarrier b :: (List.replicate n q).map factorialCarrier) T
        (headSlice b (fun _ => 1)) := by
  constructor
  · apply headSlice_mass_pos _ _ T a hab (by omega)
    simpa only [totalCap_factorial, List.sum_replicate, smul_eq_mul] using hfeasible
  · apply headSlice_mass_pos _ _ T b le_rfl hbT
    have hb : T-b ≤ n*q := by omega
    simpa only [totalCap_factorial, List.sum_replicate, smul_eq_mul] using hb

-- All comparisons refer to the same initial product carrier, with first
-- cap b and every residual cap q. Only the value of the first coordinate
-- being conditioned on changes.
theorem labelled_maximum_regression (n q T a b : ℕ) (hqa : q ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) (hfeasible : T-a ≤ n*q)
    (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : ∀ x y, (∑ i, x i) = T → (∑ i, y i) = T → LoadLE x y → F x ≤ F y) :
    pinnedMean (factorialCarrier b) ((List.replicate n q).map factorialCarrier) T a
      (fun xs => F (Fin.cons a (fun i => xs.getD i.val 0))) ≤
    pinnedMean (factorialCarrier b) ((List.replicate n q).map factorialCarrier) T b
      (fun xs => F (Fin.cons b (fun i => xs.getD i.val 0))) := by
  rw [pinnedMean_eq _ _ T a hab (by omega), pinnedMean_eq _ _ T b le_rfl hbT]
  exact pinned_efron_majorization n q T a b hqa hab hbT hfeasible F hF

end MatchingCapacity
