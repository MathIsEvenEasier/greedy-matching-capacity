import CappedCapRegression

/-! Capped factorial association, for every dimension, cap and total.
Induction is on the common cap. Conditional tie strata reduce to the
strictly smaller cap, and the same lower-cap association proves their
regression through pinning and Efron. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem tieMean_covariance_of_lower_association (q : ℕ)
    (hA : ∀ b T, CappedAssociation b q T)
    (k b T : ℕ) (F G : (Fin b → ℕ) → ℚ) (hF : SchurIncreasing F) (hG : SchurIncreasing G)
    (hk : 0 < tieTotal b (q+1) T k) :
    tieMean b (q+1) T k F * tieMean b (q+1) T k G ≤
      tieMean b (q+1) T k (fun x => F x*G x) := by
  induction k generalizing b T with
  | zero =>
    rw [tieMean_zero, tieMean_zero, tieMean_zero]
    have hc := hA b T (fun x => F (fun i => (x.val i).val))
      (fun x => G (fun i => (x.val i).val))
      (by intro x y h; exact hF _ _ h) (by intro x y h; exact hG _ _ h)
    have hZ : 0 < total (cappedWeight (b := b) (q := q) (r := T)) := by
      change 0 < total (tieWeight (b := b) (q := q+1) (r := T) 0) at hk
      rwa [zeroTie_total_lowerCap] at hk
    exact (covariance_iff_mean _ _ _ (fun x => le_of_lt (cappedWeight_pos x)) hZ).mp hc
  | succ k ih =>
    obtain ⟨hb, ht⟩ := tieTotal_pos_bounds b (q+1) T (k+1) hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have hqT : q+1 ≤ T := by nlinarith
    have hT : T = q+1+(T-(q+1)) := by omega
    rw [hT] at hk ⊢
    rw [tieMean_succ n (q+1) (T-(q+1)) k F hF,
      tieMean_succ n (q+1) (T-(q+1)) k G hG,
      tieMean_succ_symmetric n (q+1) (T-(q+1)) k (fun x => F x*G x)
        (by intro e x; rw [schur_symmetric F hF, schur_symmetric G hG])]
    exact ih n (T-(q+1)) (fun x => F (Fin.cons (q+1) x))
      (fun x => G (Fin.cons (q+1) x)) (schur_cons _ F hF) (schur_cons _ G hG)
      ((tieStratum_mass_pos_iff n (q+1) (T-(q+1)) k).mp hk)

theorem cappedFiber_eq_tieWeight (b q T : ℕ) (k : Fin (b+1)) :
    fiberWeight (cappedWeight (b := b) (q := q) (r := T)) maxClass k = tieWeight k.val := by
  funext x
  simp only [fiberWeight, tieWeight, maxClass, Fin.ext_iff]

theorem cappedAssociation_succ_ambient (q : ℕ) (hA : ∀ b T, CappedAssociation b q T)
    (b T : ℕ) (F G : (Fin b → ℕ) → ℚ) (hF : SchurIncreasing F) (hG : SchurIncreasing G) :
    CovNonneg (cappedWeight (b := b) (q := q+1) (r := T))
      (fun x => F (fun i => (x.val i).val)) (fun x => G (fun i => (x.val i).val)) := by
  apply covariance_of_fiber_association _ _ _ maxClass (fun x => le_of_lt (cappedWeight_pos x))
  · intro k hk
    rw [cappedFiber_eq_tieWeight] at hk ⊢
    exact (covariance_iff_mean _ _ _ (tieWeight_nonneg k.val) hk).mpr
      (tieMean_covariance_of_lower_association q hA k.val b T F G hF hG hk)
  · intro i j hi hj
    simp only [cappedFiber_eq_tieWeight] at hi hj ⊢
    rcases le_total i j with hij | hji
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (tieMean_regression_of_lower_association q hA b T F hF i.val j.val hi hj hij))
        (sub_nonpos.mpr (tieMean_regression_of_lower_association q hA b T G hG i.val j.val hi hj hij))
    · exact mul_nonneg
        (sub_nonneg.mpr (tieMean_regression_of_lower_association q hA b T F hF j.val i.val hj hi hji))
        (sub_nonneg.mpr (tieMean_regression_of_lower_association q hA b T G hG j.val i.val hj hi hji))

theorem cappedAssociation_succ (q : ℕ) (hA : ∀ b T, CappedAssociation b q T)
    (b T : ℕ) : CappedAssociation b (q+1) T := by
  intro F G hF hG
  have h := cappedAssociation_succ_ambient q hA b T
    (schurExtension F) (schurExtension G) (schurExtension_mono F) (schurExtension_mono G)
  simpa only [schurExtension_eq F hF, schurExtension_eq G hG] using h

theorem cappedAssociation_zero (b T : ℕ) : CappedAssociation b 0 T := by
  intro F G _ _
  apply covariance_of_pairwise _ F G (fun x => le_of_lt (cappedWeight_pos x))
  intro x y
  have he : x = y := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hx := (x.val i).isLt
    have hy := (y.val i).isLt
    omega
  subst y
  simp

-- No association, regression or feasibility premise remains in this theorem.
theorem cappedAssociation_all (b q T : ℕ) : CappedAssociation b q T := by
  induction q generalizing b T with
  | zero => exact cappedAssociation_zero b T
  | succ q ih => exact cappedAssociation_succ q ih b T

theorem capped_tie_regression (b q T k l : ℕ) (F : (Fin b → ℕ) → ℚ)
    (hF : SchurIncreasing F) (hk : 0 < tieTotal b (q+1) T k)
    (hl : 0 < tieTotal b (q+1) T l) (hkl : k ≤ l) :
    tieMean b (q+1) T k F ≤ tieMean b (q+1) T l F :=
  tieMean_regression_of_lower_association q (fun n r => cappedAssociation_all n q r)
    b T F hF k l hk hl hkl

theorem capped_pin_comparison (n q r : ℕ) (hr : r ≤ n*q)
    (F : (Fin (n+1) → ℕ) → ℚ) (hF : SchurIncreasing F) :
    cappedMean (n+1) q (q+r) F ≤ cappedMean n q r (fun x => F (Fin.cons q x)) :=
  capped_pin_of_association n q r (cappedAssociation_all (n+1) q (q+r)) hr F hF

theorem capped_tie_regression_all (b q T k l : ℕ) (F : CappedLoad b q T → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y)
    (hk : 0 < tieTotal b q T k) (hl : 0 < tieTotal b q T l) (hkl : k ≤ l) :
    expectation (tieWeight k) F ≤ expectation (tieWeight l) F := by
  cases q with
  | zero =>
    have hk' : k = b := by
      by_contra h
      have hb : b ≠ k := Ne.symm h
      simp [tieTotal, tieWeight, maxCount_zeroCap, hb, total] at hk
    have hl' : l = b := by
      by_contra h
      have hb : b ≠ l := Ne.symm h
      simp [tieTotal, tieWeight, maxCount_zeroCap, hb, total] at hl
    subst k
    subst l
    exact le_rfl
  | succ q =>
    have h := capped_tie_regression b q T k l (schurExtension F)
      (schurExtension_mono F) hk hl hkl
    simpa only [tieMean, schurExtension_eq F hF] using h

theorem capped_maxCount_covariance (b q T : ℕ) (F : CappedLoad b q T → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y) :
    CovNonneg cappedWeight (fun x => (maxCount x : ℚ)) F :=
  cappedAssociation_all b q T _ F
    (fun x y h => Nat.cast_le.mpr (maxCount_mono x y h)) hF

end MatchingCapacity
