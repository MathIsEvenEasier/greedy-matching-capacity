import NextStateMoments

/-! A complete rational coupling of the actual next states from two
positive finite ordered current states. Both marginal laws are proved
for every observable, and the cemetery cases are included. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N m q : ℕ}

theorem positive_time_mass_next (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (i : Fin (N+1)) (hi : i.val < N)
    (hs : 0 < stoppingMass L N q K (some (s,a)))
    (ht : 0 < stoppingTimeMass L N q K s a i.val) :
    0 < stoppingNextMoment L N q K s.val a.val (i.val+1) (fun _ => 1) := by
  rw [stoppingTimeMass, ite_eq_left hi] at ht
  have h := (lt_div_iff₀ hs).mp ht
  simpa only [zero_mul] using h

theorem actual_marked_coupling (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s t : Fin (N+1)) (a b : Fin (m+1)) (hst : s ≤ t) (hab : a ≤ b)
    (hrv : 0 < stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)))
    (hrk : 0 < stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K (some (t,b))) :
    ∃ g : (Fin (N+1) × Bool) → (Fin (N+1) × Bool) → ℚ,
      (∀ x y, 0 ≤ g x y) ∧
      (∀ x, ∑ y, g x y = actualMarkedMass (fun j => rvKernel (m := m) (degree j)) N q K s a x) ∧
      (∀ y, ∑ x, g x y = actualMarkedMass (fun j => rankingKernel (m := m) (degree j)) N q K t b y) ∧
      (∀ x y, ¬ RawStopLE (markedNextState a.val x) (markedNextState b.val y) → g x y = 0) := by
  obtain ⟨c,hc,hrow,hcol,horder⟩ := actual_waiting_ordered_coupling degree hd K s t a b hst hab hrv hrk
  let p := fun i : Fin (N+1) => stoppingNextSaturation (fun j => rvKernel (m := m) (degree j)) N q K s.val a.val (i.val+1)
  let r := fun j : Fin (N+1) => stoppingNextSaturation (fun j => rankingKernel (m := m) (degree j)) N q K t.val b.val (j.val+1)
  refine ⟨markedTimeJoint c p r a.val b.val, ?_, ?_, ?_, ?_⟩
  · apply markedTimeJoint_nonneg c p r a.val b.val hc
    · exact fun i => stopping_saturation_bounds _ (fun j A o => rvKernel_nonneg (degree j) A o) K s.val a.val (i.val+1)
    · exact fun j => stopping_saturation_bounds _ (fun j A o => rankingKernel_nonneg (degree j) A o) K t.val b.val (j.val+1)
    · intro i j hij he hi hj
      have ha : a = b := Fin.ext he
      subst b
      have hpi := coupling_row_positive c hc i j hij
      have hrj := coupling_column_positive c hc i j hij
      rw [hrow] at hpi
      rw [hcol] at hrj
      exact actual_equal_count_mark_order degree hd K s t a (i.val+1) (j.val+1) (by omega) (by omega) hrv
        (positive_time_mass_next _ K s a i hi hrv hpi) (positive_time_mass_next _ K t a j hj hrk hrj)
  · intro x
    exact markedTimeJoint_row c _ p r a.val b.val hrow x
  · intro y
    exact markedTimeJoint_column c _ p r a.val b.val hcol y
  · exact markedTimeJoint_state_support c p r a.val b.val hab horder

theorem actual_next_state_coupling (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s t : Fin (N+1)) (a b : Fin (m+1)) (hst : s ≤ t) (hab : a ≤ b)
    (hrv : 0 < stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)))
    (hrk : 0 < stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K (some (t,b))) :
    ∃ g : (Fin (N+1) × Bool) → (Fin (N+1) × Bool) → ℚ,
      (∀ x y, 0 ≤ g x y) ∧ (∑ x, ∑ y, g x y) = 1 ∧
      (∀ F : Option (ℕ × ℕ) → ℚ,
        (∑ x, ∑ y, g x y * F (markedNextState a.val x)) =
          ∑ z : StopState N m, stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)) z * F (stopValue z)) ∧
      (∀ F : Option (ℕ × ℕ) → ℚ,
        (∑ x, ∑ y, g x y * F (markedNextState b.val y)) =
          ∑ z : StopState N m, stoppingTransition (fun j => rankingKernel (m := m) (degree j)) N q K (some (t,b)) z * F (stopValue z)) ∧
      (∀ x y, ¬ RawStopLE (markedNextState a.val x) (markedNextState b.val y) → g x y = 0) := by
  obtain ⟨g,hg,hr,hc,ho⟩ := actual_marked_coupling degree hd K s t a b hst hab hrv hrk
  have hl : ∀ F : Option (ℕ × ℕ) → ℚ,
      (∑ x, ∑ y, g x y * F (markedNextState a.val x)) =
        ∑ z : StopState N m, stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)) z * F (stopValue z) := by
    intro F
    simp only [← Finset.sum_mul, hr]
    exact actual_marked_state_moment _ (fun j A o => rvKernel_nonneg (degree j) A o)
      (fun j A => rvKernel_probability (degree j) (hd j) A)
      (fun j A k hk => rvKernel_unavailable (degree j) A k hk) K s a F
  have hr' : ∀ F : Option (ℕ × ℕ) → ℚ,
      (∑ x, ∑ y, g x y * F (markedNextState b.val y)) =
        ∑ z : StopState N m, stoppingTransition (fun j => rankingKernel (m := m) (degree j)) N q K (some (t,b)) z * F (stopValue z) := by
    intro F
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hc]
    exact actual_marked_state_moment _ (fun j A o => rankingKernel_nonneg (degree j) A o)
      (fun j A => rankingKernel_probability (degree j) (hd j) A)
      (fun j A k hk => rankingKernel_unavailable (degree j) A k hk) K t b F
  refine ⟨g,hg,?_,hl,hr',ho⟩
  have h := hl (fun _ => 1)
  simp only [mul_one] at h
  exact h.trans (stoppingTransition_probability _ K (some (s,a)) hrv)

end MatchingCapacity
