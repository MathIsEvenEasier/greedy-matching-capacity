import ActualNextCoupling
import FiniteJointPush

/-! The coupling lives on the actual bounded state space. The retraction
to bounded states is order preserving; cemetery current states are handled
explicitly. No Markov property is assumed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N m q : ℕ}

def boundStop (N m : ℕ) : Option (ℕ × ℕ) → StopState N m
  | none => none
  | some (s,a) => if hs : s ≤ N then
      if ha : a ≤ m then some (⟨s,Nat.lt_succ_of_le hs⟩,⟨a,Nat.lt_succ_of_le ha⟩) else none
    else none

def StopLE (x y : StopState N m) : Prop := RawStopLE (stopValue x) (stopValue y)

theorem boundStop_value (z : StopState N m) : boundStop N m (stopValue z) = z := by
  cases z with
  | none => rfl
  | some z =>
    simp [stopValue, boundStop, Nat.le_of_lt_succ z.1.isLt, Nat.le_of_lt_succ z.2.isLt]

theorem boundStop_order (x y : Option (ℕ × ℕ)) (h : RawStopLE x y) :
    StopLE (boundStop N m x) (boundStop N m y) := by
  cases y with
  | none => simp [StopLE, boundStop, stopValue, RawStopLE]
  | some y =>
    cases x with
    | none => exact False.elim h
    | some x =>
      change x.1 ≤ y.1 ∧ x.2 ≤ y.2 at h
      by_cases ht : y.1 ≤ N
      · by_cases ha : y.2 ≤ m
        · have hx := h.1.trans ht
          have hx' := h.2.trans ha
          simpa [StopLE, boundStop, stopValue, ht, ha, hx, hx', RawStopLE] using h
        · simp [StopLE, boundStop, stopValue, ht, ha, RawStopLE]
      · simp [StopLE, boundStop, stopValue, ht, RawStopLE]

theorem finite_current_transition_coupling (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s t : Fin (N+1)) (a b : Fin (m+1)) (hst : s ≤ t) (hab : a ≤ b)
    (hrv : 0 < stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)))
    (hrk : 0 < stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K (some (t,b))) :
    ∃ c : StopState N m → StopState N m → ℚ,
      (∀ u v, 0 ≤ c u v) ∧
      (∀ u, ∑ v, c u v = stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)) u) ∧
      (∀ v, ∑ u, c u v = stoppingTransition (fun j => rankingKernel (m := m) (degree j)) N q K (some (t,b)) v) ∧
      (∀ u v, ¬ StopLE u v → c u v = 0) := by
  obtain ⟨g,hg,_,hl,hr,ho⟩ := actual_next_state_coupling degree hd K s t a b hst hab hrv hrk
  let f := fun x : Fin (N+1) × Bool => boundStop N m (markedNextState a.val x)
  let h := fun y : Fin (N+1) × Bool => boundStop N m (markedNextState b.val y)
  refine ⟨jointPush g f h, jointPush_nonneg g hg f h, ?_, ?_, ?_⟩
  · intro u
    rw [jointPush_row]
    have he := hl (fun r => if boundStop N m r = u then 1 else 0)
    simpa only [mul_ite, mul_one, mul_zero, boundStop_value, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he
  · intro v
    rw [jointPush_column]
    have he := hr (fun r => if boundStop N m r = v then 1 else 0)
    simpa only [mul_ite, mul_one, mul_zero, boundStop_value, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he
  · exact jointPush_support g f h _ StopLE ho (fun x y hh => boundStop_order _ _ hh)

theorem stoppingTransition_nonneg (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K : ℕ) (s t : StopState N m) :
    0 ≤ stoppingTransition L N q K s t :=
  div_nonneg (stoppingJoint_nonneg L hL K s t) (stoppingMass_nonneg L hL K s)

theorem stoppingTransition_cemetery (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (hs : 0 < stoppingMass L N q K none) (t : StopState N m) :
    stoppingTransition L N q K none t = if t = none then 1 else 0 := by
  rw [stoppingTransition, stoppingJoint_cemetery]
  split_ifs
  · exact div_self (ne_of_gt hs)
  · exact zero_div _

theorem actual_ordered_transition_coupling (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s t : StopState N m) (hst : StopLE s t)
    (hrv : 0 < stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K s)
    (hrk : 0 < stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K t) :
    ∃ c : StopState N m → StopState N m → ℚ,
      (∀ u v, 0 ≤ c u v) ∧
      (∀ u, ∑ v, c u v = stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K s u) ∧
      (∀ v, ∑ u, c u v = stoppingTransition (fun j => rankingKernel (m := m) (degree j)) N q K t v) ∧
      (∀ u v, ¬ StopLE u v → c u v = 0) := by
  cases t with
  | none =>
    refine ⟨fun u v => stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K s u *
      (if v = none then 1 else 0), ?_, ?_, ?_, ?_⟩
    · intro u v
      apply mul_nonneg (stoppingTransition_nonneg _ (fun j A o => rvKernel_nonneg (degree j) A o) K s u)
      split_ifs <;> norm_num
    · intro u
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · intro v
      rw [stoppingTransition_cemetery _ K hrk v, ← Finset.sum_mul, stoppingTransition_probability _ K s hrv, one_mul]
    · intro u v hv
      by_cases he : v = none
      · subst v
        exact False.elim (hv (by simp [StopLE, stopValue, RawStopLE]))
      · simp [he]
  | some t =>
    cases s with
    | none => exact False.elim hst
    | some s =>
      exact finite_current_transition_coupling degree hd K s.1 t.1 s.2 t.2 hst.1 hst.2 hrv hrk

end MatchingCapacity
