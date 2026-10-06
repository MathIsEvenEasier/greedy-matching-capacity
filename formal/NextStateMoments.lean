import StoppingMarkMoments
import MarkedTimeCoupling

/-! Decoding the marked waiting law gives every observable moment of
the actual next stopping state, including the cemetery outcome. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N m q : ℕ}

def markedNextState (a : ℕ) (z : Fin (N+1) × Bool) : Option (ℕ × ℕ) :=
  if z.1.val < N then some (z.1.val+1,a+z.2.toNat) else none

def actualMarkedMass (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (z : Fin (N+1) × Bool) : ℚ :=
  markedTimeMass (fun i => stoppingTimeMass L N q K s a i.val)
    (fun i => stoppingNextSaturation L N q K s.val a.val (i.val+1)) z

theorem next_state_moment_decomposition (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (F : Option (ℕ × ℕ) → ℚ) :
    (∑ z : StopState N m, stoppingTransition L N q K (some (s,a)) z * F (stopValue z)) =
      rawStoppingJoint L N q K (some (s.val,a.val)) none /
        stoppingMass L N q K (some (s,a)) * F none +
      ∑ i : Fin N, stoppingNextMoment L N q K s.val a.val (i.val+1)
        (fun b => F (some (i.val+1,b))) / stoppingMass L N q K (some (s,a)) := by
  simp only [stoppingTransition, stoppingJoint_raw, Fintype.sum_option, Fintype.sum_prod_type,
    stopValue, Option.map_none, Option.map_some]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, raw_joint_nonfuture_zero L K s.val a.val 0 _ (Nat.zero_le _),
    zero_div, zero_mul, Finset.sum_const_zero, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [stoppingNextMoment, Finset.sum_div, div_mul_eq_mul_div]

theorem marked_finite_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (h0 : ∀ j A o, 0 ≤ L j A o) (hL : ∀ j A, ∑ o, L j A o = 1)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (i : Fin N) (F : Option (ℕ × ℕ) → ℚ) :
    (∑ b : Bool, actualMarkedMass L N q K s a (i.castSucc,b) * F (markedNextState a.val (i.castSucc,b))) =
      stoppingNextMoment L N q K s.val a.val (i.val+1) (fun b => F (some (i.val+1,b))) /
        stoppingMass L N q K (some (s,a)) := by
  simp only [actualMarkedMass, markedTimeMass, markedNextState, Fin.val_castSucc,
    stoppingTimeMass, ite_eq_left i.isLt]
  rw [stopping_mark_moment L h0 hL hz K s.val a.val (i.val+1) (by omega)
    (fun b => F (some (i.val+1,b)))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem marked_terminal_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (F : Option (ℕ × ℕ) → ℚ) :
    (∑ b : Bool, actualMarkedMass L N q K s a (Fin.last N,b) * F (markedNextState a.val (Fin.last N,b))) =
      rawStoppingJoint L N q K (some (s.val,a.val)) none /
        stoppingMass L N q K (some (s,a)) * F none := by
  simp only [actualMarkedMass, markedTimeMass, markedNextState, Fin.val_last,
    stoppingTimeMass, lt_self_iff_false, ite_false, ite_true]
  rw [← Finset.sum_mul, ← Finset.mul_sum, bernoulliMass_probability, mul_one]

theorem actual_marked_state_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (h0 : ∀ j A o, 0 ≤ L j A o) (hL : ∀ j A, ∑ o, L j A o = 1)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (F : Option (ℕ × ℕ) → ℚ) :
    (∑ z : Fin (N+1) × Bool, actualMarkedMass L N q K s a z * F (markedNextState a.val z)) =
      ∑ z : StopState N m, stoppingTransition L N q K (some (s,a)) z * F (stopValue z) := by
  rw [next_state_moment_decomposition, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp only [marked_finite_moment L h0 hL hz K s a, marked_terminal_moment L K s a]
  exact add_comm _ _

def RawStopLE (x y : Option (ℕ × ℕ)) : Prop :=
  match x,y with
  | _,none => True
  | none,some _ => False
  | some x,some y => x.1 ≤ y.1 ∧ x.2 ≤ y.2

theorem markedNextState_order (a b : ℕ) (x y : Fin (N+1) × Bool)
    (h : y.1.val < N → x.1 ≤ y.1 ∧ a+x.2.toNat ≤ b+y.2.toNat) :
    RawStopLE (markedNextState a x) (markedNextState b y) := by
  by_cases hy : y.1.val < N
  · obtain ⟨ht,hc⟩ := h hy
    have hx : x.1.val < N := lt_of_le_of_lt ht hy
    simp only [markedNextState, ite_eq_left hx, ite_eq_left hy, RawStopLE]
    exact ⟨Nat.succ_le_succ ht,hc⟩
  · simp [markedNextState, hy, RawStopLE]

theorem markedTimeJoint_state_support (c : Fin (N+1) → Fin (N+1) → ℚ)
    (p r : Fin (N+1) → ℚ) (a b : ℕ) (hab : a ≤ b)
    (hc : ∀ i j, j < i → c i j = 0) (x y : Fin (N+1) × Bool)
    (h : ¬ RawStopLE (markedNextState a x) (markedNextState b y)) :
    markedTimeJoint c p r a b x y = 0 := by
  by_cases hy : y.1.val < N
  · apply markedTimeJoint_ordered c p r a b hab hc x y hy
    intro hh
    exact h (markedNextState_order a b x y (fun _ => hh))
  · exact False.elim (h (markedNextState_order a b x y (fun hh => False.elim (hy hh))))

end MatchingCapacity
