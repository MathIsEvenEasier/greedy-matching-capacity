import WaitingOrder
import StoppingTransitionLaws

/-! Ordered rational waiting coupling with the actual conditional
stopping-time marginals, including the no-further-acceptance atom. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

theorem coarse_never_factor (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : ℕ → ℕ)
    (hL : ∀ j A, L j A none = failureRatio degree m Aᶜ.card j) (K a t : ℕ) :
    coarseNeverMass L n q K a t =
      (∏ j ∈ Finset.range t, failureRatio degree m a (n+j)) * coarseHistoryMass L n q K a := by
  rw [coarse_never_partition, coarse_history_partition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : KeyPrefix q K a r.val
  · simp only [ite_eq_left hp]
    rw [fiber_never_mass L r.val.1 r.val.2.1 r.val.2.2 r.property.2.2 t]
    simp only [waitingWeight, hL, compl_compl, hp.2.1]
    ring
  · simp [hp]

theorem stopping_never_waiting (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : ℕ → ℕ) (hL : ∀ j A, ∑ o, L j A o = 1)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (hf : ∀ j A, L j A none = failureRatio degree m Aᶜ.card j)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1))
    (hm : 0 < stoppingMass L N q K (some (s,a))) :
    rawStoppingJoint L N q K (some (s.val,a.val)) none /
      stoppingMass L N q K (some (s,a)) = survivalProduct (delayedFailure degree m s.val a.val) N := by
  have he : s.val+(N-s.val) = N := Nat.add_sub_of_le (Nat.le_of_lt_succ s.isLt)
  have hj := stopping_joint_never_identity (n := s.val) (q := q) L hz (N-s.val) K a.val
  rw [he] at hj
  rw [hj, coarse_never_factor L degree hf, stoppingMass_finite L hL hz]
  rw [stoppingMass_finite L hL hz] at hm
  rw [mul_div_cancel_right₀ _ (ne_of_gt hm)]
  exact (he ▸ delayed_survival_shift degree m s.val a.val (N-s.val)).symm

def stoppingTimeMass (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (i : ℕ) : ℚ :=
  if i < N then stoppingNextMoment L N q K s.val a.val (i+1) (fun _ => 1) /
    stoppingMass L N q K (some (s,a))
  else if i = N then rawStoppingJoint L N q K (some (s.val,a.val)) none /
    stoppingMass L N q K (some (s,a)) else 0

theorem stopping_time_mass_identity (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : ℕ → ℕ) (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1))
    (hh : ∀ t, s.val+t+1 ≤ N →
      stoppingNextMoment L N q K s.val a.val (s.val+t+1) (fun _ => 1) /
        stoppingMass L N q K (some (s,a)) = countWaitingFactor degree m s.val a.val t)
    (hn : rawStoppingJoint L N q K (some (s.val,a.val)) none /
      stoppingMass L N q K (some (s,a)) = survivalProduct (delayedFailure degree m s.val a.val) N)
    (i : ℕ) : stoppingTimeMass L N q K s a i = finiteWaitMass (delayedFailure degree m s.val a.val) N i := by
  by_cases hi : i < N
  · simp only [stoppingTimeMass, ite_eq_left hi]
    by_cases hs : s.val ≤ i
    · have he : s.val+(i-s.val) = i := Nat.add_sub_of_le hs
      have hv := hh (i-s.val) (by omega)
      rw [he] at hv
      have hw := delayed_waiting_hit degree m s.val a.val N (i-s.val) (by omega : s.val+(i-s.val) < N)
      rw [he] at hw
      exact hv.trans hw.symm
    · have hb : i < s.val := by omega
      rw [delayed_waiting_before degree m s.val a.val N i (Nat.le_of_lt_succ s.isLt) hb]
      unfold stoppingNextMoment
      simp only [raw_joint_nonfuture_zero L K s.val a.val (i+1) _ (by omega), zero_mul,
        Finset.sum_const_zero, zero_div]
  · by_cases he : i = N
    · subst i
      simp only [stoppingTimeMass, finiteWaitMass, lt_self_iff_false, ite_false, ite_true]
      exact hn
    · simp [stoppingTimeMass, finiteWaitMass, hi, he]

theorem stopping_rv_time_mass (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1))
    (hm : 0 < stoppingMass (fun j => rvKernel (degree j)) N q K (some (s,a))) (i : ℕ) :
    stoppingTimeMass (fun j => rvKernel (degree j)) N q K s a i =
      finiteWaitMass (delayedFailure degree m s.val a.val) N i := by
  apply stopping_time_mass_identity _ degree K s a
  · exact fun t ht => stopping_rv_waiting degree hd K t s a ht hm
  · exact stopping_never_waiting _ degree (fun j A => rvKernel_probability (degree j) (hd j) A)
      (fun j A k hk => rvKernel_unavailable (degree j) A k hk)
      (fun j A => rv_rejection_formula (degree j) A) K s a hm

theorem stopping_ranking_time_mass (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1))
    (hm : 0 < stoppingMass (fun j => rankingKernel (degree j)) N q K (some (s,a))) (i : ℕ) :
    stoppingTimeMass (fun j => rankingKernel (degree j)) N q K s a i =
      finiteWaitMass (delayedFailure degree m s.val a.val) N i := by
  apply stopping_time_mass_identity _ degree K s a
  · exact fun t ht => stopping_ranking_waiting degree hd K t s a ht hm
  · exact stopping_never_waiting _ degree (fun j A => rankingKernel_probability (degree j) (hd j) A)
      (fun j A k hk => rankingKernel_unavailable (degree j) A k hk)
      (fun j A => ranking_rejection_formula (degree j) A) K s a hm

theorem actual_waiting_ordered_coupling (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s t : Fin (N+1)) (a b : Fin (m+1)) (hst : s ≤ t) (hab : a ≤ b)
    (hrv : 0 < stoppingMass (fun j => rvKernel (degree j)) N q K (some (s,a)))
    (hrk : 0 < stoppingMass (fun j => rankingKernel (degree j)) N q K (some (t,b))) :
    ∃ c : Fin (N+1) → Fin (N+1) → ℚ,
      (∀ i j, 0 ≤ c i j) ∧
      (∀ i, ∑ j, c i j = stoppingTimeMass (fun j => rvKernel (degree j)) N q K s a i.val) ∧
      (∀ j, ∑ i, c i j = stoppingTimeMass (fun j => rankingKernel (degree j)) N q K t b j.val) ∧
      (∀ i j, j < i → c i j = 0) := by
  simp only [stopping_rv_time_mass degree hd K s a hrv,
    stopping_ranking_time_mass degree hd K t b hrk]
  exact count_waiting_ordered_coupling degree m s.val t.val a.val b.val N hd hst hab
    (Nat.le_of_lt_succ b.isLt)

end MatchingCapacity
