import StoppingWaitingCoupling
import TwoPointMoments

/-! Actual conditional next-count moments are Bernoulli increments,
including null next-hit events and boundary full-bin counts. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N m q : ℕ}

theorem rawStoppingJoint_nonneg (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K : ℕ) (s t : Option (ℕ × ℕ)) :
    0 ≤ rawStoppingJoint L N q K s t := by
  unfold rawStoppingJoint
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact historyWeight_nonneg _ (fun j A o => hL j.val A o) q h
  · rfl

theorem stopping_saturation_bounds (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K n a u : ℕ) :
    0 ≤ stoppingNextSaturation L N q K n a u ∧ stoppingNextSaturation L N q K n a u ≤ 1 := by
  simpa only [stoppingNextSaturation, stoppingNextMoment, mul_one] using
    indicator_ratio_bounds (fun b : Fin (m+1) => rawStoppingJoint L N q K (some (n,a)) (some (u,b.val)))
      (fun _ => rawStoppingJoint_nonneg L hL K _ _) (fun b => b.val = a+1)

theorem stopping_mark_support (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (K s a u b : ℕ) (hu : u ≤ N) (hb : b ≠ a) (hb' : b ≠ a+1) :
    rawStoppingJoint L N q K (some (s,a)) (some (u,b)) = 0 := by
  by_cases hs : u ≤ s
  · exact raw_joint_nonfuture_zero L K s a u b hs
  · have he : s+(u-s-1)+1 = u := by omega
    have hi := stopping_joint_next_identity (n := s) (q := q) L hL hz (u-s-1) K a b (by omega : s+(u-s-1)+1 ≤ N)
    rw [coarse_next_mark_support L K a (u-s-1) b hb hb'] at hi
    simpa only [he] using hi

theorem stopping_mark_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (h0 : ∀ j A o, 0 ≤ L j A o) (hL : ∀ j A, ∑ o, L j A o = 1)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (K s a u : ℕ) (hu : u ≤ N) (F : ℕ → ℚ) :
    stoppingNextMoment L N q K s a u F = ∑ b : Bool,
      stoppingNextMoment L N q K s a u (fun _ => 1) *
      bernoulliMass (stoppingNextSaturation L N q K s a u) b * F (a+b.toNat) := by
  simpa only [stoppingNextMoment, stoppingNextSaturation, mul_one] using
    twoPoint_bernoulli_moment (fun b : Fin (m+1) => rawStoppingJoint L N q K (some (s,a)) (some (u,b.val)))
      (fun _ => rawStoppingJoint_nonneg L h0 K _ _) Fin.val a
      (fun b hb hb' => stopping_mark_support L hL hz K s a u b.val hu hb hb') F

theorem positive_next_hit_future (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K s a u : ℕ) (hm : 0 < stoppingNextMoment L N q K s a u (fun _ => 1)) : s < u := by
  by_contra h
  have he : stoppingNextMoment L N q K s a u (fun _ => 1) = 0 := by
    simp only [stoppingNextMoment, raw_joint_nonfuture_zero L K s a u _ (by omega), zero_mul,
      Finset.sum_const_zero]
  rw [he] at hm
  exact lt_irrefl 0 hm

theorem full_count_waiting_zero (degree : ℕ → ℕ) (m s t : ℕ) (hd : degree (s+t) ≤ m) :
    countWaitingFactor degree m s m t = 0 := by
  have hp : (Nat.choose m (degree (s+t)) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hd).ne'
  simp [countWaitingFactor, div_self hp]

theorem positive_rv_next_not_full (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (u : ℕ) (hu : u ≤ N)
    (hs : 0 < stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)))
    (hm : 0 < stoppingNextMoment (fun j => rvKernel (m := m) (degree j)) N q K s.val a.val u (fun _ => 1)) : a.val < m := by
  have hf := positive_next_hit_future _ K s.val a.val u hm
  have he : s.val+(u-s.val-1)+1 = u := by omega
  have hw := stopping_rv_waiting degree hd K (u-s.val-1) s a (by omega) hs
  rw [he] at hw
  have ha : a.val ≤ m := Nat.le_of_lt_succ a.isLt
  by_contra h
  have ha' : a.val = m := by omega
  rw [ha', full_count_waiting_zero degree m s.val (u-s.val-1) (hd _)] at hw
  have hp := div_pos hm hs
  rw [ha',hw] at hp
  exact lt_irrefl 0 hp

theorem actual_equal_count_mark_order (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K : ℕ) (s t : Fin (N+1)) (a : Fin (m+1)) (u v : ℕ) (hu : u ≤ N) (hv : v ≤ N)
    (hs : 0 < stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K (some (s,a)))
    (hrv : 0 < stoppingNextMoment (fun j => rvKernel (m := m) (degree j)) N q K s.val a.val u (fun _ => 1))
    (hrk : 0 < stoppingNextMoment (fun j => rankingKernel (m := m) (degree j)) N q K t.val a.val v (fun _ => 1)) :
    stoppingNextSaturation (fun j => rvKernel (m := m) (degree j)) N q K s.val a.val u ≤
      stoppingNextSaturation (fun j => rankingKernel (m := m) (degree j)) N q K t.val a.val v := by
  have ha := positive_rv_next_not_full degree hd K s a u hu hs hrv
  have hf := positive_next_hit_future _ K s.val a.val u hrv
  have hg := positive_next_hit_future _ K t.val a.val v hrk
  have he : s.val+(u-s.val-1)+1 = u := by omega
  have he' : t.val+(v-t.val-1)+1 = v := by omega
  have hr := stopping_rv_saturation (N := N) (n := s.val) degree hd (u-s.val-1) K a.val (by omega) ha (by simpa only [he] using hrv)
  have hk := stopping_ranking_saturation (N := N) (n := t.val) degree hd (v-t.val-1) K a.val (by omega) ha (by simpa only [he'] using hrk)
  rw [he] at hr
  rw [he'] at hk
  exact hr.trans_le hk

end MatchingCapacity
