import StoppingTransitionBridge

/-! Waiting and Bernoulli mark comparisons for the actual finite-horizon
Kth-acceptance random variables, not an assumed transition system. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

def stoppingNextMoment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K n a u : ℕ) (F : ℕ → ℚ) : ℚ :=
  ∑ b : Fin (m+1), rawStoppingJoint L N q K (some (n,a)) (some (u,b.val)) * F b.val

theorem finite_nat_indicator_sum (r : ℕ) (hr : r ≤ m) (F : ℕ → ℚ) :
    (∑ b : Fin (m+1), if r = b.val then F b.val else 0) = F r := by
  have he : ∀ b : Fin (m+1), (r = b.val) ↔ (⟨r,Nat.lt_succ_of_le hr⟩ : Fin (m+1)) = b :=
    fun _ => ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem stopping_next_moment_identity (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (t K a : ℕ) (hn : n+t+1 ≤ N) (F : ℕ → ℚ) :
    stoppingNextMoment L N q K n a (n+t+1) F =
      coarseNextMoment L n q K a t (fun h k => F (historyFullBins q (acceptedExtension h t k)).card) := by
  unfold stoppingNextMoment
  simp only [stopping_joint_next_identity L hL hz t K a _ hn]
  unfold coarseNextMoment availableNextMoment
  simp only [Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hp : AcceptedPrefix q K a h.val
  · simp only [ite_eq_left hp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact finite_nat_indicator_sum _ ((Finset.card_le_univ _).trans_eq (Fintype.card_fin m))
      (fun b => historyWeight (fun j => L j.val) q (acceptedExtension h.val t k) * F b)
  · simp [hp]

theorem coarse_next_mark_indicator (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (K a t : ℕ) :
    coarseNextMoment L n q K a t
      (fun h k => if (historyFullBins q (acceptedExtension h t k)).card = a+1 then 1 else 0) =
      coarseNextMoment L n q K a t (fun h k => if historyLoad h n k = q then 1 else 0) := by
  unfold coarseNextMoment
  apply Finset.sum_congr rfl
  intro h _
  by_cases hp : AcceptedPrefix q K a h.val
  · simp only [ite_eq_left hp]
    unfold availableNextMoment
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [acceptedExtension_full_count h.val t k hk, hp.2.1]
    split_ifs <;> simp_all
  · simp [hp]

theorem coarse_next_mark_support (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K a t b : ℕ) (hb : b ≠ a) (hb' : b ≠ a+1) :
    coarseNextMoment L n q K a t
      (fun h k => if (historyFullBins q (acceptedExtension h t k)).card = b then 1 else 0) = 0 := by
  unfold coarseNextMoment
  apply Finset.sum_eq_zero
  intro h _
  by_cases hp : AcceptedPrefix q K a h.val
  · simp only [ite_eq_left hp]
    unfold availableNextMoment
    apply Finset.sum_eq_zero
    intro k hk
    dsimp only
    rw [acceptedExtension_full_count h.val t k hk, hp.2.1]
    split_ifs <;> simp_all
  · simp [hp]

def stoppingNextSaturation (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K n a u : ℕ) : ℚ :=
  stoppingNextMoment L N q K n a u (fun b => if b = a+1 then 1 else 0) /
    stoppingNextMoment L N q K n a u (fun _ => 1)

theorem stopping_saturation_identity (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (t K a : ℕ) (hn : n+t+1 ≤ N) :
    stoppingNextSaturation L N q K n a (n+t+1) = coarseNextSaturation L n q K a t := by
  unfold stoppingNextSaturation coarseNextSaturation
  rw [stopping_next_moment_identity L hL hz t K a hn,
    stopping_next_moment_identity L hL hz t K a hn, coarse_next_mark_indicator]

theorem stopping_rv_saturation (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (t K a : ℕ) (hn : n+t+1 ≤ N) (ha : a < m)
    (hm : 0 < stoppingNextMoment (fun j => rvKernel (m := m) (degree j)) N q K n a (n+t+1) (fun _ => 1)) :
    stoppingNextSaturation (fun j => rvKernel (m := m) (degree j)) N q K n a (n+t+1) =
      referenceHazard (m-a) q (K-a*(q+1)) := by
  have hL := fun j A => rvKernel_probability (degree j) (hd j) A
  have hz := fun j A k hk => rvKernel_unavailable (m := m) (degree j) A k hk
  rw [stopping_saturation_identity _ hL hz t K a hn]
  rw [stopping_next_moment_identity _ hL hz t K a hn] at hm
  exact coarse_rv_saturation degree K a t ha hm

theorem stopping_ranking_saturation (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (t K a : ℕ) (hn : n+t+1 ≤ N) (ha : a < m)
    (hm : 0 < stoppingNextMoment (fun j => rankingKernel (m := m) (degree j)) N q K n a (n+t+1) (fun _ => 1)) :
    referenceHazard (m-a) q (K-a*(q+1)) ≤
      stoppingNextSaturation (fun j => rankingKernel (m := m) (degree j)) N q K n a (n+t+1) := by
  have hL := fun j A => rankingKernel_probability (degree j) (hd j) A
  have hz := fun j A k hk => rankingKernel_unavailable (m := m) (degree j) A k hk
  rw [stopping_saturation_identity _ hL hz t K a hn]
  rw [stopping_next_moment_identity _ hL hz t K a hn] at hm
  exact coarse_ranking_saturation degree K a t ha hm

theorem stopping_rv_waiting (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K t : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (hn : s.val+t+1 ≤ N)
    (hm : 0 < stoppingMass (fun j => rvKernel (degree j)) N q K (some (s,a))) :
    stoppingNextMoment (fun j => rvKernel (m := m) (degree j)) N q K s.val a.val (s.val+t+1) (fun _ => 1) /
      stoppingMass (fun j => rvKernel (degree j)) N q K (some (s,a)) = countWaitingFactor degree m s.val a.val t := by
  have hL := fun j A => rvKernel_probability (degree j) (hd j) A
  have hz := fun j A k hk => rvKernel_unavailable (m := m) (degree j) A k hk
  rw [stoppingMass_finite _ hL hz K s a] at hm ⊢
  rw [stopping_next_moment_identity _ hL hz t K a.val hn]
  exact coarse_rv_waiting_law degree K a.val t (hd _) hm

theorem stopping_ranking_waiting (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (K t : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) (hn : s.val+t+1 ≤ N)
    (hm : 0 < stoppingMass (fun j => rankingKernel (degree j)) N q K (some (s,a))) :
    stoppingNextMoment (fun j => rankingKernel (m := m) (degree j)) N q K s.val a.val (s.val+t+1) (fun _ => 1) /
      stoppingMass (fun j => rankingKernel (degree j)) N q K (some (s,a)) = countWaitingFactor degree m s.val a.val t := by
  have hL := fun j A => rankingKernel_probability (degree j) (hd j) A
  have hz := fun j A k hk => rankingKernel_unavailable (m := m) (degree j) A k hk
  rw [stoppingMass_finite _ hL hz K s a] at hm ⊢
  rw [stopping_next_moment_identity _ hL hz t K a.val hn]
  exact coarse_ranking_waiting_law degree K a.val t (hd _) hm

end MatchingCapacity
