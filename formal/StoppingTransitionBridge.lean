import StoppingExtensions

/-! Exact joint stopping-event masses, obtained from the actual history
law by prefix marginalization and the injective first-success extension. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

def rawStoppingJoint (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K : ℕ) (s t : Option (ℕ × ℕ)) : ℚ :=
  ∑ h : Fin N → Option (Fin m), if stoppingState q h K = s ∧ stoppingState q h (K+1) = t
    then historyWeight (fun j => L j.val) q h else 0

theorem stoppingJoint_raw (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (s t : StopState N m) :
    stoppingJointMass L N q K s t = rawStoppingJoint L N q K (stopValue s) (stopValue t) := by
  simp only [stoppingJointMass, rawStoppingJoint, finiteStoppingState_eq_iff]

theorem available_next_all_bins (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (h : Fin n → Option (Fin m)) (t : ℕ) (G : (Fin n → Option (Fin m)) → Fin m → ℚ) :
    availableNextMoment L q h t G =
      ∑ k : Fin m, historyWeight (fun j => L j.val) q (acceptedExtension h t k) * G h k := by
  unfold availableNextMoment
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  rw [acceptedExtension_weight, hz (n+t) (historyAvailable q h n) k hk]
  ring

theorem raw_joint_at_next_hit (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0) (t K a b : ℕ) :
    rawStoppingJoint L (n+t+1) q K (some (n,a)) (some (n+t+1,b)) =
      coarseNextMoment L n q K a t (fun h k => if (historyFullBins q (acceptedExtension h t k)).card = b then 1 else 0) := by
  rw [coarse_next_unrestricted L hz]
  simp only [available_next_all_bins L hz, mul_ite, mul_one, mul_zero]
  have he := Fintype.sum_of_injective
    (fun x : (Fin n → Option (Fin m)) × Fin m => acceptedExtension x.1 t x.2)
    (acceptedExtension_injective t)
    (fun x => if AcceptedPrefix q K a x.1 ∧ (historyFullBins q (acceptedExtension x.1 t x.2)).card = b
      then historyWeight (fun j => L j.val) q (acceptedExtension x.1 t x.2) else 0)
    (fun h => if stoppingState q h K = some (n,a) ∧ stoppingState q h (K+1) = some (n+t+1,b)
      then historyWeight (fun j => L j.val) q h else 0)
    (by
      intro h hn
      by_cases hh : stoppingState q h K = some (n,a) ∧ stoppingState q h (K+1) = some (n+t+1,b)
      · obtain ⟨g,k,_,he⟩ := consecutive_hit_extension t K a b h hh.1 hh.2
        exact False.elim (hn ⟨(g,k),he.symm⟩)
      · simp only [ite_eq_right hh])
    (by
      intro x
      simp only [acceptedExtension_old_hit, acceptedExtension_next_hit]
      by_cases hp : AcceptedPrefix q K a x.1
      · simp [hp,hp.1]
      · simp [hp])
  unfold rawStoppingJoint
  rw [← he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hp : AcceptedPrefix q K a h <;> simp [hp]

theorem raw_joint_prefix (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (t K a b : ℕ) (hn : n+t+1 ≤ N) :
    rawStoppingJoint L N q K (some (n,a)) (some (n+t+1,b)) =
      rawStoppingJoint L (n+t+1) q K (some (n,a)) (some (n+t+1,b)) := by
  have htake : ∀ h : Fin N → Option (Fin m),
      (stoppingState q h K = some (n,a) ∧ stoppingState q h (K+1) = some (n+t+1,b)) ↔
      (stoppingState q (historyTake h (n+t+1) hn) K = some (n,a) ∧
        stoppingState q (historyTake h (n+t+1) hn) (K+1) = some (n+t+1,b)) := by
    intro h
    rw [stoppingState_prefix_iff h (by omega : n ≤ N), stoppingState_prefix_iff h hn,
      stoppingState_prefix_iff _ (by omega : n ≤ n+t+1), stoppingState_at_end, historyTake_trans]
  unfold rawStoppingJoint
  simp_rw [htake]
  convert! history_prefix_event (q := q) L hL hn
    (fun h => stoppingState q h K = some (n,a) ∧ stoppingState q h (K+1) = some (n+t+1,b)) using 1
  all_goals
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> rfl

theorem stopping_joint_next_identity (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (t K a b : ℕ) (hn : n+t+1 ≤ N) :
    rawStoppingJoint L N q K (some (n,a)) (some (n+t+1,b)) =
      coarseNextMoment L n q K a t (fun h k => if (historyFullBins q (acceptedExtension h t k)).card = b then 1 else 0) := by
  rw [raw_joint_prefix L hL t K a b hn, raw_joint_at_next_hit L hz]

theorem stopping_joint_never_identity (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0) (t K a : ℕ) :
    rawStoppingJoint L (n+t) q K (some (n,a)) none = coarseNeverMass L n q K a t := by
  rw [coarse_never_unrestricted L hz]
  symm
  apply Fintype.sum_of_injective (fun h : Fin n → Option (Fin m) => rejectExtension h t)
    (rejectExtension_injective t)
  · intro h hn
    by_cases hh : stoppingState q h K = some (n,a) ∧ stoppingState q h (K+1) = none
    · have he := never_next_rejectExtension t K a h hh.1 hh.2
      exact False.elim (hn ⟨historyTake h n (Nat.le_add_right n t),he.symm⟩)
    · simp only [ite_eq_right hh]
  · intro h
    simp only [rejectExtension_old_hit]
    by_cases hp : AcceptedPrefix q K a h
    · simp only [hp, rejectExtension_next_none h t K a hp, and_self, ite_true]
    · simp only [hp, false_and, ite_false]

theorem raw_joint_nonfuture_zero (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K s a u b : ℕ) (hu : u ≤ s) : rawStoppingJoint L N q K (some (s,a)) (some (u,b)) = 0 := by
  unfold rawStoppingJoint
  apply Finset.sum_eq_zero
  intro h _
  have hn : ¬ (stoppingState q h K = some (s,a) ∧ stoppingState q h (K+1) = some (u,b)) := by
    intro hh
    have ht := stoppingState_strict_times h K s a u b hh.1 hh.2
    omega
  simp only [ite_eq_right hn]

end MatchingCapacity
