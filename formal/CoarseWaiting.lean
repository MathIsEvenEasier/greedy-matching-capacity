import CoarseSaturation

/-! The coarse prefix event has the concrete common waiting law, including
its finite-horizon no-further-success outcome. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def coarseHistoryMass (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (n q K a : ℕ) : ℚ :=
  ∑ h : LegalHistory n m q, if AcceptedPrefix q K a h.val then historyWeight (fun j => L j.val) q h.val else 0

def coarseNeverMass (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (n q K a N : ℕ) : ℚ :=
  ∑ h : LegalHistory n m q, if AcceptedPrefix q K a h.val then
    historyWeight (fun j => L j.val) q (rejectExtension h.val N) else 0

def countWaitingFactor (degree : ℕ → ℕ) (m n a t : ℕ) : ℚ :=
  (∏ j ∈ Finset.range t, (Nat.choose a (degree (n+j)) : ℚ) / (Nat.choose m (degree (n+j)) : ℚ)) *
    (1 - (Nat.choose a (degree (n+t)) : ℚ) / (Nat.choose m (degree (n+t)) : ℚ))

theorem coarse_history_partition (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (K a : ℕ) :
    coarseHistoryMass L n q K a = ∑ r : GoodRefinement n m q, if KeyPrefix q K a r.val then
      ∑ h : KeyFiber q r.val, historyWeight (fun j => L j.val) q h.val else 0 := by
  exact accepted_prefix_partition K a _

theorem coarse_never_partition (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (K a N : ℕ) :
    coarseNeverMass L n q K a N = ∑ r : GoodRefinement n m q, if KeyPrefix q K a r.val then
      fiberNeverMass L q r.val.1 r.val.2.1 r.val.2.2 N else 0 := by
  exact accepted_prefix_partition (q := q) K a (fun h => historyWeight (fun j => L j.val) q (rejectExtension h N))

theorem coarse_rv_waiting_mass (degree : ℕ → ℕ) (K a t : ℕ) (hd : degree (n+t) ≤ m) :
    coarseNextMoment (fun j => rvKernel (m := m) (degree j)) n q K a t (fun _ _ => 1) =
      countWaitingFactor degree m n a t * coarseHistoryMass (fun j => rvKernel (m := m) (degree j)) n q K a := by
  rw [coarse_next_partition, coarse_history_partition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : KeyPrefix q K a r.val
  · simp only [ite_eq_left hp]
    rw [fiber_next_mass (fun j => rvKernel (m := m) (degree j)) r.val.1 r.val.2.1 r.val.2.2 r.property.2.2 t,
      rv_residual_success_formula (degree (n+t)) hd r.val.1]
    simp only [waitingWeight, rv_rejection_formula, compl_compl, hp.2.1, countWaitingFactor]
    ring
  · simp [hp]

theorem coarse_ranking_waiting_mass (degree : ℕ → ℕ) (K a t : ℕ) (hd : degree (n+t) ≤ m) :
    coarseNextMoment (fun j => rankingKernel (m := m) (degree j)) n q K a t (fun _ _ => 1) =
      countWaitingFactor degree m n a t * coarseHistoryMass (fun j => rankingKernel (m := m) (degree j)) n q K a := by
  rw [coarse_next_partition, coarse_history_partition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : KeyPrefix q K a r.val
  · simp only [ite_eq_left hp]
    rw [fiber_next_mass (fun j => rankingKernel (m := m) (degree j)) r.val.1 r.val.2.1 r.val.2.2 r.property.2.2 t,
      ranking_residual_success_formula (degree (n+t)) hd r.val.1]
    simp only [waitingWeight, ranking_rejection_formula, compl_compl, hp.2.1, countWaitingFactor]
    ring
  · simp [hp]

theorem coarse_rv_waiting_law (degree : ℕ → ℕ) (K a t : ℕ) (hd : degree (n+t) ≤ m)
    (hm : 0 < coarseHistoryMass (fun j => rvKernel (m := m) (degree j)) n q K a) :
    coarseNextMoment (fun j => rvKernel (m := m) (degree j)) n q K a t (fun _ _ => 1) /
      coarseHistoryMass (fun j => rvKernel (m := m) (degree j)) n q K a = countWaitingFactor degree m n a t := by
  rw [coarse_rv_waiting_mass degree K a t hd]
  exact mul_div_cancel_right₀ _ (ne_of_gt hm)

theorem coarse_ranking_waiting_law (degree : ℕ → ℕ) (K a t : ℕ) (hd : degree (n+t) ≤ m)
    (hm : 0 < coarseHistoryMass (fun j => rankingKernel (m := m) (degree j)) n q K a) :
    coarseNextMoment (fun j => rankingKernel (m := m) (degree j)) n q K a t (fun _ _ => 1) /
      coarseHistoryMass (fun j => rankingKernel (m := m) (degree j)) n q K a = countWaitingFactor degree m n a t := by
  rw [coarse_ranking_waiting_mass degree K a t hd]
  exact mul_div_cancel_right₀ _ (ne_of_gt hm)

theorem coarse_next_or_never_total (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K a N : ℕ) (hL : ∀ j A, ∑ o, L j A o = 1)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0) :
    (∑ t ∈ Finset.range N, coarseNextMoment L n q K a t (fun _ _ => 1)) + coarseNeverMass L n q K a N =
      coarseHistoryMass L n q K a := by
  simp only [coarse_next_partition, coarse_never_partition, coarse_history_partition]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : KeyPrefix q K a r.val
  · simp only [ite_eq_left hp]
    exact fiber_next_or_never_total L r.val.1 r.val.2.1 r.val.2.2 r.property.2.2 N
      (fun t _ => hL (n+t) r.val.1ᶜ) (fun t _ k hk => hz (n+t) r.val.1ᶜ k hk)
  · simp [hp]

end MatchingCapacity
