import IndependentNeighborhoods

/-! Literal source model: independent uniform neighborhoods, one uniformly
random arrival permutation and one independent uniformly random bin ranking.
Capacity is q+1. The theorem holds for every finite size and every threshold. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m : ℕ}

def uniformAverage {α : Type*} [Fintype α] (f : α → ℚ) : ℚ :=
  (∑ a, f a) / (Fintype.card α : ℚ)

theorem uniform_average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℚ) :
    uniformAverage (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [uniformAverage,hc]

theorem uniform_average_mono {α : Type*} [Fintype α] (f g : α → ℚ)
    (h : ∀ a, f a ≤ g a) : uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem uniform_average_nonneg {α : Type*} [Fintype α] (f : α → ℚ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformAverage f := by
  unfold uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (by positivity)

theorem uniform_average_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℚ) :
    uniformAverage (fun a => ∑ b, f a b) = ∑ b, uniformAverage (fun a => f a b) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem matching_tail_average {α : Type*} [Fintype α] [Nonempty α]
    (w : α → (Fin n → Option (Fin m)) → ℚ) (K : ℕ) :
    matchingTail (fun h => uniformAverage (fun a => w a h)) K =
      uniformAverage (fun a => matchingTail (w a) K) := by
  unfold matchingTail
  rw [uniform_average_sum]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hc : K ≤ acceptedCount h
  · simp only [ite_eq_left hc]
  · simp only [ite_eq_right hc, uniform_average_const]

/-- Sample the original independent neighborhoods and an independent arrival order. -/
def sourceRVHistory (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m)) : ℚ :=
  uniformAverage (fun order : Equiv.Perm (Fin n) =>
    orderedGraphHistoryMass rvResponse degree order q h)

/-- The rank permutation is sampled once outside the entire history product. -/
def sourceRankingHistory (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m)) : ℚ :=
  uniformAverage (fun order : Equiv.Perm (Fin n) =>
    uniformAverage (fun rank : Equiv.Perm (Fin m) =>
      orderedGraphHistoryMass (priorityResponse rank) degree order q h))

theorem source_rv_probability (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) (q : ℕ) :
    (∑ h : Fin n → Option (Fin m), sourceRVHistory degree q h) = 1 := by
  unfold sourceRVHistory
  simp only [ordered_graph_history_identity]
  rw [← uniform_average_sum]
  simp only [graph_history_probability rvResponse rvResponse_probability _ (fun j => hd _) q,
    uniform_average_const]

theorem source_ranking_probability (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) (q : ℕ) :
    (∑ h : Fin n → Option (Fin m), sourceRankingHistory degree q h) = 1 := by
  unfold sourceRankingHistory
  simp only [ordered_graph_history_identity]
  rw [← uniform_average_sum]
  simp only [← uniform_average_sum]
  simp only [graph_history_probability _ (priority_response_probability _) _ (fun j => hd _) q,
    uniform_average_const]

theorem source_rv_nonneg (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m)) :
    0 ≤ sourceRVHistory degree q h := by
  apply uniform_average_nonneg
  intro order
  rw [ordered_graph_history_identity]
  exact graph_history_nonneg rvResponse rvResponse_nonneg _ q h

theorem source_ranking_nonneg (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m)) :
    0 ≤ sourceRankingHistory degree q h := by
  apply uniform_average_nonneg
  intro order
  apply uniform_average_nonneg
  intro rank
  rw [ordered_graph_history_identity]
  exact graph_history_nonneg _ (fun A S o => rankingResponse_nonneg _ _ _) _ q h

/-- Arnosti's source-model comparison, simultaneously for every natural threshold.
The only data restriction is that each job degree fits the bin set.
All positive common capacities are represented by q+1. -/
theorem source_matching_tail_comparison (degree : Fin n → ℕ)
    (hd : ∀ j, degree j ≤ m) (q K : ℕ) :
    matchingTail (sourceRankingHistory (m := m) degree q) K ≤
      matchingTail (sourceRVHistory (m := m) degree q) K := by
  unfold sourceRankingHistory sourceRVHistory
  rw [matching_tail_average, matching_tail_average]
  apply uniform_average_mono
  intro order
  rw [matching_tail_average]
  unfold matchingTail
  simp only [ordered_graph_history_identity, graph_history_kernel_identity]
  change uniformAverage (fun rank : Equiv.Perm (Fin m) =>
    matchingTail (historyWeight (fun j => priorityKernel rank (degree (order j))) q) K) ≤
      matchingTail (historyWeight (fun j => rvKernel (m := m) (degree (order j))) q) K
  rw [← uniform_average_const (α := Equiv.Perm (Fin m))
    (matchingTail (historyWeight (fun j => rvKernel (m := m) (degree (order j))) q) K)]
  apply uniform_average_mono
  intro rank
  exact arbitrary_priority_matching_tail_comparison rank _ (fun j => hd (order j)) q K

end MatchingCapacity
