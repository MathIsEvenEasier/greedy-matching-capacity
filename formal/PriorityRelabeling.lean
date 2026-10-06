import FixedPriorityComparison
import NeighborhoodPermutation
import Mathlib.Logic.Equiv.Option

/-! A priority permutation maps bin labels to their ranks. The same permutation
acts on every outcome in a history; it preserves loads and matching size. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m : ℕ}

def relabelHistory (e : Equiv.Perm (Fin m)) (h : Fin n → Option (Fin m)) :
    Fin n → Option (Fin m) := fun j => Equiv.optionCongr e (h j)

def historyRelabelEquiv (e : Equiv.Perm (Fin m)) : Equiv.Perm (Fin n → Option (Fin m)) where
  toFun := relabelHistory e
  invFun := relabelHistory e.symm
  left_inv := by intro h; funext j; cases ho : h j <;> simp [relabelHistory, Equiv.optionCongr, ho]
  right_inv := by intro h; funext j; cases ho : h j <;> simp [relabelHistory, Equiv.optionCongr, ho]

theorem relabel_history_load (e : Equiv.Perm (Fin m)) (h : Fin n → Option (Fin m))
    (t : ℕ) (k : Fin m) : historyLoad (relabelHistory e h) t (e k) = historyLoad h t k := by
  unfold historyLoad
  apply Finset.sum_congr rfl
  intro j _
  have he : relabelHistory e h j = some (e k) ↔ h j = some k := by
    cases ho : h j <;> simp [relabelHistory, Equiv.optionCongr, ho]
  simp only [he]

theorem relabel_history_available (e : Equiv.Perm (Fin m)) (q : ℕ)
    (h : Fin n → Option (Fin m)) (t : ℕ) :
    historyAvailable q (relabelHistory e h) t = permuteBins e (historyAvailable q h t) := by
  ext k
  obtain ⟨i,rfl⟩ := e.surjective k
  rw [mem_permuteBins]
  simp only [historyAvailable, Finset.mem_filter, Finset.mem_univ, true_and, relabel_history_load]

theorem relabel_accepted_count (e : Equiv.Perm (Fin m)) (h : Fin n → Option (Fin m)) :
    acceptedCount (relabelHistory e h) = acceptedCount h := by
  unfold acceptedCount
  apply Finset.sum_congr rfl
  intro j _
  cases ho : h j <;> simp [relabelHistory, Equiv.optionCongr, ho]

/-- Literal ranked choice: map labels to ranks, take the least available rank. -/
def priorityResponse (e : Equiv.Perm (Fin m)) (A N : Finset (Fin m))
    (o : Option (Fin m)) : ℚ :=
  rankingResponse (permuteBins e A) (permuteBins e N) (Equiv.optionCongr e o)

def priorityKernel (e : Equiv.Perm (Fin m)) (degree : ℕ) :=
  neighborhoodKernel (priorityResponse e) degree

theorem priority_response_choice (e : Equiv.Perm (Fin m)) (A N : Finset (Fin m))
    (k : Fin m) : priorityResponse e A N (some k) = 1 ↔
      k ∈ A ∩ N ∧ ∀ i ∈ A ∩ N, e k ≤ e i := by
  unfold priorityResponse rankingResponse rankingPick
  rw [← permuteBins_inter]
  by_cases h : (permuteBins e (A ∩ N)).Nonempty
  · rw [dite_eq_left h]
    change (if some ((permuteBins e (A ∩ N)).min' h) = some (e k) then (1 : ℚ) else 0) = 1 ↔ _
    simp only [Option.some.injEq, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
    constructor
    · intro he
      constructor
      · rw [← mem_permuteBins e (A ∩ N) k, ← he]
        exact Finset.min'_mem _ _
      · intro i hi
        rw [← he]
        exact Finset.min'_le _ _ ((mem_permuteBins e (A ∩ N) i).mpr hi)
    · rintro ⟨hk,hle⟩
      apply le_antisymm
      · exact Finset.min'_le _ _ ((mem_permuteBins e (A ∩ N) k).mpr hk)
      · obtain ⟨i,hi,he⟩ := Finset.mem_map.mp (Finset.min'_mem (permuteBins e (A ∩ N)) h)
        exact he ▸ hle i hi
  · rw [dite_eq_right h]
    change (if none = some (e k) then (1 : ℚ) else 0) = 1 ↔ _
    simp only [reduceCtorEq, ite_false, zero_ne_one, false_iff, not_and]
    intro hk _
    exact h ⟨e k, (mem_permuteBins e (A ∩ N) k).mpr hk⟩

theorem priority_kernel_relabel (e : Equiv.Perm (Fin m)) (degree : ℕ)
    (A : Finset (Fin m)) (o : Option (Fin m)) :
    priorityKernel e degree A o = rankingKernel degree (permuteBins e A) (Equiv.optionCongr e o) := by
  unfold priorityKernel neighborhoodKernel priorityResponse rankingKernel
  unfold neighborhoodKernel
  rw [neighborhood_sum_permutation e degree
    (fun S => rankingResponse (permuteBins e A) S (Equiv.optionCongr e o))]

theorem priority_history_relabel (e : Equiv.Perm (Fin m)) (degree : Fin n → ℕ)
    (q : ℕ) (h : Fin n → Option (Fin m)) :
    historyWeight (fun j => priorityKernel e (degree j)) q h =
      historyWeight (fun j => rankingKernel (m := m) (degree j)) q (relabelHistory e h) := by
  unfold historyWeight
  apply Finset.prod_congr rfl
  intro j _
  dsimp only
  rw [priority_kernel_relabel, relabel_history_available]
  rfl

def matchingTail (w : (Fin n → Option (Fin m)) → ℚ) (K : ℕ) : ℚ :=
  ∑ h, if K ≤ acceptedCount h then w h else 0

theorem priority_matching_tail (e : Equiv.Perm (Fin m)) (degree : Fin n → ℕ) (q K : ℕ) :
    matchingTail (historyWeight (fun j => priorityKernel e (degree j)) q) K =
      matchingTail (historyWeight (fun j => rankingKernel (m := m) (degree j)) q) K := by
  unfold matchingTail
  apply Fintype.sum_equiv (historyRelabelEquiv e)
  intro h
  change (if K ≤ acceptedCount h then _ else _) =
    (if K ≤ acceptedCount (relabelHistory e h) then _ else _)
  rw [relabel_accepted_count, priority_history_relabel]
  rfl

theorem finite_degree_matching_tail_comparison (degree : Fin n → ℕ)
    (hd : ∀ j, degree j ≤ m) (q K : ℕ) :
    matchingTail (historyWeight (fun j => rankingKernel (m := m) (degree j)) q) K ≤
      matchingTail (historyWeight (fun j => rvKernel (m := m) (degree j)) q) K := by
  let d : ℕ → ℕ := fun j => if hj : j < n then degree ⟨j,hj⟩ else 0
  have hb : ∀ j, d j ≤ m := by
    intro j
    dsimp [d]
    split_ifs with hj
    · exact hd ⟨j,hj⟩
    · exact Nat.zero_le m
  have he : ∀ j : Fin n, d j.val = degree j := by intro j; simp [d,j.isLt]
  simpa only [matchingTail, he] using fixed_priority_matching_tail_comparison d hb n q K

theorem arbitrary_priority_matching_tail_comparison (e : Equiv.Perm (Fin m))
    (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) (q K : ℕ) :
    matchingTail (historyWeight (fun j => priorityKernel e (degree j)) q) K ≤
      matchingTail (historyWeight (fun j => rvKernel (m := m) (degree j)) q) K := by
  rw [priority_matching_tail]
  exact finite_degree_matching_tail_comparison degree hd q K

end MatchingCapacity
