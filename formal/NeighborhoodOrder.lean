import NeighborhoodPermutation

/-! An explicit swap of neighborhoods proves monotonicity of the literal
RANKING kernel without assuming a closed formula for its probabilities. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {m : ℕ}

theorem rankingPick_eq_some_iff (A N : Finset (Fin m)) (k : Fin m) :
    rankingPick A N = some k ↔ k ∈ A ∩ N ∧ ∀ l ∈ A ∩ N, k ≤ l := by
  constructor
  · intro hk
    have hn : (A ∩ N).Nonempty := by
      by_contra hn
      simp [rankingPick, hn] at hk
    have he : (A ∩ N).min' hn = k := by simpa [rankingPick, hn] using hk
    rw [← he]
    exact ⟨Finset.min'_mem _ hn, fun l hl => Finset.min'_le _ l hl⟩
  · rintro ⟨hk,hle⟩
    have hn : (A ∩ N).Nonempty := ⟨k,hk⟩
    have he : (A ∩ N).min' hn = k := le_antisymm (Finset.min'_le _ k hk) (hle _ (Finset.min'_mem _ hn))
    simp [rankingPick, hn, he]

theorem ranking_swap_improves (A N : Finset (Fin m)) (i j : Fin m)
    (hi : i ∈ A) (hij : i ≤ j) (hchoice : rankingPick A N = some j) :
    rankingPick A (permuteBins (Equiv.swap i j) N) = some i := by
  obtain ⟨hj,hle⟩ := (rankingPick_eq_some_iff A N j).mp hchoice
  apply (rankingPick_eq_some_iff _ _ _).mpr
  constructor
  · refine Finset.mem_inter.mpr ⟨hi,?_⟩
    simpa using (mem_permuteBins (Equiv.swap i j) N j).mpr (Finset.mem_inter.mp hj).2
  · intro k hk
    obtain ⟨hkA,hkN⟩ := Finset.mem_inter.mp hk
    by_cases hki : k = i
    · subst k; exact le_rfl
    by_cases hkj : k = j
    · subst k; exact hij
    have hkOld : k ∈ N := by
      rw [mem_permuteBins_iff] at hkN
      simpa [Equiv.swap_apply_of_ne_of_ne hki hkj] using hkN
    exact hij.trans (hle k (Finset.mem_inter.mpr ⟨hkA,hkOld⟩))

theorem rankingResponse_swap_le (A N : Finset (Fin m)) (i j : Fin m)
    (hi : i ∈ A) (hij : i ≤ j) :
    rankingResponse A N (some j) ≤ rankingResponse A (permuteBins (Equiv.swap i j) N) (some i) := by
  by_cases hc : rankingPick A N = some j
  · have h := ranking_swap_improves A N i j hi hij hc
    simp [rankingResponse, hc, h]
  · simp only [rankingResponse, ite_eq_right hc]
    split_ifs <;> norm_num

theorem rankingKernel_ordered_on_available (degree : ℕ) (A : Finset (Fin m))
    (i j : Fin m) (hi : i ∈ A) (hij : i ≤ j) : rankingKernel degree A (some j) ≤ rankingKernel degree A (some i) := by
  unfold rankingKernel neighborhoodKernel
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ N ∈ Finset.univ.powersetCard degree,
      rankingResponse A (permuteBins (Equiv.swap i j) N) (some i) :=
      Finset.sum_le_sum (fun N _ => rankingResponse_swap_le A N i j hi hij)
    _ = _ := neighborhood_sum_permutation (Equiv.swap i j) degree (fun N => rankingResponse A N (some i))

end MatchingCapacity
