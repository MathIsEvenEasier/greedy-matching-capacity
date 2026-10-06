import ResidualKernelRows
import HistoryFiber
import ConstantRows

/-! Saturation comparisons for the actual refined history laws. A fresh
successful choice is represented by its normalized residual kernel. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def refinedSaturation (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (v : ResidualBins D → ℚ) : ℚ :=
  (∑ h : historyFiber q D J f, historyWeight K q h.val *
    ∑ k : ResidualBins D, if historyLoad h.val n k.val = q then v k else 0) /
    (∑ h : historyFiber q D J f, historyWeight K q h.val)

theorem history_fiber_cap_mass_pos (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight K q h.val) :
    0 < assignmentEventMass (residualRows K q (D := D) J f) (assignmentCapped q) := by
  rw [history_fiber_total K D J f hf] at hm
  rcases mul_pos_iff.mp hm with h | h
  · exact h.2
  · have hk := fixedPathFactor_nonneg K hK q J f
    linarith [h.1]

theorem refined_saturation_eq (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight K q h.val)
    (v : ResidualBins D → ℚ) :
    refinedSaturation K q D J f v = nextSaturationProbability (residualRows K q (D := D) J f) v q := by
  unfold refinedSaturation
  rw [history_fiber_conditional_moment K hK D J f hf hm
    (fun h => ∑ k : ResidualBins D, if historyLoad h n k.val = q then v k else 0)]
  unfold nextSaturationProbability nextSaturationMass
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [complete_final_residual D J f hf]
  by_cases hd : ∀ k, assignmentLoad d k ≤ q
  · simp [ResidualCapped, assignmentCapped, hd, Finset.mul_sum, mul_ite]
  · simp only [ResidualCapped, assignmentCapped, hd, false_and, ite_false, Finset.sum_const_zero]

theorem history_available_complement (h : Fin n → Option (Fin m)) (q : ℕ) :
    historyAvailable q h n = (historyFullBins q h)ᶜ := by
  ext k
  simp [historyAvailable, historyFullBins, not_lt]

theorem history_fiber_final_availability (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1)
    (h : historyFiber q D J f) : historyAvailable q h.val n = Dᶜ := by
  rw [history_available_complement, history_fiber_full_bins D J f hD h]

theorem ranking_refined_saturation_bound (degree : Fin n → ℕ) (nextDegree : ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (hb : 0 < Fintype.card (ResidualBins D))
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => rankingKernel (degree j)) q h.val)
    (hn : 0 < ∑ k : ResidualBins D, rankingKernel nextDegree Dᶜ (some k.val)) :
    nextSaturationProbability (uniformRows (ι := ResidualJobs J) (Fintype.card (ResidualBins D)))
      (fun _ => 1/(Fintype.card (ResidualBins D) : ℚ)) q ≤
    refinedSaturation (fun j => rankingKernel (degree j)) q D J f (residualNextRow (rankingKernel nextDegree) D) := by
  rw [refined_saturation_eq _ (fun j A o => rankingKernel_nonneg (degree j) A o) D J f hf hm,
    ← next_saturation_relabel (residualOrder D).toEquiv]
  apply ordered_vs_uniform_saturation hb
  · intro j k
    exact rankingKernel_nonneg _ _ _
  · exact ranking_residual_rows_antitone degree D J f hf
  · exact ranking_residual_next_antitone nextDegree D hn
  · rw [(residualOrder D).toEquiv.sum_comp]
    exact residualNextRow_probability _ D hn
  · rw [assignment_cap_mass_relabel]
    exact history_fiber_cap_mass_pos _ (fun j A o => rankingKernel_nonneg (degree j) A o) D J f hf hm

theorem rv_refined_saturation_reference (degree : Fin n → ℕ) (nextDegree : ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (hb : 0 < Fintype.card (ResidualBins D))
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => rvKernel (degree j)) q h.val)
    (hn : 0 < ∑ k : ResidualBins D, rvKernel nextDegree Dᶜ (some k.val)) :
    refinedSaturation (fun j => rvKernel (degree j)) q D J f (residualNextRow (rvKernel nextDegree) D) =
    nextSaturationProbability (uniformRows (ι := ResidualJobs J) (Fintype.card (ResidualBins D)))
      (fun _ => 1/(Fintype.card (ResidualBins D) : ℚ)) q := by
  rw [refined_saturation_eq _ (fun j A o => rvKernel_nonneg (degree j) A o) D J f hf hm,
    ← next_saturation_relabel (residualOrder D).toEquiv]
  have hv : (fun k => residualNextRow (rvKernel nextDegree) D ((residualOrder D).toEquiv k)) =
      fun _ => 1/(Fintype.card (ResidualBins D) : ℚ) := by
    funext k
    exact rv_residual_next_uniform nextDegree D hn _
  rw [hv]
  apply constant_rows_eq_uniform hb
  · intro j i k
    exact rv_residual_rows_constant degree D J f hf j _ _
  · rw [assignment_cap_mass_relabel]
    exact history_fiber_cap_mass_pos _ (fun j A o => rvKernel_nonneg (degree j) A o) D J f hf hm

theorem rv_le_ranking_refined_saturation (rvDegree rkDegree : Fin n → ℕ) (rvNext rkNext : ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (rvFixed rkFixed : Fin n → Option (Fin m))
    (hrv : FixedSupported D J rvFixed) (hrk : FixedSupported D J rkFixed)
    (hb : 0 < Fintype.card (ResidualBins D))
    (hmrv : 0 < ∑ h : historyFiber q D J rvFixed, historyWeight (fun j => rvKernel (rvDegree j)) q h.val)
    (hmrk : 0 < ∑ h : historyFiber q D J rkFixed, historyWeight (fun j => rankingKernel (rkDegree j)) q h.val)
    (hnrv : 0 < ∑ k : ResidualBins D, rvKernel rvNext Dᶜ (some k.val))
    (hnrk : 0 < ∑ k : ResidualBins D, rankingKernel rkNext Dᶜ (some k.val)) :
    refinedSaturation (fun j => rvKernel (rvDegree j)) q D J rvFixed (residualNextRow (rvKernel rvNext) D) ≤
    refinedSaturation (fun j => rankingKernel (rkDegree j)) q D J rkFixed (residualNextRow (rankingKernel rkNext) D) := by
  rw [rv_refined_saturation_reference rvDegree rvNext D J rvFixed hrv hb hmrv hnrv]
  exact ranking_refined_saturation_bound rkDegree rkNext D J rkFixed hrk hb hmrk hnrk

end MatchingCapacity
