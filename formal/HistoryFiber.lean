import HistoryFactorization

/-! A genuine bijection between a refined history fiber and residual
assignments satisfying the cap. This justifies summing actual histories,
rather than postulating a conditional categorical law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def HistoryRefines (D : Finset (Fin m)) (J : Finset (Fin n))
    (f h : Fin n → Option (Fin m)) : Prop :=
  (∀ j, j ∉ J → h j = f j) ∧ (∀ j, j ∈ J → ∃ k : ResidualBins D, h j = some k.val)

def extractResidual {D : Finset (Fin m)} {J : Finset (Fin n)}
    {f h : Fin n → Option (Fin m)} (hh : HistoryRefines D J f h)
    (j : ResidualJobs J) : ResidualBins D := (hh.2 j.val j.property).choose

theorem extractResidual_spec {D : Finset (Fin m)} {J : Finset (Fin n)}
    {f h : Fin n → Option (Fin m)} (hh : HistoryRefines D J f h) (j : ResidualJobs J) :
    h j.val = some (extractResidual hh j).val := (hh.2 j.val j.property).choose_spec

theorem complete_refines (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (d : ResidualJobs J → ResidualBins D) :
    HistoryRefines D J f (completeHistory J f d) := by
  constructor
  · intro j hj
    exact completeHistory_fixed J f d hj
  · intro j hj
    exact ⟨d ⟨j,hj⟩, completeHistory_free J f d ⟨j,hj⟩⟩

theorem complete_extract {D : Finset (Fin m)} {J : Finset (Fin n)}
    {f h : Fin n → Option (Fin m)} (hh : HistoryRefines D J f h) :
    completeHistory J f (extractResidual hh) = h := by
  funext j
  by_cases hj : j ∈ J
  · exact (completeHistory_free J f _ ⟨j,hj⟩).trans (extractResidual_spec hh ⟨j,hj⟩).symm
  · exact (completeHistory_fixed J f _ hj).trans (hh.1 j hj).symm

theorem extract_complete (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (d : ResidualJobs J → ResidualBins D) :
    extractResidual (complete_refines D J f d) = d := by
  apply completeHistory_injective J f D
  exact complete_extract _

abbrev historyFiber (q : ℕ) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) :=
  {h : Fin n → Option (Fin m) // HistoryRefines D J f h ∧
    ∀ k : ResidualBins D, historyLoad h n k.val ≤ q}

def historyFiberEquiv (q : ℕ) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f) :
    {d : ResidualJobs J → ResidualBins D // ResidualCapped q d} ≃ historyFiber q D J f where
  toFun d := ⟨completeHistory J f d.val, complete_refines D J f d.val,
    (complete_residual_cap_iff D J f hf d.val).mpr d.property⟩
  invFun h := ⟨extractResidual h.property.1, (complete_residual_cap_iff D J f hf _).mp (by
    rw [complete_extract h.property.1]
    exact h.property.2)⟩
  left_inv d := by
    apply Subtype.ext
    exact extract_complete D J f d.val
  right_inv h := by
    apply Subtype.ext
    exact complete_extract h.property.1

theorem history_fiber_moment (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (G : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : historyFiber q D J f, historyWeight K q h.val * G h.val) =
      ∑ d : ResidualJobs J → ResidualBins D, refinedPathWeight K q (D := D) J f d * G (completeHistory J f d) := by
  rw [← (historyFiberEquiv q D J f hf).sum_comp (fun h => historyWeight K q h.val * G h.val)]
  change (∑ d : {d : ResidualJobs J → ResidualBins D // ResidualCapped q d},
    historyWeight K q (completeHistory J f d.val) * G (completeHistory J f d.val)) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (ResidualCapped q)) (by simp)
    (fun d => historyWeight K q (completeHistory J f d) * G (completeHistory J f d)), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : ResidualCapped q d <;> simp [refinedPathWeight, hd]

theorem history_fiber_total (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f) :
    (∑ h : historyFiber q D J f, historyWeight K q h.val) =
      fixedPathFactor K q J f * assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) := by
  have h := history_fiber_moment (q := q) K D J f hf (fun _ => 1)
  simp only [mul_one] at h
  exact h.trans (refined_path_total K D J f hf)

theorem history_fiber_conditional_moment (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight K q h.val)
    (G : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : historyFiber q D J f, historyWeight K q h.val * G h.val) /
      (∑ h : historyFiber q D J f, historyWeight K q h.val) =
    (∑ d, if ResidualCapped q d then
      assignmentWeight (residualRows K q (D := D) J f) d * G (completeHistory J f d) else 0) /
      assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) := by
  have ht := history_fiber_moment (q := q) K D J f hf (fun _ => 1)
  simp only [mul_one] at ht
  rw [ht] at hm
  rw [history_fiber_moment K D J f hf, ht]
  exact refined_conditional_moment K hK D J f hf hm (fun d => G (completeHistory J f d))

def historyFreeJobs (D : Finset (Fin m)) (h : Fin n → Option (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ k : ResidualBins D, h j = some k.val)

def historyFullBins (q : ℕ) (h : Fin n → Option (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun k => q < historyLoad h n k)

theorem history_anchor_supported (D : Finset (Fin m)) (h : Fin n → Option (Fin m)) :
    FixedSupported D (historyFreeJobs D h) h := by
  intro j hj k hk
  by_contra hn
  apply hj
  simp only [historyFreeJobs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨k,hn⟩,hk⟩

theorem history_anchor_refines (D : Finset (Fin m)) (h : Fin n → Option (Fin m)) :
    HistoryRefines D (historyFreeJobs D h) h h := by
  constructor
  · intros; rfl
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

theorem history_anchor_capped (q : ℕ) (h : Fin n → Option (Fin m)) :
    ∀ k : ResidualBins (historyFullBins q h), historyLoad h n k.val ≤ q := by
  intro k
  have hk := k.property
  simp only [historyFullBins, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
  exact hk

theorem history_anchor_member (q : ℕ) (h : Fin n → Option (Fin m)) :
    HistoryRefines (historyFullBins q h) (historyFreeJobs (historyFullBins q h) h) h h ∧
      ∀ k : ResidualBins (historyFullBins q h), historyLoad h n k.val ≤ q :=
  ⟨history_anchor_refines _ h, history_anchor_capped q h⟩

theorem history_full_bin_load (q : ℕ) (h : Fin n → Option (Fin m))
    (hc : ∀ k, historyLoad h n k ≤ q+1) (k : Fin m) (hk : k ∈ historyFullBins q h) :
    historyLoad h n k = q+1 := by
  have hl := (Finset.mem_filter.mp hk).2
  have hu := hc k
  omega

theorem history_anchor_fixed_load (D : Finset (Fin m)) (h : Fin n → Option (Fin m))
    (k : Fin m) (hk : k ∈ D) :
    historyLoad (fixedHistory (historyFreeJobs D h) h) n k = historyLoad h n k := by
  have he := complete_load_in_D D (historyFreeJobs D h) h
    (extractResidual (history_anchor_refines D h)) n k hk
  rw [complete_extract] at he
  exact he.symm

theorem history_fiber_full_bins (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1)
    (h : historyFiber q D J f) : historyFullBins q h.val = D := by
  ext k
  simp only [historyFullBins, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k ∈ D
  · have he := complete_load_in_D D J f (extractResidual h.property.1) n k hk
    rw [complete_extract] at he
    rw [he, hD k hk]
    exact iff_of_true (Nat.lt_succ_self q) hk
  · exact iff_of_false (Nat.not_lt.mpr (h.property.2 ⟨k,hk⟩)) hk

theorem rv_refined_history_law (degree : Fin n → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => rvKernel (degree j)) q h.val)
    (G : (Fin n → Option (Fin m)) → ℚ) :
    let K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ := fun j => rvKernel (degree j)
    (∑ h : historyFiber q D J f, historyWeight K q h.val * G h.val) /
      (∑ h : historyFiber q D J f, historyWeight K q h.val) =
    (∑ d : ResidualJobs J → ResidualBins D, if ResidualCapped q d then
      assignmentWeight (residualRows K q (D := D) J f) d * G (completeHistory J f d) else 0) /
      assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) :=
  history_fiber_conditional_moment _ (fun j A o => rvKernel_nonneg (degree j) A o) D J f hf hm G

theorem ranking_refined_history_law (degree : Fin n → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => rankingKernel (degree j)) q h.val)
    (G : (Fin n → Option (Fin m)) → ℚ) :
    let K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ := fun j => rankingKernel (degree j)
    (∑ h : historyFiber q D J f, historyWeight K q h.val * G h.val) /
      (∑ h : historyFiber q D J f, historyWeight K q h.val) =
    (∑ d : ResidualJobs J → ResidualBins D, if ResidualCapped q d then
      assignmentWeight (residualRows K q (D := D) J f) d * G (completeHistory J f d) else 0) /
      assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) :=
  history_fiber_conditional_moment _ (fun j A o => rankingKernel_nonneg (degree j) A o) D J f hf hm G

end MatchingCapacity
