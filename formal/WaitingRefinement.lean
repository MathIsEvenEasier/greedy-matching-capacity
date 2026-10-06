import HistoryExtension
import RejectionKernel

/-! Conditioning also on the next-success index preserves the refined
old-history law and gives the actual normalized fresh-choice kernel. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def fiberNextMoment (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (t : ℕ) (G : (Fin n → Option (Fin m)) → ResidualBins D → ℚ) : ℚ :=
  ∑ h : historyFiber q D J f, ∑ k : ResidualBins D,
    historyWeight (fun j => K j.val) q (acceptedExtension h.val t k.val) * G h.val k

theorem fiber_next_moment (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1)
    (t : ℕ) (G : (Fin n → Option (Fin m)) → ResidualBins D → ℚ) :
    fiberNextMoment K q D J f t G = waitingWeight K Dᶜ n t *
      ∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val *
        ∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val) * G h.val k := by
  unfold fiberNextMoment
  simp only [acceptedExtension_fiber_weight K D J f hD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem fiber_next_mass (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ) :
    fiberNextMoment K q D J f t (fun _ _ => 1) =
      waitingWeight K Dᶜ n t * (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) *
        (∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val)) := by
  rw [fiber_next_moment K D J f hD]
  simp only [mul_one, ← Finset.sum_mul, mul_assoc]

theorem fiber_next_positive_factors (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < fiberNextMoment K q D J f t (fun _ _ => 1)) :
    (0 < ∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) ∧
      0 < waitingWeight K Dᶜ n t ∧ 0 < ∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val) := by
  rw [fiber_next_mass K D J f hD] at hm
  have hw := waitingWeight_nonneg K hK Dᶜ n t
  have hs : 0 ≤ ∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val) :=
    Finset.sum_nonneg (fun k _ => hK _ _ _)
  rcases mul_pos_iff.mp hm with hp | hp
  · rcases mul_pos_iff.mp hp.1 with hh | hh
    · exact ⟨hh.2,hh.1,hp.2⟩
    · linarith [hh.1]
  · linarith [hp.2]

theorem fiber_next_conditional_moment (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < fiberNextMoment K q D J f t (fun _ _ => 1))
    (G : (Fin n → Option (Fin m)) → ResidualBins D → ℚ) :
    fiberNextMoment K q D J f t G / fiberNextMoment K q D J f t (fun _ _ => 1) =
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val *
        ∑ k : ResidualBins D, residualNextRow (K (n+t)) D k * G h.val k) /
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) := by
  obtain ⟨hh,hw,hs⟩ := fiber_next_positive_factors K hK D J f hD t hm
  have he : (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val *
      ∑ k : ResidualBins D, residualNextRow (K (n+t)) D k * G h.val k) =
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val *
      ∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val) * G h.val k) /
        (∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val)) := by
    simp only [residualNextRow, div_mul_eq_mul_div, ← Finset.sum_div, ← mul_div_assoc]
  rw [he, fiber_next_moment K D J f hD, fiber_next_mass K D J f hD]
  field_simp

theorem fiber_next_old_law (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < fiberNextMoment K q D J f t (fun _ _ => 1))
    (F : (Fin n → Option (Fin m)) → ℚ) :
    fiberNextMoment K q D J f t (fun h _ => F h) / fiberNextMoment K q D J f t (fun _ _ => 1) =
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val * F h.val) /
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) := by
  rw [fiber_next_conditional_moment K hK D J f hD t hm]
  have hs := (fiber_next_positive_factors K hK D J f hD t hm).2.2
  simp only [← Finset.sum_mul, residualNextRow_probability _ D hs, one_mul]

def fiberNextSaturation (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (t : ℕ) : ℚ :=
  fiberNextMoment K q D J f t (fun h k => if historyLoad h n k.val = q then 1 else 0) /
    fiberNextMoment K q D J f t (fun _ _ => 1)

theorem fiber_next_saturation_eq (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < fiberNextMoment K q D J f t (fun _ _ => 1)) :
    fiberNextSaturation K q D J f t =
      refinedSaturation (fun j => K j.val) q D J f (residualNextRow (K (n+t)) D) := by
  unfold fiberNextSaturation
  rw [fiber_next_conditional_moment K hK D J f hD t hm]
  simp only [refinedSaturation, mul_ite, mul_one, mul_zero]

theorem ranking_next_success_saturation_bound (degree : ℕ → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (hb : 0 < Fintype.card (ResidualBins D))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < fiberNextMoment (fun j => rankingKernel (degree j)) q D J f t (fun _ _ => 1)) :
    nextSaturationProbability (uniformRows (ι := ResidualJobs J) (Fintype.card (ResidualBins D)))
      (fun _ => 1/(Fintype.card (ResidualBins D) : ℚ)) q ≤
      fiberNextSaturation (fun j => rankingKernel (degree j)) q D J f t := by
  have hp := fiber_next_positive_factors _ (fun j A o => rankingKernel_nonneg (degree j) A o) D J f hD t hm
  rw [fiber_next_saturation_eq _ (fun j A o => rankingKernel_nonneg (degree j) A o) D J f hD t hm]
  exact ranking_refined_saturation_bound (fun j => degree j.val) (degree (n+t)) D J f hf hb hp.1 hp.2.2

theorem rv_next_success_saturation_reference (degree : ℕ → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (hb : 0 < Fintype.card (ResidualBins D))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < fiberNextMoment (fun j => rvKernel (degree j)) q D J f t (fun _ _ => 1)) :
    fiberNextSaturation (fun j => rvKernel (degree j)) q D J f t =
      nextSaturationProbability (uniformRows (ι := ResidualJobs J) (Fintype.card (ResidualBins D)))
      (fun _ => 1/(Fintype.card (ResidualBins D) : ℚ)) q := by
  have hp := fiber_next_positive_factors _ (fun j A o => rvKernel_nonneg (degree j) A o) D J f hD t hm
  rw [fiber_next_saturation_eq _ (fun j A o => rvKernel_nonneg (degree j) A o) D J f hD t hm]
  exact rv_refined_saturation_reference (fun j => degree j.val) (degree (n+t)) D J f hf hb hp.1 hp.2.2

theorem fiber_next_waiting_law (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) :
    fiberNextMoment K q D J f t (fun _ _ => 1) /
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) =
      waitingWeight K Dᶜ n t * (∑ k : ResidualBins D, K (n+t) Dᶜ (some k.val)) := by
  rw [fiber_next_mass K D J f hD]
  field_simp

theorem rv_fiber_waiting_formula (degree : ℕ → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ) (hd : degree (n+t) ≤ m)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => rvKernel (degree j.val)) q h.val) :
    fiberNextMoment (fun j => rvKernel (degree j)) q D J f t (fun _ _ => 1) /
      (∑ h : historyFiber q D J f, historyWeight (fun j => rvKernel (degree j.val)) q h.val) =
      (∏ j ∈ Finset.range t, (Nat.choose D.card (degree (n+j)) : ℚ) / (Nat.choose m (degree (n+j)) : ℚ)) *
        (1 - (Nat.choose D.card (degree (n+t)) : ℚ) / (Nat.choose m (degree (n+t)) : ℚ)) := by
  rw [fiber_next_waiting_law (fun j => rvKernel (degree j)) D J f hD t hm]
  rw [rv_residual_success_formula (degree (n+t)) hd D]
  simp only [waitingWeight, rv_rejection_formula, compl_compl]

theorem ranking_fiber_waiting_formula (degree : ℕ → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ) (hd : degree (n+t) ≤ m)
    (hm : 0 < ∑ h : historyFiber q D J f, historyWeight (fun j => rankingKernel (degree j.val)) q h.val) :
    fiberNextMoment (fun j => rankingKernel (degree j)) q D J f t (fun _ _ => 1) /
      (∑ h : historyFiber q D J f, historyWeight (fun j => rankingKernel (degree j.val)) q h.val) =
      (∏ j ∈ Finset.range t, (Nat.choose D.card (degree (n+j)) : ℚ) / (Nat.choose m (degree (n+j)) : ℚ)) *
        (1 - (Nat.choose D.card (degree (n+t)) : ℚ) / (Nat.choose m (degree (n+t)) : ℚ)) := by
  rw [fiber_next_waiting_law (fun j => rankingKernel (degree j)) D J f hD t hm]
  rw [ranking_residual_success_formula (degree (n+t)) hd D]
  simp only [waitingWeight, ranking_rejection_formula, compl_compl]

def fiberNeverMass (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (N : ℕ) : ℚ :=
  ∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q (rejectExtension h.val N)

theorem fiber_never_mass (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (N : ℕ) :
    fiberNeverMass K q D J f N =
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) * waitingWeight K Dᶜ n N := by
  unfold fiberNeverMass
  simp only [rejectExtension_weight, history_fiber_final_availability D J f hD, Finset.sum_mul]

theorem fiber_next_mass_firstSuccess (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (t : ℕ)
    (hK : ∑ o, K (n+t) Dᶜ o = 1) (hz : ∀ k, k ∉ Dᶜ → K (n+t) Dᶜ (some k) = 0) :
    fiberNextMoment K q D J f t (fun _ _ => 1) =
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) * firstSuccessMass K Dᶜ n t := by
  rw [fiber_next_mass K D J f hD, residual_success_mass _ D hK hz,
    firstSuccessMass, successMass_eq _ Dᶜ hK]
  ring

theorem fiber_next_or_never_total (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (N : ℕ)
    (hK : ∀ t < N, ∑ o, K (n+t) Dᶜ o = 1)
    (hz : ∀ t < N, ∀ k, k ∉ Dᶜ → K (n+t) Dᶜ (some k) = 0) :
    (∑ t ∈ Finset.range N, fiberNextMoment K q D J f t (fun _ _ => 1)) + fiberNeverMass K q D J f N =
      ∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val := by
  have he : (∑ t ∈ Finset.range N, fiberNextMoment K q D J f t (fun _ _ => 1)) =
      (∑ h : historyFiber q D J f, historyWeight (fun j => K j.val) q h.val) *
        ∑ t ∈ Finset.range N, firstSuccessMass K Dᶜ n t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact fiber_next_mass_firstSuccess K D J f hD t (hK t (Finset.mem_range.mp ht)) (hz t (Finset.mem_range.mp ht))
  rw [he, fiber_never_mass K D J f hD, ← mul_add, first_success_or_never K Dᶜ n N hK, mul_one]

end MatchingCapacity
