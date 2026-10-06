import RefinementMixture

/-! Actual next-acceptance moments, averaged over disjoint history fibers.
No transition-law or Markov assumption is supplied by the caller. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

theorem coarse_moment_bound (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K a t : ℕ) (G : (Fin n → Option (Fin m)) → Fin m → ℚ) (c : ℚ)
    (hb : ∀ r : GoodRefinement n m q, KeyPrefix q K a r.val →
      c * fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun _ _ => 1) ≤
        fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun h k => G h k.val)) :
    c * coarseNextMoment L n q K a t (fun _ _ => 1) ≤ coarseNextMoment L n q K a t G := by
  rw [coarse_next_partition, coarse_next_partition, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  by_cases hp : KeyPrefix q K a r.val
  · simpa only [ite_eq_left hp] using hb r hp
  · simp [hp]

theorem coarse_moment_eq (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K a t : ℕ) (G : (Fin n → Option (Fin m)) → Fin m → ℚ) (c : ℚ)
    (hb : ∀ r : GoodRefinement n m q, KeyPrefix q K a r.val →
      fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun h k => G h k.val) =
        c * fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun _ _ => 1)) :
    coarseNextMoment L n q K a t G = c * coarseNextMoment L n q K a t (fun _ _ => 1) := by
  rw [coarse_next_partition, coarse_next_partition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : KeyPrefix q K a r.val
  · simpa only [ite_eq_left hp] using hb r hp
  · simp [hp]

def coarseNextSaturation (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (n q K a t : ℕ) : ℚ :=
  coarseNextMoment L n q K a t (fun h k => if historyLoad h n k = q then 1 else 0) /
    coarseNextMoment L n q K a t (fun _ _ => 1)

theorem coarse_rv_saturation (degree : ℕ → ℕ) (K a t : ℕ) (ha : a < m)
    (hm : 0 < coarseNextMoment (fun j => rvKernel (m := m) (degree j)) n q K a t (fun _ _ => 1)) :
    coarseNextSaturation (fun j => rvKernel (m := m) (degree j)) n q K a t = referenceHazard (m-a) q (K-a*(q+1)) := by
  unfold coarseNextSaturation
  apply (div_eq_iff (ne_of_gt hm)).mpr
  apply coarse_moment_eq
  intro r hp
  apply conditional_eq_unnormalized
  · exact fiber_next_mass_nonneg _ (fun j A o => rvKernel_nonneg (degree j) A o) r t
  · intro hz
    exact fiber_next_null_moment _ (fun j A o => rvKernel_nonneg (degree j) A o) r t hz _
  · intro hpos
    exact key_rv_saturation degree r K a t hp ha hpos

theorem coarse_ranking_saturation (degree : ℕ → ℕ) (K a t : ℕ) (ha : a < m)
    (hm : 0 < coarseNextMoment (fun j => rankingKernel (m := m) (degree j)) n q K a t (fun _ _ => 1)) :
    referenceHazard (m-a) q (K-a*(q+1)) ≤ coarseNextSaturation (fun j => rankingKernel (m := m) (degree j)) n q K a t := by
  unfold coarseNextSaturation
  apply (le_div_iff₀ hm).mpr
  apply coarse_moment_bound
  intro r hp
  apply conditional_bound_unnormalized
  · exact fiber_next_mass_nonneg _ (fun j A o => rankingKernel_nonneg (degree j) A o) r t
  · intro hz
    exact fiber_next_null_moment _ (fun j A o => rankingKernel_nonneg (degree j) A o) r t hz _
  · intro hpos
    exact key_ranking_saturation degree r K a t hp ha hpos

theorem coarse_rv_vs_ranking (degree : ℕ → ℕ) (K a t : ℕ) (ha : a < m)
    (hrv : 0 < coarseNextMoment (fun j => rvKernel (m := m) (degree j)) n q K a t (fun _ _ => 1))
    (hrk : 0 < coarseNextMoment (fun j => rankingKernel (m := m) (degree j)) n q K a t (fun _ _ => 1)) :
    coarseNextSaturation (fun j => rvKernel (m := m) (degree j)) n q K a t ≤
      coarseNextSaturation (fun j => rankingKernel (m := m) (degree j)) n q K a t := by
  rw [coarse_rv_saturation degree K a t ha hrv]
  exact coarse_ranking_saturation degree K a t ha hrk

theorem coarse_next_mark_probability (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (K a t : ℕ) :
    coarseNextMoment L n q K a t
      (fun h k => (((historyFullBins q (acceptedExtension h t k)).card - (historyFullBins q h).card : ℕ) : ℚ)) /
        coarseNextMoment L n q K a t (fun _ _ => 1) = coarseNextSaturation L n q K a t := by
  unfold coarseNextSaturation coarseNextMoment
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  split_ifs
  · unfold availableNextMoment
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [acceptedExtension_full_count h.val t k hk, Nat.add_sub_cancel_left]
    split_ifs <;> simp
  · rfl

end MatchingCapacity
