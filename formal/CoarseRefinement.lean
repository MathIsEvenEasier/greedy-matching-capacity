import CanonicalRefinement

/-! Coarse accepted-count prefix events are unions of the canonical fibers.
The last-arrival condition selects prefixes ending at an acceptance. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def keyAccepted (r : HistoryKey n m) (j : Fin n) : Bool :=
  if j ∈ r.2.1 then true else (r.2.2 j).isSome

def AcceptedPrefix (q K a : ℕ) (h : Fin n → Option (Fin m)) : Prop :=
  acceptedCount h = K ∧ (historyFullBins q h).card = a ∧
    ∀ j : Fin n, j.val+1 = n → (h j).isSome = true

def KeyPrefix (q K a : ℕ) (r : HistoryKey n m) : Prop :=
  r.1.card * (q+1) + Fintype.card (ResidualJobs r.2.1) = K ∧ r.1.card = a ∧
    ∀ j : Fin n, j.val+1 = n → keyAccepted r j = true

theorem fiber_accepted_pattern (r : GoodRefinement n m q) (h : KeyFiber q r.val) (j : Fin n) :
    (h.val j).isSome = keyAccepted r.val j := by
  by_cases hj : j ∈ r.val.2.1
  · obtain ⟨k,hk⟩ := h.property.1.2 j hj
    simp [keyAccepted, hj, hk]
  · simp [keyAccepted, hj, h.property.1.1 j hj]

theorem fiber_accepted_prefix (r : GoodRefinement n m q) (h : KeyFiber q r.val) (K a : ℕ) :
    AcceptedPrefix q K a h.val ↔ KeyPrefix q K a r.val := by
  unfold AcceptedPrefix KeyPrefix
  rw [history_fiber_accepted_count r.val.1 r.val.2.1 r.val.2.2 r.property.1 r.property.2.2 h,
    history_fiber_full_bins r.val.1 r.val.2.1 r.val.2.2 r.property.2.2 h]
  simp only [fiber_accepted_pattern r h]

theorem accepted_prefix_partition (K a : ℕ) (F : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : LegalHistory n m q, if AcceptedPrefix q K a h.val then F h.val else 0) =
      ∑ r : GoodRefinement n m q, if KeyPrefix q K a r.val then
        ∑ h : KeyFiber q r.val, F h.val else 0 := by
  rw [history_refinement_partition (q := q) (fun h => if AcceptedPrefix q K a h then F h else 0)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [fiber_accepted_prefix r]
  split_ifs <;> simp

def availableNextMoment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (h : Fin n → Option (Fin m)) (t : ℕ)
    (G : (Fin n → Option (Fin m)) → Fin m → ℚ) : ℚ :=
  ∑ k ∈ historyAvailable q h n,
    historyWeight (fun j => L j.val) q (acceptedExtension h t k) * G h k

theorem fiber_available_next (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (r : GoodRefinement n m q) (t : ℕ)
    (G : (Fin n → Option (Fin m)) → Fin m → ℚ) :
    (∑ h : KeyFiber q r.val, availableNextMoment L q h.val t G) =
      fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun h k => G h k.val) := by
  unfold availableNextMoment fiberNextMoment
  apply Finset.sum_congr rfl
  intro h _
  rw [history_fiber_final_availability r.val.1 r.val.2.1 r.val.2.2 r.property.2.2 h]
  exact Finset.sum_subtype (F := inferInstance) r.val.1ᶜ
    (fun k => (Finset.mem_compl : k ∈ r.val.1ᶜ ↔ k ∉ r.val.1)) _

def coarseNextMoment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (n q K a t : ℕ) (G : (Fin n → Option (Fin m)) → Fin m → ℚ) : ℚ :=
  ∑ h : LegalHistory n m q, if AcceptedPrefix q K a h.val then availableNextMoment L q h.val t G else 0

theorem coarse_next_partition (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K a t : ℕ) (G : (Fin n → Option (Fin m)) → Fin m → ℚ) :
    coarseNextMoment L n q K a t G =
      ∑ r : GoodRefinement n m q, if KeyPrefix q K a r.val then
        fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun h k => G h k.val) else 0 := by
  unfold coarseNextMoment
  rw [accepted_prefix_partition (q := q) K a (fun h => availableNextMoment L q h t G)]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · exact fiber_available_next L r t G
  · rfl

theorem key_residual_bin_count (r : GoodRefinement n m q) :
    Fintype.card (ResidualBins r.val.1) = m - r.val.1.card := by
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_subtype_compl (fun k : Fin m => k ∈ r.val.1)

theorem key_prefix_counts (r : GoodRefinement n m q) (K a : ℕ) (hp : KeyPrefix q K a r.val) :
    Fintype.card (ResidualBins r.val.1) = m-a ∧
      Fintype.card (ResidualJobs r.val.2.1) = K-a*(q+1) := by
  constructor
  · rw [key_residual_bin_count, hp.2.1]
  · have he := hp.1
    rw [hp.2.1] at he
    omega

end MatchingCapacity
