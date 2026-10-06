import AcceptedCount

/-! A canonical, finite, disjoint partition of every capacity-respecting
history into the refined fibers used by the local comparison. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

abbrev HistoryKey (n m : ℕ) := Finset (Fin m) × Finset (Fin n) × (Fin n → Option (Fin m))

def historyKey (q : ℕ) (h : Fin n → Option (Fin m)) : HistoryKey n m :=
  let D := historyFullBins q h
  let J := historyFreeJobs D h
  (D,J,fixedHistory J h)

def KeyValid (q : ℕ) (r : HistoryKey n m) : Prop :=
  FixedSupported r.1 r.2.1 r.2.2 ∧
    (∀ j ∈ r.2.1, r.2.2 j = none) ∧
    ∀ k ∈ r.1, historyLoad (fixedHistory r.2.1 r.2.2) n k = q+1

abbrev GoodRefinement (n m q : ℕ) := {r : HistoryKey n m // KeyValid q r}
abbrev LegalHistory (n m q : ℕ) := {h : Fin n → Option (Fin m) // ∀ k, historyLoad h n k ≤ q+1}
abbrev KeyFiber (q : ℕ) (r : HistoryKey n m) := historyFiber q r.1 r.2.1 r.2.2

theorem fixedHistory_idempotent (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) :
    fixedHistory J (fixedHistory J f) = fixedHistory J f := by
  funext j
  by_cases hj : j ∈ J <;> simp [fixedHistory, hj]

theorem history_key_member (q : ℕ) (h : Fin n → Option (Fin m)) :
    HistoryRefines (historyKey q h).1 (historyKey q h).2.1 (historyKey q h).2.2 h ∧
      ∀ k : ResidualBins (historyKey q h).1, historyLoad h n k.val ≤ q := by
  constructor
  · constructor
    · intro j hj
      simp only [historyKey] at hj ⊢
      simp [fixedHistory, hj]
    · exact (history_anchor_refines (historyFullBins q h) h).2
  · exact history_anchor_capped q h

theorem history_key_valid (q : ℕ) (h : Fin n → Option (Fin m))
    (hc : ∀ k, historyLoad h n k ≤ q+1) : KeyValid q (historyKey q h) := by
  let D := historyFullBins q h
  let J := historyFreeJobs D h
  change FixedSupported D J (fixedHistory J h) ∧
    (∀ j ∈ J, fixedHistory J h j = none) ∧
    ∀ k ∈ D, historyLoad (fixedHistory J (fixedHistory J h)) n k = q+1
  refine ⟨?_,?_,?_⟩
  · intro j hj k hk
    apply history_anchor_supported D h j hj k
    simpa [fixedHistory, hj] using hk
  · intro j hj
    simp [fixedHistory, hj]
  · intro k hk
    rw [fixedHistory_idempotent]
    exact (history_anchor_fixed_load D h k hk).trans (history_full_bin_load q h hc k hk)

theorem canonical_fiber_key (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hn : ∀ j ∈ J, f j = none)
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (h : historyFiber q D J f) :
    historyKey q h.val = (D,J,f) := by
  have hfull := history_fiber_full_bins D J f hD h
  have hfree : historyFreeJobs D h.val = J := by
    ext j
    simp only [historyFreeJobs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k,hk⟩
      by_contra hj
      rw [h.property.1.1 j hj] at hk
      exact k.property (hf j hj k.val hk)
    · exact h.property.1.2 j
  have hfixed : fixedHistory J h.val = f := by
    funext j
    by_cases hj : j ∈ J
    · simp [fixedHistory, hj, hn j hj]
    · simp [fixedHistory, hj, h.property.1.1 j hj]
  simp only [historyKey, hfull, hfree, hfixed]

theorem key_fiber_legal (r : GoodRefinement n m q) (h : KeyFiber q r.val) :
    ∀ k, historyLoad h.val n k ≤ q+1 := by
  intro k
  by_cases hk : k ∈ r.val.1
  · have he := complete_load_in_D r.val.1 r.val.2.1 r.val.2.2 (extractResidual h.property.1) n k hk
    rw [complete_extract] at he
    rw [he, r.property.2.2 k hk]
  · exact (h.property.2 ⟨k,hk⟩).trans (Nat.le_succ q)

def refinementHistoryMap (x : (r : GoodRefinement n m q) × KeyFiber q r.val) : LegalHistory n m q :=
  ⟨x.2.val,key_fiber_legal x.1 x.2⟩

theorem refinementHistoryMap_injective : Function.Injective (refinementHistoryMap (n := n) (m := m) (q := q)) := by
  rintro ⟨r,h⟩ ⟨s,g⟩ he
  have hh : h.val = g.val := congrArg Subtype.val he
  have hr := canonical_fiber_key r.val.1 r.val.2.1 r.val.2.2 r.property.1 r.property.2.1 r.property.2.2 h
  have hs := canonical_fiber_key s.val.1 s.val.2.1 s.val.2.2 s.property.1 s.property.2.1 s.property.2.2 g
  have hk : r = s := Subtype.ext (hr.symm.trans ((congrArg (historyKey q) hh).trans hs))
  subst s
  have hg : h = g := Subtype.ext hh
  subst g
  rfl

theorem refinementHistoryMap_surjective : Function.Surjective (refinementHistoryMap (n := n) (m := m) (q := q)) := by
  intro h
  exact ⟨⟨⟨historyKey q h.val,history_key_valid q h.val h.property⟩,
    ⟨h.val,history_key_member q h.val⟩⟩,rfl⟩

def historyRefinementEquiv (n m q : ℕ) :
    ((r : GoodRefinement n m q) × KeyFiber q r.val) ≃ LegalHistory n m q :=
  Equiv.ofBijective refinementHistoryMap ⟨refinementHistoryMap_injective,refinementHistoryMap_surjective⟩

theorem history_refinement_partition (F : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : LegalHistory n m q, F h.val) =
      ∑ r : GoodRefinement n m q, ∑ h : KeyFiber q r.val, F h.val := by
  rw [← (historyRefinementEquiv n m q).sum_comp (fun h => F h.val), Fintype.sum_sigma]
  rfl

end MatchingCapacity
