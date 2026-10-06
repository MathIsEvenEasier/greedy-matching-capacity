import WaitingRefinement

/-! Exact acceptance accounting for every history and every consistent
refinement; this supplies r = K - a*C without a probabilistic assumption. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def acceptedCount (h : Fin n → Option (Fin m)) : ℕ :=
  ∑ j, if (h j).isSome then 1 else 0

theorem history_accepted_total (h : Fin n → Option (Fin m)) :
    (∑ k, historyLoad h n k) = acceptedCount h := by
  simp only [historyLoad_final, acceptedCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  cases h j <;> simp

theorem acceptedCount_snoc (h : Fin n → Option (Fin m)) (o : Option (Fin m)) :
    acceptedCount (Fin.snoc h o) = acceptedCount h + if o.isSome then 1 else 0 := by
  unfold acceptedCount
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem rejectExtension_accepted_count (h : Fin n → Option (Fin m)) (t : ℕ) :
    acceptedCount (rejectExtension h t) = acceptedCount h := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [rejectExtension, acceptedCount_snoc, ih, Option.isSome_none, Bool.false_eq_true, ite_false, add_zero]

theorem acceptedExtension_accepted_count (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m) :
    acceptedCount (acceptedExtension h t k) = acceptedCount h + 1 := by
  simp [acceptedExtension, acceptedCount_snoc, rejectExtension_accepted_count]

theorem complete_accepted_count (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1)
    (d : ResidualJobs J → ResidualBins D) :
    acceptedCount (completeHistory J f d) = D.card * (q+1) + Fintype.card (ResidualJobs J) := by
  rw [← history_accepted_total, ← Finset.sum_add_sum_compl D]
  have hfull : (∑ k ∈ D, historyLoad (completeHistory J f d) n k) = D.card * (q+1) := by
    calc
      _ = ∑ _k ∈ D, (q+1) := Finset.sum_congr rfl (fun k hk => (complete_load_in_D D J f d n k hk).trans (hD k hk))
      _ = _ := by simp
  have hres : (∑ k ∈ Dᶜ, historyLoad (completeHistory J f d) n k) = Fintype.card (ResidualJobs J) := by
    rw [Finset.sum_subtype (F := inferInstance) Dᶜ (fun k => (Finset.mem_compl : k ∈ Dᶜ ↔ k ∉ D))
      (fun k => historyLoad (completeHistory J f d) n k)]
    simp only [complete_final_residual D J f hf, assignmentLoad_total]
  rw [hfull, hres]

theorem history_fiber_accepted_count (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (h : historyFiber q D J f) :
    acceptedCount h.val = D.card * (q+1) + Fintype.card (ResidualJobs J) := by
  have hh := complete_accepted_count D J f hf hD (extractResidual h.property.1)
  simpa only [complete_extract] using hh

theorem residual_job_count (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1) (h : historyFiber q D J f) :
    Fintype.card (ResidualJobs J) = acceptedCount h.val - D.card * (q+1) := by
  rw [history_fiber_accepted_count D J f hf hD h, Nat.add_sub_cancel_left]

theorem acceptedExtension_final_load (h : Fin n → Option (Fin m)) (t : ℕ) (k i : Fin m) :
    historyLoad (acceptedExtension h t k) (n+t+1) i = historyLoad h n i + if k = i then 1 else 0 := by
  rw [acceptedExtension, historyLoad_snoc_final, rejectExtension_final_load]
  simp only [Option.some.injEq]

theorem acceptedExtension_full_bins (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m)
    (hk : k ∈ historyAvailable q h n) :
    historyFullBins q (acceptedExtension h t k) =
      if historyLoad h n k = q then insert k (historyFullBins q h) else historyFullBins q h := by
  have hc := (Finset.mem_filter.mp hk).2
  ext i
  by_cases he : historyLoad h n k = q
  · rw [ite_eq_left he]
    simp only [historyFullBins, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      acceptedExtension_final_load]
    by_cases hi : k = i
    · subst i; simp [he]
    · simp [hi, Ne.symm hi]
  · rw [ite_eq_right he]
    simp only [historyFullBins, Finset.mem_filter, Finset.mem_univ, true_and, acceptedExtension_final_load]
    by_cases hi : k = i
    · subst i; simp only [ite_true]; omega
    · simp [hi]

theorem acceptedExtension_full_count (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m)
    (hk : k ∈ historyAvailable q h n) :
    (historyFullBins q (acceptedExtension h t k)).card = (historyFullBins q h).card +
      if historyLoad h n k = q then 1 else 0 := by
  have hn : k ∉ historyFullBins q h := by
    have hc := (Finset.mem_filter.mp hk).2
    simpa only [historyFullBins, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hc
  rw [acceptedExtension_full_bins h t k hk]
  split_ifs <;> simp [hn]

theorem fiber_next_mark_probability (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (t : ℕ) :
    fiberNextMoment K q D J f t
      (fun h k => (((historyFullBins q (acceptedExtension h t k.val)).card -
        (historyFullBins q h).card : ℕ) : ℚ)) /
      fiberNextMoment K q D J f t (fun _ _ => 1) = fiberNextSaturation K q D J f t := by
  unfold fiberNextSaturation fiberNextMoment
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  have hk : k.val ∈ historyAvailable q h.val n := by
    simp only [historyAvailable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h.property.2 k
  rw [acceptedExtension_full_count h.val t k.val hk, Nat.add_sub_cancel_left]
  split_ifs <;> simp

end MatchingCapacity
