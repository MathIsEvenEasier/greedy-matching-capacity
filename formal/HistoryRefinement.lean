import CategoricalLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! A refinement fixes all rejections and all destinations in D, leaving
exactly J free destinations outside D. The final residual cap determines
all earlier availability sets, not just the final one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

abbrev ResidualJobs (J : Finset (Fin n)) := {j : Fin n // j ∈ J}
abbrev ResidualBins (D : Finset (Fin m)) := {k : Fin m // k ∉ D}

def historyLoad (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m) : ℕ :=
  ∑ j, if j.val < t ∧ h j = some k then 1 else 0

def historyAvailable (q : ℕ) (h : Fin n → Option (Fin m)) (t : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun k => historyLoad h t k ≤ q)

def fixedHistory (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (j : Fin n) : Option (Fin m) :=
  if j ∈ J then none else f j

def completeHistory (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    {D : Finset (Fin m)} (d : ResidualJobs J → ResidualBins D) (j : Fin n) : Option (Fin m) :=
  if hj : j ∈ J then some (d ⟨j, hj⟩).val else f j

def FixedSupported (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) : Prop :=
  ∀ j, j ∉ J → ∀ k, f j = some k → k ∈ D

def ResidualCapped (q : ℕ) {J : Finset (Fin n)} {D : Finset (Fin m)}
    (d : ResidualJobs J → ResidualBins D) : Prop := ∀ k, assignmentLoad d k ≤ q

theorem historyLoad_mono (h : Fin n → Option (Fin m)) {s t : ℕ} (hst : s ≤ t) (k : Fin m) :
    historyLoad h s k ≤ historyLoad h t k := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hs : j.val < s ∧ h j = some k
  · have ht : j.val < t ∧ h j = some k := ⟨lt_of_lt_of_le hs.1 hst, hs.2⟩
    simp [hs, ht]
  · simp [hs]

theorem historyLoad_final (h : Fin n → Option (Fin m)) (k : Fin m) :
    historyLoad h n k = ∑ j, if h j = some k then 1 else 0 := by
  simp [historyLoad]

theorem completeHistory_free (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    {D : Finset (Fin m)} (d : ResidualJobs J → ResidualBins D) (j : ResidualJobs J) :
    completeHistory J f d j.val = some (d j).val := by
  simp [completeHistory, j.property]

theorem completeHistory_fixed (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    {D : Finset (Fin m)} (d : ResidualJobs J → ResidualBins D) {j : Fin n} (hj : j ∉ J) :
    completeHistory J f d j = f j := by simp [completeHistory, hj]

theorem completeHistory_injective (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (D : Finset (Fin m)) : Function.Injective (completeHistory J f (D := D)) := by
  intro a b hab
  funext j
  apply Subtype.ext
  have h := congrFun hab j.val
  simpa only [completeHistory_free, Option.some.injEq] using h

theorem complete_load_in_D (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (d : ResidualJobs J → ResidualBins D)
    (t : ℕ) (k : Fin m) (hk : k ∈ D) :
    historyLoad (completeHistory J f d) t k = historyLoad (fixedHistory J f) t k := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · have hd : (d ⟨j,hj⟩).val ≠ k := by
      intro he
      apply (d ⟨j,hj⟩).property
      simpa [he] using hk
    simp [completeHistory, fixedHistory, hj, hd]
  · simp [completeHistory, fixedHistory, hj]

theorem fixed_load_outside_D (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (t : ℕ) (k : Fin m) (hk : k ∉ D) : historyLoad (fixedHistory J f) t k = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j ∈ J
  · simp [fixedHistory, hj]
  · have he : f j ≠ some k := fun he => hk (hf j hj k he)
    simp [fixedHistory, hj, he]

theorem complete_final_residual (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (d : ResidualJobs J → ResidualBins D) (k : ResidualBins D) :
    historyLoad (completeHistory J f d) n k.val = assignmentLoad d k := by
  rw [historyLoad_final]
  have hsum := Finset.sum_attach_eq_sum_dite J (fun j => if d j = k then (1 : ℕ) else 0)
  change (∑ j : ResidualJobs J, if d j = k then (1 : ℕ) else 0) = _ at hsum
  unfold assignmentLoad
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · simp [completeHistory, hj, Subtype.ext_iff]
  · have he : f j ≠ some k.val := fun he => k.property (hf j hj k.val he)
    simp [completeHistory, hj, he]

theorem complete_residual_cap_iff (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (d : ResidualJobs J → ResidualBins D) :
    (∀ k : ResidualBins D, historyLoad (completeHistory J f d) n k.val ≤ q) ↔ ResidualCapped q d := by
  simp only [complete_final_residual D J f hf, ResidualCapped]

theorem complete_availability (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (d : ResidualJobs J → ResidualBins D) (hd : ResidualCapped q d)
    (t : ℕ) (ht : t ≤ n) :
    historyAvailable q (completeHistory J f d) t = historyAvailable q (fixedHistory J f) t := by
  ext k
  simp only [historyAvailable, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k ∈ D
  · rw [complete_load_in_D D J f d t k hk]
  · have hc : historyLoad (completeHistory J f d) t k ≤ q := by
      calc
        _ ≤ historyLoad (completeHistory J f d) n k := historyLoad_mono _ ht k
        _ = assignmentLoad d ⟨k,hk⟩ := complete_final_residual D J f hf d ⟨k,hk⟩
        _ ≤ q := hd ⟨k,hk⟩
    rw [fixed_load_outside_D D J f hf t k hk]
    exact iff_of_true hc (Nat.zero_le q)

end MatchingCapacity
