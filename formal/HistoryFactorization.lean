import NeighborhoodChoice
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact path weights, using actual prefix availability, factor on each
refinement. The factor is derived from the path product, not assumed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def historyWeight (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (h : Fin n → Option (Fin m)) : ℚ :=
  ∏ j, K j (historyAvailable q h j.val) (h j)

def fixedPathFactor (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) : ℚ :=
  ∏ j, if j ∈ J then 1 else K j (historyAvailable q (fixedHistory J f) j.val) (f j)

def residualRows (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) {D : Finset (Fin m)} (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (j : ResidualJobs J) (k : ResidualBins D) : ℚ :=
  K j.val (historyAvailable q (fixedHistory J f) j.val) (some k.val)

def refinedPathWeight (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) {D : Finset (Fin m)} (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (d : ResidualJobs J → ResidualBins D) : ℚ :=
  if ResidualCapped q d then historyWeight K q (completeHistory J f d) else 0

theorem historyLoad_snoc (h : Fin n → Option (Fin m)) (o : Option (Fin m))
    (t : ℕ) (ht : t ≤ n) (k : Fin m) : historyLoad (Fin.snoc h o) t k = historyLoad h t k := by
  unfold historyLoad
  rw [Fin.sum_univ_castSucc]
  have hn : ¬ n < t := Nat.not_lt.mpr ht
  simp [hn]

theorem historyAvailable_snoc (h : Fin n → Option (Fin m)) (o : Option (Fin m))
    (t : ℕ) (ht : t ≤ n) : historyAvailable q (Fin.snoc h o) t = historyAvailable q h t := by
  ext k
  simp only [historyAvailable, Finset.mem_filter, Finset.mem_univ, true_and,
    historyLoad_snoc h o t ht]

theorem historyWeight_snoc (K : Fin (n+1) → Finset (Fin m) → Option (Fin m) → ℚ)
    (q : ℕ) (h : Fin n → Option (Fin m)) (o : Option (Fin m)) :
    historyWeight K q (Fin.snoc h o) = historyWeight (fun j => K j.castSucc) q h *
      K (Fin.last n) (historyAvailable q h n) o := by
  unfold historyWeight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [historyAvailable_snoc h o n le_rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [historyAvailable_snoc h o j.val (Nat.le_of_lt j.isLt)]

theorem historyWeight_probability (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A, ∑ o, K j A o = 1) (q : ℕ) :
    (∑ h : Fin n → Option (Fin m), historyWeight K q h) = 1 := by
  induction n with
  | zero => simp [historyWeight]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Option (Fin m))).sum_comp (historyWeight K q)]
    change (∑ p : Option (Fin m) × (Fin n → Option (Fin m)), historyWeight K q (Fin.snoc p.2 p.1)) = 1
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [historyWeight_snoc, ← Finset.mul_sum, hK, mul_one]
    exact ih (fun j => K j.castSucc) (fun j A => hK j.castSucc A)

theorem rv_history_probability (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) (q : ℕ) :
    (∑ h : Fin n → Option (Fin m), historyWeight (fun j => rvKernel (degree j)) q h) = 1 :=
  historyWeight_probability _ (fun j A => rvKernel_probability (degree j) (hd j) A) q

theorem ranking_history_probability (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) (q : ℕ) :
    (∑ h : Fin n → Option (Fin m), historyWeight (fun j => rankingKernel (degree j)) q h) = 1 :=
  historyWeight_probability _ (fun j A => rankingKernel_probability (degree j) (hd j) A) q

theorem historyLoad_snoc_final (h : Fin n → Option (Fin m)) (o : Option (Fin m)) (k : Fin m) :
    historyLoad (Fin.snoc h o) (n+1) k = historyLoad h n k + if o = some k then 1 else 0 := by
  rw [historyLoad_final, Fin.sum_univ_castSucc, historyLoad_final]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem historyWeight_capacity (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A k, k ∉ A → K j A (some k) = 0) (q : ℕ)
    (h : Fin n → Option (Fin m)) (hm : historyWeight K q h ≠ 0) :
    ∀ k, historyLoad h n k ≤ q+1 := by
  induction n with
  | zero => intro k; simp [historyLoad]
  | succ n ih =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [historyWeight_snoc] at hm
    have hprev := ih (fun j => K j.castSucc) (fun j A k hk => hK j.castSucc A k hk)
      g (mul_ne_zero_iff.mp hm).1
    intro k
    rw [historyLoad_snoc_final]
    by_cases ho : o = some k
    · subst o
      have hk : k ∈ historyAvailable q g n := by
        by_contra hk
        exact (mul_ne_zero_iff.mp hm).2 (hK _ _ _ hk)
      have hc := (Finset.mem_filter.mp hk).2
      simpa using Nat.add_le_add_right hc 1
    · simpa [ho] using hprev k

theorem rv_history_capacity (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m))
    (hm : historyWeight (fun j => rvKernel (degree j)) q h ≠ 0) : ∀ k, historyLoad h n k ≤ q+1 :=
  historyWeight_capacity _ (fun j A k hk => rvKernel_unavailable (degree j) A k hk) q h hm

theorem ranking_history_capacity (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m))
    (hm : historyWeight (fun j => rankingKernel (degree j)) q h ≠ 0) : ∀ k, historyLoad h n k ≤ q+1 :=
  historyWeight_capacity _ (fun j A k hk => rankingKernel_unavailable (degree j) A k hk) q h hm

theorem historyWeight_nonneg (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (q : ℕ) (h : Fin n → Option (Fin m)) : 0 ≤ historyWeight K q h :=
  Finset.prod_nonneg (fun j _ => hK j _ _)

theorem fixedPathFactor_nonneg (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (q : ℕ) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) :
    0 ≤ fixedPathFactor K q J f := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · norm_num
  · exact hK j _ _

theorem residualRows_nonneg (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (q : ℕ) (D : Finset (Fin m))
    (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (j : ResidualJobs J) (k : ResidualBins D) :
    0 ≤ residualRows K q (D := D) J f j k := hK _ _ _

theorem history_weight_factorization (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (d : ResidualJobs J → ResidualBins D) (hd : ResidualCapped q d) :
    historyWeight K q (completeHistory J f d) =
      fixedPathFactor K q J f * assignmentWeight (residualRows K q (D := D) J f) d := by
  unfold historyWeight
  have ha (j : Fin n) := complete_availability D J f hf d hd j.val (Nat.le_of_lt j.isLt)
  simp_rw [ha]
  have hp := Finset.prod_attach_eq_prod_dite J (fun j => residualRows K q (D := D) J f j (d j))
  change assignmentWeight (residualRows K q (D := D) J f) d = _ at hp
  rw [hp]
  unfold fixedPathFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ J <;> simp [completeHistory, residualRows, hj]

theorem refined_path_factorization (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (d : ResidualJobs J → ResidualBins D) :
    refinedPathWeight K q (D := D) J f d = fixedPathFactor K q J f *
      (if ResidualCapped q d then assignmentWeight (residualRows K q (D := D) J f) d else 0) := by
  by_cases hd : ResidualCapped q d
  · simp [refinedPathWeight, hd, history_weight_factorization K D J f hf d hd]
  · simp [refinedPathWeight, hd]

theorem refined_path_total (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f) :
    (∑ d : ResidualJobs J → ResidualBins D, refinedPathWeight K q (D := D) J f d) =
      fixedPathFactor K q J f * assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) := by
  simp only [refined_path_factorization K D J f hf, assignmentEventMass, Finset.mul_sum]

theorem refined_path_moment (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (F : (ResidualJobs J → ResidualBins D) → ℚ) :
    (∑ d, refinedPathWeight K q (D := D) J f d * F d) = fixedPathFactor K q J f *
      ∑ d, if ResidualCapped q d then assignmentWeight (residualRows K q (D := D) J f) d * F d else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [refined_path_factorization K D J f hf]
  by_cases hd : ResidualCapped q d <;> simp [hd, mul_assoc]

theorem refined_positive_factors (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ d : ResidualJobs J → ResidualBins D, refinedPathWeight K q (D := D) J f d) :
    0 < fixedPathFactor K q J f ∧ 0 < assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) := by
  rw [refined_path_total K D J f hf] at hm
  rcases mul_pos_iff.mp hm with h | h
  · exact h
  · have hk := fixedPathFactor_nonneg K hK q J f
    linarith [h.1]

theorem refined_conditional_moment (K : Fin n → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (hm : 0 < ∑ d : ResidualJobs J → ResidualBins D, refinedPathWeight K q (D := D) J f d)
    (F : (ResidualJobs J → ResidualBins D) → ℚ) :
    (∑ d, refinedPathWeight K q (D := D) J f d * F d) / (∑ d, refinedPathWeight K q (D := D) J f d) =
      (∑ d, if ResidualCapped q d then assignmentWeight (residualRows K q (D := D) J f) d * F d else 0) /
        assignmentEventMass (residualRows K q (D := D) J f) (ResidualCapped q) := by
  rw [refined_path_moment K D J f hf, refined_path_total K D J f hf]
  exact mul_div_mul_left _ _ (refined_positive_factors K hK D J f hf hm).1.ne'

theorem rv_history_factorization (degree : Fin n → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (d : ResidualJobs J → ResidualBins D) (hd : ResidualCapped q d) :
    historyWeight (fun j => rvKernel (degree j)) q (completeHistory J f d) =
      fixedPathFactor (fun j => rvKernel (degree j)) q J f *
      assignmentWeight (residualRows (fun j => rvKernel (degree j)) q J f) d :=
  history_weight_factorization _ D J f hf d hd

theorem ranking_history_factorization (degree : Fin n → ℕ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hf : FixedSupported D J f) (d : ResidualJobs J → ResidualBins D) (hd : ResidualCapped q d) :
    historyWeight (fun j => rankingKernel (degree j)) q (completeHistory J f d) =
      fixedPathFactor (fun j => rankingKernel (degree j)) q J f *
      assignmentWeight (residualRows (fun j => rankingKernel (degree j)) q J f) d :=
  history_weight_factorization _ D J f hf d hd

end MatchingCapacity
