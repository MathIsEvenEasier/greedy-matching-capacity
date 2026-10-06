import WaitingKernel
import ResidualKernelRows

/-! Counting the rejecting neighborhoods gives a kernel depending only
on the number of unavailable bins, for either matching algorithm. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {m : ℕ}

theorem empty_inter_iff_subset_complement (A N : Finset (Fin m)) : A ∩ N = ∅ ↔ N ⊆ Aᶜ := by
  constructor
  · intro h k hk
    apply Finset.mem_compl.mpr
    intro ha
    have hh := Finset.mem_inter.mpr ⟨ha,hk⟩
    rw [h] at hh
    exact Finset.notMem_empty k hh
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact (Finset.mem_compl.mp (h (Finset.mem_inter.mp hk).2)) (Finset.mem_inter.mp hk).1

theorem rejecting_neighborhoods (A : Finset (Fin m)) (degree : ℕ) :
    (Finset.univ.powersetCard degree).filter (fun N => A ∩ N = ∅) = Aᶜ.powersetCard degree := by
  ext N
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    empty_inter_iff_subset_complement]
  exact and_comm

theorem rv_rejection_formula (degree : ℕ) (A : Finset (Fin m)) :
    rvKernel degree A none = (Nat.choose Aᶜ.card degree : ℚ) / (Nat.choose m degree : ℚ) := by
  unfold rvKernel neighborhoodKernel
  simp only [rvResponse]
  rw [← Finset.sum_filter, rejecting_neighborhoods]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard]
  ring

theorem ranking_rejection_formula (degree : ℕ) (A : Finset (Fin m)) :
    rankingKernel degree A none = (Nat.choose Aᶜ.card degree : ℚ) / (Nat.choose m degree : ℚ) := by
  rw [kernels_same_rejection, rv_rejection_formula]

theorem residual_success_mass (K : Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (hK : ∑ o, K Dᶜ o = 1)
    (hz : ∀ k, k ∉ Dᶜ → K Dᶜ (some k) = 0) :
    (∑ k : ResidualBins D, K Dᶜ (some k.val)) = 1-K Dᶜ none := by
  have hs : (∑ k : ResidualBins D, K Dᶜ (some k.val)) = ∑ k : Fin m, K Dᶜ (some k) := by
    rw [← Finset.sum_subtype Dᶜ (by simp) (fun k => K Dᶜ (some k))]
    exact Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => hz k hk)
  rw [hs]
  exact successMass_eq K Dᶜ hK

theorem rv_residual_success_formula (degree : ℕ) (hd : degree ≤ m) (D : Finset (Fin m)) :
    (∑ k : ResidualBins D, rvKernel degree Dᶜ (some k.val)) =
      1 - (Nat.choose D.card degree : ℚ) / (Nat.choose m degree : ℚ) := by
  rw [residual_success_mass _ D (rvKernel_probability degree hd Dᶜ)
    (fun k hk => rvKernel_unavailable degree Dᶜ k hk), rv_rejection_formula, compl_compl]

theorem ranking_residual_success_formula (degree : ℕ) (hd : degree ≤ m) (D : Finset (Fin m)) :
    (∑ k : ResidualBins D, rankingKernel degree Dᶜ (some k.val)) =
      1 - (Nat.choose D.card degree : ℚ) / (Nat.choose m degree : ℚ) := by
  rw [residual_success_mass _ D (rankingKernel_probability degree hd Dᶜ)
    (fun k hk => rankingKernel_unavailable degree Dᶜ k hk), ranking_rejection_formula, compl_compl]

end MatchingCapacity
