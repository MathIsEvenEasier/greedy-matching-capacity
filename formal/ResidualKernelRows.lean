import NeighborhoodOrder
import HistoryFactorization
import Mathlib.Data.Fintype.Sort

/-! The concrete rows left by a refined history have the common order
needed by the categorical comparison. No row-order premise is assumed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def residualOrder (D : Finset (Fin m)) : Fin (Fintype.card (ResidualBins D)) ≃o ResidualBins D :=
  monoEquivOfFin (ResidualBins D) rfl

theorem residual_always_available (D : Finset (Fin m)) (J : Finset (Fin n))
    (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f) (t : ℕ) (k : ResidualBins D) :
    k.val ∈ historyAvailable q (fixedHistory J f) t := by
  simp only [historyAvailable, Finset.mem_filter, Finset.mem_univ, true_and,
    fixed_load_outside_D D J f hf t k.val k.property, Nat.zero_le]

theorem rv_residual_rows_constant (degree : Fin n → ℕ) (D : Finset (Fin m))
    (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (j : ResidualJobs J) (i k : ResidualBins D) :
    residualRows (fun j => rvKernel (degree j)) q J f j i =
      residualRows (fun j => rvKernel (degree j)) q J f j k :=
  rvKernel_constant_on_available _ _ _ _
    (residual_always_available D J f hf j.val.val i)
    (residual_always_available D J f hf j.val.val k)

theorem ranking_residual_rows_antitone (degree : Fin n → ℕ) (D : Finset (Fin m))
    (J : Finset (Fin n)) (f : Fin n → Option (Fin m)) (hf : FixedSupported D J f)
    (j : ResidualJobs J) :
    Antitone (fun k => residualRows (fun j => rankingKernel (degree j)) q J f j (residualOrder D k)) := by
  intro i k hik
  exact rankingKernel_ordered_on_available _ _ _ _
    (residual_always_available D J f hf j.val.val (residualOrder D i))
    ((residualOrder D).monotone hik)

def residualNextRow (K : Finset (Fin m) → Option (Fin m) → ℚ) (D : Finset (Fin m))
    (k : ResidualBins D) : ℚ := K Dᶜ (some k.val) / ∑ l : ResidualBins D, K Dᶜ (some l.val)

theorem residualNextRow_probability (K : Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (hm : 0 < ∑ l : ResidualBins D, K Dᶜ (some l.val)) :
    (∑ k, residualNextRow K D k) = 1 := by
  unfold residualNextRow
  rw [← Finset.sum_div, div_self hm.ne']

theorem ranking_residual_next_antitone (degree : ℕ) (D : Finset (Fin m))
    (hm : 0 < ∑ l : ResidualBins D, rankingKernel degree Dᶜ (some l.val)) :
    Antitone (fun k => residualNextRow (rankingKernel degree) D (residualOrder D k)) := by
  intro i k hik
  apply div_le_div_of_nonneg_right _ hm.le
  exact rankingKernel_ordered_on_available _ _ _ _
    (Finset.mem_compl.mpr (residualOrder D i).property) ((residualOrder D).monotone hik)

theorem rv_residual_next_uniform (degree : ℕ) (D : Finset (Fin m))
    (hm : 0 < ∑ l : ResidualBins D, rvKernel degree Dᶜ (some l.val)) (k : ResidualBins D) :
    residualNextRow (rvKernel degree) D k = 1 / (Fintype.card (ResidualBins D) : ℚ) := by
  have he (l : ResidualBins D) : rvKernel degree Dᶜ (some l.val) = rvKernel degree Dᶜ (some k.val) :=
    rvKernel_constant_on_available _ _ _ _ (Finset.mem_compl.mpr l.property) (Finset.mem_compl.mpr k.property)
  have hs : (∑ l : ResidualBins D, rvKernel degree Dᶜ (some l.val)) =
      (Fintype.card (ResidualBins D) : ℚ) * rvKernel degree Dᶜ (some k.val) := by simp [he]
  have hz : rvKernel degree Dᶜ (some k.val) ≠ 0 := by
    intro hz
    rw [hs, hz, mul_zero] at hm
    exact (lt_irrefl 0) hm
  unfold residualNextRow
  rw [hs]
  field_simp

end MatchingCapacity
