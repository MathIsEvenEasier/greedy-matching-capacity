import HistoryRefinement
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

/-! Literal finite one-arrival laws for uniform neighborhoods: RANDOM-VERTEX
chooses uniformly among feasible available bins, and RANKING chooses the
least such bin. The value none is rejection. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {m : ℕ}

def rvResponse (A N : Finset (Fin m)) (o : Option (Fin m)) : ℚ :=
  match o with
  | none => if A ∩ N = ∅ then 1 else 0
  | some k => if k ∈ A ∩ N then 1 / ((A ∩ N).card : ℚ) else 0

def rankingPick (A N : Finset (Fin m)) : Option (Fin m) :=
  if h : (A ∩ N).Nonempty then some ((A ∩ N).min' h) else none

def rankingResponse (A N : Finset (Fin m)) (o : Option (Fin m)) : ℚ :=
  if rankingPick A N = o then 1 else 0

def neighborhoodKernel (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : ℕ) (A : Finset (Fin m)) (o : Option (Fin m)) : ℚ :=
  (Nat.choose m degree : ℚ)⁻¹ * ∑ N ∈ Finset.univ.powersetCard degree, R A N o

def rvKernel (degree : ℕ) : Finset (Fin m) → Option (Fin m) → ℚ :=
  neighborhoodKernel rvResponse degree

def rankingKernel (degree : ℕ) : Finset (Fin m) → Option (Fin m) → ℚ :=
  neighborhoodKernel rankingResponse degree

theorem rvResponse_nonneg (A N : Finset (Fin m)) (o : Option (Fin m)) : 0 ≤ rvResponse A N o := by
  cases o <;> simp only [rvResponse]
  · split_ifs <;> norm_num
  · split_ifs
    · positivity
    · exact le_rfl

theorem rvResponse_probability (A N : Finset (Fin m)) : ∑ o, rvResponse A N o = 1 := by
  rw [Fintype.sum_option]
  by_cases he : A ∩ N = ∅
  · simp [rvResponse, he]
  · have hc : ((A ∩ N).card : ℚ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    simp only [rvResponse, ite_eq_right he, zero_add]
    rw [← Finset.sum_filter]
    have hs : Finset.univ.filter (fun k : Fin m => k ∈ A ∩ N) = A ∩ N := by ext k; simp
    rw [hs]
    simp [hc]

theorem rankingResponse_nonneg (A N : Finset (Fin m)) (o : Option (Fin m)) : 0 ≤ rankingResponse A N o := by
  unfold rankingResponse
  split_ifs <;> norm_num

theorem rankingResponse_probability (A N : Finset (Fin m)) : ∑ o, rankingResponse A N o = 1 := by
  simp [rankingResponse, eq_comm]

theorem neighborhoodKernel_nonneg
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (hR : ∀ A N o, 0 ≤ R A N o) (degree : ℕ) (A : Finset (Fin m)) (o : Option (Fin m)) :
    0 ≤ neighborhoodKernel R degree A o := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun N _ => hR A N o)

theorem neighborhoodKernel_probability
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (hR : ∀ A N, ∑ o, R A N o = 1) (degree : ℕ) (hd : degree ≤ m) (A : Finset (Fin m)) :
    ∑ o, neighborhoodKernel R degree A o = 1 := by
  unfold neighborhoodKernel
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hR, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.choose_pos hd |>.ne')

theorem rvKernel_nonneg (degree : ℕ) (A : Finset (Fin m)) (o : Option (Fin m)) : 0 ≤ rvKernel degree A o :=
  neighborhoodKernel_nonneg _ rvResponse_nonneg degree A o

theorem rankingKernel_nonneg (degree : ℕ) (A : Finset (Fin m)) (o : Option (Fin m)) : 0 ≤ rankingKernel degree A o :=
  neighborhoodKernel_nonneg _ rankingResponse_nonneg degree A o

theorem rvKernel_probability (degree : ℕ) (hd : degree ≤ m) (A : Finset (Fin m)) : ∑ o, rvKernel degree A o = 1 :=
  neighborhoodKernel_probability _ rvResponse_probability degree hd A

theorem rankingKernel_probability (degree : ℕ) (hd : degree ≤ m) (A : Finset (Fin m)) : ∑ o, rankingKernel degree A o = 1 :=
  neighborhoodKernel_probability _ rankingResponse_probability degree hd A

theorem rvResponse_reject_iff (A N : Finset (Fin m)) : rvResponse A N none = if A ∩ N = ∅ then 1 else 0 := rfl

theorem rankingResponse_reject (A N : Finset (Fin m)) : rankingResponse A N none = rvResponse A N none := by
  by_cases he : A ∩ N = ∅
  · simp [rankingResponse, rankingPick, rvResponse, he]
  · have hn : (A ∩ N).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    simp [rankingResponse, rankingPick, rvResponse, he, hn]

theorem kernels_same_rejection (degree : ℕ) (A : Finset (Fin m)) : rankingKernel degree A none = rvKernel degree A none := by
  simp only [rankingKernel, rvKernel, neighborhoodKernel, rankingResponse_reject]

theorem rvResponse_unavailable (A N : Finset (Fin m)) (k : Fin m) (hk : k ∉ A) :
    rvResponse A N (some k) = 0 := by simp [rvResponse, hk]

theorem rankingResponse_unavailable (A N : Finset (Fin m)) (k : Fin m) (hk : k ∉ A) :
    rankingResponse A N (some k) = 0 := by
  unfold rankingResponse rankingPick
  by_cases hn : (A ∩ N).Nonempty
  · have he : (A ∩ N).min' hn ≠ k := by
      intro he
      have hm := (Finset.mem_inter.mp (Finset.min'_mem (A ∩ N) hn)).1
      exact hk (he ▸ hm)
    simp [hn, he]
  · simp [hn]

theorem rvKernel_unavailable (degree : ℕ) (A : Finset (Fin m)) (k : Fin m) (hk : k ∉ A) :
    rvKernel degree A (some k) = 0 := by
  simp only [rvKernel, neighborhoodKernel, rvResponse_unavailable A _ k hk, Finset.sum_const_zero, mul_zero]

theorem rankingKernel_unavailable (degree : ℕ) (A : Finset (Fin m)) (k : Fin m) (hk : k ∉ A) :
    rankingKernel degree A (some k) = 0 := by
  simp only [rankingKernel, neighborhoodKernel, rankingResponse_unavailable A _ k hk, Finset.sum_const_zero, mul_zero]

end MatchingCapacity
