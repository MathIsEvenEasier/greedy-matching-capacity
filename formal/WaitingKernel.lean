import NeighborhoodChoice

/-! Exact first-success and never-success weights while availability is
unchanged. The finite telescoping identity includes zero success rates. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {m : ℕ}

def waitingWeight (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (start t : ℕ) : ℚ :=
  ∏ j ∈ Finset.range t, K (start+j) A none

def successMass (K : Finset (Fin m) → Option (Fin m) → ℚ) (A : Finset (Fin m)) : ℚ :=
  ∑ k : Fin m, K A (some k)

def firstSuccessMass (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (start t : ℕ) : ℚ :=
  waitingWeight K A start t * successMass (K (start+t)) A

theorem waitingWeight_zero (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (start : ℕ) : waitingWeight K A start 0 = 1 := by
  simp [waitingWeight]

theorem waitingWeight_succ (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (start t : ℕ) :
    waitingWeight K A start (t+1) = waitingWeight K A start t * K (start+t) A none := by
  exact Finset.prod_range_succ _ _

theorem waitingWeight_nonneg (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (A : Finset (Fin m)) (start t : ℕ) :
    0 ≤ waitingWeight K A start t := Finset.prod_nonneg (fun j _ => hK (start+j) A none)

theorem successMass_eq (K : Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (hK : ∑ o, K A o = 1) : successMass K A = 1 - K A none := by
  rw [Fintype.sum_option] at hK
  unfold successMass
  linarith

theorem firstSuccessMass_nonneg (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hK : ∀ j A o, 0 ≤ K j A o) (A : Finset (Fin m)) (start t : ℕ) :
    0 ≤ firstSuccessMass K A start t :=
  mul_nonneg (waitingWeight_nonneg K hK A start t) (Finset.sum_nonneg (fun k _ => hK (start+t) A (some k)))

theorem firstSuccessMass_drop (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (start t : ℕ) (hK : ∑ o, K (start+t) A o = 1) :
    firstSuccessMass K A start t = waitingWeight K A start t - waitingWeight K A start (t+1) := by
  rw [firstSuccessMass, successMass_eq _ A hK, waitingWeight_succ]
  ring

theorem first_success_or_never (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (A : Finset (Fin m)) (start N : ℕ)
    (hK : ∀ t < N, ∑ o, K (start+t) A o = 1) :
    (∑ t ∈ Finset.range N, firstSuccessMass K A start t) + waitingWeight K A start N = 1 := by
  induction N with
  | zero => simp [waitingWeight]
  | succ N ih =>
    have hh := ih (fun t ht => hK t (Nat.lt_succ_of_lt ht))
    rw [Finset.sum_range_succ, firstSuccessMass_drop K A start N (hK N (Nat.lt_succ_self N))]
    linarith

theorem waitingWeight_same_rejections
    (K L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (A : Finset (Fin m))
    (h : ∀ j, K j A none = L j A none) (start t : ℕ) :
    waitingWeight K A start t = waitingWeight L A start t := by
  unfold waitingWeight
  simp only [h]

theorem rv_ranking_same_waiting (degree : ℕ → ℕ) (A : Finset (Fin m)) (start t : ℕ) :
    waitingWeight (fun j => rankingKernel (degree j)) A start t =
      waitingWeight (fun j => rvKernel (degree j)) A start t :=
  waitingWeight_same_rejections _ _ A (fun j => kernels_same_rejection (degree j) A) start t

end MatchingCapacity
