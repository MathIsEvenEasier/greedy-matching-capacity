import CoarseWaiting

/-! Restricting sums to capacity-respecting histories discards only zero
weight. This connects the coarse moments to the unrestricted path space. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

theorem illegal_history_weight_zero (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (h : Fin n → Option (Fin m)) (hc : ¬ ∀ k, historyLoad h n k ≤ q+1) :
    historyWeight (fun j => L j.val) q h = 0 := by
  by_contra hw
  exact hc (historyWeight_capacity _ (fun j A k hk => hz j.val A k hk) q h hw)

theorem legal_history_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (F : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : Fin n → Option (Fin m), historyWeight (fun j => L j.val) q h * F h) =
      ∑ h : LegalHistory n m q, historyWeight (fun j => L j.val) q h.val * F h.val := by
  apply Finset.sum_congr_set {h | ∀ k, historyLoad h n k ≤ q+1}
  · intro h _
    rfl
  · intro h hc
    simp only [illegal_history_weight_zero L hz h hc, zero_mul]

theorem coarse_history_unrestricted (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0) (K a : ℕ) :
    coarseHistoryMass L n q K a = ∑ h : Fin n → Option (Fin m),
      if AcceptedPrefix q K a h then historyWeight (fun j => L j.val) q h else 0 := by
  symm
  unfold coarseHistoryMass
  apply Finset.sum_congr_set {h | ∀ k, historyLoad h n k ≤ q+1}
  · intro h _
    rfl
  · intro h hc
    simp only [illegal_history_weight_zero L hz h hc, ite_self]

theorem coarse_next_unrestricted (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0) (K a t : ℕ)
    (G : (Fin n → Option (Fin m)) → Fin m → ℚ) :
    coarseNextMoment L n q K a t G = ∑ h : Fin n → Option (Fin m),
      if AcceptedPrefix q K a h then availableNextMoment L q h t G else 0 := by
  symm
  unfold coarseNextMoment
  apply Finset.sum_congr_set {h | ∀ k, historyLoad h n k ≤ q+1}
  · intro h _
    rfl
  · intro h hc
    simp only [availableNextMoment, acceptedExtension_weight, illegal_history_weight_zero L hz h hc,
      zero_mul, Finset.sum_const_zero, ite_self]

theorem coarse_never_unrestricted (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hz : ∀ j A k, k ∉ A → L j A (some k) = 0) (K a N : ℕ) :
    coarseNeverMass L n q K a N = ∑ h : Fin n → Option (Fin m),
      if AcceptedPrefix q K a h then historyWeight (fun j => L j.val) q (rejectExtension h N) else 0 := by
  symm
  unfold coarseNeverMass
  apply Finset.sum_congr_set {h | ∀ k, historyLoad h n k ≤ q+1}
  · intro h _
    rfl
  · intro h hc
    simp only [rejectExtension_weight, illegal_history_weight_zero L hz h hc, zero_mul, ite_self]

end MatchingCapacity
