import FiniteWaitingLaw

/-! Earlier starts and fewer full bins give an earlier next success.
The degree sequence need not be ordered or positive. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def failureRatio (degree : ℕ → ℕ) (m a j : ℕ) : ℚ :=
  (Nat.choose a (degree j) : ℚ) / (Nat.choose m (degree j) : ℚ)

def delayedFailure (degree : ℕ → ℕ) (m n a j : ℕ) : ℚ :=
  if j < n then 1 else failureRatio degree m a j

theorem failureRatio_nonneg (degree : ℕ → ℕ) (m a j : ℕ) :
    0 ≤ failureRatio degree m a j := by
  unfold failureRatio
  positivity

theorem failureRatio_mono (degree : ℕ → ℕ) (m a b j : ℕ) (hab : a ≤ b) :
    failureRatio degree m a j ≤ failureRatio degree m b j := by
  unfold failureRatio
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.choose_le_choose (degree j) hab
  · positivity

theorem failureRatio_le_one (degree : ℕ → ℕ) (m a j : ℕ)
    (ha : a ≤ m) (hd : degree j ≤ m) : failureRatio degree m a j ≤ 1 := by
  have h := failureRatio_mono degree m a m j ha
  have hp : (Nat.choose m (degree j) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hd).ne'
  simpa only [failureRatio, div_self hp] using h

theorem delayedFailure_nonneg (degree : ℕ → ℕ) (m n a j : ℕ) :
    0 ≤ delayedFailure degree m n a j := by
  unfold delayedFailure
  split_ifs
  · norm_num
  · exact failureRatio_nonneg degree m a j

theorem delayedFailure_le_one (degree : ℕ → ℕ) (m n a j : ℕ)
    (ha : a ≤ m) (hd : degree j ≤ m) : delayedFailure degree m n a j ≤ 1 := by
  unfold delayedFailure
  split_ifs
  · exact le_rfl
  · exact failureRatio_le_one degree m a j ha hd

theorem delayedFailure_mono (degree : ℕ → ℕ) (m n s a b : ℕ)
    (hd : ∀ j, degree j ≤ m) (hns : n ≤ s) (hab : a ≤ b) (hb : b ≤ m) (j : ℕ) :
    delayedFailure degree m n a j ≤ delayedFailure degree m s b j := by
  unfold delayedFailure
  split_ifs with h1 h2 h3
  · exact le_rfl
  · omega
  · exact failureRatio_le_one degree m a j (hab.trans hb) (hd j)
  · exact failureRatio_mono degree m a b j hab

theorem delayed_survival_before (degree : ℕ → ℕ) (m n a k : ℕ) (hk : k ≤ n) :
    survivalProduct (delayedFailure degree m n a) k = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_range] at hj
  exact ite_eq_left (show j < n by omega)

theorem delayed_survival_shift (degree : ℕ → ℕ) (m n a t : ℕ) :
    survivalProduct (delayedFailure degree m n a) (n+t) =
      ∏ j ∈ Finset.range t, failureRatio degree m a (n+j) := by
  induction t with
  | zero => simpa using delayed_survival_before degree m n a n le_rfl
  | succ t ih =>
    rw [show n+(t+1) = (n+t)+1 by omega, survivalProduct_succ, ih, Finset.prod_range_succ]
    simp only [delayedFailure, Nat.not_lt.mpr (Nat.le_add_right n t), ite_false]

theorem delayed_waiting_before (degree : ℕ → ℕ) (m n a N i : ℕ)
    (hn : n ≤ N) (hi : i < n) : finiteWaitMass (delayedFailure degree m n a) N i = 0 := by
  simp [finiteWaitMass, show i < N by omega, delayedFailure, hi]

theorem delayed_waiting_hit (degree : ℕ → ℕ) (m n a N t : ℕ) (ht : n+t < N) :
    finiteWaitMass (delayedFailure degree m n a) N (n+t) = countWaitingFactor degree m n a t := by
  rw [finiteWaitMass, ite_eq_left ht, delayed_survival_shift]
  simp only [delayedFailure, Nat.not_lt.mpr (Nat.le_add_right n t), ite_false,
    failureRatio, countWaitingFactor]

theorem delayed_waiting_never (degree : ℕ → ℕ) (m n a t : ℕ) :
    finiteWaitMass (delayedFailure degree m n a) (n+t) (n+t) =
      ∏ j ∈ Finset.range t, failureRatio degree m a (n+j) := by
  simp only [finiteWaitMass, lt_self_iff_false, ite_false, ite_true, delayed_survival_shift]

theorem count_waiting_cdf_order (degree : ℕ → ℕ) (m n s a b N k : ℕ)
    (hd : ∀ j, degree j ≤ m) (hns : n ≤ s) (hab : a ≤ b) (hb : b ≤ m) (hk : k ≤ N+1) :
    cumMass (finiteWaitMass (delayedFailure degree m s b) N) k ≤
      cumMass (finiteWaitMass (delayedFailure degree m n a) N) k :=
  finiteWaitMass_cdf_order _ _ (delayedFailure_nonneg degree m n a)
    (delayedFailure_mono degree m n s a b hd hns hab hb) N k hk

theorem count_waiting_ordered_coupling (degree : ℕ → ℕ) (m n s a b N : ℕ)
    (hd : ∀ j, degree j ≤ m) (hns : n ≤ s) (hab : a ≤ b) (hb : b ≤ m) :
    ∃ c : Fin (N+1) → Fin (N+1) → ℚ,
      (∀ i j, 0 ≤ c i j) ∧
      (∀ i, ∑ j, c i j = finiteWaitMass (delayedFailure degree m n a) N i.val) ∧
      (∀ j, ∑ i, c i j = finiteWaitMass (delayedFailure degree m s b) N j.val) ∧
      (∀ i j, j < i → c i j = 0) :=
  finite_waiting_coupling _ _ (delayedFailure_nonneg degree m n a)
    (fun j => delayedFailure_le_one degree m s b j hb (hd j))
    (delayedFailure_mono degree m n s a b hd hns hab hb) N

end MatchingCapacity
