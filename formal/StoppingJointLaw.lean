import StoppingLaw

/-! Joint successive stopping states and exact one-time marginals. These
identities justify total-probability updates without a Markov assumption. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N m q : ℕ}

def stoppingJointMass (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K : ℕ) (s t : StopState N m) : ℚ :=
  ∑ h : Fin N → Option (Fin m), if finiteStoppingState q K h = s ∧ finiteStoppingState q (K+1) h = t
    then historyWeight (fun j => L j.val) q h else 0

theorem stoppingJoint_nonneg (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K : ℕ) (s t : StopState N m) : 0 ≤ stoppingJointMass L N q K s t := by
  unfold stoppingJointMass
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact historyWeight_nonneg _ (fun j A o => hL j.val A o) q h
  · rfl

theorem stoppingJoint_first_marginal (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (s : StopState N m) : (∑ t, stoppingJointMass L N q K s t) = stoppingMass L N q K s := by
  unfold stoppingJointMass stoppingMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : finiteStoppingState q K h = s <;> simp [hh]

theorem stoppingJoint_second_marginal (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (t : StopState N m) : (∑ s, stoppingJointMass L N q K s t) = stoppingMass L N q (K+1) t := by
  unfold stoppingJointMass stoppingMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : finiteStoppingState q (K+1) h = t <;> simp [hh]

theorem stoppingJoint_null_row (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K : ℕ) (s : StopState N m)
    (hs : stoppingMass L N q K s = 0) : ∀ t, stoppingJointMass L N q K s t = 0 := by
  apply finite_zero_mass _ (stoppingJoint_nonneg L hL K s)
  rw [stoppingJoint_first_marginal, hs]

def stoppingTransition (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (N q K : ℕ) (s t : StopState N m) : ℚ :=
  stoppingJointMass L N q K s t / stoppingMass L N q K s

theorem stoppingTransition_probability (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (s : StopState N m) (hs : 0 < stoppingMass L N q K s) :
    (∑ t, stoppingTransition L N q K s t) = 1 := by
  simp only [stoppingTransition, ← Finset.sum_div, stoppingJoint_first_marginal]
  exact div_self (ne_of_gt hs)

theorem stoppingTransition_total_probability (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K : ℕ) (t : StopState N m) :
    (∑ s, stoppingMass L N q K s * stoppingTransition L N q K s t) = stoppingMass L N q (K+1) t := by
  rw [← stoppingJoint_second_marginal L K t]
  apply Finset.sum_congr rfl
  intro s _
  unfold stoppingTransition
  by_cases hs : stoppingMass L N q K s = 0
  · rw [stoppingJoint_null_row L hL K s hs t, hs]
    norm_num
  · field_simp

theorem stoppingJoint_cemetery (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (K : ℕ) (t : StopState N m) :
    stoppingJointMass L N q K none t = if t = none then stoppingMass L N q K none else 0 := by
  unfold stoppingJointMass stoppingMass
  by_cases ht : t = none
  · subst t
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : finiteStoppingState q K h = none
    · simp [hh, finiteStoppingState_absorbing h K hh]
    · simp [hh]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro h _
    by_cases hh : finiteStoppingState q K h = none
    · simp [hh, finiteStoppingState_absorbing h K hh, Ne.symm ht]
    · simp [hh]

end MatchingCapacity
