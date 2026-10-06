import StoppingState

/-! A finite pushforward law for the actual stopping state, including the
never-reached outcome, and its exact prefix and matching-tail marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

abbrev StopState (N m : ℕ) := Option (Fin (N+1) × Fin (m+1))

def stopValue (s : StopState N m) : Option (ℕ × ℕ) :=
  s.map (fun x => (x.1.val,x.2.val))

def finiteStoppingState (q K : ℕ) (h : Fin N → Option (Fin m)) : StopState N m :=
  match he : stoppingState q h K with
  | none => none
  | some (s,a) => some (⟨s,Nat.lt_succ_of_le (stoppingState_bounds h K s a he).1⟩,
      ⟨a,Nat.lt_succ_of_le (stoppingState_bounds h K s a he).2⟩)

theorem stopValue_injective : Function.Injective (stopValue (N := N) (m := m)) := by
  intro s t he
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some t => simp [stopValue] at he
  | some s =>
    cases t with
    | none => simp [stopValue] at he
    | some t =>
      have hh : s.1.val = t.1.val ∧ s.2.val = t.2.val := by simpa [stopValue] using he
      exact congrArg some (Prod.ext (Fin.ext hh.1) (Fin.ext hh.2))

theorem finiteStoppingState_value (h : Fin N → Option (Fin m)) (K : ℕ) :
    stopValue (finiteStoppingState q K h) = stoppingState q h K := by
  unfold finiteStoppingState
  split <;> simp_all [stopValue]

theorem finiteStoppingState_eq_iff (h : Fin N → Option (Fin m)) (K : ℕ) (s : StopState N m) :
    finiteStoppingState q K h = s ↔ stoppingState q h K = stopValue s := by
  rw [← finiteStoppingState_value h K]
  exact stopValue_injective.eq_iff.symm

theorem finiteStoppingState_none_iff (h : Fin N → Option (Fin m)) (K : ℕ) :
    finiteStoppingState q K h = none ↔ acceptedCount h < K := by
  rw [finiteStoppingState_eq_iff]
  exact stoppingState_none_iff h K

theorem finiteStoppingState_absorbing (h : Fin N → Option (Fin m)) (K : ℕ)
    (hh : finiteStoppingState q K h = none) : finiteStoppingState q (K+1) h = none := by
  apply (finiteStoppingState_none_iff h (K+1)).mpr
  have hk := (finiteStoppingState_none_iff h K).mp hh
  omega

def stoppingMass (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (N q K : ℕ) (s : StopState N m) : ℚ :=
  ∑ h : Fin N → Option (Fin m), if finiteStoppingState q K h = s then historyWeight (fun j => L j.val) q h else 0

theorem stoppingMass_nonneg (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (K : ℕ) (s : StopState N m) : 0 ≤ stoppingMass L N q K s := by
  unfold stoppingMass
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact historyWeight_nonneg _ (fun j A o => hL j.val A o) q h
  · rfl

theorem stoppingMass_probability (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (N q K : ℕ) : (∑ s, stoppingMass L N q K s) = 1 := by
  unfold stoppingMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact historyWeight_probability _ (fun j A => hL j.val A) q

theorem stoppingMass_finite (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hz : ∀ j A k, k ∉ A → L j A (some k) = 0)
    (K : ℕ) (s : Fin (N+1)) (a : Fin (m+1)) :
    stoppingMass L N q K (some (s,a)) = coarseHistoryMass L s.val q K a.val := by
  unfold stoppingMass
  simp only [finiteStoppingState_eq_iff, stopValue, Option.map_some]
  simp_rw [stoppingState_prefix_iff _ (Nat.le_of_lt_succ s.isLt)]
  rw [history_prefix_event L hL, ← coarse_history_unrestricted L hz]

theorem stoppingMass_never (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ) (N q K : ℕ) :
    stoppingMass L N q K none = ∑ h : Fin N → Option (Fin m),
      if acceptedCount h < K then historyWeight (fun j => L j.val) q h else 0 := by
  simp only [stoppingMass, finiteStoppingState_none_iff]

theorem stoppingMass_tail (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (N q K : ℕ) :
    (∑ h : Fin N → Option (Fin m), if K ≤ acceptedCount h then historyWeight (fun j => L j.val) q h else 0) =
      1 - stoppingMass L N q K none := by
  rw [stoppingMass_never, ← historyWeight_probability (fun j : Fin N => L j.val) (fun j A => hL j.val A) q,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : acceptedCount h < K
  · simp [hh, Nat.not_le.mpr hh]
  · simp [hh, Nat.le_of_not_lt hh]

theorem finiteStoppingState_zero (h : Fin N → Option (Fin m)) :
    finiteStoppingState q 0 h = some (0,0) := by
  apply stopValue_injective
  rw [finiteStoppingState_value, stoppingState_zero]
  rfl

theorem stoppingMass_zero (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (N q : ℕ) (s : StopState N m) :
    stoppingMass L N q 0 s = if s = some (0,0) then 1 else 0 := by
  unfold stoppingMass
  simp only [finiteStoppingState_zero]
  by_cases hs : s = some (0,0)
  · subst s
    simp only [ite_true]
    exact historyWeight_probability _ (fun j A => hL j.val A) q
  · simp [hs, Ne.symm hs]

end MatchingCapacity
