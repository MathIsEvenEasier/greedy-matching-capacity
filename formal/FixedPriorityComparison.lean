import BoundedNextCoupling
import CouplingInduction

/-! All accepted-count levels and matching-size tails in the concrete
uniform-neighborhood model with fixed bin priority. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N m q : ℕ}

theorem stopping_laws_ordered_coupling (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m) (K : ℕ) :
    HasRelCoupling (StopLE (N := N) (m := m))
      (stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K)
      (stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K) := by
  induction K with
  | zero =>
    have hr : stoppingMass (fun j => rvKernel (m := m) (degree j)) N q 0 = fun s => if s = some (0,0) then 1 else 0 := by
      funext s
      exact stoppingMass_zero _ (fun j A => rvKernel_probability (degree j) (hd j) A) N q s
    have hk : stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q 0 = fun s => if s = some (0,0) then 1 else 0 := by
      funext s
      exact stoppingMass_zero _ (fun j A => rankingKernel_probability (degree j) (hd j) A) N q s
    rw [hr,hk]
    exact coupling_diagonal StopLE (some (0,0)) (by simp [StopLE,stopValue,RawStopLE])
  | succ K ih =>
    have h := coupling_step StopLE _ _
      (stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K)
      (stoppingTransition (fun j => rankingKernel (m := m) (degree j)) N q K) ih
      (fun s t hs ht ho => actual_ordered_transition_coupling degree hd K s t ho hs ht)
    have hr : (fun u => ∑ s, stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K s *
        stoppingTransition (fun j => rvKernel (m := m) (degree j)) N q K s u) =
        stoppingMass (fun j => rvKernel (m := m) (degree j)) N q (K+1) := by
      funext u
      exact stoppingTransition_total_probability _ (fun j A o => rvKernel_nonneg (degree j) A o) K u
    have hk : (fun v => ∑ t, stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K t *
        stoppingTransition (fun j => rankingKernel (m := m) (degree j)) N q K t v) =
        stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q (K+1) := by
      funext v
      exact stoppingTransition_total_probability _ (fun j A o => rankingKernel_nonneg (degree j) A o) K v
    rw [hr,hk] at h
    exact h

theorem stopping_never_mass_comparison (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m) (K : ℕ) :
    stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K none ≤
      stoppingMass (fun j => rankingKernel (m := m) (degree j)) N q K none := by
  obtain ⟨c,hc,hr,hk,ho⟩ := stopping_laws_ordered_coupling (N := N) (q := q) degree hd K
  have he : ∀ v, c none v = if v = none then c none none else 0 := by
    intro v
    cases v with
    | none => simp
    | some v =>
      rw [ho none (some v) (by simp [StopLE,stopValue,RawStopLE])]
      simp
  have hrow : stoppingMass (fun j => rvKernel (m := m) (degree j)) N q K none = c none none := by
    rw [← hr none]
    apply Finset.sum_eq_single none
    · intro v _ hv
      exact (he v).trans (ite_eq_right hv)
    · intro hn
      exact False.elim (hn (Finset.mem_univ none))
  rw [hrow, ← hk none]
  exact Finset.single_le_sum (fun s _ => hc s none) (Finset.mem_univ none)

theorem fixed_priority_matching_tail_comparison (degree : ℕ → ℕ) (hd : ∀ j, degree j ≤ m)
    (N q K : ℕ) :
    (∑ h : Fin N → Option (Fin m), if K ≤ acceptedCount h then
      historyWeight (fun j => rankingKernel (m := m) (degree j.val)) q h else 0) ≤
    (∑ h : Fin N → Option (Fin m), if K ≤ acceptedCount h then
      historyWeight (fun j => rvKernel (m := m) (degree j.val)) q h else 0) := by
  rw [stoppingMass_tail _ (fun j A => rankingKernel_probability (degree j) (hd j) A),
    stoppingMass_tail _ (fun j A => rvKernel_probability (degree j) (hd j) A)]
  exact sub_le_sub_left (stopping_never_mass_comparison (N := N) (q := q) degree hd K) 1

end MatchingCapacity
