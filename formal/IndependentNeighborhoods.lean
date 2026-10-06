import PriorityRelabeling
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The history kernels are the exact marginal of independently sampled
uniform neighborhoods, including degree zero. No independence assumption
about the evolving available sets is used. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m : ℕ}

def uniformNeighborhoodMass (degree : ℕ) (S : Finset (Fin m)) : ℚ :=
  if S ∈ Finset.univ.powersetCard degree then (Nat.choose m degree : ℚ)⁻¹ else 0

theorem uniform_neighborhood_moment (degree : ℕ) (F : Finset (Fin m) → ℚ) :
    (∑ S, uniformNeighborhoodMass degree S * F S) =
      (Nat.choose m degree : ℚ)⁻¹ * ∑ S ∈ Finset.univ.powersetCard degree, F S := by
  calc
    _ = ∑ S ∈ Finset.univ.powersetCard degree, uniformNeighborhoodMass degree S * F S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hs
      simp [uniformNeighborhoodMass,hs]
    _ = ∑ S ∈ Finset.univ.powersetCard degree, (Nat.choose m degree : ℚ)⁻¹ * F S := by
      apply Finset.sum_congr rfl
      intro S hs
      simp only [uniformNeighborhoodMass,ite_eq_left hs]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem uniform_neighborhood_probability (degree : ℕ) (hd : degree ≤ m) :
    (∑ S : Finset (Fin m), uniformNeighborhoodMass degree S) = 1 := by
  have hm := uniform_neighborhood_moment (m := m) degree (fun _ => (1 : ℚ))
  simp only [mul_one] at hm
  rw [hm]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.choose_pos hd |>.ne')

def neighborhoodProfileMass (degree : Fin n → ℕ) (G : Fin n → Finset (Fin m)) : ℚ :=
  ∏ j, uniformNeighborhoodMass (degree j) (G j)

def graphHistoryMass (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m)) : ℚ :=
  ∑ G : Fin n → Finset (Fin m), neighborhoodProfileMass degree G *
    historyWeight (fun j A o => R A (G j) o) q h

theorem neighborhood_profile_nonneg (degree : Fin n → ℕ) (G : Fin n → Finset (Fin m)) :
    0 ≤ neighborhoodProfileMass degree G := by
  apply Finset.prod_nonneg
  intro j _
  unfold uniformNeighborhoodMass
  split_ifs <;> positivity

theorem neighborhood_profile_probability (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) :
    (∑ G : Fin n → Finset (Fin m), neighborhoodProfileMass degree G) = 1 := by
  unfold neighborhoodProfileMass
  rw [← Fintype.prod_sum]
  simp only [uniform_neighborhood_probability _ (hd _), Finset.prod_const_one]

theorem graph_history_kernel_identity
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : Fin n → ℕ) (q : ℕ) (h : Fin n → Option (Fin m)) :
    graphHistoryMass R degree q h =
      historyWeight (fun j => neighborhoodKernel R (degree j)) q h := by
  unfold graphHistoryMass neighborhoodProfileMass historyWeight
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (S : Finset (Fin m)) =>
    uniformNeighborhoodMass (degree j) S * R (historyAvailable q h j.val) S (h j))]
  apply Finset.prod_congr rfl
  intro j _
  exact uniform_neighborhood_moment (degree j) (fun S => R (historyAvailable q h j.val) S (h j))

theorem graph_history_probability
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (hR : ∀ A S, ∑ o, R A S o = 1) (degree : Fin n → ℕ) (hd : ∀ j, degree j ≤ m) (q : ℕ) :
    (∑ h : Fin n → Option (Fin m), graphHistoryMass R degree q h) = 1 := by
  simp only [graph_history_kernel_identity]
  exact historyWeight_probability _ (fun j A => neighborhoodKernel_probability R hR (degree j) (hd j) A) q

theorem graph_history_nonneg
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (hR : ∀ A S o, 0 ≤ R A S o) (degree : Fin n → ℕ) (q : ℕ)
    (h : Fin n → Option (Fin m)) : 0 ≤ graphHistoryMass R degree q h := by
  rw [graph_history_kernel_identity]
  exact historyWeight_nonneg _ (fun j A o => neighborhoodKernel_nonneg R hR (degree j) A o) q h

/-- Reindex the original job-labeled graph by the sampled arrival order. -/
def profileOrderEquiv (order : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n → Finset (Fin m)) where
  toFun := fun G j => G (order j)
  invFun := fun G j => G (order.symm j)
  left_inv := by intro G; funext j; simp
  right_inv := by intro G; funext j; simp

theorem neighborhood_profile_reorder (order : Equiv.Perm (Fin n))
    (degree : Fin n → ℕ) (G : Fin n → Finset (Fin m)) :
    neighborhoodProfileMass (fun j => degree (order j)) (fun j => G (order j)) =
      neighborhoodProfileMass degree G := by
  unfold neighborhoodProfileMass
  exact Equiv.prod_comp order (fun j => uniformNeighborhoodMass (degree j) (G j))

/-- Draw the original job-labeled graph first, then process it in the chosen order. -/
def orderedGraphHistoryMass
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : Fin n → ℕ) (order : Equiv.Perm (Fin n)) (q : ℕ)
    (h : Fin n → Option (Fin m)) : ℚ :=
  ∑ G : Fin n → Finset (Fin m), neighborhoodProfileMass degree G *
    historyWeight (fun j A o => R A (G (order j)) o) q h

theorem ordered_graph_history_identity
    (R : Finset (Fin m) → Finset (Fin m) → Option (Fin m) → ℚ)
    (degree : Fin n → ℕ) (order : Equiv.Perm (Fin n)) (q : ℕ)
    (h : Fin n → Option (Fin m)) :
    orderedGraphHistoryMass R degree order q h =
      graphHistoryMass R (fun j => degree (order j)) q h := by
  unfold orderedGraphHistoryMass graphHistoryMass
  apply Fintype.sum_equiv (profileOrderEquiv order)
  intro G
  change neighborhoodProfileMass degree G * _ =
    neighborhoodProfileMass (fun j => degree (order j)) (fun j => G (order j)) * _
  rw [neighborhood_profile_reorder]
  rfl

theorem priority_response_probability (e : Equiv.Perm (Fin m)) (A S : Finset (Fin m)) :
    (∑ o, priorityResponse e A S o) = 1 := by
  unfold priorityResponse
  rw [Equiv.sum_comp]
  exact rankingResponse_probability _ _

end MatchingCapacity
