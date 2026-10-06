import CategoricalLoadPair
import LoadMajorization

/-! Permutation sums turn a two-coordinate paired inequality into
majorization monotonicity, on the same LoadLE relation as association. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {b : ℕ}

def symmetrizeLoad (F : (Fin b → ℕ) → ℚ) (x : Fin b → ℕ) : ℚ :=
  ∑ e : Equiv.Perm (Fin b), F (fun k => x (e k))

theorem symmetrizeLoad_permute (F : (Fin b → ℕ) → ℚ)
    (e : Equiv.Perm (Fin b)) (x : Fin b → ℕ) :
    symmetrizeLoad F (fun k => x (e k)) = symmetrizeLoad F x := by
  exact (Group.mulLeft_bijective e).sum_comp (fun f => F (fun k => x (f k)))

theorem replacePair_original (x : Fin b → ℕ) (i j : Fin b) :
    replacePair x i j (x i) (x j) = x := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [replacePair]
  · by_cases hj : k = j
    · subst k
      simp [replacePair, hi]
    · simp [replacePair, hi, hj]

theorem replacePair_exchange (x : Fin b → ℕ) (i j : Fin b) (hij : i ≠ j)
    (a c : ℕ) :
    (fun k => replacePair x i j a c (Equiv.swap i j k)) = replacePair x i j c a := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [replacePair, hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [replacePair, hij.symm]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj, replacePair, hi, hj]

theorem replacePair_permute (x : Fin b → ℕ) (i j : Fin b) (a c : ℕ)
    (e : Equiv.Perm (Fin b)) :
    (fun k => replacePair x i j a c (e k)) =
      replacePair (fun k => x (e k)) (e.symm i) (e.symm j) a c := by
  funext k
  simp only [replacePair, ← Equiv.eq_symm_apply]

theorem symmetrizeLoad_balancing (F : (Fin b → ℕ) → ℚ)
    (hpair : ∀ x i j a c, i ≠ j → c+2 ≤ a →
      F (replacePair x i j (a-1) (c+1)) + F (replacePair x i j (c+1) (a-1)) ≤
        F (replacePair x i j a c) + F (replacePair x i j c a))
    (y : Fin b → ℕ) (i j : Fin b) (hij : i ≠ j) (hgap : y j+2 ≤ y i) :
    symmetrizeLoad F (balanceLoad y i j) ≤ symmetrizeLoad F y := by
  have hpoint (e : Equiv.Perm (Fin b)) :
      F (fun k => replacePair y i j (y i-1) (y j+1) (e k)) +
        F (fun k => replacePair y i j (y j+1) (y i-1) (e k)) ≤
      F (fun k => replacePair y i j (y i) (y j) (e k)) +
        F (fun k => replacePair y i j (y j) (y i) (e k)) := by
    simp only [replacePair_permute]
    exact hpair _ _ _ _ _ (fun h => hij (e.symm.injective h)) hgap
  have hsum :
      symmetrizeLoad F (replacePair y i j (y i-1) (y j+1)) +
        symmetrizeLoad F (replacePair y i j (y j+1) (y i-1)) ≤
      symmetrizeLoad F (replacePair y i j (y i) (y j)) +
        symmetrizeLoad F (replacePair y i j (y j) (y i)) := by
    simpa only [symmetrizeLoad, Finset.sum_add_distrib] using
      (Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e))
  have hswap (a c : ℕ) :
      symmetrizeLoad F (replacePair y i j c a) = symmetrizeLoad F (replacePair y i j a c) := by
    rw [← replacePair_exchange y i j hij a c]
    exact symmetrizeLoad_permute F (Equiv.swap i j) _
  rw [hswap (y i-1) (y j+1), hswap (y i) (y j), replacePair_original] at hsum
  change symmetrizeLoad F (replacePair y i j (y i-1) (y j+1)) ≤ _
  linarith

theorem symmetrizeLoad_mono (F : (Fin b → ℕ) → ℚ)
    (hpair : ∀ x i j a c, i ≠ j → c+2 ≤ a →
      F (replacePair x i j (a-1) (c+1)) + F (replacePair x i j (c+1) (a-1)) ≤
        F (replacePair x i j a c) + F (replacePair x i j c a))
    (x y : Fin b → ℕ) (hT : (∑ i, x i) = ∑ i, y i) (hxy : LoadLE x y) :
    symmetrizeLoad F x ≤ symmetrizeLoad F y := by
  exact loadLE_mono_of_balancing (symmetrizeLoad F) (symmetrizeLoad_permute F)
    (fun y i j hij hgap => symmetrizeLoad_balancing F hpair y i j hij hgap) x y hT hxy

end MatchingCapacity
