import LoadSymmetrization

/-! The actual permutation-averaged categorical load mass has a
factorial-weighted density increasing in integer majorization. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ℕ}

def symmetrizedLoadMass (p : ι → Fin b → ℚ) (x : Fin b → ℕ) : ℚ :=
  symmetrizeLoad (categoricalLoadMass p) x / (Fintype.card (Equiv.Perm (Fin b)) : ℚ)

def categoricalDensity (p : ι → Fin b → ℚ) (x : Fin b → ℕ) : ℚ :=
  symmetrizeLoad (factorialLoadMass p) x / (Fintype.card (Equiv.Perm (Fin b)) : ℚ)

theorem loadFactorial_permute (x : Fin b → ℕ) (e : Equiv.Perm (Fin b)) :
    loadFactorial (fun k => x (e k)) = loadFactorial x := by
  exact Equiv.prod_comp e (fun k => ((x k).factorial : ℚ))

theorem categoricalDensity_eq (p : ι → Fin b → ℚ) (x : Fin b → ℕ) :
    categoricalDensity p x = loadFactorial x * symmetrizedLoadMass p x := by
  unfold categoricalDensity symmetrizedLoadMass symmetrizeLoad factorialLoadMass
  simp only [loadFactorial_permute]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem categoricalDensity_nonneg (p : ι → Fin b → ℚ) (hp : ∀ r k, 0 ≤ p r k)
    (x : Fin b → ℕ) : 0 ≤ categoricalDensity p x := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (loadFactorial_pos _).le (assignmentEventMass_nonneg p hp _)

theorem categoricalDensity_symmetric (p : ι → Fin b → ℚ)
    (e : Equiv.Perm (Fin b)) (x : Fin b → ℕ) :
    categoricalDensity p (fun k => x (e k)) = categoricalDensity p x := by
  unfold categoricalDensity
  rw [symmetrizeLoad_permute]

theorem categoricalDensity_majorization (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (x y : Fin b → ℕ) (hT : (∑ i, x i) = ∑ i, y i) (hxy : LoadLE x y) :
    categoricalDensity p x ≤ categoricalDensity p y := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply symmetrizeLoad_mono _ _ x y hT hxy
  intro z i j a c hij hgap
  apply factorialLoadMass_pair_balancing p hp z i j hij _ a c hgap
  rcases le_total i j with h | h
  · exact Or.inl (fun r => horder r h)
  · exact Or.inr (fun r => horder r h)

end MatchingCapacity
