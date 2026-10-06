import CappedCarrier

/-! An explicit statement of the finite association obligation.
`CappedAssociation` is a definition of a proposition, NOT a proved theorem
and NOT an axiom. The weight and order infrastructure below is proved. -/

set_option autoImplicit false
open scoped BigOperators

namespace MatchingCapacity

-- On vectors with the same total this is the usual majorization order:
-- each k-element coordinate sum is bounded by some k-element sum of y.
def LoadLE {b : ℕ} (x y : Fin b → ℕ) : Prop :=
  ∀ s : Finset (Fin b), ∃ t : Finset (Fin b),
    t.card = s.card ∧ (∑ i ∈ s, x i) ≤ ∑ i ∈ t, y i

theorem loadLE_refl {b : ℕ} (x : Fin b → ℕ) : LoadLE x x := by
  intro s
  exact ⟨s, rfl, le_rfl⟩

theorem loadLE_trans {b : ℕ} {x y z : Fin b → ℕ}
    (hxy : LoadLE x y) (hyz : LoadLE y z) : LoadLE x z := by
  intro s
  obtain ⟨t, ht, hst⟩ := hxy s
  obtain ⟨u, hu, htu⟩ := hyz t
  exact ⟨u, hu.trans ht, hst.trans htu⟩

abbrev CappedLoad (b q r : ℕ) :=
  {x : Fin b → Fin (q+1) // (∑ i, (x i).val) = r}

def cappedWeight {b q r : ℕ} (x : CappedLoad b q r) : ℚ :=
  ∏ i, factorialWeight (x.val i).val

theorem cappedWeight_pos {b q r : ℕ} (x : CappedLoad b q r) :
    0 < cappedWeight x := by
  exact Finset.prod_pos fun i _ => factorialWeight_pos (x.val i).val

def CappedAssociation (b q r : ℕ) : Prop :=
  ∀ F G : CappedLoad b q r → ℚ,
    (∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y) →
    (∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → G x ≤ G y) →
    CovNonneg cappedWeight F G

end MatchingCapacity
