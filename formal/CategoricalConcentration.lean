import CategoricalDensity
import CappedAssociation

/-! Apply capped factorial association to the proved categorical density.
Permutation averaging preserves moments of majorization-increasing
observables, so the comparison holds for the original categorical load law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b q T : ℕ}

def cappedCategoricalWeight (p : ι → Fin b → ℚ) (x : CappedLoad b q T) : ℚ :=
  categoricalLoadMass p (fun i => (x.val i).val)

def cappedSymmetrizedWeight (p : ι → Fin b → ℚ) (x : CappedLoad b q T) : ℚ :=
  symmetrizedLoadMass p (fun i => (x.val i).val)

theorem capped_symmetrized_moment (p : ι → Fin b → ℚ) (F : CappedLoad b q T → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    moment (cappedSymmetrizedWeight p) F = moment (cappedCategoricalWeight p) F := by
  have h (e : Equiv.Perm (Fin b)) :
      (∑ x : CappedLoad b q T,
        categoricalLoadMass p (fun i => (x.val (e i)).val) * F x) =
      moment (cappedCategoricalWeight p) F := by
    have hh := (cappedPermEquiv (q := q) (r := T) e).sum_comp
      (fun x => cappedCategoricalWeight p x * F x)
    change (∑ x : CappedLoad b q T,
      categoricalLoadMass p (fun i => (x.val (e i)).val) * F (permuteCapped e x)) = _ at hh
    simpa only [hF, moment] using hh
  unfold moment cappedSymmetrizedWeight symmetrizedLoadMass symmetrizeLoad
  simp only [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [h]
  have hc : (Fintype.card (Equiv.Perm (Fin b)) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hc, moment]

theorem capped_symmetrized_total (p : ι → Fin b → ℚ) :
    total (cappedSymmetrizedWeight (q := q) (T := T) p) = total (cappedCategoricalWeight (q := q) (T := T) p) := by
  simpa only [moment, total, mul_one] using
    capped_symmetrized_moment (q := q) (T := T) p (fun _ => 1) (by intros; rfl)

theorem capped_density_weight (p : ι → Fin b → ℚ) (x : CappedLoad b q T) :
    cappedWeight x * categoricalDensity p (fun i => (x.val i).val) = cappedSymmetrizedWeight p x := by
  rw [categoricalDensity_eq, ← mul_assoc]
  have h : cappedWeight x * loadFactorial (fun i => (x.val i).val) = 1 := by
    unfold cappedWeight loadFactorial factorialWeight
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    apply inv_mul_cancel₀
    exact_mod_cast Nat.factorial_ne_zero (x.val i).val
  rw [h, one_mul]
  rfl

theorem capped_density_total (p : ι → Fin b → ℚ) :
    moment (cappedWeight (b := b) (q := q) (r := T))
      (fun x => categoricalDensity p (fun i => (x.val i).val)) = total (cappedCategoricalWeight (q := q) (T := T) p) := by
  rw [← capped_symmetrized_total]
  simp only [moment, total, capped_density_weight]

theorem capped_density_moment (p : ι → Fin b → ℚ) (F : CappedLoad b q T → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    moment cappedWeight (fun x => F x * categoricalDensity p (fun i => (x.val i).val)) =
      moment (cappedCategoricalWeight p) F := by
  rw [← capped_symmetrized_moment p F hF]
  unfold moment
  apply Finset.sum_congr rfl
  intro x _
  change cappedWeight x * (F x * categoricalDensity p (fun i => (x.val i).val)) = _
  rw [mul_left_comm (cappedWeight x) (F x), capped_density_weight, mul_comm]

theorem capped_categorical_concentration (p : ι → Fin b → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (horder : ∀ r, Antitone (p r))
    (hmass : 0 < total (cappedCategoricalWeight (q := q) (T := T) p))
    (F : CappedLoad b q T → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y) :
    expectation cappedWeight F ≤ expectation (cappedCategoricalWeight p) F := by
  have hnonempty : Nonempty (CappedLoad b q T) := by
    by_contra h
    have : IsEmpty (CappedLoad b q T) := not_nonempty_iff.mp h
    simp [total] at hmass
  have hZ : 0 < total (cappedWeight (b := b) (q := q) (r := T)) :=
    Finset.sum_pos (fun x _ => cappedWeight_pos x) (by
      obtain ⟨x⟩ := hnonempty
      exact ⟨x, Finset.mem_univ x⟩)
  have hcov := cappedAssociation_all b q T F
    (fun x => categoricalDensity p (fun i => (x.val i).val)) hF (by
      intro x y hxy
      exact categoricalDensity_majorization p hp horder _ _ (x.property.trans y.property.symm) hxy)
  unfold CovNonneg at hcov
  rw [capped_density_total, capped_density_moment p F (capped_increasing_symmetric F hF)] at hcov
  unfold expectation
  apply (div_le_div_iff₀ hZ hmass).mpr
  nlinarith

end MatchingCapacity
