import EfronTwo
import CappedCarrier

/-! The carrier hypotheses of the two-variable Efron theorem are proved
for arbitrary rectangular caps, including the zero boundaries. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem factorialWeight_cross (i j : ℕ) (hij : i ≤ j) :
    factorialWeight i * factorialWeight (j+1) ≤
      factorialWeight (i+1) * factorialWeight j := by
  have hij' : (i : ℚ)+1 ≤ (j : ℚ)+1 := by exact_mod_cast Nat.add_le_add_right hij 1
  have hn := mul_nonneg (le_of_lt (factorialWeight_pos (i+1)))
    (le_of_lt (factorialWeight_pos (j+1)))
  calc
    factorialWeight i * factorialWeight (j+1) =
        ((i : ℚ)+1) * (factorialWeight (i+1) * factorialWeight (j+1)) := by
      rw [← factorialWeight_step i]; ring
    _ ≤ ((j : ℚ)+1) * (factorialWeight (i+1) * factorialWeight (j+1)) :=
      mul_le_mul_of_nonneg_right hij' hn
    _ = factorialWeight (i+1) * factorialWeight j := by
      rw [← factorialWeight_step j]; ring

theorem cappedCarrier_cross (q i j : ℕ) (hij : i ≤ j) :
    cappedCarrier q i * cappedCarrier q (j+1) ≤
      cappedCarrier q (i+1) * cappedCarrier q j := by
  by_cases hj : j+1 ≤ q
  · have hi : i ≤ q := by omega
    have hi1 : i+1 ≤ q := by omega
    have hj0 : j ≤ q := by omega
    simpa only [cappedCarrier, ite_eq_left hj, ite_eq_left hi,
      ite_eq_left hi1, ite_eq_left hj0] using factorialWeight_cross i j hij
  · have hz : cappedCarrier q (j+1) = 0 := by simp [cappedCarrier, hj]
    rw [hz, mul_zero]
    exact mul_nonneg (cappedCarrier_nonneg q (i+1)) (cappedCarrier_nonneg q j)

def integerCarrier (q : ℕ) (k : ℤ) : ℚ :=
  if 0 ≤ k then cappedCarrier q k.toNat else 0

theorem integerCarrier_nat (q k : ℕ) : integerCarrier q k = cappedCarrier q k := by
  simp [integerCarrier]

theorem integerCarrier_nonneg (q : ℕ) (k : ℤ) : 0 ≤ integerCarrier q k := by
  unfold integerCarrier
  split
  · exact cappedCarrier_nonneg _ _
  · exact le_rfl

theorem integerCarrier_neg_one (q : ℕ) : integerCarrier q (-1) = 0 := by
  norm_num [integerCarrier]

theorem integerCarrier_step_logconcave (q : ℕ) : StepLogConcave (integerCarrier q) := by
  intro i j hij
  by_cases hi : 0 ≤ i
  · have hj : 0 ≤ j := by omega
    have hi1 : 0 ≤ i+1 := by omega
    have hj1 : 0 ≤ j+1 := by omega
    have hti : (i+1).toNat = i.toNat+1 := by omega
    have htj : (j+1).toNat = j.toNat+1 := by omega
    simp only [integerCarrier, ite_eq_left hi, ite_eq_left hj,
      ite_eq_left hi1, ite_eq_left hj1, hti, htj]
    exact cappedCarrier_cross q i.toNat j.toNat (by omega)
  · have hz : integerCarrier q i = 0 := by simp [integerCarrier, hi]
    rw [hz, zero_mul]
    exact mul_nonneg (integerCarrier_nonneg q (i+1)) (integerCarrier_nonneg q j)

theorem capped_layer_mass_pos (q r s : ℕ) (hs : s ≤ q+r) :
    0 < cumMass (sumLayer (integerCarrier q) (integerCarrier r) s) (s+1) := by
  let i := min s q
  have his : i ≤ s := min_le_left _ _
  have hiq : i ≤ q := min_le_right _ _
  have hir : s-i ≤ r := by dsimp [i]; omega
  have hd : (s : ℤ) - (i : ℤ) = ((s-i : ℕ) : ℤ) := by omega
  have hp : 0 < sumLayer (integerCarrier q) (integerCarrier r) s i := by
    rw [sumLayer, hd, integerCarrier_nat, integerCarrier_nat]
    exact mul_pos ((cappedCarrier_pos_iff q i).mpr hiq)
      ((cappedCarrier_pos_iff r (s-i)).mpr hir)
  have hb : sumLayer (integerCarrier q) (integerCarrier r) s i ≤
      cumMass (sumLayer (integerCarrier q) (integerCarrier r) s) (s+1) := by
    apply Finset.single_le_sum
    · intro j _
      exact mul_nonneg (integerCarrier_nonneg q j) (integerCarrier_nonneg r ((s : ℤ)-j))
    · exact Finset.mem_range.mpr (by omega)
  exact lt_of_lt_of_le hp hb

theorem capped_efron_adjacent (q r s : ℕ) (hs : s < q+r) (φ : ℕ → ℕ → ℚ)
    (hφ : ∀ i j k l, i ≤ k → j ≤ l → φ i j ≤ φ k l) :
    twoExpectation (integerCarrier q) (integerCarrier r) s φ ≤
      twoExpectation (integerCarrier q) (integerCarrier r) (s+1) φ := by
  apply efron_two_adjacent _ _ _ _ (integerCarrier_nonneg q) (integerCarrier_nonneg r)
    (integerCarrier_neg_one q) (integerCarrier_neg_one r)
    (integerCarrier_step_logconcave q) (integerCarrier_step_logconcave r)
    (capped_layer_mass_pos q r s (by omega))
  · simpa only [Nat.cast_add, Nat.cast_one] using capped_layer_mass_pos q r (s+1) (by omega)
  · exact hφ

theorem capped_efron_monotone (q r s t : ℕ) (hst : s ≤ t) (ht : t ≤ q+r)
    (φ : ℕ → ℕ → ℚ)
    (hφ : ∀ i j k l, i ≤ k → j ≤ l → φ i j ≤ φ k l) :
    twoExpectation (integerCarrier q) (integerCarrier r) s φ ≤
      twoExpectation (integerCarrier q) (integerCarrier r) t φ := by
  have hm : Monotone (fun n =>
      twoExpectation (integerCarrier q) (integerCarrier r) (min n (q+r)) φ) := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n < q+r
    · simpa only [Nat.min_eq_left (show n ≤ q+r by omega),
        Nat.min_eq_left (show n+1 ≤ q+r by omega)] using capped_efron_adjacent q r n hn φ hφ
    · simp only [Nat.min_eq_right (show q+r ≤ n by omega),
        Nat.min_eq_right (show q+r ≤ n+1 by omega), le_refl]
  simpa only [Nat.min_eq_left (hst.trans ht), Nat.min_eq_left ht] using hm hst

end MatchingCapacity
