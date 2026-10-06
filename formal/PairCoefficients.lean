import FiniteCovariance
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic

/-! Normalized coefficients of an ordered pair-product polynomial.
A nonnegative binomial-basis expansion proves monotonicity and convexity
at every degree, with zero factors allowed. -/
set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace MatchingCapacity
noncomputable section
variable {ι : Type*} [DecidableEq ι]

def pairPolynomial (s : Finset ι) (u v : ι → ℚ) : ℚ[X] :=
  ∏ i ∈ s, (C (u i)*X + C (v i))

def pairWeight (s : Finset ι) (u v : ι → ℚ) (a : Finset ι) : ℚ :=
  (∏ i ∈ a, (u i-v i)) * ∏ i ∈ s \ a, v i

def pairBasis (s : Finset ι) (u v : ι → ℚ) (k : ℕ) : ℚ :=
  ∑ a ∈ s.powerset, pairWeight s u v a * ((k.choose a.card : ℚ) / (s.card.choose a.card : ℚ))

def normalizedPairCoeff (s : Finset ι) (u v : ι → ℚ) (k : ℕ) : ℚ :=
  (pairPolynomial s u v).coeff k / (s.card.choose k : ℚ)

theorem pairWeight_nonneg (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (a : Finset ι) (ha : a ⊆ s) : 0 ≤ pairWeight s u v a := by
  exact mul_nonneg
    (Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (huv i (ha hi))))
    (Finset.prod_nonneg (fun i hi => hv i (Finset.mem_sdiff.mp hi).1))

theorem pairPolynomial_expansion (s : Finset ι) (u v : ι → ℚ) :
    pairPolynomial s u v = ∑ a ∈ s.powerset,
      C (pairWeight s u v a) * ((1+X)^(s.card-a.card) * X^a.card) := by
  have he : pairPolynomial s u v =
      ∏ i ∈ s, (C (u i-v i)*X + C (v i)*(1+X)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [map_sub]
    ring
  rw [he, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro a ha
  have has := Finset.mem_powerset.mp ha
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← map_prod, ← map_prod]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset has]
  simp only [pairWeight, map_mul]
  ring

theorem choose_ratio_identity (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n) :
    (if j ≤ k then ((n-j).choose (k-j) : ℚ) else 0) / (n.choose k : ℚ) =
      (k.choose j : ℚ) / (n.choose j : ℚ) := by
  by_cases hjk : j ≤ k
  · rw [ite_eq_left hjk]
    have hkn : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    have hjn : (n.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    apply (div_eq_div_iff hkn hjn).mpr
    have h : (n.choose k : ℚ)*(k.choose j : ℚ) =
        (n.choose j : ℚ)*((n-j).choose (k-j) : ℚ) := by
      exact_mod_cast (Nat.choose_mul (n := n) hjk)
    nlinarith
  · simp only [ite_eq_right hjk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hjk),
      Nat.cast_zero, zero_div]

theorem normalizedPairCoeff_eq_basis (s : Finset ι) (u v : ι → ℚ) (k : ℕ)
    (hk : k ≤ s.card) : normalizedPairCoeff s u v k = pairBasis s u v k := by
  unfold normalizedPairCoeff pairBasis
  rw [pairPolynomial_expansion, Polynomial.finsetSum_coeff, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  simp only [Polynomial.coeff_one_add_X_pow]
  rw [mul_div_assoc, choose_ratio_identity s.card k a.card hk
    (Finset.card_le_card (Finset.mem_powerset.mp ha))]

theorem choose_second_difference_nonneg (k j : ℕ) :
    0 ≤ ((k+2).choose j : ℚ) - 2*((k+1).choose j : ℚ) + (k.choose j : ℚ) := by
  cases j with
  | zero => norm_num
  | succ j =>
    have h1 : ((k+1).choose (j+1) : ℚ) = (k.choose j : ℚ)+(k.choose (j+1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ' k j
    have h2 : ((k+2).choose (j+1) : ℚ) = ((k+1).choose j : ℚ)+((k+1).choose (j+1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ' (k+1) j
    have hm : (k.choose j : ℚ) ≤ ((k+1).choose j : ℚ) := by
      exact_mod_cast Nat.choose_le_succ k j
    linarith

theorem pairBasis_monotone (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    Monotone (pairBasis s u v) := by
  intro k l hkl
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left
  · apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.choose_le_choose a.card hkl
    · positivity
  · exact pairWeight_nonneg s u v huv hv a (Finset.mem_powerset.mp ha)

theorem pairBasis_convex (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) (k : ℕ) :
    0 ≤ pairBasis s u v (k+2) - 2*pairBasis s u v (k+1) + pairBasis s u v k := by
  have h : 0 ≤ ∑ a ∈ s.powerset,
      (pairWeight s u v a * (((k+2).choose a.card : ℚ)/(s.card.choose a.card : ℚ)) -
        2*(pairWeight s u v a * (((k+1).choose a.card : ℚ)/(s.card.choose a.card : ℚ))) +
        pairWeight s u v a * ((k.choose a.card : ℚ)/(s.card.choose a.card : ℚ))) := by
    apply Finset.sum_nonneg
    intro a ha
    have hw := pairWeight_nonneg s u v huv hv a (Finset.mem_powerset.mp ha)
    have he := mul_nonneg (div_nonneg hw (Nat.cast_nonneg (s.card.choose a.card)))
      (choose_second_difference_nonneg k a.card)
    convert he using 1
    ring
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, pairBasis] using h

theorem normalizedPairCoeff_monotone (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ s.card) :
    normalizedPairCoeff s u v k ≤ normalizedPairCoeff s u v l := by
  rw [normalizedPairCoeff_eq_basis s u v k (hkl.trans hl), normalizedPairCoeff_eq_basis s u v l hl]
  exact pairBasis_monotone s u v huv hv hkl

theorem normalizedPairCoeff_convex (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (k : ℕ) (hk : k+2 ≤ s.card) :
    0 ≤ normalizedPairCoeff s u v (k+2) - 2*normalizedPairCoeff s u v (k+1) +
      normalizedPairCoeff s u v k := by
  rw [normalizedPairCoeff_eq_basis s u v (k+2) hk,
    normalizedPairCoeff_eq_basis s u v (k+1) (by omega), normalizedPairCoeff_eq_basis s u v k (by omega)]
  exact pairBasis_convex s u v huv hv k

theorem pairBasis_difference_monotone (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    Monotone (fun k => pairBasis s u v (k+1) - pairBasis s u v k) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := pairBasis_convex s u v huv hv k
  change pairBasis s u v (k+1) - pairBasis s u v k ≤
    pairBasis s u v (k+2) - pairBasis s u v (k+1)
  linarith

theorem normalizedPairCoeff_balancing (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (a c : ℕ) (hgap : c+2 ≤ a) (ha : a ≤ s.card) :
    normalizedPairCoeff s u v (a-1) + normalizedPairCoeff s u v (c+1) ≤
      normalizedPairCoeff s u v a + normalizedPairCoeff s u v c := by
  rw [normalizedPairCoeff_eq_basis s u v (a-1) (by omega),
    normalizedPairCoeff_eq_basis s u v (c+1) (by omega),
    normalizedPairCoeff_eq_basis s u v a ha, normalizedPairCoeff_eq_basis s u v c (by omega)]
  have h := pairBasis_difference_monotone s u v huv hv (show c ≤ a-1 by omega)
  have he : a-1+1 = a := by omega
  dsimp only at h
  rw [he] at h
  linarith

end
end MatchingCapacity
