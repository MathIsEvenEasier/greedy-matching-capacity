import PairCoefficients

/-! The two coefficient inequalities used by the matching argument.
These statements concern exact coefficients, including their factorial
weights and division by a common positive conditioning mass. -/
set_option autoImplicit false
open Polynomial
namespace MatchingCapacity
variable {ι : Type*} [DecidableEq ι]

theorem pair_boundary_coeff (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (q : ℕ) (hq : q ≤ s.card) (ht : s.card ≤ 2*q) :
    (pairPolynomial s u v).coeff (s.card-q) ≤ (pairPolynomial s u v).coeff q := by
  have h := normalizedPairCoeff_monotone s u v huv hv (s.card-q) q (by omega) hq
  unfold normalizedPairCoeff at h
  rw [Nat.choose_symm hq] at h
  have hp : (0 : ℚ) < (s.card.choose q : ℚ) := by
    exact_mod_cast Nat.choose_pos hq
  exact (div_le_div_iff_of_pos_right hp).mp h

theorem pair_boundary_conditional (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (q : ℕ) (hq : q ≤ s.card) (ht : s.card ≤ 2*q)
    (mass : ℚ) (hmass : 0 < mass) :
    (pairPolynomial s u v).coeff (s.card-q) / mass ≤
      (pairPolynomial s u v).coeff q / mass := by
  exact div_le_div_of_nonneg_right (pair_boundary_coeff s u v huv hv q hq ht) hmass.le

omit [DecidableEq ι] in
theorem pair_factorial_coeff (s : Finset ι) (u v : ι → ℚ)
    (a c : ℕ) (hac : a+c = s.card) :
    (a.factorial : ℚ)*(c.factorial : ℚ)*(pairPolynomial s u v).coeff a =
      (s.card.factorial : ℚ)*normalizedPairCoeff s u v a := by
  have ha : a ≤ s.card := by omega
  have hc : s.card-a = c := by omega
  have he : (s.card.choose a : ℚ)*(a.factorial : ℚ)*(c.factorial : ℚ) =
      (s.card.factorial : ℚ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial ha
    rw [hc] at hn
    exact_mod_cast hn
  have hp : (s.card.choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ha).ne'
  unfold normalizedPairCoeff
  rw [← he]
  field_simp [hp]

omit [DecidableEq ι] in
theorem pair_factorial_sum (s : Finset ι) (u v : ι → ℚ)
    (a c : ℕ) (hac : a+c = s.card) :
    (a.factorial : ℚ)*(c.factorial : ℚ)*
        ((pairPolynomial s u v).coeff a + (pairPolynomial s u v).coeff c) =
      (s.card.factorial : ℚ)*(normalizedPairCoeff s u v a + normalizedPairCoeff s u v c) := by
  rw [mul_add, mul_add, pair_factorial_coeff s u v a c hac]
  have hca : c+a = s.card := by omega
  rw [← pair_factorial_coeff s u v c a hca]
  ring

theorem pair_factorial_balancing (s : Finset ι) (u v : ι → ℚ)
    (huv : ∀ i ∈ s, v i ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (a c : ℕ) (hac : a+c = s.card) (hgap : c+2 ≤ a) :
    ((a-1).factorial : ℚ)*((c+1).factorial : ℚ)*
        ((pairPolynomial s u v).coeff (a-1) + (pairPolynomial s u v).coeff (c+1)) ≤
      (a.factorial : ℚ)*(c.factorial : ℚ)*
        ((pairPolynomial s u v).coeff a + (pairPolynomial s u v).coeff c) := by
  rw [pair_factorial_sum s u v (a-1) (c+1) (by omega), pair_factorial_sum s u v a c hac]
  exact mul_le_mul_of_nonneg_left
    (normalizedPairCoeff_balancing s u v huv hv a c hgap (by omega)) (by positivity)

end MatchingCapacity
