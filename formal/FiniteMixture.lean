import FiniteCovariance

/-! Averaging conditional bounds, with explicit treatment of null pieces. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι]

theorem finite_zero_mass (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (hz : (∑ i, w i) = 0) :
    ∀ i, w i = 0 := by
  intro i
  have hi : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  rw [hz] at hi
  exact le_antisymm hi (hw i)

theorem finite_null_moment (w f : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (hz : (∑ i, w i) = 0) :
    (∑ i, w i * f i) = 0 := by
  simp only [finite_zero_mass w hw hz, zero_mul, Finset.sum_const_zero]

theorem conditional_bound_unnormalized (M N c : ℚ) (hM : 0 ≤ M)
    (hz : M = 0 → N = 0) (hb : 0 < M → c ≤ N/M) : c*M ≤ N := by
  by_cases h : M = 0
  · simp [h, hz h]
  · exact (le_div_iff₀ (lt_of_le_of_ne hM (Ne.symm h))).mp (hb (lt_of_le_of_ne hM (Ne.symm h)))

theorem conditional_eq_unnormalized (M N c : ℚ) (hM : 0 ≤ M)
    (hz : M = 0 → N = 0) (hb : 0 < M → N/M = c) : N = c*M := by
  by_cases h : M = 0
  · simp [h, hz h]
  · exact (div_eq_iff h).mp (hb (lt_of_le_of_ne hM (Ne.symm h)))

theorem finite_mixture_bound (M N : ι → ℚ) (c : ℚ) (hM : ∀ i, 0 ≤ M i)
    (hz : ∀ i, M i = 0 → N i = 0) (hb : ∀ i, 0 < M i → c ≤ N i/M i)
    (hp : 0 < ∑ i, M i) : c ≤ (∑ i, N i)/(∑ i, M i) := by
  apply (le_div_iff₀ hp).mpr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => conditional_bound_unnormalized (M i) (N i) c (hM i) (hz i) (hb i))

theorem finite_mixture_eq (M N : ι → ℚ) (c : ℚ) (hM : ∀ i, 0 ≤ M i)
    (hz : ∀ i, M i = 0 → N i = 0) (hb : ∀ i, 0 < M i → N i/M i = c)
    (hp : 0 < ∑ i, M i) : (∑ i, N i)/(∑ i, M i) = c := by
  apply (div_eq_iff (ne_of_gt hp)).mpr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => conditional_eq_unnormalized (M i) (N i) c (hM i) (hz i) (hb i))

end MatchingCapacity
