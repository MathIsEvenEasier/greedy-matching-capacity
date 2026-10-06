import BernoulliCoupling
import FiniteMixture

/-! Exact two-point moments, including null conditioning events. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι]

theorem indicator_ratio_bounds (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (P : ι → Prop) [DecidablePred P] :
    0 ≤ (∑ i, w i * (if P i then 1 else 0)) / (∑ i, w i) ∧
    (∑ i, w i * (if P i then 1 else 0)) / (∑ i, w i) ≤ 1 := by
  have hD : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hC : 0 ≤ ∑ i, w i * (if P i then 1 else 0) := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> simp [hw i]
  have hCD : (∑ i, w i * (if P i then 1 else 0)) ≤ ∑ i, w i := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp [hw i]
  refine ⟨div_nonneg hC hD, ?_⟩
  by_cases hz : (∑ i, w i) = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne hD (Ne.symm hz))).mpr hCD

theorem twoPoint_raw_moment (w : ι → ℚ) (v : ι → ℕ) (a : ℕ)
    (hs : ∀ i, v i ≠ a → v i ≠ a+1 → w i = 0) (F : ℕ → ℚ) :
    (∑ i, w i * F (v i)) =
      ((∑ i, w i) - ∑ i, w i * (if v i = a+1 then 1 else 0)) * F a +
        (∑ i, w i * (if v i = a+1 then 1 else 0)) * F (a+1) := by
  rw [sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v i = a
  · simp [h]
  · by_cases h' : v i = a+1
    · simp [h']
    · simp [hs i h h']

theorem twoPoint_bernoulli_moment (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (v : ι → ℕ) (a : ℕ) (hs : ∀ i, v i ≠ a → v i ≠ a+1 → w i = 0)
    (F : ℕ → ℚ) :
    (∑ i, w i * F (v i)) = ∑ b : Bool,
      (∑ i, w i) * bernoulliMass
        ((∑ i, w i * (if v i = a+1 then 1 else 0)) / (∑ i, w i)) b * F (a+b.toNat) := by
  by_cases hz : (∑ i, w i) = 0
  · simp only [finite_zero_mass w hw hz, zero_mul, Finset.sum_const_zero]
  · rw [twoPoint_raw_moment w v a hs F]
    simp only [Fintype.sum_bool, bernoulliMass, Bool.toNat_true, Bool.toNat_false,
      Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
    field_simp
    ring

end MatchingCapacity
