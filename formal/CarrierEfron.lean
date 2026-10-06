import CarrierConvolution

/-! The pair theorem applies to arbitrary finite interval carriers, hence
also to a block sum created by any finite number of convolutions. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem conv_eq_layer (a b : FiniteCarrier) (s : ℕ) :
    finiteConv a.cap a.weight b.weight s = cumMass (sumLayer a.weight b.weight s) (s+1) := by
  by_cases h : a.cap ≤ s
  · exact (convolution_extend a.cap (s+1) a.weight b.weight s (by omega)
      (by intro k hk; exact a.zero_outside k (by omega))).symm
  · symm
    apply Finset.sum_subset (Finset.range_mono (show s+1 ≤ a.cap+1 by omega))
    intro k _ hk
    have hk' : s < k := by simp only [Finset.mem_range] at hk; omega
    change a.weight k * b.weight ((s : ℤ)-k) = 0
    rw [b.zero_outside ((s : ℤ)-k) (by omega), mul_zero]

theorem carrier_layer_mass_pos (a b : FiniteCarrier) (s : ℕ) (hs : s ≤ a.cap+b.cap) :
    0 < cumMass (sumLayer a.weight b.weight s) (s+1) := by
  rw [← conv_eq_layer]
  exact conv_pos a b s (by exact_mod_cast (show 0 ≤ s ∧ s ≤ a.cap+b.cap from ⟨Nat.zero_le s, hs⟩))

theorem carrier_efron_adjacent (a b : FiniteCarrier) (s : ℕ) (hs : s < a.cap+b.cap)
    (φ : ℕ → ℕ → ℚ) (hφ : ∀ i j k l, i ≤ k → j ≤ l → φ i j ≤ φ k l) :
    twoExpectation a.weight b.weight s φ ≤ twoExpectation a.weight b.weight (s+1) φ := by
  apply efron_two_adjacent _ _ _ _ a.nonneg b.nonneg
    (a.zero_outside (-1) (by omega)) (b.zero_outside (-1) (by omega))
    (wide_implies_step _ a.wide) (wide_implies_step _ b.wide)
    (carrier_layer_mass_pos a b s (by omega))
  · simpa only [Nat.cast_add, Nat.cast_one] using carrier_layer_mass_pos a b (s+1) (by omega)
  · exact hφ

theorem carrier_efron_monotone (a b : FiniteCarrier) (s t : ℕ)
    (hst : s ≤ t) (ht : t ≤ a.cap+b.cap) (φ : ℕ → ℕ → ℚ)
    (hφ : ∀ i j k l, i ≤ k → j ≤ l → φ i j ≤ φ k l) :
    twoExpectation a.weight b.weight s φ ≤ twoExpectation a.weight b.weight t φ := by
  have hm : Monotone (fun n => twoExpectation a.weight b.weight (min n (a.cap+b.cap)) φ) := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n < a.cap+b.cap
    · simpa only [Nat.min_eq_left (show n ≤ a.cap+b.cap by omega),
        Nat.min_eq_left (show n+1 ≤ a.cap+b.cap by omega)] using carrier_efron_adjacent a b n hn φ hφ
    · simp only [Nat.min_eq_right (show a.cap+b.cap ≤ n by omega),
        Nat.min_eq_right (show a.cap+b.cap ≤ n+1 by omega), le_refl]
  simpa only [Nat.min_eq_left (hst.trans ht), Nat.min_eq_left ht] using hm hst

end MatchingCapacity
