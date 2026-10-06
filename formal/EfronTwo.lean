import FiniteLikelihood

/-! The adjacent-sum two-variable Efron theorem, for nonnegative integer
carriers whose adjacent ratios decrease in cross-multiplied form. The
explicit transport increases exactly one coordinate by one. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def StepLogConcave (a : ℤ → ℚ) : Prop :=
  ∀ i j, i ≤ j → a i * a (j+1) ≤ a (i+1) * a j

def sumLayer (a b : ℤ → ℚ) (s : ℤ) (i : ℕ) : ℚ := a i * b (s-i)
def shiftedLayer (a b : ℤ → ℚ) (s : ℤ) (i : ℕ) : ℚ := a ((i : ℤ)-1) * b (s+1-i)

def rightShift (p : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | i+1 => p i

theorem prefix_rightShift (p : ℕ → ℚ) (n : ℕ) :
    cumMass (rightShift p) (n+1) = cumMass p n := by
  induction n with
  | zero => simp [cumMass, rightShift]
  | succ n ih =>
    rw [prefix_succ, ih, prefix_succ]
    rfl

theorem normalized_rightShift (p : ℕ → ℚ) (n : ℕ) :
    normalized (rightShift p) (n+1) = rightShift (normalized p n) := by
  funext i
  cases i <;> simp [normalized, rightShift, prefix_rightShift]

theorem shiftedLayer_eq (a b : ℤ → ℚ) (s : ℤ) (ha : a (-1) = 0) :
    shiftedLayer a b s = rightShift (sumLayer a b s) := by
  funext i
  cases i with
  | zero => simp [shiftedLayer, rightShift, ha]
  | succ i =>
    simp only [shiftedLayer, rightShift, sumLayer, Nat.cast_add, Nat.cast_one]
    congr 1 <;> congr 1 <;> ring

theorem layer_cross (a b : ℤ → ℚ) (s : ℤ)
    (ha : ∀ i, 0 ≤ a i) (hb : StepLogConcave b) :
    CrossLE (sumLayer a b s) (sumLayer a b (s+1)) := by
  intro i j hij
  have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
  have h := mul_le_mul_of_nonneg_left (hb (s-j) (s-i) (by omega))
    (mul_nonneg (ha i) (ha j))
  convert h using 1 <;> simp only [sumLayer] <;> ring_nf

theorem shifted_layer_cross (a b : ℤ → ℚ) (s : ℤ)
    (ha : StepLogConcave a) (hb : ∀ i, 0 ≤ b i) :
    CrossLE (sumLayer a b (s+1)) (shiftedLayer a b s) := by
  intro i j hij
  have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
  have h := mul_le_mul_of_nonneg_left (ha ((i : ℤ)-1) ((j : ℤ)-1) (by omega))
    (mul_nonneg (hb (s+1-i)) (hb (s+1-j)))
  convert h using 1 <;> simp only [sumLayer, shiftedLayer] <;> ring_nf

def twoExpectation (a b : ℤ → ℚ) (s : ℕ) (φ : ℕ → ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range (s+1), normalized (sumLayer a b s) (s+1) i * φ i (s-i)

theorem efron_two_adjacent (a b : ℤ → ℚ) (s : ℕ) (φ : ℕ → ℕ → ℚ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ha0 : a (-1) = 0) (hb0 : b (-1) = 0)
    (hla : StepLogConcave a) (hlb : StepLogConcave b)
    (hZ : 0 < cumMass (sumLayer a b s) (s+1))
    (hZ' : 0 < cumMass (sumLayer a b ((s : ℤ)+1)) (s+2))
    (hφ : ∀ i j k l, i ≤ k → j ≤ l → φ i j ≤ φ k l) :
    twoExpectation a b s φ ≤ twoExpectation a b (s+1) φ := by
  let p := normalized (sumLayer a b s) (s+1)
  let q := normalized (sumLayer a b ((s : ℤ)+1)) (s+2)
  have hp : cumMass p (s+1) = 1 := normalized_total _ _ hZ
  have hq : cumMass q (s+2) = 1 := normalized_total _ _ hZ'
  have hpLast : p (s+1) = 0 := by
    simp [p, normalized, sumLayer, hb0]
  have hp' : cumMass p (s+2) = 1 := by
    rw [prefix_succ, hp, hpLast, add_zero]
  have hsp : cumMass (rightShift p) (s+2) = 1 := by
    rw [prefix_rightShift, hp]
  have hc : CrossLE p q := normalized_cross _ _ _ _ hZ hZ' (layer_cross a b s ha hlb)
  have hsc : CrossLE q (rightShift p) := by
    have hc0 : CrossLE (sumLayer a b ((s : ℤ)+1)) (rightShift (sumLayer a b s)) := by
      rw [← shiftedLayer_eq a b s ha0]
      exact shifted_layer_cross a b s hla hb
    have hz : 0 < cumMass (rightShift (sumLayer a b s)) (s+2) := by
      rw [prefix_rightShift]
      exact hZ
    have hc1 := normalized_cross _ _ (s+2) (s+2) hZ' hz hc0
    rw [normalized_rightShift] at hc1
    exact hc1
  have hleft : ∀ k, k ≤ s+1 → cumMass q k ≤ cumMass p k := by
    intro k hk
    exact likelihood_cdf p q (s+2) k (by omega) hp' hq hc
  have hright : ∀ k, k ≤ s+1 → cumMass p k ≤ cumMass q (k+1) := by
    intro k hk
    have h := likelihood_cdf q (rightShift p) (s+2) (k+1) (by omega) hq hsp hsc
    rwa [prefix_rightShift] at h
  have ht := adjacent_transport_expectation p q
    (fun i => φ i (s-i)) (fun i => φ i (s+1-i)) (s+1) hp hq hleft hright
    (by intro i hi; exact hφ i (s-i) i (s+1-i) le_rfl (by omega))
    (by intro i hi; exact hφ i (s-i) (i+1) (s+1-(i+1)) (by omega) (by omega))
  simpa only [twoExpectation, Nat.cast_add, Nat.cast_one] using ht

end MatchingCapacity
