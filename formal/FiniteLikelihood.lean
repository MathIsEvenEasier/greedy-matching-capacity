import FiniteTransport

/-! Monotone likelihood ratios imply ordered cumulative masses, including
zeros in either support. No division by point masses is used. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def CrossLE (p q : ℕ → ℚ) : Prop :=
  ∀ i j, i ≤ j → p j * q i ≤ p i * q j

theorem likelihood_identity (p q f : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (p i * q j - p j * q i) * (f j - f i)) =
      2 * (cumMass p n * (∑ i ∈ Finset.range n, q i * f i) -
        cumMass q n * (∑ i ∈ Finset.range n, p i * f i)) := by
  have he : ∀ i j, (p i * q j - p j * q i) * (f j - f i) =
      p i * (q j * f j) - (p i * f i) * q j -
      q i * (p j * f j) + (q i * f i) * p j := by intros; ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, cumMass]
  ring

theorem likelihood_moment (p q f : ℕ → ℚ) (n : ℕ)
    (hc : CrossLE p q) (hf : Monotone f) :
    cumMass q n * (∑ i ∈ Finset.range n, p i * f i) ≤
      cumMass p n * (∑ i ∈ Finset.range n, q i * f i) := by
  have h : 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (p i * q j - p j * q i) * (f j - f i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    rcases le_total i j with hij | hji
    · exact mul_nonneg (sub_nonneg.mpr (hc i j hij)) (sub_nonneg.mpr (hf hij))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hc j i hji))
        (sub_nonpos.mpr (hf hji))
  rw [likelihood_identity] at h
  linarith

theorem prefix_indicator (p : ℕ → ℚ) (k n : ℕ) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range n, if i < k then p i else 0) = cumMass p k := by
  rw [← Finset.sum_filter]
  have he : (Finset.range n).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  rfl

theorem prefix_tail (p : ℕ → ℚ) (k n : ℕ) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range n, p i * (if k ≤ i then 1 else 0)) = cumMass p n - cumMass p k := by
  have he : ∀ i, p i * (if k ≤ i then (1 : ℚ) else 0) =
      p i - (if i < k then p i else 0) := by
    intro i
    by_cases h : k ≤ i
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, prefix_indicator p k n hkn]
  rfl

theorem likelihood_cdf (p q : ℕ → ℚ) (n k : ℕ) (hkn : k ≤ n)
    (hp : cumMass p n = 1) (hq : cumMass q n = 1) (hc : CrossLE p q) :
    cumMass q k ≤ cumMass p k := by
  have hf : Monotone (fun i : ℕ => if k ≤ i then (1 : ℚ) else 0) := by
    intro i j hij
    by_cases hi : k ≤ i
    · simp [hi, hi.trans hij]
    · by_cases hj : k ≤ j <;> simp [hi, hj]
  have h := likelihood_moment p q _ n hc hf
  rw [prefix_tail p k n hkn, prefix_tail q k n hkn, hp, hq] at h
  linarith

def normalized (p : ℕ → ℚ) (n : ℕ) (i : ℕ) : ℚ := p i / cumMass p n

theorem prefix_normalized (p : ℕ → ℚ) (n k : ℕ) :
    cumMass (normalized p n) k = cumMass p k / cumMass p n := by
  simp only [cumMass, normalized, Finset.sum_div]

theorem normalized_total (p : ℕ → ℚ) (n : ℕ) (hp : 0 < cumMass p n) :
    cumMass (normalized p n) n = 1 := by
  rw [prefix_normalized, div_self (ne_of_gt hp)]

theorem normalized_cross (p q : ℕ → ℚ) (n m : ℕ)
    (hp : 0 < cumMass p n) (hq : 0 < cumMass q m) (hc : CrossLE p q) :
    CrossLE (normalized p n) (normalized q m) := by
  intro i j hij
  simp only [normalized, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (hc i j hij) (mul_nonneg (le_of_lt hp) (le_of_lt hq))

end MatchingCapacity
