import FiniteCovariance

/-! Finite adjacent-level transport. Interlacing cumulative masses gives
an explicit coupling supported on i -> i and i -> i+1. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def cumMass (p : ℕ → ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, p i

theorem prefix_zero (p : ℕ → ℚ) : cumMass p 0 = 0 := by simp [cumMass]
theorem prefix_succ (p : ℕ → ℚ) (n : ℕ) :
    cumMass p (n+1) = cumMass p n + p n := Finset.sum_range_succ _ _

def stayMass (p q : ℕ → ℚ) (i : ℕ) : ℚ := cumMass q (i+1) - cumMass p i
def riseMass (p q : ℕ → ℚ) (i : ℕ) : ℚ := cumMass p (i+1) - cumMass q (i+1)

theorem transport_row (p q : ℕ → ℚ) (i : ℕ) :
    stayMass p q i + riseMass p q i = p i := by
  simp only [stayMass, riseMass, prefix_succ]
  ring

theorem transport_identity (p q g : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (stayMass p q i * g i + riseMass p q i * g (i+1))) =
      (∑ i ∈ Finset.range (n+1), q i * g i) +
        (cumMass p n - cumMass q (n+1)) * g n := by
  induction n with
  | zero => simp [cumMass, stayMass, riseMass]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i => q i * g i) (n+1)]
    simp only [stayMass, riseMass, prefix_succ]
    ring

theorem adjacent_transport_expectation (p q f g : ℕ → ℚ) (n : ℕ)
    (hp : cumMass p n = 1) (hq : cumMass q (n+1) = 1)
    (hleft : ∀ k, k ≤ n → cumMass q k ≤ cumMass p k)
    (hright : ∀ k, k ≤ n → cumMass p k ≤ cumMass q (k+1))
    (hf : ∀ i, i < n → f i ≤ g i)
    (hg : ∀ i, i < n → f i ≤ g (i+1)) :
    (∑ i ∈ Finset.range n, p i * f i) ≤ ∑ i ∈ Finset.range (n+1), q i * g i := by
  have ht := transport_identity p q g n
  rw [hp, hq] at ht
  simp only [sub_self, zero_mul, add_zero] at ht
  rw [← ht]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have ha : 0 ≤ stayMass p q i := sub_nonneg.mpr (hright i (by omega))
  have hb : 0 ≤ riseMass p q i := sub_nonneg.mpr (hleft (i+1) (by omega))
  have h1 := mul_le_mul_of_nonneg_left (hf i hi') ha
  have h2 := mul_le_mul_of_nonneg_left (hg i hi') hb
  rw [← transport_row p q i, add_mul]
  exact add_le_add h1 h2

end MatchingCapacity
