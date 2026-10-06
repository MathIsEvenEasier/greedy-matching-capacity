import EfronTwo

/-! A finite two-by-two Cauchy--Binet identity and convolution preservation
of cross-multiplied log-concavity. All sums are finite rational sums. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def WideLogConcave (a : ℤ → ℚ) : Prop :=
  ∀ i j : ℤ, ∀ d : ℕ, i ≤ j → a i * a (j+d) ≤ a (i+d) * a j

theorem wide_implies_step (a : ℤ → ℚ) (ha : WideLogConcave a) : StepLogConcave a := by
  intro i j hij
  exact ha i j 1 hij

theorem minor_composition_identity (a b c d : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (a i*b j-a j*b i)*(c i*d j-c j*d i)) =
    2 * ((∑ i ∈ Finset.range n, a i*c i)*(∑ i ∈ Finset.range n, b i*d i) -
      (∑ i ∈ Finset.range n, a i*d i)*(∑ i ∈ Finset.range n, b i*c i)) := by
  have he : ∀ i j, (a i*b j-a j*b i)*(c i*d j-c j*d i) =
      (a i*c i)*(b j*d j) - (a i*d i)*(b j*c j) -
      (b i*c i)*(a j*d j) + (b i*d i)*(a j*c j) := by intros; ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem cross_composition (a b c d : ℕ → ℚ) (n : ℕ)
    (hab : CrossLE a b) (hcd : CrossLE c d) :
    (∑ i ∈ Finset.range n, a i*d i)*(∑ i ∈ Finset.range n, b i*c i) ≤
      (∑ i ∈ Finset.range n, a i*c i)*(∑ i ∈ Finset.range n, b i*d i) := by
  have h : 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (a i*b j-a j*b i)*(c i*d j-c j*d i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    rcases le_total i j with hij | hji
    · exact mul_nonneg (sub_nonneg.mpr (hab i j hij)) (sub_nonneg.mpr (hcd i j hij))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hab j i hji))
        (sub_nonpos.mpr (hcd j i hji))
  rw [minor_composition_identity] at h
  linarith

def finiteConv (A : ℕ) (a b : ℤ → ℚ) (s : ℤ) : ℚ :=
  ∑ k ∈ Finset.range (A+1), a k * b (s-k)

theorem convolution_extend (A N : ℕ) (a b : ℤ → ℚ) (s : ℤ)
    (hN : A+1 ≤ N) (ha : ∀ k : ℤ, A < k → a k = 0) :
    (∑ k ∈ Finset.range N, a k * b (s-k)) = finiteConv A a b s := by
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro k _ hk
  have hk' : A < (k : ℤ) := by
    simp only [Finset.mem_range] at hk
    omega
  rw [ha k hk', zero_mul]

theorem convolution_shift (A d : ℕ) (a b : ℤ → ℚ) (s : ℤ)
    (ha : ∀ k : ℤ, k < 0 → a k = 0) :
    (∑ k ∈ Finset.range (A+d+1), a ((k : ℤ)-d) * b (s+d-k)) = finiteConv A a b s := by
  rw [show A+d+1 = d+(A+1) by omega, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range d, a ((k : ℤ)-d) * b (s+d-k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [ha ((k : ℤ)-d) (by omega), zero_mul]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.cast_add]
  congr 1 <;> congr 1 <;> ring

theorem convolution_wide_logconcave (A : ℕ) (a b : ℤ → ℚ)
    (haNeg : ∀ k : ℤ, k < 0 → a k = 0)
    (haTop : ∀ k : ℤ, A < k → a k = 0)
    (ha : WideLogConcave a) (hb : WideLogConcave b) :
    WideLogConcave (finiteConv A a b) := by
  intro i j d hij
  let f : ℕ → ℚ := fun k => a k
  let g : ℕ → ℚ := fun k => a ((k : ℤ)-d)
  let u : ℕ → ℚ := fun k => b (i+d-k)
  let v : ℕ → ℚ := fun k => b (j+d-k)
  have hfg : CrossLE f g := by
    intro k l hkl
    have hh := ha ((k : ℤ)-d) ((l : ℤ)-d) d (by omega)
    convert hh using 1 <;> dsimp [f, g] <;> ring_nf
  have huv : CrossLE u v := by
    intro k l hkl
    have he : ((j-i).toNat : ℤ) = j-i := by omega
    have hh := hb (i+d-l) (i+d-k) (j-i).toNat (by omega)
    convert hh using 1 <;> dsimp [u, v] <;> rw [he] <;> ring_nf
  have h := cross_composition f g u v (A+d+1) hfg huv
  dsimp [f, g, u, v] at h
  rw [convolution_extend A (A+d+1) a b (j+d) (by omega) haTop,
    convolution_shift A d a b i haNeg,
    convolution_extend A (A+d+1) a b (i+d) (by omega) haTop,
    convolution_shift A d a b j haNeg] at h
  simpa only [mul_comm] using h

end MatchingCapacity
