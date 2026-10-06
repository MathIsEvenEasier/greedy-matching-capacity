import ConvolutionMinor
import CappedEfron

/-! Finite carriers with positive interval support. This module proves
closure under convolution and constructs carriers for arbitrary lists of caps. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem factorialWeight_succ_div (k : ℕ) :
    factorialWeight (k+1) = factorialWeight k / ((k : ℚ)+1) := by
  apply (eq_div_iff (by positivity)).2
  simpa only [mul_comm] using factorialWeight_step k

theorem factorialWeight_wide (i j d : ℕ) (hij : i ≤ j) :
    factorialWeight i * factorialWeight (j+d) ≤
      factorialWeight (i+d) * factorialWeight j := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : (0 : ℚ) < ((i+d : ℕ) : ℚ)+1 := by positivity
    have he : ((i+d : ℕ) : ℚ)+1 ≤ ((j+d : ℕ) : ℚ)+1 := by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hij d) 1
    have hp : 0 ≤ factorialWeight (i+d)*factorialWeight j :=
      mul_nonneg (le_of_lt (factorialWeight_pos _)) (le_of_lt (factorialWeight_pos _))
    simp only [Nat.add_succ, factorialWeight_succ_div, mul_div_assoc, div_mul_eq_mul_div]
    simpa only [mul_div_assoc] using
      (div_le_div_of_nonneg_right ih (by positivity)).trans
        (div_le_div_of_nonneg_left hp hd he)

theorem cappedCarrier_wide (q i j d : ℕ) (hij : i ≤ j) :
    cappedCarrier q i * cappedCarrier q (j+d) ≤ cappedCarrier q (i+d) * cappedCarrier q j := by
  by_cases hj : j+d ≤ q
  · have hi : i ≤ q := by omega
    have hid : i+d ≤ q := by omega
    have hj0 : j ≤ q := by omega
    simpa only [cappedCarrier, ite_eq_left hj, ite_eq_left hi,
      ite_eq_left hid, ite_eq_left hj0] using factorialWeight_wide i j d hij
  · have hz : cappedCarrier q (j+d) = 0 := by simp [cappedCarrier, hj]
    rw [hz, mul_zero]
    exact mul_nonneg (cappedCarrier_nonneg _ _) (cappedCarrier_nonneg _ _)

theorem integerCarrier_wide (q : ℕ) : WideLogConcave (integerCarrier q) := by
  intro i j d hij
  by_cases hi : 0 ≤ i
  · have hj : 0 ≤ j := by omega
    have hid : 0 ≤ i+d := by omega
    have hjd : 0 ≤ j+d := by omega
    have hti : (i+d).toNat = i.toNat+d := by omega
    have htj : (j+d).toNat = j.toNat+d := by omega
    simp only [integerCarrier, ite_eq_left hi, ite_eq_left hj,
      ite_eq_left hid, ite_eq_left hjd, hti, htj]
    exact cappedCarrier_wide q i.toNat j.toNat d (by omega)
  · have hz : integerCarrier q i = 0 := by simp [integerCarrier, hi]
    rw [hz, zero_mul]
    exact mul_nonneg (integerCarrier_nonneg _ _) (integerCarrier_nonneg _ _)

structure FiniteCarrier where
  cap : ℕ
  weight : ℤ → ℚ
  nonneg : ∀ k, 0 ≤ weight k
  positive_iff : ∀ k, 0 < weight k ↔ 0 ≤ k ∧ k ≤ cap
  wide : WideLogConcave weight

theorem FiniteCarrier.zero_outside (a : FiniteCarrier) (k : ℤ)
    (h : ¬ (0 ≤ k ∧ k ≤ a.cap)) : a.weight k = 0 := by
  have hn : ¬ 0 < a.weight k := by simpa only [a.positive_iff] using h
  exact le_antisymm (le_of_not_gt hn) (a.nonneg k)

def factorialCarrier (q : ℕ) : FiniteCarrier where
  cap := q
  weight := integerCarrier q
  nonneg := integerCarrier_nonneg q
  positive_iff := by
    intro k
    by_cases hk : 0 ≤ k
    · simp only [integerCarrier, ite_eq_left hk, cappedCarrier_pos_iff]
      omega
    · simp [integerCarrier, hk]
  wide := integerCarrier_wide q

theorem conv_nonneg (a b : FiniteCarrier) (s : ℤ) :
    0 ≤ finiteConv a.cap a.weight b.weight s := by
  exact Finset.sum_nonneg fun k _ => mul_nonneg (a.nonneg k) (b.nonneg (s-k))

theorem conv_zero_outside (a b : FiniteCarrier) (s : ℤ)
    (hs : ¬ (0 ≤ s ∧ s ≤ a.cap+b.cap)) : finiteConv a.cap a.weight b.weight s = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have h : ¬ (0 ≤ s-k ∧ s-k ≤ b.cap) := by omega
  rw [b.zero_outside (s-k) h, mul_zero]

theorem conv_pos (a b : FiniteCarrier) (s : ℤ)
    (hs : 0 ≤ s ∧ s ≤ a.cap+b.cap) : 0 < finiteConv a.cap a.weight b.weight s := by
  let k := min s.toNat a.cap
  have hks : (k : ℤ) ≤ s := by dsimp [k]; omega
  have hka : k ≤ a.cap := min_le_right _ _
  have hkb : 0 ≤ s-k ∧ s-k ≤ b.cap := by dsimp [k]; omega
  have hp : 0 < a.weight k*b.weight (s-k) :=
    mul_pos ((a.positive_iff k).mpr (by omega)) ((b.positive_iff (s-k)).mpr hkb)
  apply lt_of_lt_of_le hp
  unfold finiteConv
  apply Finset.single_le_sum (f := fun j : ℕ => a.weight j * b.weight (s-j)) (a := k)
  · intro j _
    exact mul_nonneg (a.nonneg j) (b.nonneg (s-j))
  · exact Finset.mem_range.mpr (by omega)

def carrierConv (a b : FiniteCarrier) : FiniteCarrier where
  cap := a.cap+b.cap
  weight := finiteConv a.cap a.weight b.weight
  nonneg := conv_nonneg a b
  positive_iff := by
    intro s
    constructor
    · intro hp
      by_contra hs
      have hz := conv_zero_outside a b s (by exact_mod_cast hs)
      rw [hz] at hp
      exact (lt_irrefl 0) hp
    · intro hs
      exact conv_pos a b s (by exact_mod_cast hs)
  wide := convolution_wide_logconcave a.cap a.weight b.weight
    (by intro k hk; exact a.zero_outside k (by omega))
    (by intro k hk; exact a.zero_outside k (by omega)) a.wide b.wide

def totalCap (cs : List FiniteCarrier) : ℕ := (cs.map FiniteCarrier.cap).sum

def carrierProduct : List FiniteCarrier → FiniteCarrier
  | [] => factorialCarrier 0
  | a :: cs => carrierConv a (carrierProduct cs)

theorem carrierProduct_cap (cs : List FiniteCarrier) : (carrierProduct cs).cap = totalCap cs := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    change a.cap + (carrierProduct cs).cap = a.cap + totalCap cs
    rw [ih]

def capProduct (qs : List ℕ) : FiniteCarrier := carrierProduct (qs.map factorialCarrier)

theorem totalCap_factorial (qs : List ℕ) : totalCap (qs.map factorialCarrier) = qs.sum := by
  simp only [totalCap, List.map_map]
  change (qs.map id).sum = qs.sum
  rw [List.map_id]

theorem capProduct_cap (qs : List ℕ) : (capProduct qs).cap = qs.sum := by
  rw [capProduct, carrierProduct_cap, totalCap_factorial]

theorem capProduct_step (qs : List ℕ) : StepLogConcave (capProduct qs).weight :=
  wide_implies_step _ (capProduct qs).wide

end MatchingCapacity
