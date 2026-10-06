import FiniteTransport

/-! Rational interval-overlap coupling. Both marginals and ordered support
are proved explicitly, including zero atoms. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def quantileMass (p q : ℕ → ℚ) (i j : ℕ) : ℚ :=
  min (cumMass p (i+1)) (cumMass q (j+1)) -
  min (cumMass p i) (cumMass q (j+1)) -
  min (cumMass p (i+1)) (cumMass q j) + min (cumMass p i) (cumMass q j)

theorem cumMass_nonneg (p : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i) (n : ℕ) :
    0 ≤ cumMass p n := Finset.sum_nonneg (fun i _ => hp i)

theorem cumMass_mono (p : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i) : Monotone (cumMass p) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [prefix_succ]
  exact le_add_of_nonneg_right (hp n)

theorem min_rectangle_nonneg (a b c d : ℚ) (hab : a ≤ b) (hcd : c ≤ d) :
    0 ≤ min b d - min a d - min b c + min a c := by
  simp only [min_def]
  split_ifs <;> linarith

theorem quantileMass_nonneg (p q : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (i j : ℕ) : 0 ≤ quantileMass p q i j :=
  min_rectangle_nonneg _ _ _ _ (cumMass_mono p hp (Nat.le_succ i))
    (cumMass_mono q hq (Nat.le_succ j))

theorem quantileMass_symm (p q : ℕ → ℚ) (i j : ℕ) :
    quantileMass p q i j = quantileMass q p j i := by
  simp only [quantileMass, min_comm]
  ring

theorem quantile_row_telescope (p q : ℕ → ℚ) (i n : ℕ) :
    (∑ j ∈ Finset.range n, quantileMass p q i j) =
      min (cumMass p (i+1)) (cumMass q n) - min (cumMass p i) (cumMass q n) -
      min (cumMass p (i+1)) 0 + min (cumMass p i) 0 := by
  induction n with
  | zero => simp only [Finset.sum_range_zero, prefix_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold quantileMass
    ring

theorem quantile_row (p q : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i)
    (n : ℕ) (hpn : cumMass p n = 1) (hqn : cumMass q n = 1)
    (i : ℕ) (hi : i < n) :
    (∑ j ∈ Finset.range n, quantileMass p q i j) = p i := by
  have h0 := cumMass_nonneg p hp i
  have h1 := cumMass_nonneg p hp (i+1)
  have hu := cumMass_mono p hp (show i+1 ≤ n by omega)
  rw [hpn] at hu
  have hu' := (cumMass_mono p hp (Nat.le_succ i)).trans hu
  rw [quantile_row_telescope, hqn, min_eq_left hu, min_eq_left hu',
    min_eq_right h1, min_eq_right h0, prefix_succ]
  ring

theorem quantile_column (p q : ℕ → ℚ) (hq : ∀ i, 0 ≤ q i)
    (n : ℕ) (hpn : cumMass p n = 1) (hqn : cumMass q n = 1)
    (j : ℕ) (hj : j < n) :
    (∑ i ∈ Finset.range n, quantileMass p q i j) = q j := by
  simp only [quantileMass_symm p q]
  exact quantile_row q p hq n hqn hpn j hj

theorem quantile_ordered_support (p q : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (n : ℕ)
    (hc : ∀ k, k ≤ n → cumMass q k ≤ cumMass p k)
    (i j : ℕ) (hi : i < n) (hji : j < i) : quantileMass p q i j = 0 := by
  have h := (hc (j+1) (by omega)).trans (cumMass_mono p hp (by omega : j+1 ≤ i))
  have hpstep := cumMass_mono p hp (Nat.le_succ i)
  have hqstep := cumMass_mono q hq (Nat.le_succ j)
  rw [quantileMass, min_eq_right (h.trans hpstep), min_eq_right h,
    min_eq_right (hqstep.trans (h.trans hpstep)), min_eq_right (hqstep.trans h)]
  ring

theorem ordered_quantile_coupling (p q : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (n : ℕ) (hpn : cumMass p n = 1) (hqn : cumMass q n = 1)
    (hc : ∀ k, k ≤ n → cumMass q k ≤ cumMass p k) :
    ∃ c : Fin n → Fin n → ℚ,
      (∀ i j, 0 ≤ c i j) ∧ (∀ i, ∑ j, c i j = p i.val) ∧
      (∀ j, ∑ i, c i j = q j.val) ∧ (∀ i j, j < i → c i j = 0) := by
  refine ⟨fun i j => quantileMass p q i.val j.val, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact quantileMass_nonneg p q hp hq i.val j.val
  · intro i
    change (∑ j : Fin n, quantileMass p q i.val j.val) = p i.val
    rw [Fin.sum_univ_eq_sum_range]
    exact quantile_row p q hp n hpn hqn i.val i.isLt
  · intro j
    change (∑ i : Fin n, quantileMass p q i.val j.val) = q j.val
    rw [Fin.sum_univ_eq_sum_range (fun i => quantileMass p q i j.val)]
    exact quantile_column p q hq n hpn hqn j.val j.isLt
  · intro i j hij
    exact quantile_ordered_support p q hp hq n hc i.val j.val i.isLt hij

end MatchingCapacity
