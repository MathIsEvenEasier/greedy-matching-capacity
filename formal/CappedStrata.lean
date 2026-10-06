import CappedTieComparison

/-! Exact conditioning on the number of maximal coordinates. Deleting one
of a positive, fixed number of maxima gives the next tie stratum exactly.
The zero-tie endpoint is the law with a strictly smaller cap. No monotonicity
of the conditional expectation between different strata is assumed proved. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def tieWeight {b q r : ℕ} (k : ℕ) (x : CappedLoad b q r) : ℚ :=
  if maxCount x = k then cappedWeight x else 0

def tieGate {b q r : ℕ} (k : ℕ) (F : CappedLoad b q r → ℚ) (x : CappedLoad b q r) : ℚ :=
  if maxCount x = k then F x else 0

theorem tieWeight_nonneg {b q r : ℕ} (k : ℕ) (x : CappedLoad b q r) :
    0 ≤ tieWeight k x := by
  unfold tieWeight
  split
  · exact le_of_lt (cappedWeight_pos x)
  · exact le_rfl

theorem tieGate_symmetric {b q r : ℕ} (k : ℕ) (F : CappedLoad b q r → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) (e : Equiv.Perm (Fin b)) (x : CappedLoad b q r) :
    tieGate k F (permuteCapped e x) = tieGate k F x := by
  simp only [tieGate, maxCount_permute, hF]

theorem tieBias_moment_gate {b q r : ℕ} (k : ℕ) (F : CappedLoad b q r → ℚ) :
    moment (sizeBias maximumWeight (fun x : CappedLoad b q r => (maxCount x : ℚ)))
      (tieGate (k+1) F) = ((k+1 : ℕ) : ℚ) * moment (tieWeight (k+1)) F := by
  unfold moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : maxCount x = k+1
  · have hp : 0 < maxCount x := by omega
    simp only [sizeBias, maximumWeight, tieGate, tieWeight]
    simp only [ite_eq_left hp, ite_eq_left hx]
    rw [hx]
    ring
  · simp [sizeBias, tieGate, tieWeight, hx]

theorem fixedMaximum_moment_gate_delete (n q r k : ℕ)
    (F : CappedLoad (n+1) q (q+r) → ℚ) :
    moment (fixedMaximumWeight (0 : Fin (n+1))) (tieGate (k+1) F) =
      factorialWeight q * moment (tieWeight k) (fun x : CappedLoad n q r => F (prependCapped x)) := by
  rw [fixedMaximum_moment_delete]
  congr 1
  unfold moment
  apply Finset.sum_congr rfl
  intro x _
  have he : 1 + maxCount x = k+1 ↔ maxCount x = k := by omega
  simp only [tieGate, maxCount_prepend, he, tieWeight]
  split <;> simp

-- Raw mass factors retain multiplicities; cancellation is done only later.
theorem tieStratum_moment_delete (n q r k : ℕ)
    (F : CappedLoad (n+1) q (q+r) → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    ((k+1 : ℕ) : ℚ) * moment (tieWeight (k+1)) F =
      ((n+1 : ℕ) : ℚ) * factorialWeight q *
        moment (tieWeight k) (fun x : CappedLoad n q r => F (prependCapped x)) := by
  have h := tieBias_moment_eq_fixed (0 : Fin (n+1)) (tieGate (k+1) F) (tieGate_symmetric (k+1) F hF)
  rw [tieBias_moment_gate, fixedMaximum_moment_gate_delete] at h
  simpa only [mul_assoc] using h

theorem tieStratum_total_delete (n q r k : ℕ) :
    ((k+1 : ℕ) : ℚ) * total (tieWeight (b := n+1) (q := q) (r := q+r) (k+1)) =
      ((n+1 : ℕ) : ℚ) * factorialWeight q * total (tieWeight (b := n) (q := q) (r := r) k) := by
  simpa only [moment, total, mul_one] using
    tieStratum_moment_delete n q r k (fun _ => 1) (by intros; rfl)

theorem tieStratum_expectation_delete (n q r k : ℕ)
    (F : CappedLoad (n+1) q (q+r) → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) :
    expectation (tieWeight (k+1)) F =
      expectation (tieWeight k) (fun x : CappedLoad n q r => F (prependCapped x)) := by
  have hm := tieStratum_moment_delete n q r k F hF
  have hz := tieStratum_total_delete n q r k
  have hk : ((k+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hc : ((n+1 : ℕ) : ℚ) * factorialWeight q ≠ 0 :=
    ne_of_gt (mul_pos (by positivity) (factorialWeight_pos q))
  unfold expectation
  rw [← mul_div_mul_left _ _ hk, hm, hz, mul_div_mul_left _ _ hc]

theorem tieStratum_mass_pos_iff (n q r k : ℕ) :
    0 < total (tieWeight (b := n+1) (q := q) (r := q+r) (k+1)) ↔
    0 < total (tieWeight (b := n) (q := q) (r := r) k) := by
  have h := tieStratum_total_delete n q r k
  have hk : (0 : ℚ) < ((k+1 : ℕ) : ℚ) := by positivity
  have hc : (0 : ℚ) < ((n+1 : ℕ) : ℚ) * factorialWeight q :=
    mul_pos (by positivity) (factorialWeight_pos q)
  constructor <;> intro hp
  · have hh : 0 < ((n+1 : ℕ) : ℚ) * factorialWeight q * total (tieWeight (b := n) (q := q) (r := r) k) := by
      rw [← h]; exact mul_pos hk hp
    exact (mul_pos_iff_of_pos_left hc).mp hh
  · have hh : 0 < ((k+1 : ℕ) : ℚ) * total (tieWeight (b := n+1) (q := q) (r := q+r) (k+1)) := by
      rw [h]; exact mul_pos hc hp
    exact (mul_pos_iff_of_pos_left hk).mp hh

theorem maxCount_eq_zero_iff {b q r : ℕ} (x : CappedLoad b q r) :
    maxCount x = 0 ↔ ∀ i, (x.val i).val ≠ q := by
  simp [maxCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

def raiseCap {b q r : ℕ} (x : CappedLoad b q r) : CappedLoad b (q+1) r :=
  ⟨fun i => ⟨(x.val i).val, by have h := (x.val i).isLt; omega⟩, x.property⟩

theorem maxCount_raiseCap {b q r : ℕ} (x : CappedLoad b q r) :
    maxCount (raiseCap x) = 0 := by
  rw [maxCount_eq_zero_iff]
  intro i
  have h := (x.val i).isLt
  change (x.val i).val ≠ q+1
  omega

abbrev NoMaxLoad (b q r : ℕ) := {x : CappedLoad b (q+1) r // maxCount x = 0}

def lowerCap {b q r : ℕ} (x : NoMaxLoad b q r) : CappedLoad b q r :=
  ⟨fun i => ⟨(x.val.val i).val, by
    have h := (x.val.val i).isLt
    have hn := (maxCount_eq_zero_iff x.val).mp x.property i
    omega⟩, x.val.property⟩

def strictCapEquiv (b q r : ℕ) : CappedLoad b q r ≃ NoMaxLoad b q r where
  toFun := fun x => ⟨raiseCap x, maxCount_raiseCap x⟩
  invFun := lowerCap
  left_inv := by intro x; apply Subtype.ext; funext i; rfl
  right_inv := by intro x; apply Subtype.ext; apply Subtype.ext; funext i; rfl

theorem cappedWeight_raiseCap {b q r : ℕ} (x : CappedLoad b q r) :
    cappedWeight (raiseCap x) = cappedWeight x := rfl

theorem zeroTie_moment_lowerCap (b q r : ℕ) (F : CappedLoad b (q+1) r → ℚ) :
    moment (tieWeight 0) F = moment cappedWeight (fun x : CappedLoad b q r => F (raiseCap x)) := by
  classical
  have hs : moment (tieWeight 0) F = ∑ x : NoMaxLoad b q r, cappedWeight x.val * F x.val := by
    apply Finset.sum_congr_set {x : CappedLoad b (q+1) r | maxCount x = 0} _ _
    · intro x hx; simp only [Set.mem_ofPred_eq] at hx; simp [tieWeight, hx]
    · intro x hx; simp only [Set.mem_ofPred_eq] at hx; simp [tieWeight, hx]
  rw [hs, ← (strictCapEquiv b q r).sum_comp (fun x => cappedWeight x.val * F x.val)]
  rfl

theorem zeroTie_total_lowerCap (b q r : ℕ) :
    total (tieWeight (b := b) (q := q+1) (r := r) 0) =
      total (cappedWeight (b := b) (q := q) (r := r)) := by
  simpa only [moment, total, mul_one] using zeroTie_moment_lowerCap b q r (fun _ => 1)

theorem zeroTie_expectation_lowerCap (b q r : ℕ) (F : CappedLoad b (q+1) r → ℚ) :
    expectation (tieWeight 0) F = expectation cappedWeight (fun x : CappedLoad b q r => F (raiseCap x)) := by
  unfold expectation
  rw [zeroTie_moment_lowerCap, zeroTie_total_lowerCap]

-- Symmetry survives deletion, so the recursion can be applied again.
def fixFirstPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem permuteCapped_prepend {n q r : ℕ} (e : Equiv.Perm (Fin n)) (x : CappedLoad n q r) :
    permuteCapped (fixFirstPerm e) (prependCapped x) = prependCapped (permuteCapped e x) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem prepend_symmetric {n q r : ℕ} (F : CappedLoad (n+1) q (q+r) → ℚ)
    (hF : ∀ e x, F (permuteCapped e x) = F x) (e : Equiv.Perm (Fin n)) (x : CappedLoad n q r) :
    F (prependCapped (permuteCapped e x)) = F (prependCapped x) := by
  rw [← permuteCapped_prepend, hF]

theorem maximumFiber_eq_tieWeight {b q r : ℕ} (k : Fin (b+1)) (hk : 0 < k.val) :
    maximumFiberWeight b q r k = tieWeight k.val := by
  funext x
  have he : maxClass x = k ↔ maxCount x = k.val := by
    constructor
    · intro h; exact congrArg Fin.val h
    · intro h; exact Fin.ext h
  by_cases hx : maxCount x = k.val
  · have hp : 0 < maxCount x := by omega
    change (if maxClass x = k then maximumWeight x else 0) =
      (if maxCount x = k.val then cappedWeight x else 0)
    rw [ite_eq_left (he.mpr hx), ite_eq_left hx]
    exact ite_eq_left hp
  · simp [maximumFiberWeight, fiberWeight, he, hx, tieWeight]

-- Package finite sums before rewriting their size or fixed total. This
-- avoids transporting an independently synthesized enumeration instance.
def tieTotal (b q r k : ℕ) : ℚ := total (tieWeight (b := b) (q := q) (r := r) k)

def tieMean (b q r k : ℕ) (F : (Fin b → ℕ) → ℚ) : ℚ :=
  expectation (tieWeight (b := b) (q := q) (r := r) k) (fun x => F (fun i => (x.val i).val))

-- Iterating the recursion gives the exact normalizing constant for any
-- number k of maxima, including empty residual spaces.
theorem tieStratum_total_closed (n q r k : ℕ) :
    tieTotal (n+k) (q+1) ((q+1)*k+r) k =
      ((n+k).choose k : ℚ) * factorialWeight (q+1)^k *
        total (cappedWeight (b := n) (q := q) (r := r)) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add, Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul, mul_one]
    exact zeroTie_total_lowerCap n q r
  | succ k ih =>
    have h := tieStratum_total_delete (n+k) (q+1) ((q+1)*k+r) k
    change ((k+1 : ℕ) : ℚ) * tieTotal (n+k+1) (q+1) ((q+1)+((q+1)*k+r)) (k+1) =
      ((n+k+1 : ℕ) : ℚ) * factorialWeight (q+1) * tieTotal (n+k) (q+1) ((q+1)*k+r) k at h
    have hh : ((k+1 : ℕ) : ℚ) *
        tieTotal (n+(k+1)) (q+1) ((q+1)*(k+1)+r) (k+1) =
        ((n+k+1 : ℕ) : ℚ) * factorialWeight (q+1) *
        tieTotal (n+k) (q+1) ((q+1)*k+r) k := by
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hc : ((n+k+1 : ℕ) : ℚ) * ((n+k).choose k : ℚ) =
        ((n+(k+1)).choose (k+1) : ℚ) * ((k+1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (n+k) k
    apply (mul_left_cancel₀ (by positivity : ((k+1 : ℕ) : ℚ) ≠ 0))
    rw [hh, ih, pow_succ]
    calc
      _ = (((n+k+1 : ℕ) : ℚ) * ((n+k).choose k : ℚ)) *
          (factorialWeight (q+1)^k * factorialWeight (q+1)) *
          total (cappedWeight (b := n) (q := q) (r := r)) := by ring
      _ = _ := by rw [hc]; ring

theorem tieStratum_all_mass_pos_iff (n q r k : ℕ) :
    0 < tieTotal (n+k) (q+1) ((q+1)*k+r) k ↔
    0 < total (cappedWeight (b := n) (q := q) (r := r)) := by
  rw [tieStratum_total_closed]
  have hc : (0 : ℚ) < ((n+k).choose k : ℚ) := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ n+k))
  exact mul_pos_iff_of_pos_left (mul_pos hc (pow_pos (factorialWeight_pos (q+1)) k))

theorem maxCount_zeroCap {b r : ℕ} (x : CappedLoad b 0 r) : maxCount x = b := by
  simp [maxCount]

-- An ambient symmetric statistic makes repeated deletion independent of
-- proof fields in the changing fixed-sum subtypes.
def repeatMaxima {n : ℕ} (q : ℕ) : (k : ℕ) → (Fin n → ℕ) → (Fin (n+k) → ℕ)
  | 0, x => x
  | k+1, x => Fin.cons q (repeatMaxima q k x)

theorem cons_symmetric {n : ℕ} (a : ℕ) (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : ∀ (e : Equiv.Perm (Fin (n+1))) x, F (fun i => x (e i)) = F x)
    (e : Equiv.Perm (Fin n)) (x : Fin n → ℕ) :
    F (Fin.cons a (fun i => x (e i))) = F (Fin.cons a x) := by
  have h := hF (fixFirstPerm e) (Fin.cons a x)
  have he : (fun i : Fin (n+1) => (Fin.cons a x : Fin (n+1) → ℕ) (fixFirstPerm e i)) =
      (Fin.cons a (fun i : Fin n => x (e i)) : Fin (n+1) → ℕ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rwa [he] at h

theorem prependCapped_values {n q r : ℕ} (x : CappedLoad n q r) :
    (fun i => ((prependCapped x).val i).val) = Fin.cons q (fun i => (x.val i).val) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem tieStratum_expectation_allDelete (n q r k : ℕ)
    (F : (Fin (n+k) → ℕ) → ℚ)
    (hF : ∀ (e : Equiv.Perm (Fin (n+k))) x, F (fun i => x (e i)) = F x) :
    tieMean (n+k) (q+1) ((q+1)*k+r) k F =
    expectation (cappedWeight (b := n) (q := q) (r := r))
      (fun x => F (repeatMaxima (q+1) k (fun i => (x.val i).val))) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add, repeatMaxima]
    exact zeroTie_expectation_lowerCap n q r (fun x => F (fun i => (x.val i).val))
  | succ k ih =>
    have h := tieStratum_expectation_delete (n+k) (q+1) ((q+1)*k+r) k
      (fun x => F (fun i => (x.val i).val)) (by
        intro e x
        exact hF e (fun i => (x.val i).val))
    have he : (q+1) * (k+1) + r = (q+1) + ((q+1)*k+r) := by ring
    have hi := ih (fun x => F (Fin.cons (q+1) x)) (cons_symmetric (q+1) F hF)
    have hobs : (fun x : CappedLoad (n+k) (q+1) ((q+1)*k+r) =>
        F (fun i => ((prependCapped x).val i).val)) =
        (fun x => F (Fin.cons (q+1) (fun i => (x.val i).val))) := by
      funext x
      exact congrArg F (prependCapped_values x)
    rw [hobs] at h
    change tieMean (n+k+1) (q+1) ((q+1)+((q+1)*k+r)) (k+1) F =
      tieMean (n+k) (q+1) ((q+1)*k+r) k (fun x => F (Fin.cons (q+1) x)) at h
    rw [he]
    exact h.trans hi

end MatchingCapacity
