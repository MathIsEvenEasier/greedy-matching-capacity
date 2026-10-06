import CategoricalBoundary

/-! Exact two-coordinate slices of the full categorical load mass.
Pairing swapped loads converts the coefficient balancing inequality into
an inequality between actual assignment masses. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def replacePair (x : κ → ℕ) (i j : κ) (a c : ℕ) : κ → ℕ :=
  fun k => if k = i then a else if k = j then c else x k

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
theorem replacePair_swap (x : κ → ℕ) (i j : κ) (hij : i ≠ j) (a c : ℕ) :
    replacePair x i j a c = replacePair x j i c a := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [replacePair, hij]
  · by_cases hj : k = j
    · subst k
      simp [replacePair, hij.symm]
    · simp [replacePair, hi, hj]

def pairLoadAllowed (x : κ → ℕ) (i j : κ) (o : ι → PairOutside i j) (t : ℕ) : Prop :=
  (∀ k, pairOutsideLoad i j o k = x k.val) ∧ (pairActive i j o).card = t

omit [Fintype κ] [DecidableEq ι] in
theorem assignmentLoad_replacePair (x : κ → ℕ) (i j : κ) (hij : i ≠ j)
    (d : ι → κ) (o : ι → PairOutside i j) (ho : pairPattern i j d = o) (a c : ℕ) :
    assignmentLoad d = replacePair x i j a c ↔
      pairLoadAllowed x i j o (a+c) ∧ assignmentLoad d i = a := by
  have hc := pairPattern_count i j hij d o ho
  constructor
  · intro h
    have hi : assignmentLoad d i = a := by simpa [replacePair] using congrFun h i
    have hj : assignmentLoad d j = c := by simpa [replacePair, hij.symm] using congrFun h j
    refine ⟨⟨?_, by omega⟩, hi⟩
    intro k
    rw [← pairPattern_outside_load i j d o ho k, h]
    simp [replacePair, k.property.1, k.property.2]
  · rintro ⟨⟨hout, ht⟩, hi⟩
    have hj : assignmentLoad d j = c := by omega
    funext k
    by_cases hki : k = i
    · subst k
      simpa [replacePair] using hi
    · by_cases hkj : k = j
      · subst k
        simpa [replacePair, hij.symm] using hj
      · rw [pairPattern_outside_load i j d o ho ⟨k, hki, hkj⟩, hout]
        simp [replacePair, hki, hkj]

theorem categoricalLoadMass_pair (p : ι → κ → ℚ) (x : κ → ℕ)
    (i j : κ) (hij : i ≠ j) (a c : ℕ) :
    categoricalLoadMass p (replacePair x i j a c) =
      ∑ o, if pairLoadAllowed x i j o (a+c) then pairSliceMass p i j o a else 0 := by
  exact pairSliceMass_partition_event p i j _ _ _
    (fun d o ho => assignmentLoad_replacePair x i j hij d o ho a c)

theorem categorical_pair_balancing_ordered (p : ι → κ → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (x : κ → ℕ) (i j : κ) (hij : i ≠ j)
    (horder : ∀ r, p r j ≤ p r i) (a c : ℕ) (hgap : c+2 ≤ a) :
    ((a-1).factorial : ℚ)*((c+1).factorial : ℚ)*
      (categoricalLoadMass p (replacePair x i j (a-1) (c+1)) +
       categoricalLoadMass p (replacePair x i j (c+1) (a-1))) ≤
    (a.factorial : ℚ)*(c.factorial : ℚ)*
      (categoricalLoadMass p (replacePair x i j a c) +
       categoricalLoadMass p (replacePair x i j c a)) := by
  simp only [categoricalLoadMass_pair p x i j hij]
  have h1 : a-1+(c+1) = a+c := by omega
  have h2 : c+1+(a-1) = a+c := by omega
  rw [h1, h2, Nat.add_comm c a, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  by_cases ho : pairLoadAllowed x i j o (a+c)
  · simp only [ite_eq_left ho]
    exact pairSliceMass_balancing p hp i j hij horder o a c ho.2.symm hgap
  · simp [ho]

theorem categorical_pair_balancing (p : ι → κ → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (x : κ → ℕ) (i j : κ) (hij : i ≠ j)
    (horder : (∀ r, p r j ≤ p r i) ∨ (∀ r, p r i ≤ p r j))
    (a c : ℕ) (hgap : c+2 ≤ a) :
    ((a-1).factorial : ℚ)*((c+1).factorial : ℚ)*
      (categoricalLoadMass p (replacePair x i j (a-1) (c+1)) +
       categoricalLoadMass p (replacePair x i j (c+1) (a-1))) ≤
    (a.factorial : ℚ)*(c.factorial : ℚ)*
      (categoricalLoadMass p (replacePair x i j a c) +
       categoricalLoadMass p (replacePair x i j c a)) := by
  rcases horder with h | h
  · exact categorical_pair_balancing_ordered p hp x i j hij h a c hgap
  · have hh := categorical_pair_balancing_ordered p hp x j i hij.symm h a c hgap
    simpa only [replacePair_swap x j i hij.symm, add_comm] using hh

def loadFactorial (x : κ → ℕ) : ℚ := ∏ k, (x k).factorial

def factorialLoadMass (p : ι → κ → ℚ) (x : κ → ℕ) : ℚ :=
  loadFactorial x * categoricalLoadMass p x

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem loadFactorial_pos (x : κ → ℕ) : 0 < loadFactorial x := by
  apply Finset.prod_pos
  intro k _
  exact_mod_cast Nat.factorial_pos (x k)

omit [Fintype ι] [DecidableEq ι] in
theorem loadFactorial_pair (x : κ → ℕ) (i j : κ) (hij : i ≠ j) (a c : ℕ) :
    loadFactorial (replacePair x i j a c) =
      (a.factorial : ℚ)*(c.factorial : ℚ)*
        ∏ k ∈ (Finset.univ.erase i).erase j, ((x k).factorial : ℚ) := by
  let f := fun k => ((replacePair x i j a c k).factorial : ℚ)
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  change (∏ k, f k) = _
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f hj]
  have hprod : (∏ k ∈ (Finset.univ.erase i).erase j, f k) =
      ∏ k ∈ (Finset.univ.erase i).erase j, ((x k).factorial : ℚ) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hi := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hj' := (Finset.mem_erase.mp hk).1
    simp [f, replacePair, hi, hj']
  rw [hprod]
  simp [f, replacePair, hij.symm, mul_assoc]

theorem factorialLoadMass_pair_balancing (p : ι → κ → ℚ)
    (hp : ∀ r k, 0 ≤ p r k) (x : κ → ℕ) (i j : κ) (hij : i ≠ j)
    (horder : (∀ r, p r j ≤ p r i) ∨ (∀ r, p r i ≤ p r j))
    (a c : ℕ) (hgap : c+2 ≤ a) :
    factorialLoadMass p (replacePair x i j (a-1) (c+1)) +
      factorialLoadMass p (replacePair x i j (c+1) (a-1)) ≤
    factorialLoadMass p (replacePair x i j a c) +
      factorialLoadMass p (replacePair x i j c a) := by
  have h := mul_le_mul_of_nonneg_right
    (categorical_pair_balancing p hp x i j hij horder a c hgap)
    (show (0 : ℚ) ≤ ∏ k ∈ (Finset.univ.erase i).erase j, ((x k).factorial : ℚ) from
      Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
  simp only [factorialLoadMass, loadFactorial_pair x i j hij]
  nlinarith

end MatchingCapacity
