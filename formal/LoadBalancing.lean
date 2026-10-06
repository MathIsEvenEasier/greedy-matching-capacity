import CappedSymmetry
import Mathlib.Data.Fin.Tuple.Sort

/-! Finite integer majorization from unit balancing moves.
Only the target is sorted during the descent. The total excess above
that target decreases by one at each move. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def balanceLoad {n : ℕ} (y : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  fun k => if k = i then y i-1 else if k = j then y j+1 else y k

def loadExcess {n : ℕ} (x y : Fin n → ℕ) : ℕ := ∑ i, (y i-x i)

def PrefixLE {n : ℕ} (x y : Fin n → ℕ) : Prop :=
  ∀ k, (∑ i ∈ Finset.Iic k, x i) ≤ ∑ i ∈ Finset.Iic k, y i

theorem balanceLoad_sum {n : ℕ} (y : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < y i) (s : Finset (Fin n)) :
    (∑ k ∈ s, balanceLoad y i j k) + (if i ∈ s then 1 else 0) =
      (∑ k ∈ s, y k) + (if j ∈ s then 1 else 0) := by
  have hp : ∀ k, balanceLoad y i j k + (if k = i then 1 else 0) =
      y k + (if k = j then 1 else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp only [balanceLoad, ite_true, ite_eq_right hij]
      omega
    · by_cases hkj : k = j
      · subst k
        simp [balanceLoad, hki]
      · simp [balanceLoad, hki, hkj]
  have h := Finset.sum_congr (s₁ := s) rfl (fun k _ => hp k)
  simpa [Finset.sum_add_distrib] using h

theorem balanceLoad_total {n : ℕ} (y : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < y i) :
    (∑ k, balanceLoad y i j k) = ∑ k, y k := by
  have h := balanceLoad_sum y i j hij hi Finset.univ
  simpa using h

theorem balanceLoad_excess {n : ℕ} (x y : Fin n → ℕ) (i j : Fin n)
    (hi : x i < y i) (hj : y j < x j) :
    loadExcess x (balanceLoad y i j) + 1 = loadExcess x y := by
  have hp : ∀ k, (balanceLoad y i j k-x k) + (if k = i then 1 else 0) = y k-x k := by
    intro k
    by_cases hki : k = i
    · subst k
      simp only [balanceLoad, ite_true]
      omega
    · by_cases hkj : k = j
      · subst k
        simp only [balanceLoad, ite_eq_right hki, ite_true]
        omega
      · simp [balanceLoad, hki, hkj]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hp k)
  simpa [Finset.sum_add_distrib, loadExcess] using h

theorem exists_first_deficit {n : ℕ} (x y : Fin n → ℕ)
    (hT : (∑ i, x i) = ∑ i, y i) (hne : x ≠ y) :
    ∃ j, y j < x j ∧ ∀ i, i < j → x i ≤ y i := by
  classical
  let s := Finset.univ.filter (fun j => y j < x j)
  have hs : s.Nonempty := by
    by_contra he
    have hle : ∀ i, x i ≤ y i := by
      intro i
      by_contra hi
      exact he ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩⟩
    have heq := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => hle i)).mp hT
    exact hne (funext (fun i => heq i (Finset.mem_univ i)))
  let j := s.min' hs
  refine ⟨j, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, ?_⟩
  intro i hij
  by_contra hi
  have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
  have hji : j ≤ i := Finset.min'_le s i his
  omega

theorem exists_prefix_donor {n : ℕ} (x y : Fin n → ℕ) (j : Fin n)
    (hpre : PrefixLE x y) (hj : y j < x j) :
    ∃ i, i < j ∧ x i < y i := by
  classical
  by_contra he
  have hle : ∀ i ∈ Finset.Iic j, y i ≤ x i := by
    intro i hi
    have hij := Finset.mem_Iic.mp hi
    by_cases heq : i = j
    · subst i
      exact hj.le
    · by_contra h
      exact he ⟨i, lt_of_le_of_ne hij heq, by omega⟩
  have hlt := Finset.sum_lt_sum hle ⟨j, Finset.mem_Iic.mpr le_rfl, hj⟩
  have hh := hpre j
  omega

theorem balanceLoad_prefix {n : ℕ} (x y : Fin n → ℕ) (i j : Fin n)
    (hij : i < j) (hi : x i < y i) (hpre : PrefixLE x y)
    (hbefore : ∀ k, k < j → x k ≤ y k) : PrefixLE x (balanceLoad y i j) := by
  intro k
  have hs := balanceLoad_sum y i j (ne_of_lt hij) (by omega) (Finset.Iic k)
  have hh := hpre k
  by_cases hjk : j ≤ k
  · have hik : i ≤ k := hij.le.trans hjk
    simp only [Finset.mem_Iic, ite_eq_left hik, ite_eq_left hjk] at hs
    omega
  · by_cases hik : i ≤ k
    · have hlt : (∑ l ∈ Finset.Iic k, x l) < ∑ l ∈ Finset.Iic k, y l := by
        apply Finset.sum_lt_sum
        · intro l hl
          exact hbefore l (lt_of_le_of_lt (Finset.mem_Iic.mp hl) (lt_of_not_ge hjk))
        · exact ⟨i, Finset.mem_Iic.mpr hik, hi⟩
      simp only [Finset.mem_Iic, ite_eq_left hik, ite_eq_right hjk] at hs
      omega
    · simp only [Finset.mem_Iic, ite_eq_right hik, ite_eq_right hjk] at hs
      omega

theorem prefix_mono_of_balancing {n : ℕ} (F : (Fin n → ℕ) → ℚ)
    (hbal : ∀ y i j, i ≠ j → y j+2 ≤ y i → F (balanceLoad y i j) ≤ F y)
    (x y : Fin n → ℕ) (hx : Antitone x)
    (hT : (∑ i, x i) = ∑ i, y i) (hpre : PrefixLE x y) : F x ≤ F y := by
  suffices hh : ∀ m (z : Fin n → ℕ), loadExcess x z = m →
      (∑ i, x i) = ∑ i, z i → PrefixLE x z → F x ≤ F z by
    exact hh (loadExcess x y) y rfl hT hpre
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro z hm hsum hp
    by_cases he : x = z
    · rw [he]
    · obtain ⟨j, hj, hbefore⟩ := exists_first_deficit x z hsum he
      obtain ⟨i, hij, hi⟩ := exists_prefix_donor x z j hp hj
      have hg : z j+2 ≤ z i := by
        have hh := hx hij.le
        omega
      have hm' := balanceLoad_excess x z i j hi hj
      have ht := balanceLoad_total z i j (ne_of_lt hij) (by omega)
      have hnew := ih (loadExcess x (balanceLoad z i j)) (by omega)
        (balanceLoad z i j) rfl (hsum.trans ht.symm)
        (balanceLoad_prefix x z i j hij hi hp hbefore)
      exact hnew.trans (hbal z i j (ne_of_lt hij) hg)

end MatchingCapacity
