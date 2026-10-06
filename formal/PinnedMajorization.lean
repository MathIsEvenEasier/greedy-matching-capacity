import EfronBand
import AssociationTarget
import Mathlib.Data.List.OfFn

/-! Transferring mass from coordinates to an already largest distinguished
coordinate increases majorization. This gives the pinned-maximum comparison
needed in the discrete Cohen--Sackrowitz argument. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem loadLE_of_reservoir {b : ℕ} (x y : Fin b → ℕ) (j : Fin b)
    (hT : (∑ i, x i) = ∑ i, y i)
    (hrest : ∀ i, i ≠ j → x i ≤ y i)
    (hmax : ∀ i, y i ≤ y j) : LoadLE y x := by
  classical
  have hsums : ∀ s : Finset (Fin b), j ∈ s → (∑ i ∈ s, y i) ≤ ∑ i ∈ s, x i := by
    intro s hj
    have hc : (∑ i ∈ sᶜ, x i) ≤ ∑ i ∈ sᶜ, y i := by
      apply Finset.sum_le_sum
      intro i hi
      apply hrest i
      intro he
      subst i
      exact Finset.mem_compl.mp hi hj
    have hx := Finset.sum_add_sum_compl s x
    have hy := Finset.sum_add_sum_compl s y
    omega
  intro s
  by_cases hj : j ∈ s
  · exact ⟨s, rfl, hsums s hj⟩
  · by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      let u := insert j (s.erase i)
      have hji : j ≠ i := by intro he; subst i; exact hj hi
      have hj' : j ∉ s.erase i := fun h => hj (Finset.mem_of_mem_erase h)
      have hu : u.card = s.card := by
        dsimp [u]
        rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi]
        have hp := Finset.card_pos.mpr ⟨i,hi⟩
        omega
      have hsu : (∑ k ∈ s, y k) ≤ ∑ k ∈ u, y k := by
        have he := Finset.sum_erase_add s y hi
        dsimp [u]
        rw [Finset.sum_insert hj']
        have hm := hmax i
        omega
      exact ⟨u, hu, hsu.trans (hsums u (Finset.mem_insert_self _ _))⟩
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨∅, rfl, by simp⟩

theorem coordLE_getD (xs ys : List ℕ) (h : CoordLE xs ys) (i : ℕ) :
    xs.getD i 0 ≤ ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => cases ys <;> simp_all [CoordLE]
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim h
    | cons y ys => cases i with
      | zero => exact h.1
      | succ i => exact ih ys h.2 i

theorem fitsCaps_getD (n q : ℕ) (xs : List ℕ)
    (h : FitsCaps (List.replicate n q) xs) (i : ℕ) : xs.getD i 0 ≤ q := by
  induction n generalizing xs i with
  | zero => cases xs <;> simp_all [FitsCaps]
  | succ n ih =>
    cases xs with
    | nil => exact False.elim h
    | cons x xs =>
      change x ≤ q ∧ FitsCaps (List.replicate n q) xs at h
      cases i with
      | zero => exact h.1
      | succ i => exact ih xs h.2 i

theorem sum_getD (n : ℕ) (xs : List ℕ) (h : xs.length = n) :
    (∑ i : Fin n, xs.getD i.val 0) = xs.sum := by
  induction n generalizing xs with
  | zero => have he : xs = [] := List.length_eq_zero_iff.mp h; subst xs; simp
  | succ n ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      have ht : xs.length = n := by simpa using h
      rw [Fin.sum_univ_succ]
      change x + (∑ i : Fin n, xs.getD i.val 0) = x + xs.sum
      rw [ih xs ht]

def completeLoad (n T : ℕ) (xs : List ℕ) : Fin (n+1) → ℕ :=
  Fin.cons (T-xs.sum) (fun i => xs.getD i.val 0)

theorem completeLoad_sum (n T : ℕ) (xs : List ℕ) (hlen : xs.length = n)
    (hs : xs.sum ≤ T) : (∑ i, completeLoad n T xs i) = T := by
  rw [Fin.sum_univ_succ]
  simp only [completeLoad, Fin.cons_zero, Fin.cons_succ]
  rw [sum_getD n xs hlen]
  omega

theorem completeLoad_antitone (n q T : ℕ) (xs ys : List ℕ)
    (hx : FitsCaps (List.replicate n q) xs) (hy : FitsCaps (List.replicate n q) ys)
    (hmax : q + ys.sum ≤ T) (hxy : CoordLE xs ys) :
    LoadLE (completeLoad n T ys) (completeLoad n T xs) := by
  have hs := coordLE_sum xs ys hxy
  apply loadLE_of_reservoir _ _ (0 : Fin (n+1))
  · rw [completeLoad_sum n T xs (by simpa using fitsCaps_length _ _ hx) (by omega),
      completeLoad_sum n T ys (by simpa using fitsCaps_length _ _ hy) (by omega)]
  · intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi; exact False.elim (hi rfl)
    · intro _; exact coordLE_getD xs ys hxy j.val
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · have hj := fitsCaps_getD n q ys hy j.val
      change ys.getD j.val 0 ≤ T-ys.sum
      omega

-- The residual coordinates have a fixed cap q, while the pinned value
-- increases from a to b. Both complete vectors have total T.
theorem pinned_efron_majorization (n q T a b : ℕ) (hqa : q ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) (hfeasible : T-a ≤ n*q)
    (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : ∀ x y, (∑ i, x i) = T → (∑ i, y i) = T → LoadLE x y → F x ≤ F y) :
    productMean ((List.replicate n q).map factorialCarrier) (T-a)
      (fun xs => F (Fin.cons a (fun i => xs.getD i.val 0))) ≤
    productMean ((List.replicate n q).map factorialCarrier) (T-b)
      (fun xs => F (Fin.cons b (fun i => xs.getD i.val 0))) := by
  let φ := fun xs => F (completeLoad n T xs)
  have h := capped_efron_band_antitone (List.replicate n q) (T-b) (T-a) (by omega)
    (by simpa only [List.sum_replicate, smul_eq_mul] using hfeasible) φ (by
      intro xs ys hx hy hs ht hxy
      apply hF
      · exact completeLoad_sum n T ys (by simpa using fitsCaps_length _ _ hy) (by omega)
      · have hsum := coordLE_sum xs ys hxy
        exact completeLoad_sum n T xs (by simpa using fitsCaps_length _ _ hx) (by omega)
      · exact completeLoad_antitone n q T xs ys hx hy (by omega) hxy)
  have he : ∀ c, c ≤ T → productMean ((List.replicate n q).map factorialCarrier) (T-c) φ =
      productMean ((List.replicate n q).map factorialCarrier) (T-c)
        (fun xs => F (Fin.cons c (fun i => xs.getD i.val 0))) := by
    intro c hc
    unfold productMean
    congr 1
    apply cappedMoment_congr
    intro xs hx hs
    have hp : T-xs.sum = c := by omega
    simp only [φ, completeLoad, hp]
  rwa [he a (by omega), he b hbT] at h

end MatchingCapacity
