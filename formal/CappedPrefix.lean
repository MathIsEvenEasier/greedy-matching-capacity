import CappedProduct

/-! Fixing a prefix preserves majorization of the remaining coordinates.
This checks the observable hypothesis needed when applying the smaller-
dimension regressions to the exact tie strata. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem loadLE_cons {n : ℕ} (a : ℕ) (x y : Fin n → ℕ) (hxy : LoadLE x y) :
    LoadLE (Fin.cons a x) (Fin.cons a y) := by
  classical
  intro s
  let e : Fin n ↪ Fin (n+1) := ⟨Fin.succ, Fin.succ_injective n⟩
  let u := Finset.univ.filter (fun i : Fin n => i.succ ∈ s)
  obtain ⟨t, ht, hut⟩ := hxy u
  have hzero : ∀ v : Finset (Fin n), (0 : Fin (n+1)) ∉ v.map e := by
    intro v
    simp [e]
  by_cases h0 : (0 : Fin (n+1)) ∈ s
  · have hs : s = insert 0 (u.map e) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [u, e, h0]
    refine ⟨insert 0 (t.map e), ?_, ?_⟩
    · rw [hs, Finset.card_insert_of_notMem (hzero t), Finset.card_insert_of_notMem (hzero u)]
      simpa using ht
    · rw [hs, Finset.sum_insert (hzero u), Finset.sum_insert (hzero t)]
      simpa [Finset.sum_map, e] using Nat.add_le_add_left hut a
  · have hs : s = u.map e := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [u, e, h0]
    refine ⟨t.map e, ?_, ?_⟩
    · rw [hs]; simpa using ht
    · rw [hs]
      simpa [Finset.sum_map, e] using hut

theorem loadLE_repeatMaxima {n : ℕ} (q k : ℕ) (x y : Fin n → ℕ) (hxy : LoadLE x y) :
    LoadLE (repeatMaxima q k x) (repeatMaxima q k y) := by
  induction k with
  | zero => exact hxy
  | succ k ih => exact loadLE_cons q _ _ ih

theorem repeatMaxima_sum {n : ℕ} (q k : ℕ) (x : Fin n → ℕ) :
    (∑ i, repeatMaxima q k x i) = q*k + ∑ i, x i := by
  induction k with
  | zero => simp [repeatMaxima]
  | succ k ih =>
    calc
      _ = q + ∑ i, repeatMaxima q k x i :=
        Fin.sum_univ_succ (fun i : Fin ((n+k)+1) => Fin.cons q (repeatMaxima q k x) i)
      _ = q*(k+1) + ∑ i, x i := by rw [ih]; ring

theorem repeatMaxima_increasing (n q r k : ℕ) (F : (Fin (n+k) → ℕ) → ℚ)
    (hF : ∀ x y, (∑ i, x i) = q*k+r → (∑ i, y i) = q*k+r → LoadLE x y → F x ≤ F y)
    (x y : Fin n → ℕ) (hx : (∑ i, x i) = r) (hy : (∑ i, y i) = r)
    (hxy : LoadLE x y) : F (repeatMaxima q k x) ≤ F (repeatMaxima q k y) := by
  apply hF
  · rw [repeatMaxima_sum, hx]
  · rw [repeatMaxima_sum, hy]
  · exact loadLE_repeatMaxima q k x y hxy

theorem capped_prefixed_pinned_majorization (n c T a b p k : ℕ)
    (hca : c ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hfeasible : T-a ≤ n*c)
    (F : (Fin ((n+1)+k) → ℕ) → ℚ)
    (hF : ∀ x y, (∑ i, x i) = p*k+T → (∑ i, y i) = p*k+T → LoadLE x y → F x ≤ F y) :
    cappedMean n c (T-a) (fun x => F (repeatMaxima p k (Fin.cons a x))) ≤
      cappedMean n c (T-b) (fun x => F (repeatMaxima p k (Fin.cons b x))) := by
  exact capped_vector_pinned_majorization n c T a b hca hab hbT hfeasible
    (fun x => F (repeatMaxima p k x)) (repeatMaxima_increasing (n+1) p T k F hF)

end MatchingCapacity
