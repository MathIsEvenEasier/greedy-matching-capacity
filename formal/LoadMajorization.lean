import LoadBalancing

/-! Bridge from the existing subset-sum majorization relation to
symmetric statistics that decrease under integer balancing moves. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem loadLE_balance {n : ℕ} (y : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hgap : y j+2 ≤ y i) : LoadLE (balanceLoad y i j) y := by
  intro s
  have hp : 0 < y i := by omega
  have hs := balanceLoad_sum y i j hij hp s
  by_cases hj : j ∈ s
  · by_cases hi : i ∈ s
    · refine ⟨s, rfl, ?_⟩
      simp only [ite_eq_left hi, ite_eq_left hj] at hs
      omega
    · let t := insert i (s.erase j)
      have hi' : i ∉ s.erase j := fun h => hi (Finset.mem_of_mem_erase h)
      have hcard : t.card = s.card := by
        dsimp [t]
        rw [Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem hj]
        have hh := Finset.card_pos.mpr ⟨j, hj⟩
        omega
      refine ⟨t, hcard, ?_⟩
      have he := Finset.sum_erase_add s y hj
      have ht : (∑ k ∈ t, y k) = y i + ∑ k ∈ s.erase j, y k := by
        exact Finset.sum_insert hi'
      simp only [ite_eq_right hi, ite_eq_left hj] at hs
      omega
  · refine ⟨s, rfl, ?_⟩
    simp only [ite_eq_right hj] at hs
    split_ifs at hs <;> omega

theorem antitone_prefix_max {n : ℕ} (y : Fin n → ℕ) (hy : Antitone y)
    (k : Fin n) (s : Finset (Fin n)) (hcard : s.card ≤ (Finset.Iic k).card) :
    (∑ i ∈ s, y i) ≤ ∑ i ∈ Finset.Iic k, y i := by
  let t := Finset.Iic k
  have hc : (s \ t).card ≤ (t \ s).card := Finset.card_sdiff_le_card_sdiff_iff.mpr hcard
  have hleft : (∑ i ∈ s \ t, y i) ≤ (s \ t).card * y k := by
    calc
      _ ≤ ∑ _i ∈ s \ t, y k := by
        apply Finset.sum_le_sum
        intro i hi
        have hh : ¬ i ≤ k := by simpa only [t, Finset.mem_Iic] using (Finset.mem_sdiff.mp hi).2
        exact hy (le_of_lt (lt_of_not_ge hh))
      _ = _ := by simp
  have hright : (t \ s).card * y k ≤ ∑ i ∈ t \ s, y i := by
    calc
      _ = ∑ _i ∈ t \ s, y k := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hy (Finset.mem_Iic.mp (Finset.mem_sdiff.mp hi).1)
  have hmid := Nat.mul_le_mul_right (y k) hc
  have hs : (∑ i ∈ s \ t, y i) + (∑ i ∈ s ∩ t, y i) = ∑ i ∈ s, y i := by
    simpa only [Finset.sdiff_inter_self_left] using
      (Finset.sum_sdiff (f := y) (show s ∩ t ⊆ s from Finset.inter_subset_left))
  have ht : (∑ i ∈ t \ s, y i) + (∑ i ∈ s ∩ t, y i) = ∑ i ∈ t, y i := by
    simpa only [Finset.sdiff_inter_self_right] using
      (Finset.sum_sdiff (f := y) (show s ∩ t ⊆ t from Finset.inter_subset_right))
  change (∑ i ∈ s, y i) ≤ ∑ i ∈ t, y i
  omega

theorem prefixLE_of_loadLE {n : ℕ} (x y : Fin n → ℕ) (hy : Antitone y)
    (hxy : LoadLE x y) : PrefixLE x y := by
  intro k
  obtain ⟨s, hs, hsum⟩ := hxy (Finset.Iic k)
  exact hsum.trans (antitone_prefix_max y hy k s hs.le)

theorem loadLE_permute_both {n : ℕ} (x y : Fin n → ℕ)
    (e f : Equiv.Perm (Fin n)) (hxy : LoadLE x y) :
    LoadLE (fun i => x (e i)) (fun i => y (f i)) := by
  apply loadLE_trans (loadLE_trans (loadLE_reindex x e) hxy)
  have h := loadLE_reindex (fun i => y (f i)) f.symm
  simpa only [Equiv.apply_symm_apply] using h

theorem loadLE_mono_of_balancing {n : ℕ} (F : (Fin n → ℕ) → ℚ)
    (hsym : ∀ (e : Equiv.Perm (Fin n)) x, F (fun i => x (e i)) = F x)
    (hbal : ∀ y i j, i ≠ j → y j+2 ≤ y i → F (balanceLoad y i j) ≤ F y)
    (x y : Fin n → ℕ) (hT : (∑ i, x i) = ∑ i, y i) (hxy : LoadLE x y) : F x ≤ F y := by
  let e := Tuple.sort (α := OrderDual ℕ) x
  let f := Tuple.sort (α := OrderDual ℕ) y
  have hx : Antitone (fun i => x (e i)) := Tuple.monotone_sort (α := OrderDual ℕ) x
  have hy : Antitone (fun i => y (f i)) := Tuple.monotone_sort (α := OrderDual ℕ) y
  rw [← hsym e x, ← hsym f y]
  apply prefix_mono_of_balancing F hbal _ _ hx
  · simpa only [Equiv.sum_comp] using hT
  · exact prefixLE_of_loadLE _ _ hy (loadLE_permute_both x y e f hxy)

theorem loadLE_mono_iff_balancing {n : ℕ} (F : (Fin n → ℕ) → ℚ) :
    (∀ x y, (∑ i, x i) = ∑ i, y i → LoadLE x y → F x ≤ F y) ↔
      (∀ (e : Equiv.Perm (Fin n)) x, F (fun i => x (e i)) = F x) ∧
      (∀ y i j, i ≠ j → y j+2 ≤ y i → F (balanceLoad y i j) ≤ F y) := by
  constructor
  · intro h
    constructor
    · intro e x
      apply le_antisymm
      · exact h _ _ (Equiv.sum_comp e x) (loadLE_reindex x e)
      · have hh := h _ _ (Equiv.sum_comp e.symm (fun i => x (e i)))
          (loadLE_reindex (fun i => x (e i)) e.symm)
        simpa only [Equiv.apply_symm_apply] using hh
    · intro y i j hij hgap
      exact h _ _ (balanceLoad_total y i j hij (by omega)) (loadLE_balance y i j hij hgap)
  · rintro ⟨hsym, hbal⟩ x y hT hxy
    exact loadLE_mono_of_balancing F hsym hbal x y hT hxy

end MatchingCapacity
