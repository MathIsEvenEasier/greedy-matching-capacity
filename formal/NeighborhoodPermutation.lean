import NeighborhoodChoice

/-! Relabeling preserves uniform neighborhoods and the literal RV law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {m : ℕ}

def permuteBins (e : Equiv.Perm (Fin m)) (S : Finset (Fin m)) : Finset (Fin m) := S.map e.toEmbedding

theorem mem_permuteBins (e : Equiv.Perm (Fin m)) (S : Finset (Fin m)) (k : Fin m) :
    e k ∈ permuteBins e S ↔ k ∈ S := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp h
    exact e.injective he ▸ ha
  · intro h
    exact Finset.mem_map.mpr ⟨k,h,rfl⟩

theorem mem_permuteBins_iff (e : Equiv.Perm (Fin m)) (S : Finset (Fin m)) (k : Fin m) :
    k ∈ permuteBins e S ↔ e.symm k ∈ S := by
  simpa only [Equiv.apply_symm_apply] using mem_permuteBins e S (e.symm k)

theorem permuteBins_card (e : Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    (permuteBins e S).card = S.card := Finset.card_map _

theorem permuteBins_inverse (e : Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    permuteBins e.symm (permuteBins e S) = S := by
  ext k
  simp only [mem_permuteBins_iff, Equiv.symm_symm, Equiv.symm_apply_apply]

def permuteBinsEquiv (e : Equiv.Perm (Fin m)) : Equiv.Perm (Finset (Fin m)) where
  toFun := permuteBins e
  invFun := permuteBins e.symm
  left_inv := permuteBins_inverse e
  right_inv := by intro S; simpa only [Equiv.symm_symm] using permuteBins_inverse e.symm S

theorem permuteBins_inter (e : Equiv.Perm (Fin m)) (A N : Finset (Fin m)) :
    permuteBins e (A ∩ N) = permuteBins e A ∩ permuteBins e N := by
  ext k
  simp only [Finset.mem_inter, mem_permuteBins_iff]

theorem neighborhood_sum_permutation (e : Equiv.Perm (Fin m)) (degree : ℕ)
    (F : Finset (Fin m) → ℚ) :
    (∑ N ∈ Finset.univ.powersetCard degree, F (permuteBins e N)) =
      ∑ N ∈ Finset.univ.powersetCard degree, F N := by
  apply Finset.sum_equiv (permuteBinsEquiv e)
  · intro N
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
    change N.card = degree ↔ (permuteBins e N).card = degree
    rw [permuteBins_card]
  · intro N _
    rfl

theorem rvResponse_permutation (e : Equiv.Perm (Fin m)) (A N : Finset (Fin m)) (k : Fin m) :
    rvResponse (permuteBins e A) (permuteBins e N) (some (e k)) = rvResponse A N (some k) := by
  simp only [rvResponse, ← permuteBins_inter, mem_permuteBins, permuteBins_card]

theorem rvKernel_permutation (e : Equiv.Perm (Fin m)) (degree : ℕ) (A : Finset (Fin m)) (k : Fin m) :
    rvKernel degree (permuteBins e A) (some (e k)) = rvKernel degree A (some k) := by
  unfold rvKernel neighborhoodKernel
  congr 1
  rw [← neighborhood_sum_permutation e degree (fun N => rvResponse (permuteBins e A) N (some (e k)))]
  simp only [rvResponse_permutation]

theorem swap_preserves_available (A : Finset (Fin m)) (i j : Fin m) (hi : i ∈ A) (hj : j ∈ A) :
    permuteBins (Equiv.swap i j) A = A := by
  ext k
  rw [mem_permuteBins_iff]
  by_cases hki : k = i
  · subst k; simp [hi, hj]
  by_cases hkj : k = j
  · subst k; simp [hi, hj]
  simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem rvKernel_constant_on_available (degree : ℕ) (A : Finset (Fin m))
    (i j : Fin m) (hi : i ∈ A) (hj : j ∈ A) : rvKernel degree A (some i) = rvKernel degree A (some j) := by
  have h := rvKernel_permutation (Equiv.swap i j) degree A i
  rw [swap_preserves_available A i j hi hj, Equiv.swap_apply_left] at h
  exact h.symm

end MatchingCapacity
