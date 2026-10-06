import CappedAssociationTools

/-! Tie regression at cap q+1 follows from association at cap q.
The hypothesis is strictly smaller in the cap; no current-cap regression
or association is assumed. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

theorem tieTotal_pos_bounds (b q T k : ℕ) (hZ : 0 < tieTotal b q T k) :
    k ≤ b ∧ q*k ≤ T := by
  classical
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun x _ => tieWeight_nonneg k (x : CappedLoad b q T))).mp hZ
  have hk : maxCount x = k := by
    by_contra hn
    simp [tieWeight, hn] at hx
  have hb : maxCount x ≤ b := by
    have h := (maxClass x).isLt
    change maxCount x < b+1 at h
    omega
  have hs : (∑ i ∈ Finset.univ.filter (fun i => (x.val i).val = q), (x.val i).val) =
      maxCount x * q := by
    calc
      _ = ∑ _i ∈ Finset.univ.filter (fun i => (x.val i).val = q), q :=
        Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
      _ = _ := by simp [maxCount]
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun i => (x.val i).val = q) Finset.univ)
    (fun i _ _ => Nat.zero_le ((x.val i).val))
  rw [hs, hk, x.property] at hsub
  exact ⟨by omega, by simpa only [Nat.mul_comm] using hsub⟩

theorem tieTotal_pos_iff (b q T k : ℕ) :
    0 < tieTotal b (q+1) T k ↔ k ≤ b ∧ (q+1)*k ≤ T ∧ T ≤ b*q+k := by
  constructor
  · intro h
    obtain ⟨hb, ht⟩ := tieTotal_pos_bounds b (q+1) T k h
    have he : (q+1)*k + (T-(q+1)*k) = T := by omega
    have hiff := tieStratum_feasible (b-k) q (T-(q+1)*k) k
    rw [Nat.sub_add_cancel hb, he] at hiff
    have hr := hiff.mp h
    have hm := congrArg (fun a : ℕ => a*q) (Nat.sub_add_cancel hb)
    exact ⟨hb, ht, by nlinarith⟩
  · rintro ⟨hb, ht, hu⟩
    have he : (q+1)*k + (T-(q+1)*k) = T := by omega
    have hiff := tieStratum_feasible (b-k) q (T-(q+1)*k) k
    rw [Nat.sub_add_cancel hb, he] at hiff
    apply hiff.mpr
    have hm := congrArg (fun a : ℕ => a*q) (Nat.sub_add_cancel hb)
    nlinarith

theorem tieTotal_pos_between (b q T i j k : ℕ)
    (hi : 0 < tieTotal b (q+1) T i) (hk : 0 < tieTotal b (q+1) T k)
    (hij : i ≤ j) (hjk : j ≤ k) : 0 < tieTotal b (q+1) T j := by
  obtain ⟨_, _, hiu⟩ := (tieTotal_pos_iff b q T i).mp hi
  obtain ⟨hkb, hkl, _⟩ := (tieTotal_pos_iff b q T k).mp hk
  exact (tieTotal_pos_iff b q T j).mpr ⟨by omega, le_trans (Nat.mul_le_mul_left _ hjk) hkl, by omega⟩

theorem tieMean_zero (b q T : ℕ) (F : (Fin b → ℕ) → ℚ) :
    tieMean b (q+1) T 0 F = cappedMean b q T F := by
  exact zeroTie_expectation_lowerCap b q T (fun x => F (fun i => (x.val i).val))

theorem tieMean_succ_symmetric (n q r k : ℕ) (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : ∀ (e : Equiv.Perm (Fin (n+1))) x, F (fun i => x (e i)) = F x) :
    tieMean (n+1) q (q+r) (k+1) F =
      tieMean n q r k (fun x => F (Fin.cons q x)) := by
  have h := tieStratum_expectation_delete n q r k
    (fun x => F (fun i => (x.val i).val)) (by
      intro e x
      simpa only [permuteCapped] using hF e (fun i => (x.val i).val))
  simpa only [tieMean, prependCapped_values] using h

theorem tieMean_succ (n q r k : ℕ) (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : SchurIncreasing F) :
    tieMean (n+1) q (q+r) (k+1) F =
      tieMean n q r k (fun x => F (Fin.cons q x)) :=
  tieMean_succ_symmetric n q r k F (schur_symmetric F hF)

theorem tieMean_zero_le_one (q : ℕ) (hA : ∀ b T, CappedAssociation b q T)
    (n r : ℕ) (hr : r+1 ≤ n*q) (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : SchurIncreasing F) :
    tieMean (n+1) (q+1) (q+1+r) 0 F ≤ tieMean (n+1) (q+1) (q+1+r) 1 F := by
  rw [tieMean_zero, tieMean_succ n (q+1) r 0 F hF, tieMean_zero]
  have hp := capped_pin_of_association n q (r+1) (hA _ _) hr F hF
  have he : q+(r+1) = q+1+r := by omega
  rw [he] at hp
  have hi := capped_vector_pinned_majorization n q (q+1+r) q (q+1)
    (by omega) (by omega) (by omega) (by omega) F
    (by intro x y _ _ h; exact hF x y h)
  have hleft : q+1+r-q = r+1 := by omega
  have hright : q+1+r-(q+1) = r := by omega
  rw [hleft, hright] at hi
  exact hp.trans hi

theorem tieMean_adjacent_of_lower_association (q : ℕ) (hA : ∀ b T, CappedAssociation b q T)
    (k b T : ℕ) (F : (Fin b → ℕ) → ℚ) (hF : SchurIncreasing F)
    (hk : 0 < tieTotal b (q+1) T k) (hl : 0 < tieTotal b (q+1) T (k+1)) :
    tieMean b (q+1) T k F ≤ tieMean b (q+1) T (k+1) F := by
  induction k generalizing b T with
  | zero =>
    obtain ⟨hb, ht⟩ := tieTotal_pos_bounds b (q+1) T 1 hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have hT : T = q+1+(T-(q+1)) := by omega
    rw [hT] at hk hl ⊢
    apply tieMean_zero_le_one q hA n (T-(q+1)) _ F hF
    have hu := ((tieTotal_pos_iff (n+1) q (q+1+(T-(q+1))) 0).mp hk).2.2
    nlinarith
  | succ k ih =>
    obtain ⟨hb, ht⟩ := tieTotal_pos_bounds b (q+1) T (k+1) hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have hqT : q+1 ≤ T := by nlinarith
    have hT : T = q+1+(T-(q+1)) := by omega
    rw [hT] at hk hl ⊢
    rw [tieMean_succ n (q+1) (T-(q+1)) k F hF,
      tieMean_succ n (q+1) (T-(q+1)) (k+1) F hF]
    exact ih n (T-(q+1)) (fun x => F (Fin.cons (q+1) x)) (schur_cons _ F hF)
      ((tieStratum_mass_pos_iff n (q+1) (T-(q+1)) k).mp hk)
      ((tieStratum_mass_pos_iff n (q+1) (T-(q+1)) (k+1)).mp hl)

theorem tieMean_regression_of_lower_association (q : ℕ) (hA : ∀ b T, CappedAssociation b q T)
    (b T : ℕ) (F : (Fin b → ℕ) → ℚ) (hF : SchurIncreasing F)
    (k l : ℕ) (hk : 0 < tieTotal b (q+1) T k) (hl : 0 < tieTotal b (q+1) T l)
    (hkl : k ≤ l) : tieMean b (q+1) T k F ≤ tieMean b (q+1) T l F := by
  induction l generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    exact le_rfl
  | succ l ih =>
    by_cases he : k = l+1
    · subst k; exact le_rfl
    · have hkl' : k ≤ l := by omega
      have hm := tieTotal_pos_between b q T k l (l+1) hk hl hkl' (by omega)
      exact (ih k hk hm hkl').trans
        (tieMean_adjacent_of_lower_association q hA l b T F hF hm hl)

end MatchingCapacity
