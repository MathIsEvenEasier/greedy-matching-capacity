import CappedPrefix
import Mathlib.Data.Finset.Lattice.Fold

/-! Tools for induction on the common cap. All association premises below
are explicit; this file alone does not prove the final association theorem. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity

def SchurIncreasing {n : ℕ} (F : (Fin n → ℕ) → ℚ) : Prop :=
  ∀ x y, LoadLE x y → F x ≤ F y

theorem schur_symmetric {n : ℕ} (F : (Fin n → ℕ) → ℚ) (hF : SchurIncreasing F)
    (e : Equiv.Perm (Fin n)) (x : Fin n → ℕ) : F (fun i => x (e i)) = F x := by
  apply le_antisymm
  · exact hF _ _ (loadLE_reindex x e)
  · have h := loadLE_reindex (fun i => x (e i)) e.symm
    simp only [Equiv.apply_symm_apply] at h
    exact hF _ _ h

theorem schur_cons {n : ℕ} (a : ℕ) (F : (Fin (n+1) → ℕ) → ℚ)
    (hF : SchurIncreasing F) : SchurIncreasing (fun x => F (Fin.cons a x)) := by
  intro x y hxy
  exact hF _ _ (loadLE_cons a x y hxy)

def schurCandidates {b q r : ℕ} (F : CappedLoad b q r → ℚ) (y : Fin b → ℕ) : Finset ℚ := by
  classical
  exact insert (-(∑ z, |F z|))
    ((Finset.univ.filter (fun z : CappedLoad b q r => LoadLE (fun i => (z.val i).val) y)).image F)

theorem schurCandidates_nonempty {b q r : ℕ} (F : CappedLoad b q r → ℚ) (y : Fin b → ℕ) :
    (schurCandidates F y).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

def schurExtension {b q r : ℕ} (F : CappedLoad b q r → ℚ) (y : Fin b → ℕ) : ℚ :=
  (schurCandidates F y).sup' (schurCandidates_nonempty F y) id

theorem schurExtension_mono {b q r : ℕ} (F : CappedLoad b q r → ℚ) :
    SchurIncreasing (schurExtension F) := by
  classical
  intro x y hxy
  apply Finset.sup'_le
  intro a ha
  apply Finset.le_sup' id
  rcases Finset.mem_insert.mp ha with he | he
  · exact Finset.mem_insert.mpr (Or.inl he)
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
      ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        loadLE_trans (Finset.mem_filter.mp hz).2 hxy⟩, rfl⟩))

theorem schurExtension_eq {b q r : ℕ} (F : CappedLoad b q r → ℚ)
    (hF : ∀ x y, LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val) → F x ≤ F y)
    (x : CappedLoad b q r) : schurExtension F (fun i => (x.val i).val) = F x := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    rcases Finset.mem_insert.mp ha with he | he
    · subst a
      have h : |F x| ≤ ∑ z, |F z| :=
        Finset.single_le_sum (fun z _ => abs_nonneg (F z)) (Finset.mem_univ x)
      exact (neg_le_neg h).trans (neg_abs_le _)
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
      exact hF z x (Finset.mem_filter.mp hz).2
  · apply Finset.le_sup' id
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, loadLE_refl _⟩, rfl⟩))

theorem maxCount_mono {b q r : ℕ} (x y : CappedLoad b q r)
    (hxy : LoadLE (fun i => (x.val i).val) (fun i => (y.val i).val)) :
    maxCount x ≤ maxCount y := by
  classical
  let s := Finset.univ.filter (fun i => (x.val i).val = q)
  obtain ⟨t, ht, hst⟩ := hxy s
  have hs : (∑ i ∈ s, (x.val i).val) = s.card * q := by
    calc
      _ = ∑ _i ∈ s, q := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
      _ = _ := by simp
  have hb : ∀ i ∈ t, (y.val i).val ≤ q := by
    intro i _
    exact Nat.le_of_lt_succ (y.val i).isLt
  have he : (∑ i ∈ t, (y.val i).val) = ∑ _i ∈ t, q := by
    apply le_antisymm (Finset.sum_le_sum hb)
    simpa only [Finset.sum_const, smul_eq_mul, ht, hs] using hst
  have hi := (Finset.sum_eq_sum_iff_of_le hb).mp he
  have hsub : t ⊆ Finset.univ.filter (fun i => (y.val i).val = q) := by
    intro i hit
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi i hit⟩
  change s.card ≤ _
  rw [← ht]
  exact Finset.card_le_card hsub

theorem capped_sizeBias_eq_maximum {b q r : ℕ} :
    sizeBias (cappedWeight (b := b) (q := q) (r := r)) (fun x => (maxCount x : ℚ)) =
    sizeBias maximumWeight (fun x => (maxCount x : ℚ)) := by
  funext x
  by_cases h : 0 < maxCount x
  · simp only [sizeBias, maximumWeight, ite_eq_left h]
  · have hz : maxCount x = 0 := by omega
    simp [sizeBias, maximumWeight, hz]

theorem expectation_le_bias_of_covariance {Ω : Type*} [Fintype Ω] (w l f : Ω → ℚ)
    (hZ : 0 < total w) (hL : 0 < moment w l) (hcov : CovNonneg w l f) :
    expectation w f ≤ expectation (sizeBias w l) f := by
  have hm : moment (sizeBias w l) f = moment w (fun x => l x * f x) := by
    simp only [moment, sizeBias, mul_assoc]
  unfold expectation
  rw [show total (sizeBias w l) = moment w l from rfl, hm]
  apply (div_le_div_iff₀ hZ hL).mpr
  unfold CovNonneg at hcov
  nlinarith

theorem capped_pin_of_association (n q r : ℕ)
    (hA : CappedAssociation (n+1) q (q+r)) (hr : r ≤ n*q)
    (F : (Fin (n+1) → ℕ) → ℚ) (hF : SchurIncreasing F) :
    cappedMean (n+1) q (q+r) F ≤ cappedMean n q r (fun x => F (Fin.cons q x)) := by
  let f := fun x : CappedLoad (n+1) q (q+r) => F (fun i => (x.val i).val)
  have hZ := (maximum_mass_pos_iff n q r).mpr hr
  have hL : 0 < moment (cappedWeight (b := n+1) (q := q) (r := q+r))
      (fun x => (maxCount x : ℚ)) := by
    change 0 < total (sizeBias cappedWeight (fun x : CappedLoad (n+1) q (q+r) => (maxCount x : ℚ)))
    rw [capped_sizeBias_eq_maximum]
    exact maximum_tie_mass_pos hZ
  have hcap : 0 < total (cappedWeight (b := n+1) (q := q) (r := q+r)) :=
    (capped_total_pos_iff (n+1) q (q+r)).mpr (by nlinarith)
  have hc := hA (fun x => (maxCount x : ℚ)) f
    (by intro x y h; exact Nat.cast_le.mpr (maxCount_mono x y h))
    (by intro x y h; exact hF _ _ h)
  have h := expectation_le_bias_of_covariance cappedWeight _ f hcap hL hc
  rw [capped_sizeBias_eq_maximum,
    tieBias_expectation_delete n q r f (by
      intro e x
      simpa only [f, permuteCapped] using schur_symmetric F hF e (fun i => (x.val i).val))] at h
  simpa only [cappedMean, f, prependCapped_values] using h

theorem covariance_iff_mean {Ω : Type*} [Fintype Ω] (w f g : Ω → ℚ)
    (hw : ∀ x, 0 ≤ w x) (hZ : 0 < total w) :
    CovNonneg w f g ↔ expectation w f * expectation w g ≤ expectation w (fun x => f x*g x) := by
  rw [CovNonneg, moment_eq_total_mul_expectation w f hw,
    moment_eq_total_mul_expectation w g hw,
    moment_eq_total_mul_expectation w (fun x => f x*g x) hw]
  have hp : 0 < total w * total w := mul_pos hZ hZ
  constructor <;> intro h <;> nlinarith

theorem covariance_of_fiber_association {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w f g : Ω → ℚ) (c : Ω → κ) (hw : ∀ x, 0 ≤ w x)
    (hfib : ∀ k, 0 < total (fiberWeight w c k) → CovNonneg (fiberWeight w c k) f g)
    (hreg : ∀ i j, 0 < total (fiberWeight w c i) → 0 < total (fiberWeight w c j) →
      0 ≤ (expectation (fiberWeight w c i) f - expectation (fiberWeight w c j) f) *
        (expectation (fiberWeight w c i) g - expectation (fiberWeight w c j) g)) :
    CovNonneg w f g := by
  have h := covariance_on_support (fun k => total (fiberWeight w c k))
    (fun k => expectation (fiberWeight w c k) f) (fun k => expectation (fiberWeight w c k) g)
    (fun k => total_nonneg _ (fiberWeight_nonneg w c hw k)) hreg
  have hi := moment_mono_on_support (fun k => total (fiberWeight w c k))
    (fun k => expectation (fiberWeight w c k) f * expectation (fiberWeight w c k) g)
    (fun k => expectation (fiberWeight w c k) (fun x => f x*g x))
    (fun k => total_nonneg _ (fiberWeight_nonneg w c hw k))
    (fun k hk => (covariance_iff_mean _ f g (fiberWeight_nonneg w c hw k) hk).mp (hfib k hk))
  have hz := total_nonneg (fun k => total (fiberWeight w c k))
    (fun k => total_nonneg _ (fiberWeight_nonneg w c hw k))
  have hh := le_trans h (mul_le_mul_of_nonneg_left hi hz)
  simpa only [CovNonneg, fiber_mass_total, fiber_mean_moment w f c hw, fiber_mean_moment w g c hw,
    fiber_mean_moment w (fun x => f x*g x) c hw] using hh

end MatchingCapacity
