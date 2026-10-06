import FiniteQuantile
import CoarseWaiting

/-! A finite first-success law, with index N reserved for no success.
All masses are rational and the terminal atom is included. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def survivalProduct (f : ℕ → ℚ) (t : ℕ) : ℚ := ∏ j ∈ Finset.range t, f j

def finiteWaitMass (f : ℕ → ℚ) (N i : ℕ) : ℚ :=
  if i < N then survivalProduct f i * (1-f i)
  else if i = N then survivalProduct f N else 0

theorem survivalProduct_zero (f : ℕ → ℚ) : survivalProduct f 0 = 1 := by
  simp [survivalProduct]

theorem survivalProduct_succ (f : ℕ → ℚ) (t : ℕ) :
    survivalProduct f (t+1) = survivalProduct f t * f t := Finset.prod_range_succ _ _

theorem survivalProduct_nonneg (f : ℕ → ℚ) (hf : ∀ j, 0 ≤ f j) (t : ℕ) :
    0 ≤ survivalProduct f t := Finset.prod_nonneg (fun j _ => hf j)

theorem survivalProduct_le_one (f : ℕ → ℚ) (h0 : ∀ j, 0 ≤ f j)
    (h1 : ∀ j, f j ≤ 1) (t : ℕ) : survivalProduct f t ≤ 1 := by
  induction t with
  | zero => simp [survivalProduct]
  | succ t ih =>
    rw [survivalProduct_succ]
    exact (mul_le_mul_of_nonneg_left (h1 t) (survivalProduct_nonneg f h0 t)).trans (by simpa using ih)

theorem survivalProduct_mono (f g : ℕ → ℚ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ g j) (t : ℕ) : survivalProduct f t ≤ survivalProduct g t := by
  induction t with
  | zero => simp [survivalProduct]
  | succ t ih =>
    rw [survivalProduct_succ, survivalProduct_succ]
    exact mul_le_mul ih (hfg t) (hf t) (le_trans (survivalProduct_nonneg f hf t) ih)

theorem finiteWaitMass_nonneg (f : ℕ → ℚ) (h0 : ∀ j, 0 ≤ f j)
    (h1 : ∀ j, f j ≤ 1) (N i : ℕ) : 0 ≤ finiteWaitMass f N i := by
  unfold finiteWaitMass
  split_ifs
  · exact mul_nonneg (survivalProduct_nonneg f h0 i) (sub_nonneg.mpr (h1 i))
  · exact survivalProduct_nonneg f h0 N
  · exact le_rfl

theorem finiteWaitMass_cdf (f : ℕ → ℚ) (N k : ℕ) (hk : k ≤ N) :
    cumMass (finiteWaitMass f N) k = 1-survivalProduct f k := by
  induction k with
  | zero => simp [prefix_zero, survivalProduct_zero]
  | succ k ih =>
    rw [prefix_succ, ih (by omega), finiteWaitMass, ite_eq_left (by omega), survivalProduct_succ]
    ring

theorem finiteWaitMass_probability (f : ℕ → ℚ) (N : ℕ) :
    cumMass (finiteWaitMass f N) (N+1) = 1 := by
  rw [prefix_succ, finiteWaitMass_cdf f N N le_rfl]
  simp only [finiteWaitMass, lt_self_iff_false, ite_false, ite_true]
  ring

theorem finiteWaitMass_cdf_order (f g : ℕ → ℚ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ g j) (N k : ℕ) (hk : k ≤ N+1) :
    cumMass (finiteWaitMass g N) k ≤ cumMass (finiteWaitMass f N) k := by
  by_cases h : k ≤ N
  · rw [finiteWaitMass_cdf f N k h, finiteWaitMass_cdf g N k h]
    exact sub_le_sub_left (survivalProduct_mono f g hf hfg k) 1
  · have he : k = N+1 := by omega
    subst k
    rw [finiteWaitMass_probability, finiteWaitMass_probability]

theorem finite_waiting_coupling (f g : ℕ → ℚ) (hf : ∀ j, 0 ≤ f j)
    (hg : ∀ j, g j ≤ 1) (hfg : ∀ j, f j ≤ g j) (N : ℕ) :
    ∃ c : Fin (N+1) → Fin (N+1) → ℚ,
      (∀ i j, 0 ≤ c i j) ∧ (∀ i, ∑ j, c i j = finiteWaitMass f N i.val) ∧
      (∀ j, ∑ i, c i j = finiteWaitMass g N j.val) ∧
      (∀ i j, j < i → c i j = 0) :=
  ordered_quantile_coupling _ _
    (finiteWaitMass_nonneg f hf (fun j => (hfg j).trans (hg j)) N)
    (finiteWaitMass_nonneg g (fun j => (hf j).trans (hfg j)) hg N)
    (N+1) (finiteWaitMass_probability f N) (finiteWaitMass_probability g N)
    (finiteWaitMass_cdf_order f g hf hfg N)

end MatchingCapacity
