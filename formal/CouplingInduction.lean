import FiniteJointPush

/-! Finite coupling composition on positive pairs only. Exact marginal
updates suffice; no Markov hypothesis on an underlying process is used. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {ι : Type*} [Fintype ι]

def HasRelCoupling (R : ι → ι → Prop) (p q : ι → ℚ) : Prop :=
  ∃ c : ι → ι → ℚ, (∀ s t, 0 ≤ c s t) ∧ (∀ s, ∑ t, c s t = p s) ∧
    (∀ t, ∑ s, c s t = q t) ∧ (∀ s t, ¬ R s t → c s t = 0)

theorem coupling_diagonal [DecidableEq ι] (R : ι → ι → Prop) (o : ι) (ho : R o o) :
    HasRelCoupling R (fun s => if s = o then 1 else 0) (fun t => if t = o then 1 else 0) := by
  refine ⟨fun s t => if s = o ∧ t = o then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro s t
    dsimp only
    split_ifs <;> norm_num
  · intro s
    by_cases h : s = o <;> simp [h]
  · intro t
    by_cases h : t = o <;> simp [h]
  · intro s t h
    by_cases he : s = o ∧ t = o
    · exact False.elim (h (by simpa only [he.1,he.2] using ho))
    · exact ite_eq_right he

theorem coupling_step (R : ι → ι → Prop) (p q : ι → ℚ) (P Q : ι → ι → ℚ)
    (hc : HasRelCoupling R p q)
    (hstep : ∀ s t, 0 < p s → 0 < q t → R s t → HasRelCoupling R (P s) (Q t)) :
    HasRelCoupling R (fun u => ∑ s, p s * P s u) (fun v => ∑ t, q t * Q t v) := by
  obtain ⟨c,hc0,hrow,hcol,hsupp⟩ := hc
  have hh : ∀ s t, 0 < c s t → HasRelCoupling R (P s) (Q t) := by
    intro s t h
    have hp : 0 < p s := by
      rw [← hrow s]
      exact h.trans_le (Finset.single_le_sum (fun j _ => hc0 s j) (Finset.mem_univ t))
    have hq : 0 < q t := by
      rw [← hcol t]
      exact h.trans_le (Finset.single_le_sum (fun i _ => hc0 i t) (Finset.mem_univ s))
    have hr : R s t := by
      by_contra hn
      rw [hsupp s t hn] at h
      exact lt_irrefl 0 h
    exact hstep s t hp hq hr
  let d := fun s t (h : 0 < c s t) => Classical.choose (hh s t h)
  have hd := fun s t (h : 0 < c s t) => Classical.choose_spec (hh s t h)
  let e := fun s t u v => if h : 0 < c s t then c s t * d s t h u v else 0
  have ez : ∀ s t, ¬ 0 < c s t → c s t = 0 := fun s t h => le_antisymm (le_of_not_gt h) (hc0 s t)
  have er : ∀ s t u, (∑ v, e s t u v) = c s t * P s u := by
    intro s t u
    by_cases h : 0 < c s t
    · simp only [e, dite_eq_left h, ← Finset.mul_sum]
      exact congrArg (fun z => c s t * z) ((hd s t h).2.1 u)
    · simp [e,ez s t h]
  have ec : ∀ s t v, (∑ u, e s t u v) = c s t * Q t v := by
    intro s t v
    by_cases h : 0 < c s t
    · simp only [e, dite_eq_left h, ← Finset.mul_sum]
      exact congrArg (fun z => c s t * z) ((hd s t h).2.2.1 v)
    · simp [e,ez s t h]
  have en : ∀ s t u v, 0 ≤ e s t u v := by
    intro s t u v
    dsimp only [e]
    split_ifs with h
    · exact mul_nonneg (hc0 s t) ((hd s t h).1 u v)
    · exact le_rfl
  have es : ∀ s t u v, ¬ R u v → e s t u v = 0 := by
    intro s t u v hbad
    dsimp only [e]
    split_ifs with h
    · have hz : d s t h u v = 0 := (hd s t h).2.2.2 u v hbad
      rw [hz, mul_zero]
    · rfl
  refine ⟨fun u v => ∑ s, ∑ t, e s t u v, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun t _ => en s t u v))
  · intro u
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    simp only [er, ← Finset.sum_mul, hrow]
  · intro v
    calc
      (∑ u, ∑ s, ∑ t, e s t u v) = ∑ s, ∑ t, ∑ u, e s t u v := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
      _ = ∑ t, q t * Q t v := by
        simp only [ec]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, hcol]
  · intro u v hbad
    simp only [es _ _ u v hbad, Finset.sum_const_zero]

end MatchingCapacity
