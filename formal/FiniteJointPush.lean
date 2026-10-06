import FiniteMixture

/-! Pushforward of a finite rational joint law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [DecidableEq γ] [DecidableEq δ]

def jointPush (g : α → β → ℚ) (f : α → γ) (h : β → δ) (u : γ) (v : δ) : ℚ :=
  ∑ x, ∑ y, if f x = u ∧ h y = v then g x y else 0

theorem jointPush_nonneg (g : α → β → ℚ) (hg : ∀ x y, 0 ≤ g x y)
    (f : α → γ) (h : β → δ) (u : γ) (v : δ) : 0 ≤ jointPush g f h u v := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact hg x y
  · rfl

theorem jointPush_row [Fintype δ] (g : α → β → ℚ) (f : α → γ) (h : β → δ) (u : γ) :
    (∑ v, jointPush g f h u v) = ∑ x, ∑ y, if f x = u then g x y else 0 := by
  unfold jointPush
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = u <;> simp [hx]

theorem jointPush_column [Fintype γ] (g : α → β → ℚ) (f : α → γ) (h : β → δ) (v : δ) :
    (∑ u, jointPush g f h u v) = ∑ x, ∑ y, if h y = v then g x y else 0 := by
  unfold jointPush
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : h y = v <;> simp [hy]

theorem jointPush_support (g : α → β → ℚ) (f : α → γ) (h : β → δ)
    (R : α → β → Prop) (S : γ → δ → Prop)
    (hg : ∀ x y, ¬ R x y → g x y = 0) (hm : ∀ x y, R x y → S (f x) (h y))
    (u : γ) (v : δ) (hs : ¬ S u v) : jointPush g f h u v = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_cases hh : f x = u ∧ h y = v
  · rw [ite_eq_left hh]
    apply hg x y
    intro hr
    have hv := hm x y hr
    rw [hh.1,hh.2] at hv
    exact hs hv
  · exact ite_eq_right hh

end MatchingCapacity
