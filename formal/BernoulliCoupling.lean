import FiniteQuantile

/-! Explicit rational coupling for ordered zero/one increments. -/
set_option autoImplicit false
open scoped BigOperators
namespace MatchingCapacity

def bernoulliMass (p : ℚ) (b : Bool) : ℚ := if b then p else 1-p

def bernoulliJoint (p q : ℚ) (b c : Bool) : ℚ :=
  match b,c with
  | false,false => 1-q
  | false,true => q-p
  | true,false => 0
  | true,true => p

theorem bernoulliMass_nonneg (p : ℚ) (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) :
    0 ≤ bernoulliMass p b := by cases b <;> simp [bernoulliMass] <;> linarith

theorem bernoulliMass_probability (p : ℚ) : ∑ b : Bool, bernoulliMass p b = 1 := by
  simp [bernoulliMass]

theorem bernoulliJoint_nonneg (p q : ℚ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    (b c : Bool) : 0 ≤ bernoulliJoint p q b c := by
  cases b <;> cases c <;> simp only [bernoulliJoint] <;> linarith

theorem bernoulliJoint_row (p q : ℚ) (b : Bool) :
    (∑ c : Bool, bernoulliJoint p q b c) = bernoulliMass p b := by
  cases b <;> simp [bernoulliJoint, bernoulliMass]

theorem bernoulliJoint_column (p q : ℚ) (c : Bool) :
    (∑ b : Bool, bernoulliJoint p q b c) = bernoulliMass q c := by
  cases c <;> simp [bernoulliJoint, bernoulliMass]

theorem bernoulliJoint_ordered (p q : ℚ) (b c : Bool) (h : c.toNat < b.toNat) :
    bernoulliJoint p q b c = 0 := by
  cases b <;> cases c <;> simp_all [bernoulliJoint]

theorem unequal_counts_stay_ordered (a b : ℕ) (hab : a < b) (x y : Bool) :
    a+x.toNat ≤ b+y.toNat := by
  cases x <;> cases y <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

end MatchingCapacity
