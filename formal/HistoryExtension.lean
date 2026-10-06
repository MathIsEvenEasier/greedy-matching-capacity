import HistorySaturation
import WaitingKernel

/-! Appending actual rejection outcomes leaves loads unchanged and gives
the exact first-success path product, rather than a postulated waiting law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def rejectExtension (h : Fin n → Option (Fin m)) : (t : ℕ) → Fin (n+t) → Option (Fin m)
  | 0 => h
  | t+1 => Fin.snoc (rejectExtension h t) none

def acceptedExtension (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m) :
    Fin (n+t+1) → Option (Fin m) := Fin.snoc (rejectExtension h t) (some k)

theorem rejectExtension_prefix (h : Fin n → Option (Fin m)) (t : ℕ) (j : Fin n) :
    rejectExtension h t (Fin.castAdd t j) = h j := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [rejectExtension, Fin.snoc_castAdd] using ih

theorem rejectExtension_injective (t : ℕ) :
    Function.Injective (fun h : Fin n → Option (Fin m) => rejectExtension h t) := by
  intro h g he
  funext j
  have hh := congrFun he (Fin.castAdd t j)
  simpa only [rejectExtension_prefix] using hh

theorem acceptedExtension_injective (t : ℕ) :
    Function.Injective (fun x : (Fin n → Option (Fin m)) × Fin m => acceptedExtension x.1 t x.2) := by
  intro x y he
  obtain ⟨hh,hk⟩ := Fin.snoc_inj.mp he
  exact Prod.ext (rejectExtension_injective t hh) (Option.some.inj hk)

theorem rejectExtension_final_load (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m) :
    historyLoad (rejectExtension h t) (n+t) k = historyLoad h n k := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change historyLoad (Fin.snoc (rejectExtension h t) none) (n+t+1) k = _
    rw [historyLoad_snoc_final, ih]
    simp

theorem rejectExtension_availability (h : Fin n → Option (Fin m)) (t : ℕ) :
    historyAvailable q (rejectExtension h t) (n+t) = historyAvailable q h n := by
  ext k
  simp only [historyAvailable, Finset.mem_filter, Finset.mem_univ, true_and, rejectExtension_final_load]

theorem rejectExtension_weight (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (h : Fin n → Option (Fin m)) (t : ℕ) :
    historyWeight (fun j => K j.val) q (rejectExtension h t) =
      historyWeight (fun j => K j.val) q h * waitingWeight K (historyAvailable q h n) n t := by
  induction t with
  | zero => simp [rejectExtension, waitingWeight]
  | succ t ih =>
    rw [rejectExtension, historyWeight_snoc]
    simp only [Fin.val_castSucc, Fin.val_last]
    change historyWeight (fun j => K j.val) q (rejectExtension h t) *
      K (n+t) (historyAvailable q (rejectExtension h t) (n+t)) none = _
    rw [rejectExtension_availability (q := q) h t, ih, waitingWeight_succ]
    ring

theorem acceptedExtension_weight (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m) :
    historyWeight (fun j => K j.val) q (acceptedExtension h t k) =
      historyWeight (fun j => K j.val) q h * waitingWeight K (historyAvailable q h n) n t *
        K (n+t) (historyAvailable q h n) (some k) := by
  rw [acceptedExtension, historyWeight_snoc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [rejectExtension_availability, rejectExtension_weight]

theorem acceptedExtension_fiber_weight (K : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (D : Finset (Fin m)) (J : Finset (Fin n)) (f : Fin n → Option (Fin m))
    (hD : ∀ k ∈ D, historyLoad (fixedHistory J f) n k = q+1)
    (h : historyFiber q D J f) (t : ℕ) (k : Fin m) :
    historyWeight (fun j => K j.val) q (acceptedExtension h.val t k) =
      historyWeight (fun j => K j.val) q h.val * waitingWeight K Dᶜ n t * K (n+t) Dᶜ (some k) := by
  rw [acceptedExtension_weight, history_fiber_final_availability D J f hD h]

end MatchingCapacity
