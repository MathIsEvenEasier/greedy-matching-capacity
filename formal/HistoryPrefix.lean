import CoarseHistorySupport

/-! Exact prefix marginalization for the original finite history law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

def historyTake (h : Fin N → Option (Fin m)) (n : ℕ) (hn : n ≤ N) : Fin n → Option (Fin m) :=
  fun j => h (Fin.castLE hn j)

theorem historyTake_self (h : Fin n → Option (Fin m)) : historyTake h n le_rfl = h := by
  rfl

theorem historyTake_snoc (h : Fin N → Option (Fin m)) (o : Option (Fin m))
    (hn : n ≤ N) :
    historyTake (Fin.snoc h o) n (hn.trans (Nat.le_succ N)) = historyTake h n hn := by
  funext j
  dsimp only [historyTake]
  have he : Fin.castLE (hn.trans (Nat.le_succ N)) j = (Fin.castLE hn j).castSucc := rfl
  rw [he, Fin.snoc_castSucc]

theorem historyTake_trans (h : Fin N → Option (Fin m)) (hn : n ≤ N)
    (s : ℕ) (hs : s ≤ n) : historyTake (historyTake h n hn) s hs = historyTake h s (hs.trans hn) := by
  rfl

theorem history_prefix_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (t : ℕ)
    (F : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : Fin (n+t) → Option (Fin m), historyWeight (fun j => L j.val) q h *
      F (historyTake h n (Nat.le_add_right n t))) =
      ∑ h : Fin n → Option (Fin m), historyWeight (fun j => L j.val) q h * F h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    trans (∑ p : Option (Fin m) × (Fin (n+t) → Option (Fin m)),
      historyWeight (fun j => L j.val) q (Fin.snoc p.2 p.1) *
        F (historyTake (Fin.snoc p.2 p.1) n (Nat.le_add_right n (t+1))))
    · exact ((Fin.snocEquiv (fun _ : Fin (n+t+1) => Option (Fin m))).sum_comp
        (fun h => historyWeight (fun j => L j.val) q h * F (historyTake h n (Nat.le_add_right n (t+1))))).symm
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [historyWeight_snoc, historyTake_snoc _ _ (Nat.le_add_right n t), Fin.val_castSucc, Fin.val_last]
      have he : ∀ h : Fin (n+t) → Option (Fin m),
          (∑ o, historyWeight (fun j => L j.val) q h * L (n+t) (historyAvailable q h (n+t)) o *
            F (historyTake h n (Nat.le_add_right n t))) =
          historyWeight (fun j => L j.val) q h * F (historyTake h n (Nat.le_add_right n t)) := by
        intro h
        calc
          _ = (historyWeight (fun j => L j.val) q h * F (historyTake h n (Nat.le_add_right n t))) *
              ∑ o, L (n+t) (historyAvailable q h (n+t)) o := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro o _
            ring
          _ = _ := by rw [hL, mul_one]
      simp only [he]
      exact ih

theorem history_prefix_moment_le (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hn : n ≤ N)
    (F : (Fin n → Option (Fin m)) → ℚ) :
    (∑ h : Fin N → Option (Fin m), historyWeight (fun j => L j.val) q h * F (historyTake h n hn)) =
      ∑ h : Fin n → Option (Fin m), historyWeight (fun j => L j.val) q h * F h := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact history_prefix_moment L hL t F

theorem history_prefix_event (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A, ∑ o, L j A o = 1) (hn : n ≤ N)
    (P : (Fin n → Option (Fin m)) → Prop) :
    (∑ h : Fin N → Option (Fin m), if P (historyTake h n hn) then historyWeight (fun j => L j.val) q h else 0) =
      ∑ h : Fin n → Option (Fin m), if P h then historyWeight (fun j => L j.val) q h else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using
    history_prefix_moment_le (q := q) L hL hn (fun h => if P h then 1 else 0)

end MatchingCapacity
