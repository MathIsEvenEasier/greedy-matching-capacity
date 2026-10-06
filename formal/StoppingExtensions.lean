import StoppingJointLaw

/-! Histories between consecutive acceptances consist exactly of a fixed
prefix, rejection outcomes, and one final accepted destination. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

theorem historyTake_rejectExtension (h : Fin n → Option (Fin m)) (t : ℕ) :
    historyTake (rejectExtension h t) n (Nat.le_add_right n t) = h := by
  funext j
  exact rejectExtension_prefix h t j

theorem historyTake_acceptedExtension (h : Fin n → Option (Fin m)) (t : ℕ) (k : Fin m) :
    historyTake (acceptedExtension h t k) n (by omega) = h := by
  rw [acceptedExtension, historyTake_snoc _ _ (Nat.le_add_right n t), historyTake_rejectExtension]

theorem acceptedCount_prefix_le (h : Fin N → Option (Fin m)) (hn : n ≤ N) :
    acceptedCount (historyTake h n hn) ≤ acceptedCount h := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (n+t+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [historyTake_snoc g o (Nat.le_add_right n t), acceptedCount_snoc]
    exact (ih g (Nat.le_add_right n t)).trans (Nat.le_add_right _ _)

theorem same_count_rejectExtension (t : ℕ) (h : Fin (n+t) → Option (Fin m))
    (hc : acceptedCount h = acceptedCount (historyTake h n (Nat.le_add_right n t))) :
    h = rejectExtension (historyTake h n (Nat.le_add_right n t)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (n+t+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [historyTake_snoc g o (Nat.le_add_right n t)] at hc ⊢
    rw [acceptedCount_snoc] at hc
    have hb := acceptedCount_prefix_le g (Nat.le_add_right n t)
    cases o with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false, add_zero] at hc
      rw [rejectExtension, ← ih g hc]
    | some k =>
      simp only [Option.isSome_some, ite_true] at hc
      omega

theorem consecutive_hit_extension (t K a b : ℕ) (h : Fin (n+t+1) → Option (Fin m))
    (hold : stoppingState q h K = some (n,a))
    (hnext : stoppingState q h (K+1) = some (n+t+1,b)) :
    ∃ g : Fin n → Option (Fin m), ∃ k : Fin m,
      AcceptedPrefix q K a g ∧ h = acceptedExtension g t k := by
  have hp := (stoppingState_prefix_iff h (by omega : n ≤ n+t+1) K a).mp hold
  have he := (stoppingState_at_end h (K+1) b).mp hnext
  obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (n+t+1) => Option (Fin m))).surjective h
  change Fin.snoc g o = h at hg
  subst h
  rw [acceptedPrefix_snoc] at he
  rw [historyTake_snoc g o (Nat.le_add_right n t)] at hp
  cases o with
  | none => simp at he
  | some k =>
    have hc : acceptedCount g = K := by
      have hh := he.1
      rw [acceptedCount_snoc] at hh
      simp only [Option.isSome_some, ite_true] at hh
      omega
    have hg := same_count_rejectExtension t g (hc.trans hp.1.symm)
    refine ⟨historyTake g n (Nat.le_add_right n t),k,hp,?_⟩
    rw [acceptedExtension, ← hg]

theorem acceptedExtension_old_hit (h : Fin n → Option (Fin m)) (t K a : ℕ) (k : Fin m) :
    stoppingState q (acceptedExtension h t k) K = some (n,a) ↔ AcceptedPrefix q K a h := by
  rw [stoppingState_prefix_iff _ (by omega : n ≤ n+t+1), historyTake_acceptedExtension]

theorem acceptedExtension_next_hit (h : Fin n → Option (Fin m)) (t K b : ℕ) (k : Fin m) :
    stoppingState q (acceptedExtension h t k) (K+1) = some (n+t+1,b) ↔
      acceptedCount h = K ∧ (historyFullBins q (acceptedExtension h t k)).card = b := by
  rw [stoppingState_at_end]
  unfold acceptedExtension
  rw [acceptedPrefix_snoc, acceptedCount_snoc, rejectExtension_accepted_count]
  simp

theorem never_next_rejectExtension (t K a : ℕ) (h : Fin (n+t) → Option (Fin m))
    (hold : stoppingState q h K = some (n,a)) (hnext : stoppingState q h (K+1) = none) :
    h = rejectExtension (historyTake h n (Nat.le_add_right n t)) t := by
  have hp := (stoppingState_prefix_iff h (Nat.le_add_right n t) K a).mp hold
  have hn := (stoppingState_none_iff h (K+1)).mp hnext
  apply same_count_rejectExtension
  have hb := acceptedCount_prefix_le h (Nat.le_add_right n t)
  have hc := hp.1
  omega

theorem rejectExtension_old_hit (h : Fin n → Option (Fin m)) (t K a : ℕ) :
    stoppingState q (rejectExtension h t) K = some (n,a) ↔ AcceptedPrefix q K a h := by
  rw [stoppingState_prefix_iff _ (Nat.le_add_right n t), historyTake_rejectExtension]

theorem rejectExtension_next_none (h : Fin n → Option (Fin m)) (t K a : ℕ)
    (hp : AcceptedPrefix q K a h) : stoppingState q (rejectExtension h t) (K+1) = none := by
  rw [stoppingState_none_iff, rejectExtension_accepted_count, hp.1]
  omega

theorem stoppingState_strict_times (h : Fin N → Option (Fin m)) (K s a u b : ℕ)
    (hs : stoppingState q h K = some (s,a)) (hu : stoppingState q h (K+1) = some (u,b)) : s < u := by
  have hsN := (stoppingState_bounds h K s a hs).1
  have huN := (stoppingState_bounds h (K+1) u b hu).1
  have hp := ((stoppingState_prefix_iff h hsN K a).mp hs).1
  have hq := ((stoppingState_prefix_iff h huN (K+1) b).mp hu).1
  by_contra he
  have hus : u ≤ s := by omega
  have hc := acceptedCount_prefix_le (historyTake h s hsN) hus
  rw [historyTake_trans, hp, hq] at hc
  omega

end MatchingCapacity
