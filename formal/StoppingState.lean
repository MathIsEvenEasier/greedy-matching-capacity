import HistoryPrefix

/-! The actual Kth-acceptance state of each finite history. None is the
never-reached outcome; level zero is the deterministic state (0,0). -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {N n m q : ℕ}

def stoppingState (q : ℕ) : {N : ℕ} → (Fin N → Option (Fin m)) → ℕ → Option (ℕ × ℕ)
  | 0, _, K => if K = 0 then some (0,0) else none
  | N+1, h, K =>
      if acceptedCount h = K ∧ (h (Fin.last N)).isSome = true then
        some (N+1,(historyFullBins q h).card)
      else stoppingState q (Fin.init h) K

theorem stoppingState_empty (h : Fin 0 → Option (Fin m)) (K : ℕ) :
    stoppingState q h K = if K = 0 then some (0,0) else none := rfl

theorem stoppingState_snoc (h : Fin n → Option (Fin m)) (o : Option (Fin m)) (K : ℕ) :
    stoppingState q (Fin.snoc h o) K =
      if acceptedCount (Fin.snoc h o) = K ∧ o.isSome = true then
        some (n+1,(historyFullBins q (Fin.snoc h o)).card) else stoppingState q h K := by
  simp only [stoppingState, Fin.snoc_last, Fin.init_snoc]

theorem stoppingState_none_iff (h : Fin N → Option (Fin m)) (K : ℕ) :
    stoppingState q h K = none ↔ acceptedCount h < K := by
  induction N with
  | zero => simp [stoppingState, acceptedCount]
  | succ N ih =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [stoppingState_snoc, acceptedCount_snoc]
    cases o with
    | none => simpa using ih g
    | some k =>
      simp only [Option.isSome_some, ite_true, and_true]
      split_ifs with he
      · simp [he]
      · simp only [ih g]
        omega

theorem stoppingState_zero (h : Fin N → Option (Fin m)) : stoppingState q h 0 = some (0,0) := by
  induction N with
  | zero => simp [stoppingState]
  | succ N ih =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [stoppingState_snoc, acceptedCount_snoc]
    cases o <;> simpa using ih g

theorem stoppingState_bounds (h : Fin N → Option (Fin m)) (K s a : ℕ)
    (hh : stoppingState q h K = some (s,a)) : s ≤ N ∧ a ≤ m := by
  induction N with
  | zero =>
    simp only [stoppingState] at hh
    split_ifs at hh with hk
    · cases hh
      omega
  | succ N ih =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [stoppingState_snoc] at hh
    split_ifs at hh with ht
    · have he := Option.some.inj hh
      have hs := congrArg Prod.fst he
      have ha := congrArg Prod.snd he
      dsimp only at hs ha
      subst s
      subst a
      exact ⟨le_rfl, (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)⟩
    · exact ⟨(ih g hh).1.trans (Nat.le_succ N), (ih g hh).2⟩

theorem acceptedPrefix_snoc (h : Fin n → Option (Fin m)) (o : Option (Fin m)) (K a : ℕ) :
    AcceptedPrefix q K a (Fin.snoc h o) ↔
      acceptedCount (Fin.snoc h o) = K ∧ (historyFullBins q (Fin.snoc h o)).card = a ∧ o.isSome = true := by
  unfold AcceptedPrefix
  constructor
  · rintro ⟨hc,ha,hl⟩
    exact ⟨hc,ha,by simpa using hl (Fin.last n) rfl⟩
  · rintro ⟨hc,ha,hl⟩
    refine ⟨hc,ha,?_⟩
    intro j hj
    have he : j = Fin.last n := Fin.ext (by simpa using Nat.add_right_cancel hj)
    simpa [he] using hl

theorem stoppingState_at_end (h : Fin N → Option (Fin m)) (K a : ℕ) :
    stoppingState q h K = some (N,a) ↔ AcceptedPrefix q K a h := by
  cases N with
  | zero =>
    simp [stoppingState, AcceptedPrefix, acceptedCount, historyFullBins, historyLoad]; omega
  | succ N =>
    obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Option (Fin m))).surjective h
    change Fin.snoc g o = h at hg
    subst h
    rw [stoppingState_snoc, acceptedPrefix_snoc]
    split_ifs with ht
    · simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      tauto
    · have hn : stoppingState q g K ≠ some (N+1,a) := by
        intro hh
        have hb := (stoppingState_bounds g K (N+1) a hh).1
        omega
      simp only [hn, false_iff]
      tauto

theorem stoppingState_persists (h : Fin n → Option (Fin m)) (o : Option (Fin m)) (K s a : ℕ)
    (hh : stoppingState q h K = some (s,a)) : stoppingState q (Fin.snoc h o) K = some (s,a) := by
  have hK : K ≤ acceptedCount h := by
    by_contra hk
    have hn := (stoppingState_none_iff (q := q) h K).mpr (by omega)
    rw [hh] at hn
    contradiction
  rw [stoppingState_snoc]
  have hn : ¬ (acceptedCount (Fin.snoc h o) = K ∧ o.isSome = true) := by
    rw [acceptedCount_snoc]
    cases o with
    | none => simp
    | some k =>
      simp only [Option.isSome_some, ite_true, and_true]
      omega
  rw [ite_eq_right hn]
  exact hh

theorem stoppingState_prefix_iff (h : Fin N → Option (Fin m)) (hn : n ≤ N) (K a : ℕ) :
    stoppingState q h K = some (n,a) ↔ AcceptedPrefix q K a (historyTake h n hn) := by
  induction N with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simpa only [historyTake_self] using stoppingState_at_end (q := q) h K a
  | succ N ih =>
    by_cases he : n = N+1
    · subst n
      simpa only [historyTake_self] using stoppingState_at_end (q := q) h K a
    · have hn' : n ≤ N := by omega
      obtain ⟨⟨o,g⟩,hg⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Option (Fin m))).surjective h
      change Fin.snoc g o = h at hg
      subst h
      rw [historyTake_snoc g o hn', ← ih g hn']
      constructor
      · intro hh
        rw [stoppingState_snoc] at hh
        split_ifs at hh with ht
        · have hs := congrArg (fun x => x.map Prod.fst) hh
          simp only [Option.map_some, Option.some.injEq] at hs
          omega
        · exact hh
      · exact stoppingState_persists g o K n a

end MatchingCapacity
