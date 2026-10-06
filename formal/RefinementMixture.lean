import CoarseRefinement
import FiniteMixture

/-! All canonical pieces of one accepted-count prefix event share one
capped-multinomial reference. Null pieces contribute zero to every moment. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace MatchingCapacity
open Classical
variable {n m q : ℕ}

def referenceHazard (b q r : ℕ) : ℚ :=
  expectation (cappedWeight (b := b) (q := q) (r := r)) (fun x => (maxCount x : ℚ)) / (b : ℚ)

theorem key_uniform_reference (r : GoodRefinement n m q) (K a : ℕ)
    (hp : KeyPrefix q K a r.val) (ha : a < m) :
    nextSaturationProbability (uniformRows (ι := ResidualJobs r.val.2.1) (Fintype.card (ResidualBins r.val.1)))
      (fun _ => 1/(Fintype.card (ResidualBins r.val.1) : ℚ)) q = referenceHazard (m-a) q (K-a*(q+1)) := by
  obtain ⟨hb,hj⟩ := key_prefix_counts r K a hp
  have hpos : 0 < Fintype.card (ResidualBins r.val.1) := by rw [hb]; omega
  rw [uniform_saturation_reference hpos]
  change referenceHazard (Fintype.card (ResidualBins r.val.1)) q (Fintype.card (ResidualJobs r.val.2.1)) = _
  rw [hb,hj]

theorem fiber_next_mass_nonneg (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (r : GoodRefinement n m q) (t : ℕ) :
    0 ≤ fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun _ _ => 1) := by
  unfold fiberNextMoment
  exact Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun k _ =>
    mul_nonneg (historyWeight_nonneg _ (fun j A o => hL j.val A o) q _) (by norm_num)))

theorem fiber_next_null_moment (L : ℕ → Finset (Fin m) → Option (Fin m) → ℚ)
    (hL : ∀ j A o, 0 ≤ L j A o) (r : GoodRefinement n m q) (t : ℕ)
    (hz : fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t (fun _ _ => 1) = 0)
    (G : (Fin n → Option (Fin m)) → ResidualBins r.val.1 → ℚ) :
    fiberNextMoment L q r.val.1 r.val.2.1 r.val.2.2 t G = 0 := by
  let w (h : KeyFiber q r.val) (k : ResidualBins r.val.1) :=
    historyWeight (fun j => L j.val) q (acceptedExtension h.val t k.val)
  have hw : ∀ h k, 0 ≤ w h k := fun h k =>
    historyWeight_nonneg _ (fun j A o => hL j.val A o) q _
  have hs : (∑ h : KeyFiber q r.val, ∑ k : ResidualBins r.val.1, w h k) = 0 := by
    simpa only [fiberNextMoment, mul_one] using hz
  have hh := finite_zero_mass (fun h => ∑ k, w h k)
    (fun h => Finset.sum_nonneg (fun k _ => hw h k)) hs
  unfold fiberNextMoment
  apply Finset.sum_eq_zero
  intro h _
  exact finite_null_moment (w h) (G h.val) (hw h) (hh h)

theorem key_rv_saturation (degree : ℕ → ℕ) (r : GoodRefinement n m q) (K a t : ℕ)
    (hp : KeyPrefix q K a r.val) (ha : a < m)
    (hm : 0 < fiberNextMoment (fun j => rvKernel (degree j)) q r.val.1 r.val.2.1 r.val.2.2 t (fun _ _ => 1)) :
    fiberNextSaturation (fun j => rvKernel (degree j)) q r.val.1 r.val.2.1 r.val.2.2 t =
      referenceHazard (m-a) q (K-a*(q+1)) := by
  have hb : 0 < Fintype.card (ResidualBins r.val.1) := by rw [(key_prefix_counts r K a hp).1]; omega
  rw [rv_next_success_saturation_reference degree r.val.1 r.val.2.1 r.val.2.2 r.property.1 hb r.property.2.2 t hm]
  exact key_uniform_reference r K a hp ha

theorem key_ranking_saturation (degree : ℕ → ℕ) (r : GoodRefinement n m q) (K a t : ℕ)
    (hp : KeyPrefix q K a r.val) (ha : a < m)
    (hm : 0 < fiberNextMoment (fun j => rankingKernel (degree j)) q r.val.1 r.val.2.1 r.val.2.2 t (fun _ _ => 1)) :
    referenceHazard (m-a) q (K-a*(q+1)) ≤
      fiberNextSaturation (fun j => rankingKernel (degree j)) q r.val.1 r.val.2.1 r.val.2.2 t := by
  have hb : 0 < Fintype.card (ResidualBins r.val.1) := by rw [(key_prefix_counts r K a hp).1]; omega
  rw [← key_uniform_reference r K a hp ha]
  exact ranking_next_success_saturation_bound degree r.val.1 r.val.2.1 r.val.2.2 r.property.1 hb r.property.2.2 t hm

end MatchingCapacity
